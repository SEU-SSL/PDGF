/*
    Identify the predecessor basic blocks
*/

#include "SVF-FE/LLVMUtil.h"
#include "Graphs/SVFG.h"
#include "WPA/Andersen.h"
#include "SABER/LeakChecker.h"
#include "SVF-FE/PAGBuilder.h"
#include "llvm/IR/CFG.h"
#include <fstream>
#include <sstream>

using namespace SVF;
using namespace llvm;
using namespace std;

SVFModule *svfModule;
ICFG *icfg;
Module *M;
LLVMContext *C;
int pre_edges = 0;

ofstream pbb_outfile("premake_results.txt", std::ios::out);
ofstream pe_outfile("pre_edges.txt", std::ios::out);

static llvm::cl::opt<std::string> InputFilename(cl::Positional,
                                                llvm::cl::desc("<input bitcode>"), llvm::cl::init("-"));

static llvm::cl::opt<std::string> TargetsFile("targets", llvm::cl::desc("specify the targets in program."),
                                              llvm::cl::Required);

std::string getDebugInfo(BasicBlock *bb)
{
    for (BasicBlock::iterator it = bb->begin(), eit = bb->end(); it != eit; ++it)
    {
        Instruction *inst = &(*it);
        std::string str = SVFUtil::getSourceLoc(inst);
        if (str != "{  }" && str.find("ln: 0  cl: 0") == str.npos)
            return str;
    }
    return "{ }";
}

std::string getDebugInfo_const(const BasicBlock *bb)
{
    for (BasicBlock::const_iterator it = bb->begin(), eit = bb->end(); it != eit; ++it)
    {
        const Instruction *inst = &(*it);
        std::string str = SVFUtil::getSourceLoc(inst);
        if (str != "{  }" && str.find("ln: 0  cl: 0") == str.npos)
            return str;
    }
    return "{ }";
}

std::vector<NodeID> loadTargets(std::string filename)
{
    ifstream inFile(filename);
    if (!inFile)
    {
        std::cerr << "can't open target file!" << std::endl;
        exit(1);
    }
    std::cout << "--  Loading targets  --" << std::endl;
    std::vector<NodeID> target_NodeID;
    std::vector<std::pair<std::string, u32_t>> targets;
    std::string line;
    while (getline(inFile, line))
    {
        std::string func;
        uint32_t num;
        std::string comma_string;
        std::istringstream text_stream(line);
        getline(text_stream, func, ':');
        text_stream >> num;
        targets.push_back(make_pair(func, num));
    }

    // itreate all basic block and located target NodeID
    for (SVFModule::iterator iter = svfModule->begin(), eiter = svfModule->end(); iter != eiter; ++iter)
    {
        const SVFFunction *fun = *iter;
        Function *F = fun->getLLVMFun();
        std::string file_name = "";
        if (llvm::DISubprogram *SP = F->getSubprogram())
        {
            if (SP->describes(F))
                file_name = (SP->getFilename()).str();
        }
        bool flag = false;
        for (auto target : targets)
        {
            auto idx = file_name.find(target.first);
            if (idx != string::npos)
            {
                flag = true;
                break;
            }
        }
        if (!flag)
            continue;

        for (Function::iterator bit = fun->getLLVMFun()->begin(), ebit = fun->getLLVMFun()->end(); bit != ebit; ++bit)
        {
            BasicBlock *bb = &(*bit);
            std::string tmp_string = getDebugInfo(bb);
            for (BasicBlock::iterator it = bb->begin(), eit = bb->end(); it != eit; ++it)
            {
                uint32_t line_num = 0;
                Instruction *inst = &(*it);
                std::string str = SVFUtil::getSourceLoc(inst);
                // if (str != "{  }" && str.find("ln: 0  cl: 0") == str.npos) {

                if (SVFUtil::isa<AllocaInst>(inst))
                {
                    for (llvm::DbgInfoIntrinsic *DII : FindDbgAddrUses(const_cast<Instruction *>(inst)))
                    {
                        if (llvm::DbgDeclareInst *DDI = SVFUtil::dyn_cast<llvm::DbgDeclareInst>(DII))
                        {
                            llvm::DIVariable *DIVar = SVFUtil::cast<llvm::DIVariable>(DDI->getVariable());
                            line_num = DIVar->getLine();
                        }
                    }
                }
                else if (MDNode *N = inst->getMetadata("dbg"))
                {
                    llvm::DILocation *Loc = SVFUtil::cast<llvm::DILocation>(N);
                    line_num = Loc->getLine();
                }

                // if the line number match the one in targets
                for (auto target : targets)
                {
                    auto idx = file_name.find(target.first);
                    if (idx != string::npos && (idx == 0 || file_name[idx - 1] == '/'))
                    {
                        if (target.second == line_num)
                        {
                            target_NodeID.push_back(icfg->getBlockICFGNode(inst)->getId());
                        }
                    }
                }
            }
        }
    }
    inFile.close();
    return target_NodeID;
}

std::vector<ICFGNode *> traverseOnICFG(ICFG *icfg, std::vector<NodeID> target_NodeID)
{
    std::set<ICFGNode *> pre_ICFGNode;
    std::cout << "--  Traversing on iCFG  --" << std::endl;
    for (NodeID id : target_NodeID)
    {
        ICFGNode *iNode = icfg->getICFGNode(id);
        FIFOWorkList<const ICFGNode *> worklist;
        worklist.push(iNode);
        while (!worklist.empty())
        {
            const ICFGNode *iNode = worklist.pop();
            for (auto it = iNode->directInEdgeBegin(), eit = iNode->directInEdgeEnd();
                 it != eit; ++it)
            {
                pre_edges++;
                ICFGEdge *edge = *it;
                if (edge->getEdgeKind() == 2)
                    continue;
                ICFGNode *preNode = edge->getSrcNode();
                if (pre_ICFGNode.find(preNode) == pre_ICFGNode.end())
                {
                    pre_ICFGNode.insert(preNode);
                    worklist.push(preNode);
                }
            }
            // pre_edges_count=pre_edges_count+tmp_bbs.size()-1;
        }
    }
    return std::vector<ICFGNode *>(pre_ICFGNode.begin(), pre_ICFGNode.end());
}

// std::vector<ICFGNode *> traverseOnICFG(ICFG *icfg, std::vector<NodeID> target_NodeID)
// {
//     std::set<ICFGNode *> pre_ICFGNode;
//     std::cout << "--  Traversing on iCFG  --" << std::endl;

//     // first traverse on CG
//     FIFOWorkList<ICFGNode*> worklist;
//     std::set<ICFGNode*> CG_node;
//     for(NodeID id:target_NodeID){
//         ICFGNode *iNode = icfg->getICFGNode(id);
//         worklist.push(iNode);
//         CG_node.insert(iNode);
//     }

//     while(!worklist.empty()){
//         ICFGNode *iNode = worklist.pop();
//         FunEntryBlockNode *fNode = icfg->getFunEntryBlockNode(iNode->getFun());
//         for (auto it = fNode->InEdgeBegin(), eit = fNode->InEdgeEnd();
//              it != eit; ++it)
//         {
//             ICFGEdge *edge = *it;
//             ICFGNode *srcNode = edge->getSrcNode();
//             if(CG_node.find(srcNode)==CG_node.end()){
//                 CG_node.insert(srcNode);
//                 worklist.push(srcNode);
//             }
//         }
//     }

//     // then traverse on CFG

//     for (NodeID id : target_NodeID)
//     {
//         ICFGNode *iNode = icfg->getICFGNode(id);
//         FIFOWorkList<const ICFGNode *> worklist;
//         worklist.push(iNode);
//         while (!worklist.empty())
//         {
//             const ICFGNode *iNode = worklist.pop();
//             for (ICFGNode::const_iterator it = iNode->InEdgeBegin(), eit =
//                                                                          iNode->InEdgeEnd();
//                  it != eit; ++it)
//             {
//                 pre_edges++;
//                 ICFGEdge *edge = *it;
//                 ICFGNode *preNode = edge->getSrcNode();
//                 if (pre_ICFGNode.find(preNode) == pre_ICFGNode.end())
//                 {
//                     pre_ICFGNode.insert(preNode);
//                     worklist.push(preNode);
//                 }
//             }
//             // pre_edges_count=pre_edges_count+tmp_bbs.size()-1;
//         }
//     }
//     return std::vector<ICFGNode *>(pre_ICFGNode.begin(), pre_ICFGNode.end());
// }

void outputResult(std::vector<ICFGNode *> pre_ICFGNode)
{
    std::cout << "-- Output the results --" << endl;
    std::set<string> output_pbb_str;
    for (auto node : pre_ICFGNode)
    {
        string strNode = getDebugInfo_const(node->getBB());
        if (strNode.find("fl:") != strNode.npos && strNode.find("ln:") != strNode.npos)
        {
            string out_str;
            if (strNode.find('/') != string::npos)
                out_str += strNode.substr(strNode.find_last_of('/') + 1, strNode.find_last_of(' ') - strNode.find_last_of('/') - 1);
            else
                out_str += strNode.substr(strNode.find_last_of('fl:') + 2, strNode.find_last_of(' ') - strNode.find_last_of('fl:') - 2);

            out_str += ',';

            if (strNode.find("  cl") != strNode.npos)
                out_str += strNode.substr(strNode.find("ln:") + 4, strNode.find("  cl") - strNode.find("ln:") - 4);
            else
                out_str += strNode.substr(strNode.find("ln:") + 4, strNode.find(" fl") - strNode.find("ln:") - 4);

            output_pbb_str.insert(out_str);
        }
    }
    for (auto s : output_pbb_str)
    {
        pbb_outfile << s << endl;
    }
    pbb_outfile.close();
}

int main(int argc, char **argv)
{
    int arg_num = 0;
    char **arg_value = new char *[argc];
    std::vector<std::string> moduleNameVec;
    SVFUtil::processArguments(argc, argv, arg_num, arg_value, moduleNameVec);
    cl::ParseCommandLineOptions(arg_num, arg_value,
                                "Identify the predecessor basic blocks\n");

    svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(moduleNameVec);

    icfg = new ICFG();
    ICFGBuilder builder(icfg);
    builder.build(svfModule);

    M = LLVMModuleSet::getLLVMModuleSet()->getMainLLVMModule();
    C = &(LLVMModuleSet::getLLVMModuleSet()->getContext());

    std::vector<NodeID> target_NodeID = loadTargets(TargetsFile);

    std::vector<ICFGNode *> pre_ICFGNode = traverseOnICFG(icfg, target_NodeID);

    outputResult(pre_ICFGNode);

    pe_outfile << pre_edges;
    std::cout << "pre_edges is " << pre_edges << endl;
}
