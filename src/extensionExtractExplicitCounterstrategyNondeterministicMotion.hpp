#ifndef __EXTENSION_EXTRACT_COUNTERSTRATEGY_NONDETERMINISTIC_HPP
#define __EXTENSION_EXTRACT_COUNTERSTRATEGY_NONDETERMINISTIC_HPP

#include "gr1context.hpp"
#include <string>
#include <sstream>

/**
 * A class that computes an explicit state counterstrategy for an unrealizable specification
 */
template<class T> class XExtractExplicitCounterStrategyNondeterministicMotion : public T {
protected:
    // Inherited stuff used
    using T::mgr;
    using T::strategyDumpingData;
    using T::livenessGuarantees;
    using T::livenessAssumptions;
    using T::varVectorPre;
    using T::varVectorPost;
    using T::varCubePostOutput;
    using T::varCubePostInput;
    using T::varCubePreOutput;
    using T::varCubePreInput;
    using T::varCubePre;
    using T::varCubePost;
    using T::safetyEnv;
    using T::safetySys;
    using T::winningPositions;
    using T::initEnv;
    using T::initSys;
    using T::preVars;
    using T::postVars;
    using T::variableTypes;
    using T::variables;
    using T::variableNames;
    using T::realizable;
    using T::determinize;
    using T::postInputVars;
    using T::postOutputVars;
    using T::doesVariableInheritType;
    using T::robotBDD;

    // Own variables local to this plugin
    SlugsVectorOfVarBFs preMotionStateVars{PreMotionState,this};
    SlugsVectorOfVarBFs postMotionStateVars{PostMotionState,this};
    SlugsVectorOfVarBFs postControllerOutputVars{PostMotionControlOutput,this};
    SlugsVarCube varCubePostMotionState{PostMotionState,this};
    SlugsVarCube varCubePostControllerOutput{PostMotionControlOutput,this};
    SlugsVarCube varCubePreMotionState{PreMotionState,this};
    SlugsVarCube varCubePreControllerOutput{PreMotionControlOutput,this};

    BF failingPreAndPostConditions = mgr.constantFalse();
    // BF candidateWinningPreConditions = mgr.constantFalse();
    // BF candidateFailingPreConditions = mgr.constantFalse();

    std::vector<boost::tuple<unsigned int,BF> > foundCutConditions;

public:

    XExtractExplicitCounterStrategyNondeterministicMotion<T>(std::list<std::string> &filenames) : T(filenames) {}

/**
 * @brief Compute and print out (to stdout) an explicit-state counter strategy that is winning for
 *        the environment. The output is compatible with the old JTLV output of LTLMoP.
 *        This function requires that the unrealizability of the specification has already been
 *        detected and that the variables "strategyDumpingData" and
 *        "winningPositions" have been filled by the synthesis algorithm with meaningful data.
 * @param outputStream - Where the strategy shall be printed to.
 */
    
void computeAndPrintExplicitStateStrategy(std::ostream &outputStream) {

    failingPreAndPostConditions = mgr.constantFalse();
    foundCutConditions.clear();

    // We don't want any reordering from this point onwards, as
    // the BDD manipulations from this point onwards are 'kind of simple'.
    mgr.setAutomaticOptimisation(false);

    // List of states in existance so far. The first map
    // maps from a BF node pointer (for the pre variable valuation) and a goal
    // to a state number. The vector then contains the concrete valuation.
    std::map<std::pair<size_t, std::pair<unsigned int, unsigned int> >, unsigned int > lookupTableForPastStates;
    std::vector<BF> bfsUsedInTheLookupTable;
    std::list<std::pair<size_t, std::pair<unsigned int, unsigned int> > > todoList;

    
    // Prepare positional strategies for the individual goals
    std::vector<std::vector<BF> > positionalStrategiesForTheIndividualGoals(livenessAssumptions.size());
    for (unsigned int i=0;i<livenessAssumptions.size();i++) {
        std::cerr << i << "\n";
        BF casesCovered = mgr.constantFalse();
        std::vector<BF> strategyAllPost(livenessGuarantees.size()+1);
        for (unsigned int j=0;j<livenessGuarantees.size()+1;j++) {
            strategyAllPost[j] = mgr.constantFalse();
        }
        for (auto it = strategyDumpingData.begin();it!=strategyDumpingData.end();it++) {
            if (boost::get<0>(*it) == i) {
                //Have to cover each guarantee (since the winning strategy depends on which guarantee is being pursued)
                //Essentially, the choice of which guarantee to pursue can be thought of as a system "move".
                //The environment always to chooses that prevent the appropriate guarantee.
                BF newCases = boost::get<2>(*it).ExistAbstract(varCubePostMotionState) & !casesCovered;
                strategyAllPost[boost::get<1>(*it)] |= newCases & boost::get<2>(*it);
                casesCovered |= newCases;
                // BF_newDumpDot(*this,strategyAllPost[boost::get<1>(*it)],NULL,"/tmp/strategyAllPost.dot"); 
                // std::stringstream fname;
                // fname << "/tmp/strategyAllPost" << i << "by" << boost::get<1>(*it) << ".dot";
                // BF_newDumpDot(*this,strategyAllPost[boost::get<1>(*it)],NULL,fname.str());
            }
        }
        positionalStrategiesForTheIndividualGoals[i] = strategyAllPost;
    }

    // Prepare initial to-do list from the allowed initial states. Select a single initial input valuation.

    // TODO: Support for non-special-robotics semantics

    // special robot init semantics:
    // BF todoInit = (winningPositions & initEnv & initSys);// & robotBDD.ExistAbstract(varCubePost));
    // non-special robot init semantics:
    BF todoInit = (initEnv & initSys.Implies(winningPositions)) & safetySys & robotBDD;// & robotBDD.ExistAbstract(varCubePost));
    todoInit = determinize(todoInit,preVars); // choose one assignment from the winning set
    BF_newDumpDot(*this,initSys,NULL,"/tmp/initSys.dot"); 
    BF_newDumpDot(*this,todoInit,NULL,"/tmp/todoInit.dot");
    BF_newDumpDot(*this,safetyEnv,NULL,"/tmp/safetyEnv.dot");
    BF_newDumpDot(*this,safetySys,NULL,"/tmp/safetySys.dot");
    BF_newDumpDot(*this,!safetySys,NULL,"/tmp/negSafetySys.dot");
    int iter = 0;
    while (!(todoInit.isFalse())) {
        std::cerr << iter << "\n";
        BF concreteState = determinize(todoInit,preVars);
        
        //find which liveness guarantee is being prevented (finds the first liveness in order specified)
        // Note by Ruediger here: Removed "!livenessGuarantees[j]" as condition as it is non-positional
        unsigned int found_j_index = 0;
        for (unsigned int j=0;j<livenessGuarantees.size();j++) {
            if (!(concreteState & positionalStrategiesForTheIndividualGoals[0][j]).isFalse()) {
                found_j_index = j;
                std::cerr << "found_j_index " << found_j_index << "\n";
                std::pair<size_t, std::pair<unsigned int, unsigned int> > lookup = std::pair<size_t, std::pair<unsigned int, unsigned int> >(concreteState.getHashCode(),std::pair<unsigned int, unsigned int>(0,found_j_index));
                lookupTableForPastStates[lookup] = bfsUsedInTheLookupTable.size();
                bfsUsedInTheLookupTable.push_back(concreteState);
                todoList.push_back(lookup);
                break;
            }
            if (j==livenessGuarantees.size()-1) {
                // throw SlugsException(false,"Error: did not find a liveness guarantee!\n");
                std::cerr << "Warning: did not find a suitable liveness guarantee.\n";
            }
        }
        //from now on use the same initial input valuation (but consider all other initial output valuations)
        todoInit &= !concreteState;
    }

    // Extract strategy
    while (todoList.size()>0) {
        std::pair<size_t, std::pair<unsigned int, unsigned int> > current = todoList.front();
        todoList.pop_front();
        unsigned int stateNum = lookupTableForPastStates[current];
        BF currentPossibilities = bfsUsedInTheLookupTable[stateNum];
        std::cerr << "stateNum " << stateNum << "\n";

        // Print state information
        outputStream << "State " << stateNum << " with rank (" << current.second.first << "," << current.second.second << ") -> <";
        bool first = true;
        for (unsigned int i=0;i<variables.size();i++) {
            if (doesVariableInheritType(i,Pre)) {
                if (first) {
                    first = false;
                } else {
                    outputStream << ", ";
                }
                outputStream << variableNames[i] << ":";
                outputStream << (((currentPossibilities & variables[i]).isFalse())?"0":"1");
            }
        }

        outputStream << ">\n\tWith successors : ";
        first = true;

        // BF_newDumpDot(*this,currentPossibilities,NULL,"/tmp/currentPossibilities.dot");
        // std::stringstream fname;
        // fname << "/tmp/currentPossibilities" << stateNum << ".dot";
        // BF_newDumpDot(*this,currentPossibilities,NULL,fname.str());

        // Can we enforce a deadlock?
        BF possibilitiesAndRobotBDD = currentPossibilities & robotBDD;
        BF deadlockInput = mgr.constantTrue();
        int indx = 0;
        // bool deadlockFound = true;
        while (!possibilitiesAndRobotBDD.isFalse()) {
            // std::cerr << "  Command combination (dead chk) " << indx << "\n";
            // BF possibilitiesForThisInput = determinize(possibilitiesAndRobotBDD, postInputVars);
            BF possibilitiesForThisControl = determinize(possibilitiesAndRobotBDD, postControllerOutputVars);
            possibilitiesAndRobotBDD &= !possibilitiesForThisControl;//.ExistAbstract(varCubePostMotionState);
            deadlockInput &= (possibilitiesForThisControl & safetyEnv & !safetySys).ExistAbstract(varCubePostMotionState).ExistAbstract(varCubePostControllerOutput);
            // BF_newDumpDot(*this,deadlockInput,NULL,"/tmp/deadlockInput.dot");
            // std::stringstream fname;
            // fname << "/tmp/deadlockInput" << stateNum << "iter" << indx << ".dot";
            // BF_newDumpDot(*this,(possibilitiesForThisControl & safetyEnv & !safetySys),NULL,fname.str());
            // if (deadlockInput!=mgr.constantFalse()) {
            //     deadlockFound = true;
            //     break;
            // }
            // else {deadlockFound = false;}
            // std::cerr << "stateNum" << stateNum << "indx" << indx << "\n";
            indx++;
        }
        if (deadlockInput!=mgr.constantFalse()) {
            addDeadlocked(deadlockInput, current, bfsUsedInTheLookupTable,  lookupTableForPastStates, outputStream);
        } else {
            
            // No deadlock in sight -> Jump to a different liveness guarantee if necessary.
            while ((currentPossibilities & positionalStrategiesForTheIndividualGoals[current.second.first][current.second.second])==mgr.constantFalse()){
                std::cerr << "  New goal " << current.second.second << "\n";
                current.second.second = (current.second.second + 1) % livenessGuarantees.size();
                // std::stringstream fname;
                // fname << "/tmp/positionalStrategiesForTheIndividualGoalsEnvGoal" << current.second.first << "SysGoal" << current.second.second << ".dot";
                // BF_newDumpDot(*this,positionalStrategiesForTheIndividualGoals[current.second.first][current.second.second],NULL,fname.str());
            } 
            currentPossibilities &= positionalStrategiesForTheIndividualGoals[current.second.first][current.second.second];
            assert(currentPossibilities != mgr.constantFalse());
            BF remainingTransitions = currentPossibilities;

            // save any combination of pre variables and post inputs found that are not included in player 1's strategy and don't falsify the environment
            //TODO: for *all* post motion states? (by definition, any control output that is winning should produce motion states that are all winning)
            BF cutCandidate = safetyEnv & robotBDD & (!remainingTransitions.ExistAbstract(varCubePre)) & remainingTransitions.ExistAbstract(varCubePost);
            if (!cutCandidate.isFalse()) {
                foundCutConditions.push_back(boost::make_tuple(stateNum,cutCandidate));
            }
            
            // candidateWinningPreConditions |= robotBDD & (!remainingTransitions.ExistAbstract(varCubePre)) & remainingTransitions.ExistAbstract(varCubePost);
            // candidateFailingPreConditions |= remainingTransitions;  // (for debugging)
            // std::stringstream fname1;
            // fname1 << "/tmp/candidateWinning" << stateNum << ".dot";
            // BF_newDumpDot(*this,robotBDD & (!remainingTransitions.ExistAbstract(varCubePre)) & remainingTransitions.ExistAbstract(varCubePost),NULL,fname1.str());
            // std::stringstream fname2;
            // fname2 << "/tmp/remainingTransitions" << stateNum << ".dot";
            // BF_newDumpDot(*this,remainingTransitions,NULL,fname2.str());

            // Choose one next input and stick to it!
            remainingTransitions = determinize(remainingTransitions & safetyEnv & robotBDD, postInputVars);

            // Switching goals
            int indx = 0;
            while (!(remainingTransitions & safetySys).isFalse()) {
                // std::cerr << "  Command combination " << indx << "\n";
                BF safeTransition = remainingTransitions & safetySys;
                BF possibleNextControlsOverTheModel = determinize(safeTransition, postControllerOutputVars);

                // std::stringstream fname1;
                // fname1 << "/tmp/possibleNextControlsOverTheModel" << stateNum << "by" << indx << ".dot";
                // BF_newDumpDot(*this,possibleNextControlsOverTheModel,NULL,fname1.str());

                //Mark which controller output has been captured by this case. Use the same control for other successors
                BF controlCaptured = possibleNextControlsOverTheModel.ExistAbstract(varCubePostMotionState).ExistAbstract(varCubePostInput);
                remainingTransitions &= !controlCaptured;

                // pick a concrete postMotionState             
                BF newCombination = determinize(safetyEnv & possibleNextControlsOverTheModel, postMotionStateVars);

                // std::stringstream fname2;
                // fname2 << "/tmp/newCombination" << stateNum << "by" << indx << ".dot";
                // BF_newDumpDot(*this,newCombination,NULL,fname2.str());
                // BF_newDumpDot(*this,remainingTransitions,NULL,"/tmp/remainingTransitions.dot");
                indx++;

                // Jump as much forward  in the liveness assumption list as possible ("stuttering avoidance")
                unsigned int nextLivenessAssumption = current.second.first;
                bool firstTry = true;
                while (((nextLivenessAssumption != current.second.first) | firstTry) && !((livenessAssumptions[nextLivenessAssumption] & newCombination).isFalse())) {
                    nextLivenessAssumption  = (nextLivenessAssumption + 1) % livenessAssumptions.size();
                    firstTry = false;
                }
                
                // We don't need the pre information from the point onwards anymore.
                newCombination = newCombination.ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost);

                unsigned int tn;

                std::pair<size_t, std::pair<unsigned int, unsigned int> > target;

                target = std::pair<size_t, std::pair<unsigned int, unsigned int> >(newCombination.getHashCode(),std::pair<unsigned int, unsigned int>(nextLivenessAssumption, current.second.second));

                if (lookupTableForPastStates.count(target)==0) {
                    tn = lookupTableForPastStates[target] = bfsUsedInTheLookupTable.size();
                    bfsUsedInTheLookupTable.push_back(newCombination);
                    todoList.push_back(target);
                } else {
                    tn = lookupTableForPastStates[target];
                }

                // Print
                if (first) {
                    first = false;
                } else {
                    outputStream << ", ";
                }
                outputStream << tn;

            }
        }

        outputStream << "\n";
    }
    }


    //This function adds a new successor-less "state" that captures the deadlock-causing input values
    //The outputvalues are omitted (indeed, no valuation exists that satisfies the system safeties)
    //Format compatible with JTLV counterstrategy

    void addDeadlocked(BF targetPositionCandidateSet, std::pair<size_t, std::pair<unsigned int, unsigned int> > current, std::vector<BF> &bfsUsedInTheLookupTable, std::map<std::pair<size_t, std::pair<unsigned int, unsigned int> >, unsigned int > &lookupTableForPastStates, std::ostream &outputStream) {
    
    // find the deadlock state's predecessor and store it..
    unsigned int stateNum = lookupTableForPastStates[current];

    // BF_newDumpDot(*this,targetPositionCandidateSet,NULL,"/tmp/targetPositionCandidateSet.dot");
    BF newCombination = determinize(targetPositionCandidateSet, postVars) ;
    // BF_newDumpDot(*this,newCombination,NULL,"/tmp/newCombinationAddDeadocked.dot");
    newCombination = newCombination.ExistAbstract(varCubePreControllerOutput).SwapVariables(varVectorPre,varVectorPost);
    
    
    std::pair<size_t, std::pair<unsigned int, unsigned int> > target = std::pair<size_t, std::pair<unsigned int, unsigned int> >(newCombination.getHashCode(),std::pair<unsigned int, unsigned int>(current.second.first, current.second.second));
    unsigned int tn;

    BF failingPostInputs = newCombination.ExistAbstract(varCubePreControllerOutput).ExistAbstract(varCubePreMotionState).ExistAbstract(varCubePost).SwapVariables(varVectorPre,varVectorPost);
    BF failingPreCommandsAndMotionStates = bfsUsedInTheLookupTable[stateNum].ExistAbstract(varCubePost).ExistAbstract(varCubePreInput);
    failingPreAndPostConditions |= failingPostInputs & failingPreCommandsAndMotionStates;

    if (lookupTableForPastStates.count(target)==0) {
        tn = lookupTableForPastStates[target] = bfsUsedInTheLookupTable.size();
        bfsUsedInTheLookupTable.push_back(newCombination);   
        outputStream << tn << "\n";
        
        //Note that since we are printing here, we usually end up with the states being printed out of order.
        //TOTO: print in order
        outputStream << "State " << tn << " with rank (" << current.second.first << "," << current.second.second << ") -> <";
        bool first = true;
        for (unsigned int i=0;i<variables.size();i++) {
            if (doesVariableInheritType(i,PreInput)) {
                if (first) {
                    first = false;
                } else {
                    outputStream << ", ";
                }
                outputStream << variableNames[i] << ":";
                outputStream << (((newCombination & variables[i]).isFalse())?"0":"1");
            }
        }
        outputStream << ">\n\tWith no successors.";
    
    } else {
        tn = lookupTableForPastStates[target];
        outputStream << tn;
    }
    
}


    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XExtractExplicitCounterStrategyNondeterministicMotion<T>(filenames);
    }
};

#endif

