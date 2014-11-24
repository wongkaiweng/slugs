#ifndef __EXTENSION_REFINE_ASSUMPTIONS_NONDETERMINISTIC_INTERACT_HPP
#define __EXTENSION_REFINE_ASSUMPTIONS_NONDETERMINISTIC_INTERACT_HPP

#include "gr1context.hpp"
#include <map>
#include <string>
#include <boost/algorithm/string.hpp>

/**
 * This extension modifies the execute() function ...
 */
template<class T> class XInteractiveRefineAssumptionsForNondeterministicMotion : public T {
protected:

    // Inherit stuff that we actually use here.
    using T::realizable;
    using T::variables;
    using T::variableTypes;
    using T::variableNames;
    using T::checkRealizability;
    using T::determinize;
    using T::doesVariableInheritType;
    using T::mgr;
    using T::varCubePre;
    using T::varCubePost;
    using T::varCubePostInput;
    using T::varCubePostOutput;
    using T::varCubePreInput;
    using T::varCubePreOutput;
    using T::preVars;
    using T::postVars;
    using T::postOutputVars;
    using T::livenessAssumptions;
    using T::livenessGuarantees;
    using T::safetyEnv;
    using T::safetySys;
    using T::initEnv;
    using T::initSys;
    using T::varVectorPre;
    using T::varVectorPost;
    using T::robotBDD;
    using T::strategyDumpingData;
    using T::winningPositions;

    std::vector<std::pair<unsigned int,BF> > strategyDumpingDataPlayer2;
    BF winningPositionsPlayer2;
    bool initSpecialRoboticsSemantics = false;

    SlugsVectorOfVarBFs preMotionStateVars{PreMotionState,this};
    SlugsVectorOfVarBFs postMotionStateVars{PostMotionState,this};
    SlugsVectorOfVarBFs preControllerOutputVars{PreMotionControlOutput,this};
    SlugsVectorOfVarBFs postControllerOutputVars{PostMotionControlOutput,this};
    SlugsVectorOfVarBFs preInputVars{PreInput,this};
    SlugsVectorOfVarBFs postInputVars{PostInput,this};
    SlugsVarCube varCubePostMotionState{PostMotionState,this};
    SlugsVarCube varCubePostControllerOutput{PostMotionControlOutput,this};
    SlugsVarCube varCubePreMotionState{PreMotionState,this};
    SlugsVarCube varCubePreControllerOutput{PreMotionControlOutput,this};

    BF failingPreAndPostConditions = mgr.constantFalse();
    std::vector<boost::tuple<unsigned int,BF> > foundCutConditions;

public:

    XInteractiveRefineAssumptionsForNondeterministicMotion<T>(std::list<std::string> &filenames) : T(filenames) {}

    BF randomDeterminize(BF in, std::vector<BF> vars) {
        for (auto it = vars.begin();it!=vars.end();it++) {
            if (rand() % 2) {
                BF res = in & !(*it);
                if (res.isFalse()) {
                    in = in & *it;
                } else {
                    in = res;
                }
            } else {
                BF res = in & *it;
                if (res.isFalse()) {
                    in = in & !(*it);
                } else {
                    in = res;
                }
            }
        }
        return in;
    }

    void execute() {
        T::execute();
        if (!realizable) {
            extractPatternsFromWinningStates();
        }

        BF_newDumpDot(*this,safetySys,NULL,"/tmp/safetySysBefore.dot");
        BF_newDumpDot(*this,safetyEnv,NULL,"/tmp/safetyEnvBefore.dot");

        // for (unsigned int i=0;i<livenessAssumptions.size();i++) {
        //     std::stringstream fname;
        //     fname << "/tmp/livenessAssumptionsBefore" << i << ".dot";
        //     BF_newDumpDot(*this,livenessAssumptions[i],NULL,fname.str());
        // }
        // for (unsigned int i=0;i<livenessGuarantees.size();i++) {
        //     std::stringstream fname;
        //     fname << "/tmp/livenessGuaranteesBefore" << i << ".dot";
        //     BF_newDumpDot(*this,livenessGuarantees[i],NULL,fname.str());
        // }

        int iter = 0;
        while (!failingPreAndPostConditions.isFalse()){ // & idx<=10){
            std::cerr << "adding safety assumptions/guarantees and re-synthesizing the counter-strategy\n";
            std::cerr << "major iter " << iter << "\n";
            std::stringstream fname;
            fname << "/tmp/failingPreAndPostConditions" << iter << ".dot";
            BF_newDumpDot(*this,failingPreAndPostConditions,NULL,fname.str());
            std::stringstream fname1;
            fname1 << "/tmp/safetySysBefore" << iter << ".dot";
            BF_newDumpDot(*this,safetySys,NULL,fname1.str());
            std::stringstream fname2;
            fname2 << "/tmp/safetyEnvBefore" << iter << ".dot";
            BF_newDumpDot(*this,safetyEnv,NULL,fname2.str());
            // BF_newDumpDot(*this,foundCutPostConditions,NULL,"/tmp/candidateWinningPreConditionsBefore.dot");

            BF TODO = failingPreAndPostConditions;
            int idx = 0;
            int counter = 0;
            bool foundRevisions = false;
            std::vector<double> xDecimalValue;
            std::vector<double> yDecimalValue;
            BF safetyEnvTent = mgr.constantTrue();
            BF safetySysTent = mgr.constantTrue();
            while (!TODO.isFalse()){
                BF deadAssignment = determinize(TODO,preControllerOutputVars);
                deadAssignment = determinize(deadAssignment,preMotionStateVars);
                TODO &= !deadAssignment;

                BF deadlockPre = deadAssignment.ExistAbstract(varCubePost);
                BF deadlockPost = deadAssignment.ExistAbstract(varCubePre);

                BF candidateEnvTrans = deadlockPre.Implies(!deadlockPost);
                BF candidateSysTrans = deadlockPost.Implies(!deadlockPre.SwapVariables(varVectorPre,varVectorPost));

                if (((safetyEnv.ExistAbstract(varCubePostInput)) & !((safetyEnv & candidateEnvTrans).ExistAbstract(varCubePostInput))).isFalse()) {
                    foundRevisions = true;
                    safetyEnvTent &= candidateEnvTrans;
                    safetySysTent &= candidateSysTrans;

                    BF flaggedMotion = deadlockPre.ExistAbstract(varCubePreControllerOutput);

                    xDecimalValue.push_back(0.0);
                    yDecimalValue.push_back(0.0);
                    int xCounter = 0;
                    int yCounter = 0;
                    double eta = 0.15;
                    for (unsigned int i=0;i<variables.size();i++) {
                        if (variableTypes[i]==PreMotionStateX) {
                            // std::cerr << "PreMotionStateX found at" << counter << " i" << i << "\n";
                            if (!(variables[i] & flaggedMotion).isFalse()) {
                                xDecimalValue[counter] += pow(2, xCounter) * eta;
                            }
                        }
                        if (variableTypes[i]==PreMotionStateY) {
                            // std::cerr << "PreMotionStateY found at" << counter << " i" << i << "\n";
                            if (!(variables[i] & flaggedMotion).isFalse()) {
                                yDecimalValue[counter] += pow(2, yCounter) * eta;
                            }
                        }
                    }
                    // std::cerr << "xDecimalValue[" << counter << "] " << xDecimalValue[counter] << "\n";
                    // std::cerr << "yDecimalValue[" << counter << "] " << yDecimalValue[counter] << "\n";

                    // std::stringstream fname3;
                    // fname3 << "/tmp/addedSafetyEnv" << iter << "index" << idx << ".dot";
                    // BF_newDumpDot(*this,candidateEnvTrans,NULL,fname3.str());
                    // std::stringstream fname4;
                    // fname4 << "/tmp/addedSafetySys" << iter << "index" << idx << ".dot";
                    // BF_newDumpDot(*this,candidateSysTrans,NULL,fname4.str());
                    // std::stringstream fname3;
                    // fname3 << "/tmp/safetyEnvAfter" << iter << "index" << idx << ".dot";
                    // BF_newDumpDot(*this,safetyEnv,NULL,fname3.str());
                    // std::stringstream fname4;
                    // fname4 << "/tmp/safetySysAfter" << iter << "index" << idx << ".dot";
                    // BF_newDumpDot(*this,safetySys,NULL,fname4.str());
                    
                    // std::cerr << idx << " ";
                    counter++;
                }
                idx++;
            }

            if (!foundRevisions) {throw SlugsException(false,"Error: could not find any refinements!\n");}
            std::cerr << "\n";

            double maxDist = 0.0;
            for (unsigned int i=0;i<counter;i++) {
                for (unsigned int j=0;j<counter;j++) {
                    double currDist = sqrt(pow(xDecimalValue[i] - xDecimalValue[j],2) + pow(yDecimalValue[i] - yDecimalValue[j],2));
                    if (currDist > maxDist) {maxDist = currDist;}
                }
            }

            // std::cerr << "Deadlock revisions found.\nWhen within " << maxDist << " of station_1, never set environment variable s1_occupied to True.\nAccept? (y/n)";
            char userResponse = 'y';
            // std::cin >> userResponse;
            if (userResponse == 'y') {
                safetySys &= safetySysTent;
                safetyEnv &= safetyEnvTent;
            }

            // prepare the variables for a new round of fixedpoint computations
            failingPreAndPostConditions = mgr.constantFalse();
            T::execute();
            if (!realizable) {
                extractPatternsFromWinningStates();
            }
            iter++;
        }

        BF_newDumpDot(*this,safetySys,NULL,"/tmp/safetySysAfter.dot");
        BF_newDumpDot(*this,safetyEnv,NULL,"/tmp/safetyEnvAfter.dot");

        // Mark states for which the counterstrategy has post inputs that are NOT winning for player 1, and enumerate those inputs.
        //   TODO: can do this post input quantification for the deadlock case also?
        BF candidateAll = mgr.constantFalse();
        BF candidateGuarAll = mgr.constantFalse();
        if (!realizable) {
        // if (false){
            std::cerr << "adding liveness assumptions and re-synthesizing the counter-strategy\n";
            // BF_newDumpDot(*this,candidateWinningPreConditions,NULL,"/tmp/candidateWinningPreConditions.dot");
            int iter = 0;
            for (auto it = foundCutConditions.begin();it!=foundCutConditions.end();it++) {
                std::cerr << "major iter " << iter << " for index " << boost::get<0>(*it) << "\n";
                BF newLivenessAssumptions = boost::get<1>(*it).ExistAbstract(varCubePostMotionState).ExistAbstract(varCubePostControllerOutput).ExistAbstract(varCubePreInput);
                
                std::stringstream fname;
                fname << "/tmp/newLivenessAssumptions" << iter << "p" << boost::get<0>(*it) << ".dot";
                BF_newDumpDot(*this,newLivenessAssumptions,NULL,fname.str());
                
                BF TODO = newLivenessAssumptions; 
                int idx = 0;
                while (!TODO.isFalse()) {
                    BF cutAssignment = determinize(TODO,preControllerOutputVars);
                    cutAssignment = determinize(cutAssignment,preMotionStateVars);
                    cutAssignment = determinize(cutAssignment,postInputVars);
                    TODO &= !cutAssignment;
                    BF cutPre = cutAssignment.ExistAbstract(varCubePost);
                    BF cutPost = cutAssignment.ExistAbstract(varCubePre);
                    // BF candidate = cutPre.Implies(cutPost);
                    BF candidate = cutPre & !cutPost;
                    int OKtoAdd = true;
                    if (!((safetySys & candidate.SwapVariables(varVectorPre,varVectorPost)).isFalse())){ // if the candidate satisfies the system transition
                        for (unsigned int i=0;i<livenessAssumptions.size();i++) {
                            if ((livenessAssumptions[i] & (!candidate)).isFalse()){ // if the new assumption is already in the list
                                // livenessAssumptions[i] &= candidate; //strengthen existing livenesses if needed, but don't append
                                OKtoAdd = false;
                                std::cerr << "didn't add a candidate assumption in " << boost::get<0>(*it) << ". It was redundant with liveness " << i << "\n";
                                break;
                            }
                            // if ((livenessAssumptions[i] & candidate).isFalse()){ // if the new assumption may falsfy the env
                            //     OKtoAdd = false;
                            //     break;
                            // }

                            // std::stringstream fname;
                            // fname << "/tmp/livenessAssumptions" << iter << "i" << i << ".dot";
                            // BF_newDumpDot(*this,livenessAssumptions[i],NULL,fname.str());
                        }
                    }
                    else {OKtoAdd = false;}
                    // std::stringstream fname;
                    // fname << "/tmp/newLivenessAssumptionsFalseSys" << boost::get<0>(*it) << ".dot";
                    // BF_newDumpDot(*this,(safetySys & candidate.SwapVariables(varVectorPre,varVectorPost)),NULL,fname.str());    
                    if (OKtoAdd){
                        // livenessAssumptions.push_back(candidate);
                        candidateAll |= candidate;
                        candidateGuarAll |= cutPre;
                        std::stringstream fname;
                        fname << "/tmp/addedLivenessAssumptions" << iter << "p" << boost::get<0>(*it) << "index" << idx << ".dot";
                        BF_newDumpDot(*this,candidate,NULL,fname.str());      
                    }
                    idx++;
                }
                // std::cerr << boost::get<0>(*it) << "\n";
                iter++;
            }
            livenessAssumptions.push_back(candidateAll); 
            livenessGuarantees.push_back(candidateGuarAll);
            // BF_newDumpDot(*this,livenessAssumptions.back(),NULL,"/tmp/livenessAssumptionsLast.dot");

            T::execute();
            if (!realizable) {
                extractPatternsFromWinningStates();
            }
        }   
        // livenessAssumptions.push_back(candidateWinningPreConditions);

        // check realizability; interact with the strategy
        checkRealizabilityPlayer2();
        if (realizable) {
            std::cerr << "RESULT: Specification is realizable.\n";
            computeInteractiveStrategy();
        } else {
            std::cerr << "RESULT: Specification is unrealizable.\n";
        }

    }

    void computeInteractiveStrategy() {
        std::vector<BF> positionalStrategiesForTheIndividualGoals(livenessGuarantees.size());
        for (unsigned int i=0;i<livenessGuarantees.size();i++) {
            BF casesCovered = mgr.constantFalse();
            BF strategy = mgr.constantFalse();
            for (auto it = strategyDumpingDataPlayer2.begin();it!=strategyDumpingDataPlayer2.end();it++) {
                if (it->first == i) {
                    BF newCases = it->second.ExistAbstract(varCubePostOutput) & !casesCovered;
                    strategy |= newCases & it->second;
                    casesCovered |= newCases;
                }
            }
            positionalStrategiesForTheIndividualGoals[i] = strategy;
            //BF_newDumpDot(*this,strategy,"PreInput PreOutput PostInput PostOutput","/tmp/generalStrategy.dot");
        }

        BF currentPosition = mgr.constantFalse();
        unsigned int currentLivenessGuarantee = 0;

        while(true) {

            // The prompt
            std::cout << "> ";
            std::cout.flush();
            std::string command = "";
            std::getline(std::cin,command);
            if (std::cin.eof()) return;
            // while (command=="") {
            //     std::getline(std::cin,command);
            //     if (std::cin.eof()) return;
            // }

            // Check the command
            boost::trim(command);
            boost::to_upper(command);

            if ((command=="QUIT") || (command=="EXIT")) {
                return;
            } else if (command=="STARTPOS") {
                // BF initialPosition = winningPositions & initEnv & initSys;
                BF initialPosition = initEnv.Implies(winningPositionsPlayer2 & initSys);
                assert(!(initialPosition.isFalse()));
                initialPosition = determinize(initialPosition,preVars);
                for (unsigned int i=0;i<variables.size();i++) {
                    if (doesVariableInheritType(i, Pre)) {
                        std::cout << " - " << variableNames[i] << ": ";
                        if ((variables[i] & initialPosition).isFalse()) {
                            std::cout << "0\n";
                        } else {
                            std::cout << "1\n";
                        }
                    }
                }
                currentPosition = initialPosition;
            } else if (command=="CHECKTRANS") {

                std::cout << "From: \n";
                BF from = mgr.constantTrue();
                for (unsigned int i=0;i<variables.size();i++) {
                    if ((variableTypes[i]==PreInput) || (variableTypes[i]==PreMotionState) || (variableTypes[i]==PreMotionControlOutput) || (variableTypes[i]==PreOtherOutput)  ) {
                        std::cout << " - " << variableNames[i] << ": ";
                        std::cout.flush();
                        int value;
                        std::cin >> value;
                        if (std::cin.fail()) {
                            std::cout << "    -> Error reading value. Assuming 0.\n";
                            value = 0;
                        }
                        if (value==0) {
                            from &= !variables[i];
                        } else if (value==1) {
                            from &= variables[i];
                        } else {
                            std::cout << "    -> Value != 0 or 1. Assuming 1.\n";
                            from &= variables[i];
                        }
                    }
                }

                std::cout << "To: \n";
                BF to = mgr.constantTrue();
                for (unsigned int i=0;i<variables.size();i++) {
                    if ((variableTypes[i]==PostInput) || (variableTypes[i]==PostMotionState) || (variableTypes[i]==PostMotionControlOutput) || (variableTypes[i]==PostOtherOutput)  ) {
                        std::cout << " - " << variableNames[i] << ": ";
                        std::cout.flush();
                        int value;
                        std::cin >> value;
                        if (std::cin.fail()) {
                            std::cout << "    -> Error reading value. Assuming 0.\n";
                            value = 0;
                        }
                        if (value==0) {
                            from &= !variables[i];
                        } else if (value==1) {
                            from &= variables[i];
                        } else {
                            std::cout << "    -> Value != 0 or 1. Assuming 1.\n";
                            from &= variables[i];
                        }
                    }
                }

                std::cout << "Result: \n";
                if ((from & winningPositionsPlayer2).isFalse()) {
                    std::cout << "- The pre-position is not winning.\n";
                } else {
                    std::cout << "- The pre-position is winning.\n";
                }
                if ((from & to & safetyEnv).isFalse()) {
                    std::cout << "- The transition VIOLATES the SAFETY ASSUMPTIONS\n";
                } else {
                    std::cout << "- The transition SATISFIES the SAFETY ASSUMPTIONS\n";
                }
                if ((from & to & safetySys).isFalse()) {
                    std::cout << "- The transition VIOLATES the SAFETY GUARANTEES\n";
                } else {
                    std::cout << "- The transition SATISFIES the SAFETY GUARANTEES\n";
                }
                if ((from & to & robotBDD).isFalse()) {
                    std::cout << "- The transition VIOLATES the ROBOT ABSTRACTION\n";
                } else {
                    std::cout << "- The transition SATISFIES the ROBOT ABSTRACTION\n";
                }
                std::cout << "- The transition is a goal transition for the following liveness assumptions: ";
                bool foundOne = false;
                for (unsigned int i=0;i<livenessAssumptions.size();i++) {
                    if (!(livenessAssumptions[i] & from & to).isFalse()) {
                        if (foundOne) std::cout << ", ";
                        foundOne = true;
                        std::cout << i;
                    }
                }
                if (!foundOne) std::cout << "none";
                std::cout << std::endl;
                std::cout << "- The transition is a goal transition for the following liveness guarantees: ";
                foundOne = false;
                for (unsigned int i=0;i<livenessGuarantees.size();i++) {
                    if (!(livenessGuarantees[i] & from & to).isFalse()) {
                        if (foundOne) std::cout << ", ";
                        foundOne = true;
                        std::cout << i;
                    }
                }
                if (!foundOne) std::cout << "none";
                std::cout << std::endl;

                // Analyse if it is part of a possible strategy
                std::cout << "- The transition is a possible transition in a strategy for the following goals: ";
                foundOne = false;
                for (unsigned int i=0;i<livenessGuarantees.size();i++) {
                    if (!(positionalStrategiesForTheIndividualGoals[i] & from & to).isFalse()) {
                        if (foundOne) std::cout << ", ";
                        foundOne = true;
                        std::cout << i;
                    }
                }
                if (!foundOne) std::cout << "none";
                std::cout << std::endl;

            } else if (command=="SETPOS") {

                std::cout << "Position: \n";
                BF from = mgr.constantTrue();
                for (unsigned int i=0;i<variables.size();i++) {
                    if ((variableTypes[i]==PreInput) || (variableTypes[i]==PreMotionState) || (variableTypes[i]==PreMotionControlOutput) || (variableTypes[i]==PreOtherOutput)  ) {                            std::cout << " - " << variableNames[i] << ": ";
                        std::cout.flush();
                        int value;
                        std::cin >> value;
                        if (std::cin.fail()) {
                            std::cout << "    -> Error reading value. Assuming 0.\n";
                            value = 0;
                        }
                        if (value==0) {
                            from &= !variables[i];
                        } else if (value==1) {
                            from &= variables[i];
                        } else {
                            std::cout << "    -> Value != 0 or 1. Assuming 1.\n";
                            from &= variables[i];
                        }
                    }
                }
                currentPosition = from;
            } 

            //========================================
            // Simplified functions to be called from
            // other tools.
            //========================================
            else if (command=="XMAKETRANS") {
                std::cout << "\n"; // Get rid of the prompt
                BF postInput = mgr.constantTrue();
                for (unsigned int i=0; i<variables.size(); i++) {
                    if (variableTypes[i]==PostInput) {
                        char c;
                        std::cin >> c;
                        if (c=='0') {
                            postInput &= !variables[i];
                        } else if (c=='1') {
                            postInput &= variables[i];
                        } else {
                            std::cerr << "Error: Illegal XMAKETRANS string given.\n";
                        }
                    }
                }
                BF trans = currentPosition & postInput & safetyEnv;
                if (trans.isFalse()) {
                    std::cout << "ERROR\n";
                    if (currentPosition.isFalse()) {
                    }
                } else {
                    trans &= positionalStrategiesForTheIndividualGoals[currentLivenessGuarantee];
                    if (trans.isFalse()) {
                        std::cout << "ERROR (2)\n";
                    } else {

                        // Switching goals
                        BF newCombination = determinize(trans,postControllerOutputVars);
                        newCombination &= robotBDD;
                        if (newCombination.isFalse()) {
                            std::cout << "ERROR (3)\n";
                        } else {
                            BF_newDumpDot(*this,newCombination,NULL,"/tmp/newCombinationPossibilities.dot");
                            newCombination = randomDeterminize(newCombination,postMotionStateVars);

                            // Jump as much forward  in the liveness guarantee list as possible ("stuttering avoidance")
                            unsigned int nextLivenessGuarantee = currentLivenessGuarantee;
                            bool firstTry = true;
                            while (((nextLivenessGuarantee != currentLivenessGuarantee) || firstTry) && !((livenessGuarantees[nextLivenessGuarantee] & newCombination).isFalse())) {
                                nextLivenessGuarantee = (nextLivenessGuarantee + 1) % livenessGuarantees.size();
                                firstTry = false;
                            }

                            BF_newDumpDot(*this,newCombination,NULL,"/tmp/newCombination.dot");
                            //sleep(30);

                            currentLivenessGuarantee = nextLivenessGuarantee;
                            currentPosition = newCombination.ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost);

                            // Print position
                            for (unsigned int i=0; i<variables.size(); i++) {
                                if (variableTypes[i]==PreInput) {
                                    if ((variables[i] & currentPosition).isFalse()) {
                                        std::cout << "0";
                                    } else {
                                        std::cout << "1";
                                    }
                                }
                            }
                            for (unsigned int i=0; i<variables.size(); i++) {
                                if (variableTypes[i]==PreMotionState) {
                                    if ((variables[i] & currentPosition).isFalse()) {
                                        std::cout << "0";
                                    } else {
                                        std::cout << "1";
                                    }
                                }
                            }
                            for (unsigned int i=0; i<variables.size(); i++) {
                                if (variableTypes[i]==PreOtherOutput) {
                                    if ((variables[i] & currentPosition).isFalse()) {
                                        std::cout << "0";
                                    } else {
                                        std::cout << "1";
                                    }
                                }
                            }
                            for (unsigned int i=0; i<variables.size(); i++) {
                                if (variableTypes[i]==PreMotionControlOutput) {
                                    if ((variables[i] & currentPosition).isFalse()) {
                                        std::cout << "0";
                                    } else {
                                        std::cout << "1";
                                    }
                                }
                            }
                            std::cout << "," << currentLivenessGuarantee << std::endl; // Flushes, too.
                        }
                    }
                }
                std::cout.flush();

            } else if (command=="XMAKECONTROLTRANS") {
                std::cout << "\n"; // Get rid of the prompt
                BF postInput = mgr.constantTrue();
                BF preMotionState = mgr.constantTrue();
                for (unsigned int i=0; i<variables.size(); i++) {
                    if (variableTypes[i]==PostInput) {
                        char c;
                        std::cin >> c;
                        if (c=='0') {
                            postInput &= !variables[i];
                        } else if (c=='1') {
                            postInput &= variables[i];
                        } else {
                            std::cerr << "Error: Illegal XMAKETRANS string given.\n";
                        }
                    }
                    if (variableTypes[i]==PreMotionState) {
                        char c;
                        std::cin >> c;
                        if (c=='0') {
                            preMotionState &= !variables[i];
                        } else if (c=='1') {
                            preMotionState &= variables[i];
                        } else {
                            std::cerr << "Error: Illegal XMAKETRANS string given.\n";
                        }
                    }
                }
                // BF trans = currentPosition & postInput & safetyEnv;
                BF trans = currentPosition.ExistAbstract(varCubePreMotionState) & postInput & preMotionState & safetyEnv;
                if (trans.isFalse()) {
                    std::cout << "ERROR\n";
                    if (currentPosition.isFalse()) {
                    }
                } else {
                    trans &= positionalStrategiesForTheIndividualGoals[currentLivenessGuarantee];
                    if (trans.isFalse()) {
                        std::cout << "ERROR (2)\n";
                    } else {

                        // Switching goals
                        BF newCombination = determinize(trans,postControllerOutputVars);
                        newCombination &= robotBDD;
                        if (newCombination.isFalse()) {
                            std::cout << "ERROR (3)\n";
                        } else {
                            BF_newDumpDot(*this,newCombination,NULL,"/tmp/newCombinationPossibilities.dot");
                            //newCombination &= preMotionState;
                            //newCombination = newCombination.ExistAbstract(varCubePreMotionState) & preMotionState;
                            //newCombination = randomDeterminize(newCombination,postMotionStateVars);

                            // Jump as much forward  in the liveness guarantee list as possible ("stuttering avoidance")
                            unsigned int nextLivenessGuarantee = currentLivenessGuarantee;
                            bool firstTry = true;
                            while (((nextLivenessGuarantee != currentLivenessGuarantee) || firstTry) && !((livenessGuarantees[nextLivenessGuarantee] & newCombination).isFalse())) {
                                nextLivenessGuarantee = (nextLivenessGuarantee + 1) % livenessGuarantees.size();
                                firstTry = false;
                            }

                            BF_newDumpDot(*this,newCombination,NULL,"/tmp/newCombination.dot");
                            //sleep(30);

                            currentLivenessGuarantee = nextLivenessGuarantee;
                            currentPosition = newCombination.ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost);

                            // Print position
                            for (unsigned int i=0; i<variables.size(); i++) {
                                if (variableTypes[i]==PreInput) {
                                    if ((variables[i] & currentPosition).isFalse()) {
                                        std::cout << "0";
                                    } else {
                                        std::cout << "1";
                                    }
                                }
                            }
                            for (unsigned int i=0; i<variables.size(); i++) {
                                if (variableTypes[i]==PreMotionState) {
                                    if ((variables[i] & currentPosition).isFalse()) {
                                        std::cout << "0";
                                    } else {
                                        std::cout << "1";
                                    }
                                }
                            }
                            for (unsigned int i=0; i<variables.size(); i++) {
                                if (variableTypes[i]==PreOtherOutput) {
                                    if ((variables[i] & currentPosition).isFalse()) {
                                        std::cout << "0";
                                    } else {
                                        std::cout << "1";
                                    }
                                }
                            }
                            for (unsigned int i=0; i<variables.size(); i++) {
                                if (variableTypes[i]==PreMotionControlOutput) {
                                    if ((variables[i] & currentPosition).isFalse()) {
                                        std::cout << "0";
                                    } else {
                                        std::cout << "1";
                                    }
                                }
                            }
                            std::cout << "," << currentLivenessGuarantee << std::endl; // Flushes, too.
                        }
                    }
                }
                std::cout.flush();

            } else if (command=="XMAKETRANS_INIT") {
                std::cout << "\n"; // Get rid of the prompt
                BF postInput = mgr.constantTrue();
                BF preMotionState = mgr.constantTrue();
                for (unsigned int i=0; i<variables.size(); i++) {
                    if (variableTypes[i]==PostInput) {
                        char c;
                        std::cin >> c;
                        if (c=='0') {
                            postInput &= !variables[i];
                        } else if (c=='1') {
                            postInput &= variables[i];
                        } else {
                            std::cerr << "Error: Illegal XMAKETRANS string given.\n";
                        }
                    }
                //     if (variableTypes[i]==PreMotionState) {
                //         char c;
                //         std::cin >> c;
                //         if (c=='0') {
                //             preMotionState &= !variables[i];
                //         } else if (c=='1') {
                //             preMotionState &= variables[i];
                //         } else {
                //             std::cerr << "Error: Illegal XMAKETRANS string given.\n";
                //         }
                //     }
                }

                BF trans = currentPosition & postInput & safetyEnv;
                if (trans.isFalse()) {
                    std::cout << "ERROR\n";
                    if (currentPosition.isFalse()) {
                    }
                } else {
                    trans &= positionalStrategiesForTheIndividualGoals[currentLivenessGuarantee];
                    if (trans.isFalse()) {
                        std::cout << "ERROR (2)\n";
                    } else {

                        // Switching goals
                        BF newCombination = determinize(trans,postControllerOutputVars);
                        newCombination &= robotBDD;
                        if (newCombination.isFalse()) {
                            std::cout << "ERROR (3)\n";
                        } else {
                            BF_newDumpDot(*this,newCombination,NULL,"/tmp/newCombinationPossibilities.dot");
                            newCombination = randomDeterminize(newCombination,postMotionStateVars);

                            // Jump as much forward  in the liveness guarantee list as possible ("stuttering avoidance")
                            unsigned int nextLivenessGuarantee = currentLivenessGuarantee;
                            bool firstTry = true;
                            while (((nextLivenessGuarantee != currentLivenessGuarantee) || firstTry) && !((livenessGuarantees[nextLivenessGuarantee] & newCombination).isFalse())) {
                                nextLivenessGuarantee = (nextLivenessGuarantee + 1) % livenessGuarantees.size();
                                firstTry = false;
                            }

                            BF_newDumpDot(*this,newCombination,NULL,"/tmp/newCombination.dot");
                            //sleep(30);

                            currentLivenessGuarantee = nextLivenessGuarantee;
                            currentPosition = newCombination.ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost);

                            // Print position
                            for (unsigned int i=0; i<variables.size(); i++) {
                                if (variableTypes[i]==PreInput) {
                                    if ((variables[i] & currentPosition).isFalse()) {
                                        std::cout << "0";
                                    } else {
                                        std::cout << "1";
                                    }
                                }
                            }
                            for (unsigned int i=0; i<variables.size(); i++) {
                                if (variableTypes[i]==PreMotionState) {
                                    if ((variables[i] & currentPosition).isFalse()) {
                                        std::cout << "0";
                                    } else {
                                        std::cout << "1";
                                    }
                                }
                            }
                            for (unsigned int i=0; i<variables.size(); i++) {
                                if (variableTypes[i]==PreOtherOutput) {
                                    if ((variables[i] & currentPosition).isFalse()) {
                                        std::cout << "0";
                                    } else {
                                        std::cout << "1";
                                    }
                                }
                            }
                            for (unsigned int i=0; i<variables.size(); i++) {
                                if (variableTypes[i]==PreMotionControlOutput) {
                                    if ((variables[i] & currentPosition).isFalse()) {
                                        std::cout << "0";
                                    } else {
                                        std::cout << "1";
                                    }
                                }
                            }
                            std::cout << "," << currentLivenessGuarantee << std::endl; // Flushes, too.
                        }
                    }
                }
                std::cout.flush();

            } else if (command=="XPRINTINPUTS") {
                std::cout << "\n"; // Get rid of the prompt
                for (unsigned int i=0;i<variables.size();i++) {
                    if (variableTypes[i]==PreInput)
                        std::cout << variableNames[i] << "\n";
                }
                std::cout << std::endl; // Flushes
            } else if (command=="XPRINTMOTIONSTATE") {
                std::cout << "\n"; // Get rid of the prompt
                for (unsigned int i=0; i<variables.size(); i++) {
                    if (variableTypes[i]==PreMotionState)
                        std::cout << variableNames[i] << "\n";
                }
                std::cout << std::endl; // Flushes
            } else if (command=="XPRINTMOTIONCONTROLOUTPUTS") {
                std::cout << "\n"; // Get rid of the prompt
                for (unsigned int i=0; i<variables.size(); i++) {
                    if (variableTypes[i]==PreMotionControlOutput)
                        std::cout << variableNames[i] << "\n";
                }
                std::cout << std::endl; // Flushes
            } else if (command=="XPRINTOTHEROUTPUTS") {
                std::cout << "\n"; // Get rid of the prompt
                for (unsigned int i=0; i<variables.size(); i++) {
                    if (variableTypes[i]==PreOtherOutput)
                        std::cout << variableNames[i] << "\n";
                }
                std::cout << std::endl; // Flushes
            } else if (command=="XGETINIT") {
                std::cout << "\n"; // Get rid of the prompt
                BF initialPosition = winningPositionsPlayer2 & initEnv & initSys;
                initialPosition = determinize(initialPosition,preVars);
                for (unsigned int i=0;i<variables.size();i++) {
                    if (variableTypes[i]==PreInput) {
                        if ((variables[i] & initialPosition).isFalse()) {
                            std::cout << "0";
                        } else {
                            std::cout << "1";
                        }
                    }
                }
                for (unsigned int i=0; i<variables.size(); i++) {
                    if (variableTypes[i]==PreMotionState) {
                        if ((variables[i] & initialPosition).isFalse()) {
                            std::cout << "0";
                        } else {
                            std::cout << "1";
                        }
                    }
                }
                for (unsigned int i=0; i<variables.size(); i++) {
                    if (variableTypes[i]==PreOtherOutput) {
                        if ((variables[i] & initialPosition).isFalse()) {
                            std::cout << "0";
                        } else {
                            std::cout << "1";
                        }
                    }
                }
                for (unsigned int i=0; i<variables.size(); i++) {
                    if (variableTypes[i]==PreMotionControlOutput) {
                        if ((variables[i] & initialPosition).isFalse()) {
                            std::cout << "0";
                        } else {
                            std::cout << "1";
                        }
                    }
                }
                std::cout << ",0" << std::endl; // Flushes, too.
                currentPosition = initialPosition;
            } else {
                std::cout << "Error: Did not understand command '" << command << "'" << std::endl;
            }
        }
    }

    void extractPatternsFromWinningStates() {

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

        BF robotAllowedMoves = robotBDD.ExistAbstract(varCubePostMotionState);
        // TODO: Support for non-special-robotics semantics
        failingPreAndPostConditions = winningPositions & safetyEnv & !safetySys & robotBDD;
        failingPreAndPostConditions = robotAllowedMoves.Implies(failingPreAndPostConditions).ExistAbstract(varCubePostMotionState).UnivAbstract(varCubePostControllerOutput).ExistAbstract(varCubePreInput);
        failingPreAndPostConditions &= !((failingPreAndPostConditions).UnivAbstract(varCubePostInput)); // remove safeties that are pure obstacles.

        BF_newDumpDot(*this,failingPreAndPostConditions,NULL,"/tmp/failingPreAndPostConditions.dot");

        // save any combination of pre variables and post inputs found that are not included in player 1's strategy and don't falsify the environment
        //TODO: for *all* post motion states? (by definition, any control output that is winning should produce motion states that are all winning)
        BF cutCandidate = safetyEnv & robotBDD & (!winningPositions.ExistAbstract(varCubePre)) & winningPositions.ExistAbstract(varCubePost);
        if (!cutCandidate.isFalse()) {
            foundCutConditions.push_back(boost::make_tuple(0,cutCandidate));
        }
    }

    void checkRealizabilityPlayer2() {

        // Compute first which moves by the robot are actually allowed.
        BF robotAllowedMoves = robotBDD.ExistAbstract(varCubePostMotionState);

        // The greatest fixed point - called "Z" in the GR(1) synthesis paper
        BFFixedPoint nu2(mgr.constantTrue());

        // Iterate until we have found a fixed point
        for (;!nu2.isFixedPointReached();) {

            // To extract a strategy in case of realizability, we need to store a sequence of 'preferred' transitions in the
            // game structure. These preferred transitions only need to be computed during the last execution of the outermost
            // greatest fixed point. Since we don't know which one is the last one, we store them in every iteration,
            // so that after the last iteration, we obtained the necessary data. Before any new iteration, we need to
            // clear the old data, though.
            strategyDumpingDataPlayer2.clear();

            // Iterate over all of the liveness guarantees. Put the results into the variable 'nextContraintsForGoals' for every
            // goal. Then, after we have iterated over the goals, we can update nu2.
            BF nextContraintsForGoals = mgr.constantTrue();
            for (uint j=0;j<livenessGuarantees.size();j++) {

                // Start computing the transitions that lead closer to the goal and lead to a position that is not yet known to be losing.
                // Start with the ones that actually represent reaching the goal (which is a transition in this implementation as we can have
                // nexts in the goal descriptions).
                BF livetransitions = livenessGuarantees[j] & (nu2.getValue().SwapVariables(varVectorPre,varVectorPost));
                //BF_newDumpDot(*this,livetransitions,NULL,"/tmp/liveTransitions.dot");

                // Compute the middle least-fixed point (called 'Y' in the GR(1) paper)
                BFFixedPoint mu1(mgr.constantFalse());
                for (;!mu1.isFixedPointReached();) {

                    // Update the set of transitions that lead closer to the goal.
                    livetransitions |= mu1.getValue().SwapVariables(varVectorPre,varVectorPost);

                    // Iterate over the liveness assumptions. Store the positions that are found to be winning for *any*
                    // of them into the variable 'goodForAnyLivenessAssumption'.
                    BF goodForAnyLivenessAssumption = mu1.getValue();
                    for (uint i=0;i<livenessAssumptions.size();i++) {

                        // Prepare the variable 'foundPaths' that contains the transitions that stay within the inner-most
                        // greatest fixed point or get closer to the goal. Only used for strategy extraction
                        BF foundPaths = mgr.constantTrue();

                        // Inner-most greatest fixed point. The corresponding variable in the paper would be 'X'.
                        BFFixedPoint nu0(mgr.constantTrue());
                        for (;!nu0.isFixedPointReached();) {

                            // Compute a set of paths that are safe to take - used for the enforceable predecessor operator ('cox')
                            foundPaths = livetransitions | (nu0.getValue().SwapVariables(varVectorPre,varVectorPost) & !(livenessAssumptions[i]));
                            foundPaths &= safetySys;
                            //BF_newDumpDot(*this,foundPaths,NULL,"/tmp/foundPathsPreRobot.dot");
                            // find foundPaths representation over all post states satisfying the robotBDD
                            foundPaths = robotAllowedMoves & robotBDD.Implies(foundPaths).UnivAbstract(varCubePostMotionState);
                            //BF_newDumpDot(*this,foundPaths,NULL,"/tmp/foundPathsPostRobot.dot");

                            // Update the inner-most fixed point with the result of applying the enforcable predecessor operator
                            // NB (JD): To get rid of unintended behaviors due to falsifying safetyEnv, can't we simply do this:
                            //    foundpaths = foundPaths.ExistAbstract(varCubePostControllerOutput);
                            //    foundpaths = safetyEnv.Implies(foundPaths).UnivAbstract(varCubePostInput);
                            nu0.update(safetyEnv.Implies(foundPaths).UnivAbstract(varCubePostMotionState).ExistAbstract(varCubePostControllerOutput).UnivAbstract(varCubePostInput));
                        }

                        // Update the set of positions that are winning for some liveness assumption
                        goodForAnyLivenessAssumption |= nu0.getValue();

                        // Dump the paths that we just wound into 'strategyDumpingData' - store the current goal long
                        // with the BDD
                        strategyDumpingDataPlayer2.push_back(std::pair<uint,BF>(j,foundPaths));
                    }

                    // Update the moddle fixed point
                    mu1.update(goodForAnyLivenessAssumption);
                }

                // Update the set of positions that are winning for any goal for the outermost fixed point
                nextContraintsForGoals &= mu1.getValue();
            }

            // Update the outer-most fixed point
            nu2.update(nextContraintsForGoals);

        }

        // We found the set of winning positions
        winningPositionsPlayer2 = nu2.getValue();
        BF_newDumpDot(*this,winningPositionsPlayer2,NULL,"/tmp/winningPositionsPlayer2.dot");

        // Check if for every possible environment initial position the system has a good system initial position
        // BF robotInit = robotBDD.ExistAbstract(varCubePost);
        BF result;
        if (initSpecialRoboticsSemantics) {
            // TODO: Support for special-robotics semantics
            throw SlugsException(false,"Error: special robot init semantics not yet supported.\n");
            // if (!initSys.isTrue()) std::cerr << "Warning: Initialisation guarantees have been given although these are ignored in semantics-for-robotics mode! \n";
            // result = (initEnv & initSys).Implies(winningPositions).ExistAbstract(varCubePreMotionState).UnivAbstract(varCubePreControllerOutput).UnivAbstract(varCubePreInput);
        } else {
            // result = initEnv.Implies(winningPositionsPlayer2 & initSys).UnivAbstract(varCubePreMotionState).ExistAbstract(varCubePreControllerOutput).UnivAbstract(varCubePreInput);
            result = initEnv.Implies(winningPositionsPlayer2 & initSys).ExistAbstract(varCubePreMotionState).ExistAbstract(varCubePreControllerOutput).UnivAbstract(varCubePreInput);
        }
        // BF_newDumpDot(*this,(winningPositions & initSys),NULL,"/tmp/winningAndInit.dot");
        // BF_newDumpDot(*this,result,NULL,"/tmp/result.dot");

        // Check if the result is well-defind. Might fail after an incorrect modification of the above algorithm
        if (!result.isConstant()) throw "Internal error: Could not establish realizability/unrealizability of the specification.";

        // Return the result in Boolean form.
        realizable = result.isTrue();
    }

    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XInteractiveRefineAssumptionsForNondeterministicMotion<T>(filenames);
    }
};

#endif
