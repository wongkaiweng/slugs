#ifndef __EXTENSION_INTERACTIVE_STRATEGY_NONDETERM_HPP
#define __EXTENSION_INTERACTIVE_STRATEGY_NONDETERM_HPP

#include <boost/algorithm/string.hpp>


/**
 * A class that opens an interactive shell to allow examining the property of strategies computed
 *
 */
template<class T> class XInteractiveStrategyNondeterministicMotion : public T {
protected:
    XInteractiveStrategyNondeterministicMotion<T>(std::list<std::string> &filenames) : T(filenames) {}

    using T::checkRealizability;
    using T::realizable;
    using T::variables;
    using T::variableNames;
    using T::variableTypes;
    using T::mgr;
    using T::winningPositions;
    using T::livenessAssumptions;
    using T::livenessGuarantees;
    using T::safetyEnv;
    using T::safetySys;
    using T::strategyDumpingData;
    using T::varCubePostOutput;
    using T::varCubePre;
    using T::postOutputVars;
    using T::determinize;
    using T::initEnv;
    using T::initSys;
    using T::preVars;
    using T::postVars;
    using T::varVectorPre;
    using T::varVectorPost;
    using T::doesVariableInheritType;
    using T::varCubePostControllerOutput;
    using T::postInputVars;
    using T::postMotionStateVars;
    using T::varCubePreMotionState;
    using T::robotBDD;

    SlugsVectorOfVarBFs postControllerOutputVars{PostMotionControlOutput,this};

public:
    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XInteractiveStrategyNondeterministicMotion<T>(filenames);
    }

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
        checkRealizability();

        std::vector<BF> positionalStrategiesForTheIndividualGoals(livenessGuarantees.size());
        for (unsigned int i=0;i<livenessGuarantees.size();i++) {
            BF casesCovered = mgr.constantFalse();
            BF strategy = mgr.constantFalse();
            for (auto it = strategyDumpingData.begin();it!=strategyDumpingData.end();it++) {
                if (it->first == i) {
                    BF newCases = it->second.ExistAbstract(varCubePostOutput) & !casesCovered;
                    strategy |= newCases & it->second;
                    casesCovered |= newCases;
                }
            }
            positionalStrategiesForTheIndividualGoals[i] = strategy;
            //BF_newDumpDot(*this,strategy,"PreInput PreOutput PostInput PostOutput","/tmp/generalStrategy.dot");
        }

        if (realizable) {

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
                    BF initialPosition = initEnv.Implies(winningPositions & initSys);
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
                    if ((from & winningPositions).isFalse()) {
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
                    BF initialPosition = winningPositions & initEnv & initSys;
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
        } else {
            std::cerr << "RESULT: Specification is unrealizable.\n";
        }
    }


};


#endif
