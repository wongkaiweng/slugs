#ifndef __EXTENSION_NONTERMINISTIC_MOTION_FS_HPP
#define __EXTENSION_NONTERMINISTIC_MOTION_FS_HPP

#include "gr1context.hpp"

template<class T, bool initSpecialRoboticsSemantics> class XNonDeterministicMotionFastSlow : public T {
protected:

    // Inherited stuff used
    using T::mgr;
    using T::initEnv;
    using T::initSys;
    using T::safetyEnv;
    using T::safetySys;
    using T::lineNumberCurrentlyRead;
    using T::addVariable;
    using T::parseBooleanFormula;
    using T::livenessGuarantees;
    using T::livenessAssumptions;
    using T::variableNames;
    using T::variables;
    using T::variableTypes;
    // using T::varVectorPre;
    // using T::varVectorPost;
    using T::strategyDumpingData;
    using T::varCubePostInput;
    using T::winningPositions;
    using T::varCubePreInput;
    using T::varCubePreOutput;
    using T::realizable;
    using T::determinize;
    using T::preVars;
    // using T::varCubePre;
    // using T::varCubePost;

    // Own variables local to this plugin
    BF robotBDD;
    // SlugsVarVector varVectorPre{PreInput, PreOutput, this};
    // SlugsVarVector varVectorPost{PostInput, PostOutput, this};
    SlugsVectorOfVarBFs preMotionStateVars{PreMotionState,this};
    SlugsVectorOfVarBFs postMotionStateVars{PostMotionState,this};
    // SlugsVectorOfVarBFs postInputVars{PostInput,this};
    SlugsVarCube varCubePostMotionState{PostMotionState,this};
    SlugsVarCube varCubePostControllerOutput{PostMotionControlOutput,this};
    SlugsVarCube varCubePreMotionState
    {PreMotionState,this};
    SlugsVarCube varCubePreControllerOutput{PreMotionControlOutput,this};
    SlugsVarVector varVectorPre{Pre, this}; // needed because the PreMotionState gets left out in GR1Context
    SlugsVarVector varVectorPost{Post, this};
    SlugsVarCube varCubePre{Pre,this};
    SlugsVarCube varCubePost{Post,this};

public:
    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XNonDeterministicMotionFastSlow<T,initSpecialRoboticsSemantics>(filenames);
    }

    XNonDeterministicMotionFastSlow<T,initSpecialRoboticsSemantics>(std::list<std::string> &filenames): T(filenames) {}

    /**
     * @brief init - Read input file(s)
     * @param filenames
     */
    void init(std::list<std::string> &filenames) {

        if (filenames.size()==0) {
            throw "Error: Cannot load SLUGS input file - there has been no input file name given!";
        }

        if (filenames.size()<2) {
            throw "Error: At least two file names are needed when using the supplied options!";
        }

        std::string specFileName = *(filenames.begin());
        filenames.pop_front();
        std::string robotFileName = *(filenames.begin());
        filenames.pop_front();

        std::ifstream inFile(specFileName.c_str());
        if (inFile.fail()) throw "Error: Cannot open input file";

        // Prepare safety and initialization constraints
        initEnv = mgr.constantTrue();
        initSys = mgr.constantTrue();
        safetyEnv = mgr.constantTrue();
        safetySys = mgr.constantTrue();

        // The readmode variable stores in which chapter of the input file we are
        int readMode = -1;
        std::string currentLine;
        lineNumberCurrentlyRead = 0;
        while (std::getline(inFile,currentLine)) {
            lineNumberCurrentlyRead++;
            boost::trim(currentLine);
            if ((currentLine.length()>0) && (currentLine[0]!='#')) {
                if (currentLine[0]=='[') {
                    if (currentLine=="[INPUT]") {
                        readMode = 0;
                    } else if (currentLine=="[MOTION STATE OUTPUT]") {
                        readMode = 1;
                    } else if (currentLine=="[MOTION CONTROLLER OUTPUT]") {
                        readMode = 2;
                    } else if (currentLine=="[OTHER OUTPUT]") {
                        readMode = 3;
                    } else if (currentLine=="[ENV_INIT]") {
                        readMode = 4;
                    } else if (currentLine=="[SYS_INIT]") {
                        readMode = 5;
                    } else if (currentLine=="[ENV_TRANS]") {
                        readMode = 6;
                    } else if (currentLine=="[SYS_TRANS]") {
                        readMode = 7;
                    } else if (currentLine=="[ENV_LIVENESS]") {
                        readMode = 8;
                    } else if (currentLine=="[SYS_LIVENESS]") {
                        readMode = 9;
                    } else {
                        std::cerr << "Sorry. Didn't recognize category " << currentLine << "\n";
                        throw "Aborted.";
                    }
                } else {
                    if (readMode==0) {
                        variables.push_back(mgr.newVariable());
                        variableNames.push_back(currentLine);
                        variableTypes.push_back(PreInput);
                        variables.push_back(mgr.newVariable());
                        variableNames.push_back(currentLine+"'");
                        variableTypes.push_back(PostInput);
                    } else if (readMode==1) {
                        variables.push_back(mgr.newVariable());
                        variableNames.push_back(currentLine);
                        variableTypes.push_back(PreMotionState);
                        variables.push_back(mgr.newVariable());
                        variableNames.push_back(currentLine+"'");
                        variableTypes.push_back(PostMotionState);
                    } else if (readMode==2) {
                        variables.push_back(mgr.newVariable());
                        variableNames.push_back(currentLine);
                        variableTypes.push_back(PreMotionControlOutput);
                        variables.push_back(mgr.newVariable());
                        variableNames.push_back(currentLine+"'");
                        variableTypes.push_back(PostMotionControlOutput);
                    } else if (readMode==3) {
                        variables.push_back(mgr.newVariable());
                        variableNames.push_back(currentLine);
                        variableTypes.push_back(PreOtherOutput);
                        variables.push_back(mgr.newVariable());
                        variableNames.push_back(currentLine+"'");
                        variableTypes.push_back(PostOtherOutput);
                    } else if (readMode==4) {
                        std::set<VariableType> allowedTypes;
                        allowedTypes.insert(PreInput);
                        allowedTypes.insert(PreMotionState);
                        // allowedTypes.insert(PreMotionControlOutput); -> Is not taken into account
                        allowedTypes.insert(PreOtherOutput);
                        initEnv &= parseBooleanFormula(currentLine,allowedTypes);
                    } else if (readMode==5) {
                        std::set<VariableType> allowedTypes;
                        allowedTypes.insert(PreInput);
                        allowedTypes.insert(PreMotionState);
                        allowedTypes.insert(PreMotionControlOutput); //-> Is not taken into account
                        allowedTypes.insert(PreOtherOutput);
                        initSys &= parseBooleanFormula(currentLine,allowedTypes);
                    } else if (readMode==6) {
                        std::set<VariableType> allowedTypes;
                        allowedTypes.insert(PreInput);
                        allowedTypes.insert(PreMotionState);
                        allowedTypes.insert(PreMotionControlOutput); //-> Is not taken into account
                        allowedTypes.insert(PreOtherOutput);
                        allowedTypes.insert(PostInput);
                        allowedTypes.insert(PostMotionState);
                        // allowedTypes.insert(PostOtherOutput);
                        safetyEnv &= parseBooleanFormula(currentLine,allowedTypes);
                    } else if (readMode==7) {
                        std::set<VariableType> allowedTypes;
                        allowedTypes.insert(PreInput);
                        allowedTypes.insert(PreMotionState);
                        allowedTypes.insert(PostMotionControlOutput);
                        allowedTypes.insert(PreOtherOutput);
                        allowedTypes.insert(PostInput);
                        allowedTypes.insert(PostMotionState);
                        allowedTypes.insert(PostOtherOutput);
                        safetySys &= parseBooleanFormula(currentLine,allowedTypes);
                    } else if (readMode==8) {
                        std::set<VariableType> allowedTypes;
                        allowedTypes.insert(PreInput);
                        allowedTypes.insert(PreMotionState);
                        allowedTypes.insert(PreMotionControlOutput); //-> Is not taken into account
                        allowedTypes.insert(PreOtherOutput);
                        allowedTypes.insert(PostInput);
                        livenessAssumptions.push_back(parseBooleanFormula(currentLine,allowedTypes));
                    } else if (readMode==9) {
                        std::set<VariableType> allowedTypes;
                        allowedTypes.insert(PreInput);
                        allowedTypes.insert(PreMotionState);
                        allowedTypes.insert(PostMotionControlOutput);
                        allowedTypes.insert(PreOtherOutput);
                        allowedTypes.insert(PostInput);
                        allowedTypes.insert(PostMotionState);
                        allowedTypes.insert(PostOtherOutput);
                        livenessGuarantees.push_back(parseBooleanFormula(currentLine,allowedTypes));
                    } else {
                        std::cerr << "Error with line " << lineNumberCurrentlyRead << "!";
                        throw "Found a line in the specification file that has no proper categorial context.";
                    }
                }
            }
        }

        std::vector<BF> varsBDDread;

        // Invert all order to get the least significant bit first
        for (int i=variables.size()-1;i>=0;i--) {
            if (variableTypes[i]==PreMotionState)
            varsBDDread.push_back(variables[i]);
        }
        for (int i=variables.size()-1;i>=0;i--) {
            if (variableTypes[i]==PreMotionControlOutput) // note that PRE is what's needed in fastslow
            varsBDDread.push_back(variables[i]);
        }
        for (int i=variables.size()-1;i>=0;i--) {
            if (variableTypes[i]==PostMotionState)
            varsBDDread.push_back(variables[i]);
        }
        std::cerr << "Number of bits that we expect the robot abstraction BDD to have: " << varsBDDread.size() << std::endl;
        robotBDD = mgr.readBDDFromFile(robotFileName.c_str(),varsBDDread);


    }

    void checkRealizability() {

        // The greatest fixed point - called "Z" in the GR(1) synthesis paper
        BFFixedPoint nu2(mgr.constantTrue());

        // Iterate until we have found a fixed point
        for (;!nu2.isFixedPointReached();) {

            // To extract a strategy in case of realizability, we need to store a sequence of 'preferred' transitions in the
            // game structure. These preferred transitions only need to be computed during the last execution of the outermost
            // greatest fixed point. Since we don't know which one is the last one, we store them in every iteration,
            // so that after the last iteration, we obtained the necessary data. Before any new iteration, we need to
            // clear the old data, though.
            strategyDumpingData.clear();

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

                            // Update the inner-most fixed point with the result of applying the enforcable predecessor operator
                            nu0.update(safetyEnv.Implies(foundPaths).ExistAbstract(varCubePostControllerOutput).UnivAbstract(varCubePostInput));
                        }

                        // Update the set of positions that are winning for some liveness assumption
                        goodForAnyLivenessAssumption |= nu0.getValue();

                        // Dump the paths that we just wound into 'strategyDumpingData' - store the current goal long
                        // with the BDD
                        strategyDumpingData.push_back(std::pair<uint,BF>(j,foundPaths));
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
        winningPositions = nu2.getValue();
        BF_newDumpDot(*this,winningPositions,NULL,"/tmp/winningPositions.dot");

        // Check if for every possible environment initial position the system has a good system initial position
        BF result;
        if (initSpecialRoboticsSemantics) {
            // TODO: Support for special-robotics semantics
            throw SlugsException(false,"Error: special robot init semantics not yet supported.\n");
        } else {
            result = initEnv.Implies(winningPositions & initSys).ExistAbstract(varCubePreMotionState).ExistAbstract(varCubePreControllerOutput).UnivAbstract(varCubePreInput);
        }
        
        // Check if the result is well-defind. Might fail after an incorrect modification of the above algorithm
        if (!result.isConstant()) throw "Internal error: Could not establish realizability/unrealizability of the specification.";

        // Return the result in Boolean form.
        realizable = result.isTrue();
    }

    void addAutomaticallyGeneratedLivenessAssumption() {
        
        // Create a new liveness assumption that says that always eventually, if an action/pre-state
        // combination may lead to a different position, then it is taken
        // (the completion variables always eventually catch up to the activation)
        BF prePostMotionStatesDifferent = mgr.constantFalse();
        for (uint i=0;i<preMotionStateVars.size();i++) {
            prePostMotionStatesDifferent |= (preMotionStateVars[i] ^ postMotionStateVars[i]);
        }
        BF preMotionInputCombinationsThatCanChangeState = (prePostMotionStatesDifferent & robotBDD).ExistAbstract(varCubePostMotionState);
        BF newLivenessAssumption = (!preMotionInputCombinationsThatCanChangeState) | prePostMotionStatesDifferent;
        // before adding the assumption, check first that it is not somehow already satisfied.
        bool doesNewLivenessExist = false;
        for (unsigned int i=0;i<livenessAssumptions.size();i++) { 
            if ((livenessAssumptions[i] & (!newLivenessAssumption)).isFalse()) {
                doesNewLivenessExist = true;
                break;
            }
        }
        if (!doesNewLivenessExist) {
            livenessAssumptions.push_back(newLivenessAssumption);
            if (!(newLivenessAssumption.isTrue())) {
                std::cerr << "Note: Added a liveness assumption that always eventually, we are moving if an action is taken that allows moving.\n";
            }
            BF_newDumpDot(*this,newLivenessAssumption,"PreMotionState PreMotionControlOutput PostMotionState","/tmp/changeMotionStateLivenessAssumption.dot");
        }

        // Make sure that there is at least one liveness assumption and one liveness guarantee
        // The synthesis algorithm might be unsound otherwise
        if (livenessGuarantees.size()==0) livenessGuarantees.push_back(mgr.constantTrue());
        if (livenessAssumptions.size()==0) livenessAssumptions.push_back(mgr.constantTrue());

        BF_newDumpDot(*this,robotBDD,"PreMotionState PreMotionControlOutput PostMotionState","/tmp/robotBDD.dot");
    }

    void addAutomaticallyGeneratedSafeties() {
        
        // Create new safety assumptions describing which regions the robot can end up in given the currently active controllers 
        // and new safety guarantees describing which controllers can be activated

        BF newSafetyEnv = robotBDD;
        BF newSafetySys = robotBDD.ExistAbstract(varCubePostMotionState);
        
        safetyEnv &= newSafetyEnv;
        safetySys &= newSafetySys;
        std::cerr << "Note: Added a safety assumption and guarantee describing the robot's allowed transitions.\n";
        BF_newDumpDot(*this,newSafetyEnv,"PreMotionState PreMotionControlOutput PostMotionState","/tmp/changeMotionStateSafetyAssumption.dot");

    }

    /**
     * @brief This function orchestrates the execution of slugs when this plugin is used.
     */
    void execute() {
        addAutomaticallyGeneratedSafeties();
        addAutomaticallyGeneratedLivenessAssumption();
        checkRealizability();
        if (realizable) {
            std::cerr << "RESULT: Specification is realizable.\n";
        } else {
            std::cerr << "RESULT: Specification is unrealizable.\n";
        }

        // addSafetyAssumption();
    }




};







#endif
