#ifndef __EXTENSION_COUNTERSTRATEGY_NONDETERMINISTIC_HPP
#define __EXTENSION_COUNTERSTRATEGY_NONDETERMINISTIC_HPP

#include "gr1context.hpp"
#include <string>
#include "boost/tuple/tuple.hpp"

/**
 * A class that computes a counterstrategy for an unrealizable specification
 *
 * Includes support for the special robotics semantic
 */
template<class T, bool specialRoboticsSemantics> class XCounterStrategyNondeterministicMotion : public T {
protected:

    // Inherited stuff used
    using T::mgr;
    using T::lineNumberCurrentlyRead;
    using T::addVariable;
    using T::parseBooleanFormula;
    using T::variableNames;
    using T::variables;
    using T::variableTypes;
    using T::livenessGuarantees;
    using T::livenessAssumptions;
    using T::varCubePostOutput;
    using T::varCubePostInput;
    using T::varCubePreOutput;
    using T::varCubePreInput;
    using T::safetyEnv;
    using T::safetySys;
    using T::initEnv;
    using T::initSys;
    // using T::strategyDumpingData;
    using T::determinize;
    using T::winningPositions;
    using T::realizable;
    // using T::varCubePre;
    // using T::varCubePost;

    std::vector<boost::tuple<unsigned int, unsigned int,BF> > strategyDumpingData;

    // Own variables local to this plugin
    BF robotBDD;
    SlugsVectorOfVarBFs preMotionStateVars{PreMotionState,this};
    SlugsVectorOfVarBFs postMotionStateVars{PostMotionState,this};
    SlugsVarCube varCubePostMotionState{PostMotionState,this};
    SlugsVarCube varCubePostControllerOutput{PostMotionControlOutput,this};
    SlugsVarCube varCubePreMotionState{PreMotionState,this};
    SlugsVarCube varCubePreControllerOutput{PreMotionControlOutput,this};
    SlugsVarVector varVectorPre{Pre, this}; // needed because the PreMotionState gets left out in GR1Context
    SlugsVarVector varVectorPost{Post, this};
    SlugsVarCube varCubePre{Pre,this};
    SlugsVarCube varCubePost{Post,this};

public:

    // Constructor
    XCounterStrategyNondeterministicMotion<T,specialRoboticsSemantics>(std::list<std::string> &filenames) : T(filenames) {}


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
            if (variableTypes[i]==PostMotionControlOutput)
            varsBDDread.push_back(variables[i]);
        }
        for (int i=variables.size()-1;i>=0;i--) {
            if (variableTypes[i]==PostMotionState)
            varsBDDread.push_back(variables[i]);
        }
        std::cerr << "Number of bits that we expect the robot abstraction BDD to have: " << varsBDDread.size() << std::endl;
        robotBDD = mgr.readBDDFromFile(robotFileName.c_str(),varsBDDread);
        // BF_newDumpDot(*this,robotBDD,NULL,"/tmp/robotBDD.dot");

    }

    /**
     * @brief Countersynthesis algorithm - adds to 'strategyDumpingData' transitions
     * that represent a winning strategy for the environment.
     * The algorithm implemented is transition-based, and not state-based.
     * So it computes:
     *
     * mu Z. \/_j nu Y. /\_i mu X. cox( (transitionTo(Z) \/ !G^sys_j) /\ transitionTo(Y) /\ (transitionTo(X) \/ G^env_i))
     *
     * where the cox operator computes from which positions the environment player can enforce that certain *transitions* are taken.
     * the transitionTo function takes a set of target positions and computes the set of transitions that are allowed for
     * the environment and that lead to the set of target positions
     **/
    
 void computeWinningPositions() {

    strategyDumpingData.clear();
    // Compute first which moves by the robot are actually allowed.
    BF robotAllowedMoves = robotBDD.ExistAbstract(varCubePostMotionState);

    // The greatest fixed point - called "Z" in the GR(1) synthesis paper
    BFFixedPoint mu2(mgr.constantFalse());

    // Iterate until we have found a fixed point
    for (;!mu2.isFixedPointReached();) {

        // To extract a counterstrategy in case of unrealizability, we need to store a sequence of 'preferred' transitions in the
        // game structure. These preferred transitions only need to be computed during the last execution of the middle
        // greatest fixed point. Since we don't know which one is the last one, we store them in every iteration,
        // so that after the last iteration, we obtained the necessary data. Before any new iteration, we need to
        // store the old date so that it can be discarded if needed
        std::vector<boost::tuple<unsigned int, unsigned int,BF> > strategyDumpingDataOld = strategyDumpingData;

        // Iterate over all of the liveness guarantees. Put the results into the variable 'nextContraintsForGoals' for every
        // goal. Then, after we have iterated over the goals, we can update mu2.
        BF nextContraintsForGoals = mgr.constantFalse();
        for (unsigned int j=0;j<livenessGuarantees.size();j++) {

            // Start computing the transitions that lead closer to the goal and lead to a position that is not yet known to be losing (for the environment).
            // Start with the ones that actually represent reaching the goal (which is a transition in this implementation as we can have
            // nexts in the goal descriptions).
            BF livetransitions = (!livenessGuarantees[j]) | (mu2.getValue().SwapVariables(varVectorPre,varVectorPost));

            // Compute the middle least-fixed point (called 'Y' in the GR(1) paper)
            BFFixedPoint nu1(mgr.constantTrue());
            for (;!nu1.isFixedPointReached();) {

                // New middle iteration has begun -> revert to the data before the first iteration.
                strategyDumpingData = strategyDumpingDataOld;

                // Update the set of transitions that lead closer to the goal.
                livetransitions &= nu1.getValue().SwapVariables(varVectorPre,varVectorPost);

                // Iterate over the liveness assumptions. Store the positions that are found to be winning for *all*
                // of them into the variable 'goodForAnyLivenessAssumption'.
                BF goodForAllLivenessAssumptions = nu1.getValue();
                for (unsigned int i=0;i<livenessAssumptions.size();i++) {

                    // Prepare the variable 'foundPaths' that contains the transitions that stay within the inner-most
                    // greatest fixed point or get closer to the goal. Only used for counterstrategy extraction
                    BF foundPaths = mgr.constantFalse();

                    // Inner-most greatest fixed point. The corresponding variable in the paper would be 'X'.
                    BFFixedPoint mu0(mgr.constantFalse());
                    for (;!mu0.isFixedPointReached();) {

                        // Compute a set of paths that are safe to take - used for the enforceable predecessor operator ('cox')
                        foundPaths = livetransitions & (mu0.getValue().SwapVariables(varVectorPre,varVectorPost) | (livenessAssumptions[i]));

                        foundPaths = safetyEnv & robotAllowedMoves.Implies(robotBDD & safetySys.Implies(foundPaths));
                        BF gatheredResults = foundPaths.ExistAbstract(varCubePostMotionState).UnivAbstract(varCubePostControllerOutput);
                        
                        // Dump the paths that we just found into 'strategyDumpingData' - store the current goal
                        // with the BDD
                        // strategyDumpingData.push_back(boost::make_tuple(i,j,robotBDD & foundPaths));
                        strategyDumpingData.push_back(boost::make_tuple(i,j,foundPaths));

                        // Update the inner-most fixed point with the result of applying the enforcable predecessor operator
                        mu0.update(gatheredResults.ExistAbstract(varCubePostInput));
                    }

                    // Update the set of positions that are winning for some liveness assumption
                    goodForAllLivenessAssumptions &= mu0.getValue();

                }

                // Update the middle fixed point
                nu1.update(goodForAllLivenessAssumptions);
            }

            // Update the set of positions that are winning for some environment goal for the outermost fixed point
            nextContraintsForGoals |= nu1.getValue();
        }

        // Update the outer-most fixed point
        mu2.update(nextContraintsForGoals);

    }

    // We found the set of winning positions
    winningPositions = mu2.getValue();
    BF_newDumpDot(*this,winningPositions,NULL,"/tmp/winningPositionsPlayer1.dot");
}

void addAutomaticallyGeneratedLivenessAssumption() {
    
    // Create a new liveness assumption that says that always eventually, if an action/pre-state
    // combination may lead to a different position, then it is taken
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
            // std::cerr << "doesNewLivenessExist  " << doesNewLivenessExist << "\n";
            break;
        }
    }
    if (!doesNewLivenessExist) {
        livenessAssumptions.push_back(newLivenessAssumption);
        if (!(newLivenessAssumption.isTrue())) {
            std::cerr << "Note: Added a liveness assumption that always eventually, we are moving if an action is taken that allows moving.\n";
        }
        BF_newDumpDot(*this,newLivenessAssumption,"PreMotionState PostMotionControlOutput PostMotionState","/tmp/changeMotionStateLivenessAssumption.dot");
    }

    // Make sure that there is at least one liveness assumption and one liveness guarantee
    // The synthesis algorithm might be unsound otherwise
    if (livenessGuarantees.size()==0) livenessGuarantees.push_back(mgr.constantTrue());
    if (livenessAssumptions.size()==0) livenessAssumptions.push_back(mgr.constantTrue());

    BF_newDumpDot(*this,robotBDD,"PreMotionState PostMotionControlOutput PostMotionState","/tmp/robotBDD.dot");
}

void checkRealizability() {
    addAutomaticallyGeneratedLivenessAssumption();
    computeWinningPositions();

    // Check if for every possible environment initial position the system has a good system initial position
    BF result;
    if (specialRoboticsSemantics) {
        // TODO: Support for special-robotics semantics
        throw SlugsException(false,"Error: special robot init semantics not yet supported.\n");
        // result = (robotBDD & initEnv & initSys & winningPositions).UnivAbstract(varCubePreMotionState).ExistAbstract(varCubePreControllerOutput).ExistAbstract(varCubePreInput);
    } else {
        // BF robotAllowedPreMoves = robotBDD.ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost);
        result = (initEnv & initSys.Implies(winningPositions)).UnivAbstract(varCubePreMotionState).UnivAbstract(varCubePreControllerOutput).ExistAbstract(varCubePreInput);
        // result = (robotBDD & robotAllowedPreMoves & initEnv & initSys & winningPositions).ExistAbstract(varCubePreMotionState).UnivAbstract(varCubePreControllerOutput).ExistAbstract(varCubePreInput);
        // result = (initEnv & initSys.Implies(winningPositions)).ExistAbstract(varCubePreMotionState).UnivAbstract(varCubePreControllerOutput).ExistAbstract(varCubePreInput);
        BF_newDumpDot(*this,result,NULL,"/tmp/resultCounterStrategy.dot");
    }

    // Check if the result is well-defind. Might fail after an incorrect modification of the above algorithm
    if (!result.isConstant()) throw "Internal error: Could not establish realizability/unrealizability of the specification.";

    // Return the result in Boolean form.
    realizable = !result.isTrue();
}


    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XCounterStrategyNondeterministicMotion<T,specialRoboticsSemantics>(filenames);
    }
};

#endif

