#ifndef __EXTENSION_EXTRACT_STRATEGY_WINNING_POSITIONS_HPP
#define __EXTENSION_EXTRACT_STRATEGY_WINNING_POSITIONS_HPP

#include "gr1context.hpp"
#include <string>

/**
 * An extension that triggers that a strategy is actually extracted.
 *
 *  This extension contains some code by Github user "johnyf", responsible for producing JSON output.
 */
template<class T, bool oneStepRecovery, bool jsonOutput> class XExtractExplicitStrategyWithWinningPositions : public T {
protected:
    // New variables
    std::string outputFilename;

    // Inherited stuff used
    using T::mgr;
    using T::winningPositions;
    using T::initSys;
    using T::initEnv;
    using T::preVars;
    using T::livenessGuarantees;
    using T::strategyDumpingData;
    using T::variables;
    using T::safetyEnv;
    using T::variableTypes;
    using T::realizable;
    using T::postVars;
    using T::varCubePre;
    using T::variableNames;
    using T::varVectorPre;
    using T::varVectorPost;
    using T::varCubePostOutput;
    using T::determinize;
    using T::doesVariableInheritType;

    XExtractExplicitStrategyWithWinningPositions<T,oneStepRecovery,jsonOutput>(std::list<std::string> &filenames): T(filenames) {}

    void init(std::list<std::string> &filenames) {
        T::init(filenames);
        if (filenames.size()==0) {
            outputFilename = "";
        } else {
            outputFilename = filenames.front();
            filenames.pop_front();
        }
    }

public:
    std::string BFtoCNFClauses(BF bddForConversion){
        // This function maps a BF to CNF.
        std::set<std::vector<int> > clausesFoundSoFarInt;
        std::map<unsigned int,std::vector<std::pair<std::vector<int>,BF> > > clauses; // clauses as cube (-1,0,1) over *all* variables & corresponding BF
        while (!(bddForConversion.isTrue())) {
            BF thisClause = determinize(!bddForConversion,variables);

            std::vector<int> thisClauseInt;
            unsigned int elementsInThisClause = 0;
            for (unsigned int i=0;i<variables.size();i++) {
                BF thisTry = thisClause.ExistAbstractSingleVar(variables[i]);
                if ((thisTry & bddForConversion).isFalse()) {
                    thisClauseInt.push_back(0);
                    thisClause = thisTry;
                } else if ((thisClause & variables[i]).isFalse()) {
                    thisClauseInt.push_back(1);
                    elementsInThisClause++;
                } else {
                    thisClauseInt.push_back(-1);
                    elementsInThisClause++;
                }
            }
            clauses[elementsInThisClause].push_back(std::pair<std::vector<int>,BF>(thisClauseInt,!thisClause));
            bddForConversion |= thisClause;
            clausesFoundSoFarInt.insert(thisClauseInt);
        }

        /*
        // Remove literals from the clauses whenever they are redundant. They are redundant if the
        // overall assumptions do not change when removing a literal
        std::set<std::vector<int> > clausesFoundSoFarIntAfterFiltering;
        BF clausesSoFar = mgr.constantTrue();
        while (clausesFoundSoFarInt.size()>0) {
            std::vector<int> thisClause = *(clausesFoundSoFarInt.begin());
            std::ostringstream oss;
            std::cout << "old clause -->" << std::endl;
            if (!thisClause.empty())
            {
                // Convert all but the last element to avoid a trailing ","
                std::copy(thisClause.begin(), thisClause.end()-1,
                std::ostream_iterator<int>(oss, ","));

                // Now add the last element with no delimiter
                oss << thisClause.back();
            }

            std::cout << oss.str() <<"\n"<< std::endl;

            clausesFoundSoFarInt.erase(clausesFoundSoFarInt.begin());
            // Compute BF for the rest of the clauses
            BF nextClauses = mgr.constantTrue();
            for (auto it = clausesFoundSoFarInt.begin();it!=clausesFoundSoFarInt.end();it++) {
                BF thisClauseBF = mgr.constantFalse();
                for (unsigned int i=0;i<variables.size();i++) {
                    if (thisClause[i]>0) {
                        thisClauseBF |= variables[i];
                    } else if (thisClause[i]<0) {
                        thisClauseBF |= !variables[i];
                    }
                }
                nextClauses &= thisClauseBF;
            }

            // Go over the literals
            std::vector<int> filteredLiterals;
            BF committedLiterals = mgr.constantFalse();
            for (unsigned int i=0;i<variables.size();i++) {
                BF restOfClause = committedLiterals;
                for (unsigned int j=i+1;j<variables.size();j++) {
                    if (thisClause[j]>0) {
                        restOfClause |= variables[j];
                    } else if (thisClause[j]<0) {
                        restOfClause |= !variables[j];
                    }
                }

                // Check if this literal is needed
                BF literal;
                if (thisClause[i]>0) {
                    literal = variables[i];
                } else {
                    literal = !variables[i];
                }

                if ((clausesSoFar & nextClauses & restOfClause) == (clausesSoFar & nextClauses & (restOfClause | literal))) {
                    filteredLiterals.push_back(0);
                } else {
                    committedLiterals |= literal;
                    filteredLiterals.push_back(thisClause[i]);
                }
            }
            clausesSoFar &= committedLiterals;
            std::cout << "new clause -->" << std::endl;
            if (!filteredLiterals.empty())
            {
                // Convert all but the last element to avoid a trailing ","
                std::copy(filteredLiterals.begin(), filteredLiterals.end()-1,
                std::ostream_iterator<int>(oss, ","));

                // Now add the last element with no delimiter
                oss << filteredLiterals.back();
            }

            std::cout << oss.str() <<"\n"<< std::endl;

            clausesFoundSoFarIntAfterFiltering.insert(filteredLiterals);
        }*/

        std::set<std::vector<int> > clausesFoundSoFarIntAfterFiltering;
        clausesFoundSoFarIntAfterFiltering =clausesFoundSoFarInt;

        // Print the final set of clauses to stdout
        std::string returnClause;
        for (auto it = clausesFoundSoFarIntAfterFiltering.begin();it!=clausesFoundSoFarIntAfterFiltering.end();it++) {
            std::vector<std::string> returnClauseSegmentArray;
            for (unsigned int i=0;i<variables.size();i++) {
                std::string varStr;
                if ((*it)[i]!=0) {
                    if ((*it)[i]<0) {
                        varStr += " ! ";
                    }
                    varStr += variableNames[i];
                    returnClauseSegmentArray.push_back(varStr);

                }
            }
            if (returnClauseSegmentArray.size() == 1){
                returnClause += *returnClauseSegmentArray.begin() + "\n";
            }else{
                for (auto iter=returnClauseSegmentArray.begin(); iter!=returnClauseSegmentArray.end();iter++){
                    if (iter == returnClauseSegmentArray.begin()){
                        returnClause += "| " + *iter;
                    }else if (iter == returnClauseSegmentArray.end()-1){
                        returnClause += " " + *iter;
                    } else{
                        returnClause += " | " + *iter;
                    }
                }
                returnClause += "\n";
            }

        }

        return returnClause;

    }

    void printLivenessesAndWinningPositionsConjunts(BF livenessWithWinningPos, std::ostream &outputStream){
        // map BF into boolean formula
        std::vector<std::string> livenessAndWinningPositionsStrArray;
        std::string strClause = BFtoCNFClauses(livenessWithWinningPos);

        std::vector<std::string> strSubClauses;
        boost::split(strSubClauses, strClause, boost::is_any_of("\n"));


        // exclude clauses that are the same
        for (auto subClauseIter = strSubClauses.begin(); subClauseIter != strSubClauses.end(); subClauseIter++){
            bool addClause = true;
            for (auto strIter = livenessAndWinningPositionsStrArray.begin(); strIter != livenessAndWinningPositionsStrArray.end();strIter++){
                if (*strIter == *subClauseIter){
                    addClause = false;
                    break;
                }
            }

            // output clause
            if (addClause == true){
                livenessAndWinningPositionsStrArray.push_back(*subClauseIter);
            }
        }

        /*
        outputStream << "---OLD--\n";
        // print clauses
        for(auto iter = strSubClauses.begin();iter !=strSubClauses.end();iter++){
            if (!(*iter == "")){
                outputStream << *iter;
                outputStream << "\n";
            }
        }
        outputStream << "---NEW--\n";
        */
        // print clauses
        for(auto iter = livenessAndWinningPositionsStrArray.begin();iter !=livenessAndWinningPositionsStrArray.end();iter++){
            if (!(*iter == "")){
                outputStream << *iter;
                outputStream << "\n";
            }
        }
    }

    void execute() {
        std::vector<BF> livenessGuaranteesCopy = livenessGuarantees;

        T::execute();
        if (realizable) {

            // also print out winning positions with liveness guarantees
            for (unsigned int j=0;j<livenessGuaranteesCopy.size();j++) {
                BF_newDumpDot(*this,winningPositions & livenessGuaranteesCopy[j],NULL, "/tmp/winningPositionsWithLivenessGuarantees["+std::to_string(j)+"].dot");
                if (outputFilename=="") {
                    std::cout << "System livenesses " << j << " and winning positions:\n";
                    printLivenessesAndWinningPositionsConjunts(winningPositions & livenessGuaranteesCopy[j], std::cout);}
                else{
                    std::ofstream oLiveness((outputFilename+"liveness" + std::to_string(j)).c_str());
                    printLivenessesAndWinningPositionsConjunts(winningPositions & livenessGuaranteesCopy[j], oLiveness);
                    oLiveness.close();
                }
            }

            if (outputFilename=="") {
                computeAndPrintExplicitStateStrategy(std::cout);

            } else {
                std::ofstream of(outputFilename.c_str());
                if (of.fail()) {
                    SlugsException ex(false);
                    ex << "Error: Could not open output file'" << outputFilename << "\n";
                    throw ex;
                }
                computeAndPrintExplicitStateStrategy(of);
                if (of.fail()) {
                    SlugsException ex(false);
                    ex << "Error: Writing to output file'" << outputFilename << "failed. \n";
                    throw ex;
                }
                of.close();
            }
        }
    }

    /**
     * @brief Compute and print out (to stdout) an explicit-state strategy that is winning for
     *        the system. The output is compatible with the old JTLV output of LTLMoP.
     *        This function requires that the realizability of the specification has already been
     *        detected and that the variables "strategyDumpingData" and
     *        "winningPositions" have been filled by the synthesis algorithm with meaningful data.
     * @param outputStream - Where the strategy shall be printed to.
     */
    void computeAndPrintExplicitStateStrategy(std::ostream &outputStream) {

        // We don't want any reordering from this point onwards, as
        // the BDD manipulations from this point onwards are 'kind of simple'.
        mgr.setAutomaticOptimisation(false);

        // List of states in existance so far. The first map
        // maps from a BF node pointer (for the pre variable valuation) and a goal
        // to a state number. The vector then contains the concrete valuation.
        std::map<std::pair<size_t, unsigned int>, unsigned int > lookupTableForPastStates;
        std::vector<BF> bfsUsedInTheLookupTable;
        std::list<std::pair<size_t, unsigned int> > todoList;

        // Prepare initial to-do list from the allowed initial states
        BF todoInit = (oneStepRecovery)?(winningPositions & initSys):(winningPositions & initSys & initEnv);
        while (!(todoInit.isFalse())) {
            BF concreteState = determinize(todoInit,preVars);
            std::pair<size_t, unsigned int> lookup = std::pair<size_t, unsigned int>(concreteState.getHashCode(),0);
            lookupTableForPastStates[lookup] = bfsUsedInTheLookupTable.size();
            bfsUsedInTheLookupTable.push_back(concreteState);
            todoInit &= !concreteState;
            todoList.push_back(lookup);
        }

        // Prepare positional strategies for the individual goals
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

        // Print JSON Header if JSON output is desired
        if (jsonOutput) {
            outputStream << "{\"version\": 0,\n \"slugs\": \"0.0.1\",\n\n";

            // print names of variables
            bool first = true;
            outputStream << " \"variables\": [";
            for (unsigned int i=0; i<variables.size(); i++) {
                if (doesVariableInheritType(i, Pre)) {
                    if (first) {
                        first = false;
                    } else {
                        outputStream << ", ";
                    }
                    outputStream << "\"" << variableNames[i] << "\"";
                }
            }
            outputStream << "],\n\n \"nodes\": {\n";
        }

        // Extract strategy
        while (todoList.size()>0) {
            std::pair<size_t, unsigned int> current = todoList.front();
            todoList.pop_front();
            unsigned int stateNum = lookupTableForPastStates[current];
            BF currentPossibilities = bfsUsedInTheLookupTable[stateNum];

            /*{
                std::ostringstream filename;
                filename << "/tmp/state" << stateNum << ".dot";
                BF_newDumpDot(*this,currentPossibilities,"PreInput PreOutput PostInput PostOutput",filename.str());
            }*/

            // Print state information
            if (jsonOutput) {
                outputStream << "\"" << stateNum << "\": {\n\t\"rank\": " << current.second << ",\n\t\"state\": [";
            } else {
                outputStream << "State " << stateNum << " with rank " << current.second << " -> <";
            }

            bool first = true;
            for (unsigned int i=0;i<variables.size();i++) {
                if (doesVariableInheritType(i,Pre)) {
                    if (first) {
                        first = false;
                    } else {
                        outputStream << ", ";
                    }
                    if (!jsonOutput) outputStream << variableNames[i] << ":";
                    outputStream << (((currentPossibilities & variables[i]).isFalse())?"0":"1");
                }
            }
            if (jsonOutput) {
                outputStream << "],\n";  // end of state list
                // start list of successors
                outputStream << "\t\"trans\": [";
            } else {
                outputStream << ">\n\tWith successors : ";
            }
            first = true;

            // Compute successors for all variables that allow these
            currentPossibilities &= positionalStrategiesForTheIndividualGoals[current.second];
            BF remainingTransitions =
                    (oneStepRecovery)?
                    currentPossibilities:
                    (currentPossibilities & safetyEnv);

            // Switching goals
            while (!(remainingTransitions.isFalse())) {
                BF newCombination = determinize(remainingTransitions,postVars);

                // Jump as much forward  in the liveness guarantee list as possible ("stuttering avoidance")
                unsigned int nextLivenessGuarantee = current.second;
                bool firstTry = true;
                while (((nextLivenessGuarantee != current.second) || firstTry) && !((livenessGuarantees[nextLivenessGuarantee] & newCombination).isFalse())) {
                    nextLivenessGuarantee = (nextLivenessGuarantee + 1) % livenessGuarantees.size();
                    firstTry = false;
                }

                // Mark which input has been captured by this case
                BF inputCaptured = newCombination.ExistAbstract(varCubePostOutput);
                newCombination = newCombination.ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost);
                remainingTransitions &= !inputCaptured;

                // Search for newCombination
                unsigned int tn;
                std::pair<size_t, unsigned int> target = std::pair<size_t, unsigned int>(newCombination.getHashCode(),nextLivenessGuarantee);
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

            if (jsonOutput) {
                outputStream << "]\n}";
                if (!(todoList.empty())) {
                    outputStream << ",";
                }
                outputStream << "\n\n";
            } else {
                outputStream << "\n";
            }
        }
        if (jsonOutput) {
            // close "nodes" dict and json object
            outputStream << "}}\n";
        }
    }

    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XExtractExplicitStrategyWithWinningPositions<T,oneStepRecovery,jsonOutput>(filenames);
    }
};

#endif
