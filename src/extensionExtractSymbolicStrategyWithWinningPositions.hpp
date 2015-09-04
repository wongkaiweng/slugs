#ifndef __EXTENSION_EXTRACT_SYMBOLIC_STRATEGY_WINNING_POSITIONS_HPP
#define __EXTENSION_EXTRACT_SYMBOLIC_STRATEGY_WINNING_POSITIONS_HPP

#include "gr1context.hpp"
#include <string>

/**
 * An extension that triggers that a symbolic strategy to be extracted.
 */
template<class T, bool oneStepRecovery, bool systemGoalEncoded> class XExtractSymbolicStrategyWithWinningPositions : public T {
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
    using T::addVariable;
    using T::computeVariableInformation;
    using T::doesVariableInheritType;
    using T::determinize;

    std::vector<int> counterVarNumbersPre;
    std::vector<int> counterVarNumbersPost; // only used if systemGoalEncoded==True
    int goalTransitionSelectorVar; // only used if not systemGoalEncoded==True

    XExtractSymbolicStrategyWithWinningPositions<T,oneStepRecovery, systemGoalEncoded>(std::list<std::string> &filenames): T(filenames) {}

    void init(std::list<std::string> &filenames) {
        T::init(filenames);
        if (filenames.size()==0) {
            std::cerr << "Error: Need a file name for extracting a symbolic strategy.\n";
            throw "Please adapt the parameters.";
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
        T::execute();
        if (realizable) {

            // also print out winning positions with liveness guarantees
            for (unsigned int j=0;j<livenessGuarantees.size();j++) {
                if (outputFilename=="") {
                    std::cout << "System livenesses " << j << " and winning positions:\n";
                    printLivenessesAndWinningPositionsConjunts(winningPositions & livenessGuarantees[j], std::cout);}
                else{
                    std::ofstream oLiveness((outputFilename+"liveness" + std::to_string(j)).c_str());
                    printLivenessesAndWinningPositionsConjunts(winningPositions & livenessGuarantees[j], oLiveness);
                    oLiveness.close();
                }
            }


            if (outputFilename=="") {
                throw "Internal Error.";
            } else {
                computeAndPrintSymbolicStrategy(outputFilename);
            }
        }
    }

    /**
     * @brief Compute and print out (to stdout) a symbolic strategy that is winning for
     *        the system.
     *        This function requires that the realizability of the specification has already been
     *        detected and that the variables "strategyDumpingData" and
     *        "winningPositions" have been filled by the synthesis algorithm with meaningful data.
     * @param outputStream - Where the strategy shall be printed to.
     */
    void computeAndPrintSymbolicStrategy(std::string filename) {

        // We don't want any reordering from this point onwards, as
        // the BDD manipulations from this point onwards are 'kind of simple'.
        mgr.setAutomaticOptimisation(false);

        // Prepare initial to-do list from the allowed initial states
        BF init = (oneStepRecovery)?(winningPositions & initSys):(winningPositions & initSys & initEnv);

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

            // std::ostringstream gsName;
            // gsName << "/tmp/generalStrategy" << i << ".dot";
            // BF dump = variables[4] & !variables[6]& !variables[8] & strategy;
            // BF_newDumpDot(*this,dump,"PreInput PreOutput PostInput PostOutput",gsName.str().c_str());
        }

        // Allocate counter variables
        for (unsigned int i=1;i<=livenessGuarantees.size();i = i << 1) {
            std::ostringstream os;
            os << "_jx_b" << counterVarNumbersPre.size();
            counterVarNumbersPre.push_back(addVariable(SymbolicStrategyCounterVar,os.str()));
            if (systemGoalEncoded) counterVarNumbersPost.push_back(addVariable(SymbolicStrategyCounterVar,os.str()+"'"));
        }

        if (!systemGoalEncoded) {
            goalTransitionSelectorVar = addVariable(SymbolicStrategyCounterVar,"strat_type");
        }

        computeVariableInformation();

        BF combinedStrategy = mgr.constantFalse();
        for (unsigned int i=0;i<livenessGuarantees.size();i++) {
            BF thisEncoding = mgr.constantTrue();
            for (unsigned j=0;j<counterVarNumbersPre.size();j++) {
                if (i&(1 << j)) {
                    thisEncoding &= variables[counterVarNumbersPre[j]];
                } else {
                    thisEncoding &= !variables[counterVarNumbersPre[j]];
                }
            }

            if (systemGoalEncoded) {
                // SystemGoalEncoded -- The full format for deterministic systems
                // Here, we also include the transitions for moving to the next goal.
                BF thisEncodingPostStay = mgr.constantTrue();
                for (unsigned j=0;j<counterVarNumbersPre.size();j++) {
                    if (i&(1 << j)) {
                        thisEncodingPostStay &= variables[counterVarNumbersPost[j]];
                    } else {
                        thisEncodingPostStay &= !variables[counterVarNumbersPost[j]];
                    }
                }

                BF thisEncodingPostGo = mgr.constantTrue();
                for (unsigned j=0;j<counterVarNumbersPre.size();j++) {
                    if (((i+1) % livenessGuarantees.size()) & (1 << j)) {
                        thisEncodingPostGo &= variables[counterVarNumbersPost[j]];
                    } else {
                        thisEncodingPostGo &= !variables[counterVarNumbersPost[j]];
                    }
                }

                BF theseTrans = (thisEncodingPostGo & livenessGuarantees[i]) | (thisEncodingPostStay & !(livenessGuarantees[i]));
                combinedStrategy |= thisEncoding & positionalStrategiesForTheIndividualGoals[i] & theseTrans;

            } else {
                // not SystemGoalEncoded -- The LTLMoP format
                combinedStrategy |= thisEncoding & positionalStrategiesForTheIndividualGoals[i] &
                    ((!variables[goalTransitionSelectorVar]) | livenessGuarantees[i]);

            }
        }

        std::ostringstream fileExtraHeader;
        fileExtraHeader << "# This file is a BDD exported by the SLUGS\n#\n# This BDD is a strategy.\n";
        if (!systemGoalEncoded)
            fileExtraHeader << "#\n# This header contains extra information used by LTLMoP's BDDStrategy.\n";
        fileExtraHeader << "# Currently, the only metadata is 1) the total number of system goals\n";
        fileExtraHeader << "# and 2) the mapping between variable numbers and proposition names.\n#\n";
        fileExtraHeader << "# Some special variables are also added:\n";
        fileExtraHeader << "#       - `_jx_b*` are used as a binary vector (b0 is LSB) to indicate\n";
        fileExtraHeader << "#         the index of the currently-pursued goal.\n";
        if (!systemGoalEncoded) {
            fileExtraHeader << "#       - `strat_type` is a binary variable used to indicate whether we are\n";
            fileExtraHeader << "#          moving closer to the current goal (0) or transitioning to the next goal (1)\n#\n";
        }
        fileExtraHeader << "# Num goals: " << livenessGuarantees.size() << "\n";
        fileExtraHeader << "# Variable names:\n";
        if (!systemGoalEncoded) {
            for (unsigned int i=0;i<variables.size();i++) {
                fileExtraHeader << "#\t" << i << ": " << variableNames[i] << "\n";
            }
        } else {
            for (unsigned int i=0;i<variables.size();i++) {
                if (doesVariableInheritType(i,PreInput)) {
                    fileExtraHeader << "#\t" << i << ": in_" << variableNames[i] << "\n";
                } else if (doesVariableInheritType(i,PostInput)) {
                    fileExtraHeader << "#\t" << i << ": in_" << variableNames[i] << "\n";
                } else {
                    fileExtraHeader << "#\t" << i << ": " << variableNames[i] << "\n";
                }
            }
        }
        fileExtraHeader << "#\n# For information about the DDDMP format, please see:\n";
        fileExtraHeader << "#    http://www.cs.uleth.ca/~rice/cudd_docs/dddmp/dddmpAllFile.html#dddmpDump.c\n#\n";
        fileExtraHeader << "# For information about how this file is generated, please see the SLUGS source.\n#\n";

#ifndef NDEBUG
        std::string tempFilename(tmpnam(NULL));
        tempFilename = tempFilename + "_strategyBdd.dot";
        std::cerr << "Writing DOT file of the BDD to: " << tempFilename << std::endl;
        BF_newDumpDot(*this,combinedStrategy,"SymbolicStrategyCounterVar PreInput PreOutput PostInput PostOutput", tempFilename.c_str());
#endif

        mgr.writeBDDToFile(filename.c_str(),fileExtraHeader.str(),combinedStrategy,variables,variableNames);

    }

    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XExtractSymbolicStrategyWithWinningPositions<T,oneStepRecovery,systemGoalEncoded>(filenames);
    }
};

#endif

