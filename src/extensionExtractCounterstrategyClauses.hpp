#ifndef __EXTENSION_COUNTERSTRATEGY_CLAUSES_HPP
#define __EXTENSION_COUNTERSTRATEGY_CLAUSES_HPP

#include "gr1context.hpp"
#include <string>

/**
 * A class that computes an explicit state counterstrategy for an unrealizable specification
 */
template<class T> class XExtractCounterStrategyClauses: public T {
protected:
    // New variables
    std::string outputFilename;

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

    //foundCutPostConditions will eventually contain transitions that prevent the
    //counterstrategy from enforcing livelock/deadlock
    BF foundCutPostConditions = mgr.constantTrue();
    BF candidateFailingPreConditions = mgr.constantFalse();

    // build a new vector with preVars and postInputVars
    SlugsVectorOfVarBFs prePostInputVars{Pre,PostInput,this};

    XExtractCounterStrategyClauses<T>(std::list<std::string> &filenames) : T(filenames) {
        if (filenames.size()==1) {
            outputFilename = "";
        } else {
            outputFilename = filenames.front();
            filenames.pop_front();
        }
    }

public:

/**
 * @brief Compute and print out (to stdout) an explicit-state counter strategy that is winning for
 *        the environment. The output is compatible with the old JTLV output of LTLMoP.
 *        This function requires that the unrealizability of the specification has already been
 *        detected and that the variables "strategyDumpingData" and
 *        "winningPositions" have been filled by the synthesis algorithm with meaningful data.
 * @param outputStream - Where the strategy shall be printed to.
 */
void execute() {
        T::execute();
        if (!realizable) {
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
        BF_newDumpDot(*this,foundCutPostConditions,NULL,"/tmp/foundCutPostConditions.dot");
        BF_newDumpDot(*this,candidateFailingPreConditions,NULL,"/tmp/candidateFailingPreConditionsAfter.dot");
        extractClausesFromBF(foundCutPostConditions);
        trySimplerClause(foundCutPostConditions);
}

std::string combineStrArray(std::vector<std::string> strArray, char* delimiter) {
    // This function combines a vector of strings together with the key.
    // similar to the join function in python
    std::stringstream ss;
    auto end = strArray.end();
    if (!strArray.empty()) { --end;}
    std::copy(strArray.begin(), end, std::ostream_iterator<std::string>(ss, delimiter));
    if (!strArray.empty()) {ss << *end;}

    return ss.str();
}

void trySimplerClause(BF bddForConversion){
    // Translate to CNF. Sort by size
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

    // Remove literals from the clauses whenever they are redundant. They are redundant if the
    // overall assumptions do not change when removing a literal
    std::set<std::vector<int> > clausesFoundSoFarIntAfterFiltering;
    BF clausesSoFar = mgr.constantTrue();
    while (clausesFoundSoFarInt.size()>0) {
        std::vector<int> thisClause = *(clausesFoundSoFarInt.begin());
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
        clausesFoundSoFarIntAfterFiltering.insert(filteredLiterals);
    }


    // Print the final set of clauses to stdout
    std::cout << "# Simplified safety assumption CNF clauses:\n";
    for (auto it = clausesFoundSoFarIntAfterFiltering.begin();it!=clausesFoundSoFarIntAfterFiltering.end();it++) {
        for (unsigned int i=0;i<variables.size();i++) {
            if ((*it)[i]!=0) {
                if ((*it)[i]<0) {
                    std::cout << "!";
                }
                std::cout << variableNames[i] << " ";
            }
        }
        std::cout << "\n";
    }
    std::cout << "# End of list\n";

}

void extractClausesFromBF(BF bddForConversion){
    // This function extraction a clause with only preVars from bdd.
    // This only work for single chain BDD now.
    while (!(bddForConversion.isFalse())) {
        BF thisClause = determinize(bddForConversion,prePostInputVars);
        BF_newDumpDot(*this,thisClause,NULL,"/tmp/thisClause.dot");
        std::vector<std::string> clauseSegmentArray;
        for (unsigned int i=0;i<variables.size();i++) {

            if ((thisClause & variables[i]).isFalse()) { //(!a&b)&a = False
                clauseSegmentArray.push_back("!"+variableNames[i]);
                std::cout << variableNames[i] <<":0 " << std::endl; // of value 0

            } else if ((thisClause & !variables[i]).isFalse()) { //(a&b)&!a = False
                clauseSegmentArray.push_back(variableNames[i]);
                std::cout << variableNames[i] <<":1 " << std::endl; // of value 1

            } else {
                std::cout << variableNames[i] <<":-1 " << std::endl; // don't care
            }
        }

        // print to terminal the clause
        char delimiter[] = " & ";
        std::cout << combineStrArray(clauseSegmentArray, delimiter) << std::endl;

        bddForConversion &= !thisClause;
    }
}

void computeAndPrintExplicitStateStrategy(std::ostream &outputStream) {

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
        //BF casesCovered = mgr.constantFalse();
        std::vector<BF> strategy(livenessGuarantees.size()+1);
        for (unsigned int j=0;j<livenessGuarantees.size()+1;j++) {
            strategy[j] = mgr.constantFalse();
        }
        for (auto it = strategyDumpingData.begin();it!=strategyDumpingData.end();it++) {
            if (boost::get<0>(*it) == i) {
                //Have to cover each guarantee (since the winning strategy depends on which guarantee is being pursued)
                //Essentially, the choice of which guarantee to pursue can be thought of as a system "move".
                //The environment always to chooses that prevent the appropriate guarantee.
                strategy[boost::get<1>(*it)] |= boost::get<2>(*it).UnivAbstract(varCubePostOutput) & !(strategy[boost::get<1>(*it)].ExistAbstract(varCubePost));
            }
        }
        positionalStrategiesForTheIndividualGoals[i] = strategy;
    }
    
    // Prepare initial to-do list from the allowed initial states. Select a single initial input valuation.

    // TODO: Support for non-special-robotics semantics
    BF todoInit = (winningPositions & initEnv & initSys);
    while (!(todoInit.isFalse())) {
        BF concreteState = determinize(todoInit,preVars);
        
        //find which liveness guarantee is being prevented (finds the first liveness in order specified)
        // Note by Ruediger here: Removed "!livenessGuarantees[j]" as condition as it is non-positional
        unsigned int found_j_index = 0;
        for (unsigned int j=0;j<livenessGuarantees.size();j++) {
            if (!(concreteState & positionalStrategiesForTheIndividualGoals[0][j]).isFalse()) {
                found_j_index = j;
                break;
            }
        }
            
        std::pair<size_t, std::pair<unsigned int, unsigned int> > lookup = std::pair<size_t, std::pair<unsigned int, unsigned int> >(concreteState.getHashCode(),std::pair<unsigned int, unsigned int>(0,found_j_index));
        lookupTableForPastStates[lookup] = bfsUsedInTheLookupTable.size();
        bfsUsedInTheLookupTable.push_back(concreteState);
        //from now on use the same initial input valuation (but consider all other initial output valuations)
        todoInit &= !concreteState;
        todoList.push_back(lookup);
    }
    std::vector<std::string> negatedDeadlockPatternsArray;
    // Extract strategy
    while (todoList.size()>0) {
        std::pair<size_t, std::pair<unsigned int, unsigned int> > current = todoList.front();
        todoList.pop_front();
        unsigned int stateNum = lookupTableForPastStates[current];
        BF currentPossibilities = bfsUsedInTheLookupTable[stateNum];
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

        // Can we enforce a deadlock?
        BF deadlockInput = (currentPossibilities & safetyEnv & !safetySys).UnivAbstract(varCubePostOutput);
        if (deadlockInput!=mgr.constantFalse()) {
            negatedDeadlockPatternsArray.push_back(addDeadlocked(deadlockInput, current, bfsUsedInTheLookupTable,  lookupTableForPastStates, outputStream));
        } else {

            // No deadlock in sight -> Jump to a different liveness guarantee if necessary.
            while ((currentPossibilities & positionalStrategiesForTheIndividualGoals[current.second.first][current.second.second])==mgr.constantFalse()) current.second.second = (current.second.second + 1) % livenessGuarantees.size();
            currentPossibilities &= positionalStrategiesForTheIndividualGoals[current.second.first][current.second.second];
            assert(currentPossibilities != mgr.constantFalse());
            BF remainingTransitions = currentPossibilities;

            // save any combination of pre variables and post inputs found that are not included in player 1's strategy
            //BF foundCutConditions = (!remainingTransitions.ExistAbstract(varCubePre)) & remainingTransitions.ExistAbstract(varCubePost);
            foundCutPostConditions &= (remainingTransitions.ExistAbstract(varCubePost)).Implies(!remainingTransitions.ExistAbstract(varCubePre));

            candidateFailingPreConditions |= remainingTransitions;
            BF_newDumpDot(*this,!(remainingTransitions).ExistAbstract(varCubePre),NULL,"/tmp/candidateWinningThisState.dot");
            std::stringstream ss1;
            std::stringstream ss2;
            ss1 << "/tmp/candidateWinning" << stateNum << ".dot";
            ss2 << "/tmp/remainingTransitions" << stateNum << ".dot";
            BF_newDumpDot(*this,(!remainingTransitions.ExistAbstract(varCubePre)) & remainingTransitions.ExistAbstract(varCubePost),NULL,ss1.str());
            BF_newDumpDot(*this,remainingTransitions,NULL,ss2.str());

            // Choose one next input and stick to it!
            // BF_newDumpDot(*this,remainingTransitions,NULL,"/tmp/remainingTransitionsBefore.dot");
            remainingTransitions = determinize(remainingTransitions,postInputVars);
            // BF_newDumpDot(*this,remainingTransitions,NULL,"/tmp/remainingTransitionsAfter.dot");

            // Switching goals
            while (!(remainingTransitions & safetySys).isFalse()) {

                BF safeTransition = remainingTransitions & safetySys;
                BF newCombination = determinize(safeTransition, postOutputVars);

                //foundCutPostConditions |= foundCutConditions & newCombination.ExistAbstract(varCubePre).ExistAbstract(varCubePostInput);

                // Jump as much forward  in the liveness assumption list as possible ("stuttering avoidance")
                unsigned int nextLivenessAssumption = current.second.first;
                bool firstTry = true;
                while (((nextLivenessAssumption != current.second.first) | firstTry) && !((livenessAssumptions[nextLivenessAssumption] & newCombination).isFalse())) {
                    nextLivenessAssumption  = (nextLivenessAssumption + 1) % livenessAssumptions.size();
                    firstTry = false;
                }

                //Mark which input has been captured by this case. Use the same input for other successors
                remainingTransitions &= !newCombination;

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

    // output to terminal
    char delimiter[] = " &\n";
    std::cout << combineStrArray(negatedDeadlockPatternsArray, delimiter);
    }


    //This function adds a new successor-less "state" that captures the deadlock-causing input values
    //The outputvalues are omitted (indeed, no valuation exists that satisfies the system safeties)
    //Format compatible with JTLV counterstrategy

    std::string addDeadlocked(BF targetPositionCandidateSet, std::pair<size_t, std::pair<unsigned int, unsigned int> > current, std::vector<BF> &bfsUsedInTheLookupTable, std::map<std::pair<size_t, std::pair<unsigned int, unsigned int> >, unsigned int > &lookupTableForPastStates, std::ostream &outputStream) {
    std::vector<std::string> patternArray; // for saving patterns from deadlock
    BF newCombination = determinize(targetPositionCandidateSet, postVars) ;
    
    newCombination  = newCombination.ExistAbstract(varCubePreOutput).SwapVariables(varVectorPre,varVectorPost);
    
    unsigned int stateNum = lookupTableForPastStates[current];
    BF currentPossibilities = bfsUsedInTheLookupTable[stateNum];
    foundCutPostConditions &= (currentPossibilities.ExistAbstract(varCubePost)).Implies(!newCombination.SwapVariables(varVectorPre,varVectorPost).ExistAbstract(varCubePre).ExistAbstract(varCubePostOutput));

    std::pair<size_t, std::pair<unsigned int, unsigned int> > target = std::pair<size_t, std::pair<unsigned int, unsigned int> >(newCombination.getHashCode(),std::pair<unsigned int, unsigned int>(current.second.first, current.second.second));
    unsigned int tn;
    
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
                patternArray.push_back((((newCombination & variables[i]).isFalse())?" !":" ") +  variableNames[i]);
            }
        }
        outputStream << ">\n\tWith no successors.";
    
    } else {
        tn = lookupTableForPastStates[target];
        outputStream << tn;
    }
    
    // save the deadlock transition into a string
    // the output pattern is the NEGATED one: ! (a & b)  = (!a | !b)
    std::string patternStr;  //output
    char delimiter[] = " & ";
    patternStr = "!(" + combineStrArray(patternArray, delimiter) + ")";

    // return pattern found
    return patternStr;
}


    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XExtractCounterStrategyClauses<T>(filenames);
    }
};

#endif

