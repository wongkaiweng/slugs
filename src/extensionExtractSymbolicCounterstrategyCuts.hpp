#ifndef __EXTENSION_SYMBOLIC_COUNTERSTRATEGY_CUTS_HPP
#define __EXTENSION_SYMBOLIC_COUNTERSTRATEGY_CUTS_HPP

#include "gr1context.hpp"
#include <string>

/**
 * A class that computes an explicit state counterstrategy for an unrealizable specification
 */
template<class T> class XExtractSymbolicCounterStrategyCuts : public T {
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

    //foundCutConditions will eventually contain transitions that prevent the
    //counterstrategy from enforcing livelock/deadlock.
    // -- For deadlock, ALL transitions that satisfy foundCutConditions must be excluded.
    // -- For livelock, ONE transition that satisfies foundCutConditions must be excluded PER GOAL.
    // -- Computes cuts symbolically
  
    BF foundCutConditions = mgr.constantTrue(); 

    XExtractSymbolicCounterStrategyCuts<T>(std::list<std::string> &filenames) : T(filenames) {
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
                computeAndPrintSymbolicStrategy(std::cout);
            } else {
                std::ofstream of(outputFilename.c_str());
                if (of.fail()) {
                    SlugsException ex(false);
                    ex << "Error: Could not open output file'" << outputFilename << "\n";
                    throw ex;
                }
                computeAndPrintSymbolicStrategy(of);
                if (of.fail()) {
                    SlugsException ex(false);
                    ex << "Error: Writing to output file'" << outputFilename << "failed. \n";
                    throw ex;
                }
                of.close();
            }
        }
        BF_newDumpDot(*this,foundCutConditions,NULL,"/tmp/foundCutConditions.dot");
}

    
void computeAndPrintSymbolicStrategy(std::ostream &outputStream) {

    // We don't want any reordering from this point onwards, as
    // the BDD manipulations from this point onwards are 'kind of simple'.
    mgr.setAutomaticOptimisation(false);

    // List of states in existance so far. The first map
    // maps from a BF node pointer (for the pre variable valuation) and a goal
    // to a state number. The vector then contains the concrete valuation.
    std::map<std::pair<size_t, std::pair<unsigned int, unsigned int> >, unsigned int > lookupTableForPastStates;
    std::vector<BF> bfsUsedInTheLookupTable;
    std::list<std::pair<size_t, std::pair<unsigned int, unsigned int> > > todoList;

    
    BF livelockCut = mgr.constantTrue();
    BF deadlockCut = mgr.constantTrue();

    std::vector<BF> livelockCutPerGoal(livenessGuarantees.size());
    for (unsigned int j=0;j<livenessGuarantees.size();j++) {
        livelockCutPerGoal[j] = mgr.constantFalse();
    }
    
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

	    
	// adds options to exclude deadlock and livelock for goal j
	for (unsigned int j=0;j<livenessGuarantees.size();j++) {
	  // excludes deadlock
	  deadlockCut &= !((strategy[j] & safetyEnv & !safetySys).UnivAbstract(varCubePostOutput));
	  // excludes livelock
	  livelockCutPerGoal[j] |= !(strategy[j].UnivAbstract(varCubePostOutput));
        }
    }
    

	
    for (unsigned int j=0;j<livenessGuarantees.size();j++) {
      // exclude livelock for all goals
      livelockCut &= livelockCutPerGoal[j];
    }
    
    foundCutConditions = deadlockCut & livelockCut;
}



    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XExtractSymbolicCounterStrategyCuts<T>(filenames);
    }
};

#endif

