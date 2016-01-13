#ifndef __EXTENSION_UNREALIZABILITY_ANALYSIS_HPP
#define __EXTENSION_UNREALIZABILITY_ANALYSIS_HPP

#include "gr1context.hpp"
#include <string>

/**
 * An extension that triggers that a strategy is actually extracted.
 *
 *  This extension contains some code by Github user "johnyf", responsible for producing JSON output.
 */
template<class T> class XUnrealizabilityAnalysis : public T {
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

    XUnrealizabilityAnalysis<T>(std::list<std::string> &filenames): T(filenames) {}

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

    // so we need to deal with liveness guarantees = system goals. Remove one of them each time and check realizability

    void execute() {

        //for loop for checking if this goal cauases unrealizability

        // make a copy of the original livenessGuarantees
        std::vector<BF> livenessGuaranteesCopy(livenessGuarantees);
        std::vector<int> livenessGuaranteesNumber;

        // first do a sanity check on whether we need to analysis spec
        T::checkRealizability();

        if (realizable){
            std::cout << "The specification is realizable and no analysis is needed!\n";
        } else {
            livenessGuarantees.clear();
            // adding one livenessGuarantee at a time
            for (unsigned int i = 0; i < livenessGuaranteesCopy.size(); i++) {
                livenessGuarantees.push_back(livenessGuaranteesCopy[i]);

                // check if spec is realizable without this goal
                T::checkRealizability();
                if (!realizable) {
                    livenessGuaranteesNumber.push_back(i);

                    // remove the liveness that causes unrealizability
                    livenessGuarantees.pop_back();
                }
            }

            // now prints the output
            if (outputFilename=="") {
                std::cout << "Goals that cannot be satisfied:\n";
                printUnrealizableLivenessGuarantees(livenessGuaranteesNumber, std::cout);
            } else {
                std::ofstream oAnalysis(outputFilename.c_str());
                printUnrealizableLivenessGuarantees(livenessGuaranteesNumber, oAnalysis);
                oAnalysis.close();
            }
        }
    }

    void printUnrealizableLivenessGuarantees(std::vector<int> livenessGuaranteesNumber, std::ostream &outputStream){
        outputStream << "{";
        for (auto i = livenessGuaranteesNumber.begin(); i != livenessGuaranteesNumber.end(); ++i) {
            if (i != livenessGuaranteesNumber.begin()){
                outputStream << ", ";
            }
            outputStream << *i;
        }
        outputStream << "}\n";

    }

    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XUnrealizabilityAnalysis<T>(filenames);
    }
};

#endif
