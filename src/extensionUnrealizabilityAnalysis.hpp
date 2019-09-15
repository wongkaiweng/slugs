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
    using T::livenessGuarantees;
    using T::realizable;

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
        std::vector<BF> livenessGuaranteesRealizable; // realizable goals
        std::vector<int> livenessGuaranteesNumber;

        // first do a sanity check on whether we need to analysis spec
        T::checkRealizability();

        if (realizable){
            std::cerr << "RESULT: Specification is realizable.\nNo analysis is needed!\n";
        } else {
            std::cerr << "RESULT: Specification is unrealizable.\n";

            // adding one livenessGuarantee at a time
            for (unsigned int i = 0; i < livenessGuaranteesCopy.size(); i++) {
                livenessGuaranteesRealizable.push_back(livenessGuaranteesCopy[i]);

                // also clear guarantees in case of using cooperative strategy
                livenessGuarantees.assign(livenessGuaranteesRealizable.begin(), livenessGuaranteesRealizable.end());

                // check if spec is realizable without this goal
                T::checkRealizability();
                if (!realizable) {
                    livenessGuaranteesNumber.push_back(i);

                    // remove the liveness that causes unrealizability
                    livenessGuaranteesRealizable.pop_back();
                }
            }

            // now prints the output
            if (outputFilename=="") {
                printUnrealizableLivenessGuarantees(livenessGuaranteesNumber, std::cout);
            } else {
                std::ofstream oAnalysis(outputFilename.c_str());
                printUnrealizableLivenessGuarantees(livenessGuaranteesNumber, oAnalysis);
                oAnalysis.close();
            }
        }
    }

    void printUnrealizableLivenessGuarantees(std::vector<int> livenessGuaranteesNumber, std::ostream &outputStream){
        for (auto i = livenessGuaranteesNumber.begin(); i != livenessGuaranteesNumber.end(); ++i) {
            outputStream << "System highlighted goal(s) unrealizable: " << *i << "\n";
        }

    }

    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XUnrealizabilityAnalysis<T>(filenames);
    }
};

#endif
