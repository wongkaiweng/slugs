#ifndef __EXTENSION_GET_COUNTERSTRATEGY_NONDETERMINISTIC_HPP
#define __EXTENSION_GET_COUNTERSTRATEGY_NONDETERMINISTIC_HPP

#include "gr1context.hpp"
#include <map>
#include <string>

/**
 * This extension modifies the execute() function ...
 */
template<class T> class XGetCounterstrategyNondeterministicMotion : public T {
protected:

    // New variables
    std::string outputFilename;

    // Inherit stuff that we actually use here.
    using T::realizable;
    using T::variables;
    using T::variableTypes;
    using T::safetyEnv;
    using T::safetySys;
    // using T::livenessEnv;
    using T::checkRealizability;
    using T::determinize;
    using T::mgr;
    using T::variableNames;
    using T::computeAndPrintExplicitStateStrategy;
    using T::failingPreAndPostConditions;
    using T::varCubePre;
    using T::varCubePost;
    using T::varVectorPre;
    using T::varVectorPost;
    using T::robotBDD;

    SlugsVarCube varCubePostMotionState{PostMotionState,this};

public:

    XGetCounterstrategyNondeterministicMotion<T>(std::list<std::string> &filenames) : T(filenames) {
        if (filenames.size()==1) {
            outputFilename = "";
        } else {
            outputFilename = filenames.front();
            filenames.pop_front();
        }
    }

    void execute() {
        T::execute();
        // extractAutomaticallyGeneratedLivenessAssumption();
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

    }

    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XGetCounterstrategyNondeterministicMotion<T>(filenames);
    }
};

#endif
