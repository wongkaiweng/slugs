#ifndef __EXTENSION_REFINE_ASSUMPTIONS_NONDETERMINISTIC_HPP
#define __EXTENSION_REFINE_ASSUMPTIONS_NONDETERMINISTIC_HPP

#include "gr1context.hpp"
#include <map>
#include <string>

/**
 * This extension modifies the execute() function ...
 */
template<class T> class XRefineAssumptionsForNondeterministicMotion : public T {
protected:

    // New variables
    std::string outputFilename;

    // Inherit stuff that we actually use here.
    using T::realizable;
    using T::variables;
    using T::variableTypes;
    using T::safetyEnv;
    using T::safetySys;
    using T::livenessAssumptions;
    using T::checkRealizability;
    using T::determinize;
    using T::mgr;
    using T::variableNames;
    // using T::extractAutomaticallyGeneratedLivenessAssumption;
    using T::computeAndPrintExplicitStateStrategy;
    using T::failingPreAndPostConditions;
    using T::foundCutPostConditions;
    using T::candidateWinningPreConditions;
    using T::candidateFailingPreConditions;
    using T::varCubePre;
    using T::varCubePost;
    using T::varVectorPre;
    using T::varVectorPost;
    using T::robotBDD;
    using T::foundCutConditions;
    using T::preVars;

    SlugsVectorOfVarBFs preMotionStateVars{PreMotionState,this};
    SlugsVectorOfVarBFs preInputVars{PreInput,this};
    SlugsVarCube varCubePostMotionState{PostMotionState,this};
    SlugsVarCube varCubePreControllerOutput{PreMotionControlOutput,this};

public:

    XRefineAssumptionsForNondeterministicMotion<T>(std::list<std::string> &filenames) : T(filenames) {
        if (filenames.size()==1) {
            outputFilename = "";
        } else {
            outputFilename = filenames.front();
            filenames.pop_front();
        }
    }

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


        std::cerr << "adding safety assumptions/guarantees and synthesizing counter-strategy\n";
        BF psi1 = mgr.constantFalse();
        BF psi2 = mgr.constantFalse();
        int idx = 0;
        while (!failingPreAndPostConditions.isFalse()){ // & idx<=10){
            // std::stringstream fname;
            // std::stringstream fname1;
            // std::stringstream fname2;
            // fname << "/tmp/failingPreAndPostConditions" << idx << ".dot";
            // fname1 << "/tmp/safetySysBefore" << idx << ".dot";
            // fname2 << "/tmp/safetyEnvBefore" << idx << ".dot";
            // BF_newDumpDot(*this,failingPreAndPostConditions,NULL,fname.str());
            // BF_newDumpDot(*this,safetySys,NULL,fname1.str());
            // BF_newDumpDot(*this,safetyEnv,NULL,fname2.str());
            // BF_newDumpDot(*this,foundCutPostConditions,NULL,"/tmp/candidateWinningPreConditionsBefore.dot");
            idx++;
            if (!failingPreAndPostConditions.isFalse()){
                psi1 = failingPreAndPostConditions.ExistAbstract(varCubePost);
                psi2 = failingPreAndPostConditions.ExistAbstract(varCubePre);
                safetyEnv &= psi1.Implies(!psi2);
                safetySys &= (!psi2).Implies(psi1.SwapVariables(varVectorPre,varVectorPost));

                std::stringstream fname3;
                fname3 << "/tmp/addedSafetyEnv" << idx << ".dot";
                BF_newDumpDot(*this,psi1.Implies(!psi2),NULL,fname3.str());
            }

            failingPreAndPostConditions = mgr.constantFalse();
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
        }

        BF_newDumpDot(*this,safetySys,NULL,"/tmp/safetySysAfter.dot");
        BF_newDumpDot(*this,safetyEnv,NULL,"/tmp/safetyEnvAfter.dot");

        // BF_newDumpDot(*this,foundCutPostConditions,NULL,"/tmp/candidateWinningPreConditionsAfter.dot");
        // BF_newDumpDot(*this,candidateFailingPreConditions,NULL,"/tmp/candidateFailingPreConditionsAfter.dot");
        // livelock -- liveness refinement driven by the deadlock refinements found so far
        // BF failingPostCommands = (psi1.SwapVariables(varVectorPre,varVectorPost) & robotBDD).ExistAbstract(varCubePostMotionState).ExistAbstract(varCubePre);
        // BF PreMotionStates = (psi1.SwapVariables(varVectorPre,varVectorPost) & robotBDD).ExistAbstract(varCubePost);

        // the general case: mark states for which the counterstrategy has post inputs that are NOT winning for player 1, and enumerate those inputs.
        //   TODO: can do this post input quantification for the deadlock case also?
        if (!realizable) {
        // if (false){
            std::cerr << "adding liveness assumptions and synthesizing counter-strategy\n";
            BF_newDumpDot(*this,candidateWinningPreConditions,NULL,"/tmp/candidateWinningPreConditions.dot");
            for (auto it = foundCutConditions.begin();it!=foundCutConditions.end();it++) {
                BF newLivenessAssumptions = (boost::get<1>(*it).ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost)).ExistAbstract(varCubePreControllerOutput);
                
                std::stringstream fname;
                fname << "/tmp/newLivenessAssumptions" << boost::get<0>(*it) << ".dot";
                BF_newDumpDot(*this,newLivenessAssumptions,NULL,fname.str());
                
                BF TODO = newLivenessAssumptions; 
                int idx = 0;
                while (!TODO.isFalse()){
                    BF candidate = determinize(TODO,preInputVars);
                    candidate = determinize(candidate,preMotionStateVars);
                    TODO &= !candidate;
                    int OKtoAdd = true;
                    if (!((safetySys & candidate.SwapVariables(varVectorPre,varVectorPost)).isFalse())){ // if the candidate satisfies the system transition
                        for (unsigned int i=0;i<livenessAssumptions.size();i++) {
                            if ((livenessAssumptions[i] & (!candidate)).isFalse()){ // if the new assumption is already in the list
                                // livenessAssumptions[i] &= candidate; //strengthen existing livenesses if needed, but don't append
                                OKtoAdd = false;
                                break;
                            }
                            // if ((livenessAssumptions[i] & candidate).isFalse()){ // if the new assumption may falsfy the env
                            //     OKtoAdd = false;
                            //     break;
                            // }
                        }
                    }
                    else{
                        OKtoAdd = false;
                    }
                    // std::stringstream fname;
                    // fname << "/tmp/newLivenessAssumptionsFalseSys" << boost::get<0>(*it) << ".dot";
                    // BF_newDumpDot(*this,(safetySys & candidate.SwapVariables(varVectorPre,varVectorPost)),NULL,fname.str());    
                    if (OKtoAdd){
                        livenessAssumptions.push_back(candidate);    
                             
                        std::stringstream fname;
                        fname << "/tmp/newLivenessAssumptions" << boost::get<0>(*it) << "index" << idx << ".dot";
                        BF_newDumpDot(*this,candidate,NULL,fname.str());      
                    }
                }
                // std::cerr << boost::get<0>(*it) << "\n";
            }
            BF_newDumpDot(*this,livenessAssumptions.back(),NULL,"/tmp/livenessAssumptionsLast.dot");

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
        }   
        // livenessAssumptions.push_back(candidateWinningPreConditions);

    }

    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XRefineAssumptionsForNondeterministicMotion<T>(filenames);
    }
};

#endif
