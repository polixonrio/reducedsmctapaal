/*
 * DiscreteVerification.cpp
 *
 *  Created on: 23 Feb 2012
 *      Author: jakob
 */

#include "DiscreteVerification/DiscreteVerification.hpp"
#include "DiscreteVerification/DeadlockVisitor.hpp"

#include <fstream>

namespace VerifyTAPN {
    namespace DiscreteVerification {

        template<typename T>
        void VerifyAndPrint(TAPN::TimedArcPetriNet &tapn, Verification<T> &verifier, VerificationOptions &options,
                            AST::Query *query);

        void ComputeAndPrint(TAPN::TimedArcPetriNet &tapn, SMCVerification &verifier, VerificationOptions &options,
                            AST::Query *query);

        DiscreteVerification::DiscreteVerification() {
            // TODO: Auto-generated constructor stub
        }

        DiscreteVerification::~DiscreteVerification() {
            // TODO: Auto-generated destructor stub
        }

        int DiscreteVerification::run(TAPN::TimedArcPetriNet &tapn, const std::vector<int>& initialPlacement, 
                                      AST::Query *query, VerificationOptions &options) {
            if (!tapn.isNonStrict()) {
                std::cout << "The supplied net contains strict intervals." << std::endl;
                return -1;
            }

            NonStrictMarking *initialMarking = new NonStrictMarking(tapn, initialPlacement);

            std::cout << "MC: " << tapn.getMaxConstant() << std::endl;

            // Check initial marking k-bound and SMC query
            if (initialMarking->size() > options.getKBound() && !query->hasSMCQuantifier()) {
                std::cout << "The specified k-bound is less than the number of tokens in the initial markings.";
                return 1;
            }

            if(query->hasSMCQuantifier()) {
                std::cout << "SMC Verification (all irrelevant options will be ignored)" << std::endl;
                std::cout << "Model file is: " << options.getInputFile() << std::endl;
                if (!options.getQueryFile().empty()) {
                    std::cout << "Query file is: " << options.getQueryFile() << std::endl;
                }
            } else {
                std::cout << options;
            }

            // Deadlock visitor
            AST::BoolResult containsDeadlock;
            DeadlockVisitor deadlockVisitor;
            deadlockVisitor.visit(*query, containsDeadlock);

            // Check conditions for deadlock and guards
            if (containsDeadlock.value && options.getGCDLowerGuardsEnabled()) {
                std::cout << "Lowering constants by greatest common divisor is unsound for queries containing the deadlock proposition." << std::endl;
                std::exit(1);
            } else if (containsDeadlock.value && options.getTrace() == VerificationOptions::FASTEST_TRACE) {
                std::cout << "Fastest trace is not supported for queries containing the deadlock proposition." << std::endl;
                std::exit(1);
            }

            if ((query->getQuantifier() == EG || query->getQuantifier() == AF) && options.getGCDLowerGuardsEnabled()) {
                std::cout << "Lowering constants by greatest common divisor is unsound for EG and AF queries" << std::endl;
                std::exit(1);
            }

            // SMC Quantifier Handling
            if (query->getQuantifier() == PF || query->getQuantifier() == PG) {
                SMCQuery* smcQuery = static_cast<SMCQuery*>(query);
                RealMarking marking(&tapn, *initialMarking);

                if(options.isBenchmarkMode()) {
                    ProbabilityEstimation estimator(tapn, marking, smcQuery, options, options.getBenchmarkRuns());
                    ComputeAndPrint(tapn, estimator, options, query);
                } else if(options.getSmcTraces() > 0) {
                    SMCTracesGenerator estimator(tapn, marking, smcQuery, options);
                    ComputeAndPrint(tapn, estimator, options, query);
                } else if(smcQuery->getSmcSettings().compareToFloat) {
                    ProbabilityFloatComparison estimator(tapn, marking, smcQuery, options);
                    ComputeAndPrint(tapn, estimator, options, query);
                } else {
                    ProbabilityEstimation estimator(tapn, marking, smcQuery, options);
                    ComputeAndPrint(tapn, estimator, options, query);
                }
            } else {
                std::cerr << "Unsupported quantifier for SMC verification." << std::endl;
            }

            return 0;
        }

        template<typename T>
        void VerifyAndPrint(TAPN::TimedArcPetriNet &tapn, Verification<T> &verifier, VerificationOptions &options,
                            AST::Query *query) {
            bool result = (!options.isWorkflow() && (query->getQuantifier() == AG || query->getQuantifier() == AF))
                          ? !verifier.run() : verifier.run();

            if (options.getGCDLowerGuardsEnabled()) {
                std::cout << "Lowering all guards by greatest common divisor: " << tapn.getGCD() << std::endl;
            }
            std::cout << std::endl;

            verifier.printStats();
            verifier.printTransitionStatistics();
            verifier.printPlaceStatistics();

            std::cout << "Query is " << (result ? "satisfied" : "NOT satisfied") << "." << std::endl;
            std::cout << "Max number of tokens found in any reachable marking: ";
            if (verifier.maxUsedTokens() > options.getKBound())
                std::cout << ">" << options.getKBound() << std::endl;
            else
                std::cout << verifier.maxUsedTokens() << std::endl;

            if (options.getTrace() != VerificationOptions::NO_TRACE) {
                if ((query->getQuantifier() == EF && result) || (query->getQuantifier() == AG && !result) ||
                    (query->getQuantifier() == EG && result) || (query->getQuantifier() == AF && !result) ||
                    (options.isWorkflow())) {
                    verifier.getTrace();
                } else {
                    std::cout << "A trace could not be generated due to the query result" << std::endl;
                }
            }
        }

        void ComputeAndPrint(TAPN::TimedArcPetriNet &tapn, SMCVerification &estimator, VerificationOptions &options,
                            AST::Query *query) {
            std::cout << "Starting SMC..." << std::endl;

            if(options.isParallel()) {
                estimator.parallel_run();
            } else {
                estimator.run();
            }

            estimator.printStats();
            estimator.printTransitionStatistics();
            estimator.printPlaceStatistics();

            if(options.getSmcTraces() > 0) {
                estimator.getTrace();
            }

            std::cout << "Max number of tokens found in any reachable marking: ";
            std::cout << estimator.maxUsedTokens() << std::endl;

            estimator.printResult();
        }

    } // namespace DiscreteVerification
} // namespace VerifyTAPN
