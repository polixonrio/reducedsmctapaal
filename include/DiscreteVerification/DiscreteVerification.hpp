/*
 * DiscreteVerification.hpp
 *
 *  Created on: 23 Feb 2012
 *      Author: jakob
 */

#ifndef DISCRETEVERIFICATION_HPP_
#define DISCRETEVERIFICATION_HPP_

#include "DataStructures/NonStrictMarking.hpp"
#include "VerificationTypes/Verification.hpp"
#include "VerificationTypes/ProbabilityEstimation.hpp"
#include "VerificationTypes/ProbabilityFloatComparison.hpp"
#include "VerificationTypes/SMCTracesGenerator.hpp"
#include "VerificationTypes/SMCVerification.hpp"

#include "Core/TAPN/TAPN.hpp"
#include "Core/Query/AST.hpp"
#include "Core/VerificationOptions.hpp"

#include <rapidxml.hpp>
#include <rapidxml_print.hpp>

#include <stack>
#include <iostream>


namespace VerifyTAPN { namespace DiscreteVerification {

    class DiscreteVerification {
    public:
        DiscreteVerification();

        virtual ~DiscreteVerification();

        static int run(TAPN::TimedArcPetriNet &tapn, const std::vector<int>& initialPlacement, AST::Query *query,
                       VerificationOptions &options);

    };
} }

#endif /* DISCRETEVERIFICATION_HPP_ */
