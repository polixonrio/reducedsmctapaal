#include <iostream>
#include <fstream>
#include "Core/TAPN/TAPNModelBuilder.hpp"
#include "Core/VerificationOptions.hpp"
#include "Core/TAPN/TimedPlace.hpp"
#include "DiscreteVerification/DeadlockVisitor.hpp"

#include <unfoldtacpn.h>
#include <Colored/ColoredPetriNetBuilder.h>
#include <memory>


using namespace VerifyTAPN::TAPN;

namespace VerifyTAPN {

    std::unique_ptr<AST::Query> parse_queries(const VerificationOptions& options,
        const unfoldtacpn::ColoredPetriNetBuilder& builder, const TimedArcPetriNet& net) {
        try {
            auto& queryFile = options.getQueryFile();
            std::ifstream qfile(queryFile);
            if (!qfile) {
                std::cerr << "Could not open " << queryFile << std::endl;
                std::exit(-1);
            } else {
                std::vector<std::pair < unfoldtacpn::PQL::Condition_ptr, std::string>> ast_queries;
                auto qnums = options.getQueryNumbers();
                size_t quid = 0;
                if (qfile.peek() == '<') { // assumed XML
                    if (qnums.empty()) {
                        std::cerr << "Missing query-indexes for query-file (which is identified as XML-format), assuming only first query is to be verified" << std::endl;
                        qnums.emplace(0);
                    }
                    quid = *qnums.begin();
                    ast_queries = unfoldtacpn::parse_xml_queries(builder, qfile, qnums);
                } else {
                    // not xml
                    if (qnums.size() > 0) {
                        std::cerr << "Queries not provided in XML-format, --xml-queries argument is ignored" << std::endl;
                    }
                    ast_queries = unfoldtacpn::parse_string_queries(builder, qfile);
                }
                if (ast_queries.empty()) {
                    std::cerr << "There was an error parsing " << queryFile << std::endl;
                    std::exit(-1);
                }

                if (!options.getOutputQueryFile().empty()) {
                    std::fstream of(options.getOutputQueryFile(), std::ios::out);
                    unfoldtacpn::PQL::to_xml(of, ast_queries);
                }
                return std::unique_ptr<Query>(AST::toAST(ast_queries[quid].first, net));
            }

        } catch (...) {
            std::cout << "There was an error parsing the query file." << std::endl;
            std::exit(-1);
        }
        return nullptr;
    }

    std::pair<std::vector<int>, std::unique_ptr<TAPN::TimedArcPetriNet>>
    build_net(unfoldtacpn::ColoredPetriNetBuilder& builder) {
        TAPNModelBuilder modelBuilder;
        builder.unfold(modelBuilder);
        return {modelBuilder.initialMarking(), std::unique_ptr<TAPN::TimedArcPetriNet>
            {modelBuilder.make_tapn()}};
    }

    std::pair<std::vector<int>, std::unique_ptr<TAPN::TimedArcPetriNet>>
    parse_net_file(unfoldtacpn::ColoredPetriNetBuilder& builder, const std::string& filename) {
        std::ifstream mf(filename);
        builder.parseNet(mf);
        mf.close();
        return build_net(builder);
    }

    std::unique_ptr<AST::Query> make_query(const unfoldtacpn::ColoredPetriNetBuilder& builder, VerificationOptions& options, const TimedArcPetriNet& net) {
        std::unique_ptr<Query> query;
        {
            query = parse_queries(options, builder, net);
            assert(query);
            if (options.getTrace() != VerificationOptions::NO_TRACE &&
                (query->getQuantifier() == AST::CF || query->getQuantifier() == AST::CG)) {
                std::cout << "Traces are not supported for game-synthesis" << std::endl;
                std::exit(1);
            }

            if (options.getTrace() == VerificationOptions::FASTEST_TRACE &&
                (options.getSearchType() != VerificationOptions::DEFAULT ||
                query->getQuantifier() == AST::EG || query->getQuantifier() == AST::AF ||
                options.getVerificationType() == VerificationOptions::TIMEDART)) {
                std::cout
                    << "Fastest trace-option is only supported for reachability queries with default search strategy and without time darts."
                    << std::endl;
                std::exit(1);
            } else if (options.getTrace() == VerificationOptions::FASTEST_TRACE) {
                options.setSearchType(VerificationOptions::MINDELAYFIRST);
            } else if (options.getSearchType() == VerificationOptions::DEFAULT) {
                options.setSearchType(VerificationOptions::COVERMOST);
            }
        }
        return query;
    }

}
