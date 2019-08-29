
// Authors : Ph. Lacomme and G. Rault
// Date : 2019, August 
//
//
// This is the Visual Studio 2017 version
// of the basic example provided by Google at
// https://developers.google.com/optimization/routing/vrp
//
//

#include <iostream>
using namespace std;

#define _SECURE_SCL 0
#define _ALLOW_ITERATOR_DEBUG_LEVEL_MISMATCH
#define NOMINMAX

#define _SILENCE_CXX17_OLD_ALLOCATOR_MEMBERS_DEPRECATION_WARNING
#define _SILENCE_ALL_CXX17_DEPRECATION_WARNINGS


#include "ortools/base/logging.h"
#include "ortools/base/protoutil.h"

// routing Solveur
#include <vector>
#include "ortools/constraint_solver/constraint_solver.h"
#include "ortools/constraint_solver/routing.h"
#include "ortools/constraint_solver/routing_enums.pb.h"
#include "ortools/constraint_solver/routing_index_manager.h"
#include "ortools/constraint_solver/routing_parameters.h"


using namespace operations_research;


struct DataModel {
	const std::vector<std::vector<int64>> distance_matrix{
		{0, 548, 776, 696, 582, 274, 502, 194, 308, 194, 536, 502, 388, 354, 468,
		 776, 662},
		{548, 0, 684, 308, 194, 502, 730, 354, 696, 742, 1084, 594, 480, 674,
		 1016, 868, 1210},
		{776, 684, 0, 992, 878, 502, 274, 810, 468, 742, 400, 1278, 1164, 1130,
		 788, 1552, 754},
		{696, 308, 992, 0, 114, 650, 878, 502, 844, 890, 1232, 514, 628, 822,
		 1164, 560, 1358},
		{582, 194, 878, 114, 0, 536, 764, 388, 730, 776, 1118, 400, 514, 708,
		 1050, 674, 1244},
		{274, 502, 502, 650, 536, 0, 228, 308, 194, 240, 582, 776, 662, 628, 514,
		 1050, 708},
		{502, 730, 274, 878, 764, 228, 0, 536, 194, 468, 354, 1004, 890, 856, 514,
		 1278, 480},
		{194, 354, 810, 502, 388, 308, 536, 0, 342, 388, 730, 468, 354, 320, 662,
		 742, 856},
		{308, 696, 468, 844, 730, 194, 194, 342, 0, 274, 388, 810, 696, 662, 320,
		 1084, 514},
		{194, 742, 742, 890, 776, 240, 468, 388, 274, 0, 342, 536, 422, 388, 274,
		 810, 468},
		{536, 1084, 400, 1232, 1118, 582, 354, 730, 388, 342, 0, 878, 764, 730,
		 388, 1152, 354},
		{502, 594, 1278, 514, 400, 776, 1004, 468, 810, 536, 878, 0, 114, 308,
		 650, 274, 844},
		{388, 480, 1164, 628, 514, 662, 890, 354, 696, 422, 764, 114, 0, 194, 536,
		 388, 730},
		{354, 674, 1130, 822, 708, 628, 856, 320, 662, 388, 730, 308, 194, 0, 342,
		 422, 536},
		{468, 1016, 788, 1164, 1050, 514, 514, 662, 320, 274, 388, 650, 536, 342,
		 0, 764, 194},
		{776, 868, 1552, 560, 674, 1050, 1278, 742, 1084, 810, 1152, 274, 388,
		 422, 764, 0, 798},
		{662, 1210, 754, 1358, 1244, 708, 480, 856, 514, 468, 354, 844, 730, 536,
		 194, 798, 0},
	};
	const int num_vehicles = 4;
	const RoutingIndexManager::NodeIndex depot{ 0 };
};

// Monitor defined to display the new best solution during the search
namespace {
	class LoggerMonitor : public SearchMonitor {
	public:
		LoggerMonitor(const DataModel data, RoutingModel* routing,
			RoutingIndexManager* manager)
			: SearchMonitor(routing->solver())
			, data_(data)
			, routing_(routing)
			, manager_(manager)
			, solver_(routing->solver())
			, start_time_(absl::GetCurrentTimeNanos())
			, pow_(0)
			, iteration_counter_(0)
			, best_result_(kint64max)
			, prototype_(new Assignment(solver_)) {
			CHECK_NOTNULL(routing->CostVar());
			prototype_->AddObjective(routing->CostVar());
		}

		virtual void Init() {
			iteration_counter_ = 0;
			pow_ = 0;
			best_result_ = kint64max;
		}

		virtual bool AtSolution() {

			prototype_->Store();
			bool new_best = false;

			const IntVar* objective = prototype_->Objective();
			if (objective->Min() * 1.01 < best_result_) {
				int64 max_route_distance{ 0 };
				best_result_ = objective->Min();
				cout << "Iteration : " << iteration_counter_ << " Cost : " << (int64)(best_result_) << " Time : " << 1e-9 * (absl::GetCurrentTimeNanos() - start_time_) << std::endl;
				for (int route_nbr = 0; route_nbr < routing_->vehicles(); route_nbr++) {
					LOG(INFO) << "Route for Vehicle " << route_nbr << ":";
					std::stringstream route;
					for (int64 index = routing_->Start(route_nbr); !routing_->IsEnd(index); index = routing_->NextVar(index)->Value()) {
						route << manager_->IndexToNode(index).value() << " -> ";
					}
					int64 end_index = routing_->End(route_nbr);
					int64 route_distance = routing_->GetMutableDimension("Distance")->CumulVar(end_index)->Min();
					LOG(INFO) << route.str() << manager_->IndexToNode(end_index).value();
					LOG(INFO) << "Distance of the route: " << route_distance << "m";
					max_route_distance = std::max(route_distance, max_route_distance);
				}
				cout << "Maximum of the route distances: " << max_route_distance << "m" << endl;
			}

			++iteration_counter_;
			if (iteration_counter_ >= std::pow(2, pow_)) {
				std::cout << "Iteration : " << iteration_counter_ << std::endl;
				++pow_;
			}
			return true;
		}

		virtual void Copy(const SearchMonitor* const limit) {
			const LoggerMonitor* const copy_limit =
				reinterpret_cast<const LoggerMonitor * const>(limit);

			best_result_ = copy_limit->best_result_;
			iteration_counter_ = copy_limit->iteration_counter_;
			start_time_ = copy_limit->start_time_;
		}

		virtual SearchMonitor* MakeClone() const {
			return solver_->RevAlloc(new LoggerMonitor(data_, routing_, manager_));
		}

		std::vector<double> GetFinalScore() {
			return { (double)best_result_, 1e-9 * (absl::GetCurrentTimeNanos() - start_time_), (double)iteration_counter_ };
		}

		void GetFinalLog() {
			std::cout << "Final Iteration : " << iteration_counter_ << " Cost : " << (int64)(best_result_) << " Time : " << 1e-9 * (absl::GetCurrentTimeNanos() - start_time_) << std::endl;
		}

	private:
		const DataModel data_;
		RoutingModel* routing_;
		RoutingIndexManager* manager_;
		Solver* const solver_;
		int64 best_result_;
		double start_time_;
		int64 pow_;
		int64 iteration_counter_;
		std::unique_ptr<Assignment> prototype_;
	};

} // namespace

LoggerMonitor* MakeLoggerMonitor(const DataModel data, RoutingModel* routing, RoutingIndexManager* manager) {
	return routing->solver()->RevAlloc(new LoggerMonitor(data, routing, manager));
}

void PrintSolution(const DataModel data, const RoutingIndexManager& manager,
	const RoutingModel& routing, const Assignment& solution) {
	int64 max_route_distance{ 0 };
	for (int vehicle_id = 0; vehicle_id < data.num_vehicles; ++vehicle_id) {
		int64 index = routing.Start(vehicle_id);
		LOG(INFO) << "Route for Vehicle " << vehicle_id << ":";
		int64 route_distance{ 0 };
		std::stringstream route;
		while (routing.IsEnd(index) == false) {
			route << manager.IndexToNode(index).value() << " -> ";
			int64 previous_index = index;
			index = solution.Value(routing.NextVar(index));
			route_distance += const_cast<RoutingModel&>(routing).GetArcCostForVehicle(
				previous_index, index, int64{ vehicle_id });
		}
		LOG(INFO) << route.str() << manager.IndexToNode(index).value();
		LOG(INFO) << "Distance of the route: " << route_distance << "m";
		max_route_distance = std::max(route_distance, max_route_distance);
	}
	cout << "Maximum of the route distances: " << max_route_distance << "m" << endl;
	cout << "";
	cout << "Problem solved in " << routing.solver()->wall_time() << "ms" << endl;
}

void VrpGlobalSpan() {
	// Instantiate the data problem.
	DataModel data;

	// Create Routing Index Manager
	RoutingIndexManager manager(data.distance_matrix.size(), data.num_vehicles,
		data.depot);

	// Create Routing Model.
	RoutingModel routing(manager);

	// Create and register a transit callback.
	const int transit_callback_index = routing.RegisterTransitCallback(
		[&data, &manager](int64 from_index, int64 to_index) -> int64 {
			// Convert from routing variable Index to distance matrix NodeIndex.
			auto from_node = manager.IndexToNode(from_index).value();
			auto to_node = manager.IndexToNode(to_index).value();
			return data.distance_matrix[from_node][to_node];
		});

	// Define cost of each arc.
	routing.SetArcCostEvaluatorOfAllVehicles(transit_callback_index);

	// Add Distance constraint.
	routing.AddDimension(transit_callback_index, 0, 3000,
		true,  // start cumul to zero
		"Distance");
	const RoutingDimension& distance_dimension =
		routing.GetDimensionOrDie("Distance");
	const_cast<RoutingDimension&>(distance_dimension)
		.SetGlobalSpanCostCoefficient(100);

	// Setting first solution heuristic.
	RoutingSearchParameters searchParameters = DefaultRoutingSearchParameters();
	searchParameters.set_first_solution_strategy(
		FirstSolutionStrategy::PATH_CHEAPEST_ARC);
	searchParameters.set_local_search_metaheuristic(LocalSearchMetaheuristic::GUIDED_LOCAL_SEARCH);

	// Limit solve duration
	int64 time_limite_in_ms = 120000;
	CHECK_OK(util_time::EncodeGoogleApiProto(absl::Milliseconds(time_limite_in_ms),
		searchParameters.mutable_time_limit()));

	// Model definition is over
	routing.CloseModelWithParameters(searchParameters);

	//Add Intermediate solution monitor
	LoggerMonitor* const logger =
		MakeLoggerMonitor(data, &routing, &manager);
	routing.AddSearchMonitor(logger);

	// Solve the problem.
	const Assignment* solution = routing.SolveWithParameters(searchParameters);

	// Print solution on console.
	logger->GetFinalLog();
	PrintSolution(data, manager, routing, *solution);
}


//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//

int main(void) {

	VrpGlobalSpan();

	int lu;
	cout << "presser 1";
	cin >> lu;

	return EXIT_SUCCESS;
}
