
// Authors : Ph. Lacomme and G. Rault
// Date : 2019, August 
//
//
// This is the Visual Studio 2017 version
//
// Resolution using the routing ORTOOLS library of the DLP01.txt instance
//    ( see https://github.com/philippe3263/ORTools_Visual_Studio )
//
//
// --------------------------------------------------------------------------------------------------------------------------------
//
// model performances for the DLP01 instance (40 nodes)
//
// Machine used for benchmark :  Xeon E5-1630 3.70Ghz with 32 GO of memory (Windows 7 OS)
//
// Iteration : 0 Cost : 1348 Time : 0.0100006
// Iteration: 1 Cost : 1254 Time : 0.0110006
// Iteration : 2 Cost : 1234 Time : 0.0130007
// Iteration : 4 Cost : 1185 Time : 0.016001
// Iteration : 7 Cost : 1173 Time : 0.0180012
// Iteration : 9 Cost : 1137 Time : 0.0200013
// Iteration : 11 Cost : 1120 Time : 0.0220014
// Iteration : 15 Cost : 1106 Time : 0.0260017
// Iteration : 19 Cost : 1091 Time : 0.0320018
// Iteration : 21 Cost : 1067 Time : 0.033002
// Iteration : 23 Cost : 1054 Time : 0.0370022
// Iteration : 24 Cost : 1030 Time : 0.0420024
// Iteration : 25 Cost : 1015 Time : 0.0460027
// Iteration : 28 Cost : 999 Time : 0.0620037
// Iteration : 90 Cost : 979 Time : 0.564299
// Iteration : 93 Cost : 967 Time : 0.571486
// Iteration : 157 Cost : 957 Time : 1.37866
// Iteration : 160 Cost : 944 Time : 1.3864
// Iteration : 164 Cost : 923 Time : 1.39866
// Iteration : 168 Cost : 910 Time : 1.42736
// Iteration : 171 Cost : 900 Time : 1.43714
// 
// Best solution found
// 
// Route for Vehicle 0 : 0 (0) -> 39 (58) -> 18 (120) -> 26 (96) -> 40 (12) -> 32 (12) -> 0
// Distance of the route : 98
// Quantity of the route : 298
// 
// Route for Vehicle 1 : 0 (0) -> 33 (12) -> 24 (25) -> 34 (78) -> 13 (120) -> 3 (58) -> 0
// Distance of the route : 110
// Quantity of the route : 293
// 
// Route for Vehicle 3 : 0 (0) -> 23 (89) -> 0
// Distance of the route : 16
// Quantity of the route : 89
// 
// Route for Vehicle 4 : 0 (0) -> 19 (12) -> 20 (14) -> 6 (78) -> 28 (58) -> 22 (65) -> 37 (5) -> 5 (0) -> 12 (58) -> 0
// Distance of the route : 229
// Quantity of the route : 290
// 
// Route for Vehicle 5 : 0 (0) -> 7 (96) -> 30 (14) -> 25 (36) -> 35 (96) -> 0
// Distance of the route : 71
// Quantity of the route : 242
// 
// Route for Vehicle 6 : 0 (0) -> 16 (14) -> 21 (25) -> 2 (14) -> 27 (14) -> 17 (58) -> 29 (120) -> 36 (10) -> 11 (14) -> 8 (10) -> 38 (14) ->0
// Distance of the route : 127
// Quantity of the route : 293
// 
// Route for Vehicle 7 : 0 (0) -> 9 (5) -> 4 (120) -> 10 (2) -> 15 (78) -> 31 (58) -> 1 (23) -> 14 (12) -> 0
// Distance of the route : 248
// Quantity of the route : 298
// 
// Problem solved in 120015ms
// Cout total : 899
// 
// --------------------------------------------------------------------------------------------------------------------------------

#include <iostream>
using namespace std;

#define _SECURE_SCL 0
#define _ALLOW_ITERATOR_DEBUG_LEVEL_MISMATCH
#define NOMINMAX

#define _SILENCE_CXX17_OLD_ALLOCATOR_MEMBERS_DEPRECATION_WARNING
#define _SILENCE_ALL_CXX17_DEPRECATION_WARNINGS


#include "ortools/base/logging.h"

// routing Solveur
#include <vector>
#include "ortools/constraint_solver/routing.h"
#include "ortools/constraint_solver/routing_enums.pb.h"
#include "ortools/constraint_solver/routing_index_manager.h"
#include "ortools/constraint_solver/routing_parameters.h"

#include "ortools/base/commandlineflags.h"
#include "ortools/base/commandlineflags.h"
#include "ortools/base/file.h"
#include "ortools/base/mathutil.h"
#include "ortools/base/status.h"
#include "ortools/base/protoutil.h"

#include <cstdlib>
#include <sstream>
#include <fstream> 

using namespace operations_research;





struct DataModel {
	const std::vector<std::vector<int64>> distance_matrix{
		{0, 57, 22, 30, 94, 63, 105, 28, 45, 58, 72, 42, 44, 46, 39, 80, 28, 47, 42, 37, 88, 30, 87, 8, 30, 14, 38, 42, 100, 52, 18, 73, 19, 24, 33, 13, 46, 82, 28, 39, 37},
		{57, 0, 67, 29, 88, 70, 99, 45, 40, 31, 35, 46, 63, 15, 23, 35, 77, 50, 42, 25, 40, 75, 81, 49, 26, 43, 40, 45, 95, 41, 41, 16, 48, 36, 23, 44, 40, 90, 32, 55, 35},
		{22, 67, 0, 33, 79, 44, 90, 15, 26, 60, 74, 24, 23, 49, 56, 83, 10, 28, 71, 39, 73, 7, 60, 23, 46, 25, 60, 22, 85, 37, 29, 76, 41, 44, 44, 30, 30, 58, 30, 61, 65},
		{30, 29, 33, 0, 59, 54, 83, 19, 11, 29, 43, 16, 37, 17, 24, 51, 43, 28, 40, 8, 40, 41, 65, 21, 15, 16, 38, 19, 78, 23, 12, 44, 33, 24, 9, 24, 21, 73, 5, 46, 33},
		{94, 88, 79, 59, 0, 38, 7, 69, 61, 30, 23, 58, 58, 62, 83, 37, 77, 44, 99, 52, 19, 87, 31, 86, 74, 80, 97, 58, 16, 37, 78, 93, 114, 83, 63, 91, 42, 43, 63, 133, 92},
		{63, 70, 44, 54, 38, 0, 50, 34, 28, 35, 36, 25, 20, 50, 63, 51, 40, 19, 78, 36, 31, 41, 16, 54, 53, 49, 76, 23, 45, 20, 46, 81, 83, 62, 47, 60, 26, 20, 37, 102, 71},
		{105, 99, 90, 83, 7, 50, 0, 79, 72, 37, 31, 69, 71, 85, 107, 45, 100, 73, 123, 77, 26, 98, 30, 97, 98, 91, 121, 69, 10, 44, 89, 116, 125, 107, 87, 102, 50, 43, 90, 144, 116},
		{28, 45, 15, 19, 69, 34, 79, 0, 11, 46, 60, 11, 24, 34, 41, 68, 25, 19, 57, 25, 62, 23, 51, 22, 32, 16, 55, 11, 75, 39, 17, 61, 43, 41, 30, 28, 19, 55, 15, 63, 50},
		{45, 40, 26, 11, 61, 28, 72, 11, 0, 32, 46, 2, 23, 25, 35, 55, 36, 12, 51, 11, 54, 34, 44, 24, 26, 19, 49, 5, 67, 17, 16, 56, 65, 35, 24, 29, 11, 48, 9, 57, 44},
		{58, 31, 60, 29, 30, 35, 37, 46, 32, 0, 12, 34, 47, 23, 54, 24, 65, 28, 69, 21, 11, 63, 43, 50, 45, 44, 67, 43, 61, 19, 42, 47, 63, 54, 34, 55, 26, 55, 33, 75, 63},
		{72, 35, 74, 43, 23, 36, 31, 60, 46, 12, 0, 57, 57, 32, 68, 14, 76, 43, 83, 35, 5, 77, 42, 64, 58, 58, 81, 57, 40, 34, 55, 51, 77, 68, 48, 69, 41, 56, 47, 89, 76},
		{42, 46, 24, 16, 58, 25, 69, 11, 2, 34, 57, 0, 21, 30, 38, 56, 34, 8, 53, 13, 51, 32, 41, 35, 28, 29, 51, 3, 64, 14, 27, 61, 63, 38, 26, 40, 8, 45, 12, 82, 46},
		{44, 63, 23, 37, 58, 20, 71, 24, 23, 47, 57, 21, 0, 47, 60, 71, 19, 19, 75, 39, 52, 20, 37, 52, 50, 46, 73, 18, 66, 28, 44, 79, 80, 60, 48, 57, 27, 34, 34, 99, 68},
		{46, 15, 49, 17, 62, 50, 85, 34, 25, 23, 32, 30, 47, 0, 42, 37, 59, 36, 58, 14, 34, 61, 67, 38, 33, 32, 55, 31, 81, 26, 30, 31, 51, 42, 14, 43, 25, 76, 21, 64, 51},
		{39, 23, 56, 24, 83, 63, 107, 41, 35, 54, 68, 38, 60, 42, 0, 60, 66, 46, 17, 32, 63, 63, 88, 33, 11, 33, 15, 41, 102, 46, 29, 38, 27, 16, 20, 29, 45, 97, 28, 30, 10},
		{80, 35, 83, 51, 37, 51, 45, 68, 55, 24, 14, 56, 71, 37, 60, 0, 90, 53, 79, 45, 19, 87, 57, 74, 69, 69, 77, 75, 54, 45, 66, 45, 88, 78, 54, 79, 51, 71, 58, 92, 72},
		{28, 77, 10, 43, 77, 40, 100, 25, 36, 65, 76, 34, 19, 59, 66, 90, 0, 39, 82, 50, 71, 2, 56, 33, 57, 35, 65, 37, 85, 48, 39, 86, 47, 52, 55, 39, 47, 54, 40, 67, 64},
		{47, 50, 28, 28, 44, 19, 73, 19, 12, 28, 43, 8, 19, 36, 46, 53, 39, 0, 62, 21, 38, 35, 36, 39, 37, 33, 60, 7, 68, 8, 31, 65, 67, 47, 32, 44, 6, 39, 21, 86, 55},
		{42, 42, 71, 40, 99, 78, 123, 57, 51, 69, 83, 53, 75, 58, 17, 79, 82, 62, 0, 48, 79, 72, 104, 38, 24, 38, 4, 58, 118, 62, 43, 58, 23, 19, 36, 32, 61, 113, 44, 14, 10},
		{37, 25, 39, 8, 52, 36, 77, 25, 11, 21, 35, 13, 39, 14, 32, 45, 50, 21, 48, 0, 31, 42, 58, 29, 24, 23, 46, 22, 72, 16, 21, 41, 42, 33, 13, 34, 15, 67, 12, 54, 42},
		{88, 40, 73, 40, 19, 31, 26, 62, 54, 11, 5, 51, 52, 34, 63, 19, 71, 38, 79, 31, 0, 81, 37, 80, 55, 74, 78, 52, 35, 30, 72, 56, 108, 64, 45, 85, 36, 51, 44, 86, 73},
		{30, 75, 7, 41, 87, 41, 98, 23, 34, 63, 77, 32, 20, 61, 63, 87, 2, 35, 72, 42, 81, 0, 59, 31, 54, 33, 64, 30, 93, 44, 37, 84, 45, 50, 52, 37, 38, 56, 38, 65, 63},
		{87, 81, 60, 65, 31, 16, 30, 51, 44, 43, 42, 41, 37, 67, 88, 57, 56, 36, 104, 58, 37, 59, 0, 79, 81, 73, 103, 51, 28, 38, 71, 98, 107, 90, 70, 84, 44, 13, 72, 126, 99},
		{8, 49, 23, 21, 86, 54, 97, 22, 24, 50, 64, 35, 52, 38, 33, 74, 33, 39, 38, 29, 80, 31, 79, 0, 21, 5, 33, 33, 92, 43, 9, 65, 21, 19, 24, 6, 37, 74, 19, 37, 29},
		{30, 26, 46, 15, 74, 53, 98, 32, 26, 45, 58, 28, 50, 33, 11, 69, 57, 37, 24, 24, 55, 54, 81, 21, 0, 21, 19, 33, 93, 37, 20, 47, 23, 14, 11, 21, 36, 88, 19, 35, 14},
		{14, 43, 25, 16, 80, 49, 91, 16, 19, 44, 58, 29, 46, 32, 33, 69, 35, 33, 38, 23, 74, 33, 73, 5, 21, 0, 33, 27, 86, 37, 3, 59, 26, 19, 20, 10, 32, 68, 13, 41, 29},
		{38, 40, 60, 38, 97, 76, 121, 55, 49, 67, 81, 51, 73, 55, 15, 77, 65, 60, 4, 46, 78, 64, 103, 33, 19, 33, 0, 55, 116, 60, 37, 56, 18, 14, 34, 26, 59, 111, 42, 18, 5},
		{42, 45, 22, 19, 58, 23, 69, 11, 5, 43, 57, 3, 18, 31, 41, 75, 37, 7, 58, 22, 52, 30, 51, 33, 33, 27, 55, 0, 64, 16, 26, 61, 62, 42, 30, 39, 8, 43, 16, 81, 50},
		{100, 95, 85, 78, 16, 45, 10, 75, 67, 61, 40, 64, 66, 81, 102, 54, 85, 68, 118, 72, 35, 93, 28, 92, 93, 86, 116, 64, 0, 55, 84, 112, 120, 103, 83, 97, 73, 41, 86, 140, 112},
		{52, 41, 37, 23, 37, 20, 44, 39, 17, 19, 34, 14, 28, 26, 46, 45, 48, 8, 62, 16, 30, 44, 38, 43, 37, 37, 60, 16, 55, 0, 35, 57, 81, 47, 27, 48, 6, 41, 27, 68, 56},
		{18, 41, 29, 12, 78, 46, 89, 17, 16, 42, 55, 27, 44, 30, 29, 66, 39, 31, 43, 21, 72, 37, 71, 9, 20, 3, 37, 26, 84, 35, 0, 56, 30, 23, 16, 14, 29, 65, 11, 45, 34},
		{73, 16, 76, 44, 93, 81, 116, 61, 56, 47, 51, 61, 79, 31, 38, 45, 86, 65, 58, 41, 56, 84, 98, 65, 47, 59, 56, 61, 112, 57, 56, 0, 64, 52, 39, 60, 56, 106, 48, 69, 51},
		{19, 48, 41, 33, 114, 83, 125, 43, 65, 63, 77, 63, 80, 51, 27, 88, 47, 67, 23, 42, 108, 45, 107, 21, 23, 26, 18, 62, 120, 81, 30, 64, 0, 11, 34, 14, 66, 102, 35, 20, 17},
		{24, 36, 44, 24, 83, 62, 107, 41, 35, 54, 68, 38, 60, 42, 16, 78, 52, 47, 19, 33, 64, 50, 90, 19, 14, 19, 14, 42, 103, 47, 23, 52, 11, 0, 22, 14, 45, 97, 29, 21, 10},
		{33, 23, 44, 9, 63, 47, 87, 30, 24, 34, 48, 26, 48, 14, 20, 54, 55, 32, 36, 13, 45, 52, 70, 24, 11, 20, 34, 30, 83, 27, 16, 39, 34, 22, 0, 24, 26, 78, 17, 49, 29},
		{13, 44, 30, 24, 91, 60, 102, 28, 29, 55, 69, 40, 57, 43, 29, 79, 39, 44, 32, 34, 85, 37, 84, 6, 21, 10, 26, 39, 97, 48, 14, 60, 14, 14, 24, 0, 42, 79, 24, 31, 24},
		{46, 40, 30, 21, 42, 26, 50, 19, 11, 26, 41, 8, 27, 25, 45, 51, 47, 6, 61, 15, 36, 38, 44, 37, 36, 32, 59, 8, 73, 6, 29, 56, 66, 45, 26, 42, 0, 46, 25, 67, 55},
		{82, 90, 58, 73, 43, 20, 43, 55, 48, 55, 56, 45, 34, 76, 97, 71, 54, 39, 113, 67, 51, 56, 13, 74, 88, 68, 111, 43, 41, 41, 65, 106, 102, 97, 78, 79, 46, 0, 54, 122, 91},
		{28, 32, 30, 5, 63, 37, 90, 15, 9, 33, 47, 12, 34, 21, 28, 58, 40, 21, 44, 12, 44, 38, 72, 19, 19, 13, 42, 16, 86, 27, 11, 48, 35, 29, 17, 24, 25, 54, 0, 50, 37},
		{39, 55, 61, 46, 133, 102, 144, 63, 57, 75, 89, 82, 99, 64, 30, 92, 67, 86, 14, 54, 86, 65, 126, 37, 35, 41, 18, 81, 140, 68, 45, 69, 20, 21, 49, 31, 67, 122, 50, 0, 20},
		{37, 35, 65, 33, 92, 71, 116, 50, 44, 63, 76, 46, 68, 51, 10, 72, 64, 55, 10, 42, 73, 63, 99, 29, 14, 29, 5, 50, 112, 56, 34, 51, 17, 10, 29, 24, 55, 91, 37, 20, 0},
			};

	std::vector<int64> demands = { 0, 23,14, 58,120,	0,	78,	96,	10,	5,	2,	14,	58,	120,	12,	78,	14,	58,	120,	12,	14,	25,	65	,89,	25,	36,	96,	14,	58,	120,	14,	58,	12,	12,	78,	96,	10,	5,	14,	58,	12
	};
	std::vector<int64> vehicle_capacities = { 300,300,300,300,300,300,300,300,300,300 };

	const int num_vehicles = 10;
	const RoutingIndexManager::NodeIndex depot{ 0 };
};


namespace {
	class LoggerMonitor : public SearchMonitor {
	public:
		LoggerMonitor(const DataModel data,
			RoutingModel* routing,
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
				int64 cout_total = 0;
				int64 max_route_distance{ 0 };
				best_result_ = objective->Min();
				
				cout << "Iteration : " << iteration_counter_ << " Cost : " << (int64)(best_result_) << " Time : " << 1e-9 * (absl::GetCurrentTimeNanos() - start_time_) << std::endl;
				
				/* to have the full details of each solution, use the following code : 

				for (int route_nbr = 0; route_nbr < routing_->vehicles(); route_nbr++) {
					cout << "   Route for Vehicle " << route_nbr << ":" << endl;
					std::stringstream route;
					route << "   ";

					// for (int64 index = routing_->Start(route_nbr); !routing_->IsEnd(index); index = routing_->NextVar(index)->Value()) 
					int64 index = routing_->Start(route_nbr);
					while (!routing_->IsEnd(index))
					{
						index = routing_->NextVar(index)->Value();
						route << manager_->IndexToNode(index).value() << " -> ";
					}
					int64 end_index = routing_->End(route_nbr);
					int64 route_distance = routing_->GetMutableDimension("Distance")->CumulVar(end_index)->Min();
					cout << route.str() << manager_->IndexToNode(end_index).value() << endl;;
					cout << "   Distance of the route: " << route_distance << endl;
					cout_total = cout_total + route_distance;
					max_route_distance = std::max(route_distance, max_route_distance);
				}

				cout << endl;
				cout << "Solution cost: " << cout_total << endl;
				cout << "---------------" << endl;
				*/


			}

			++iteration_counter_;
			/* if (iteration_counter_ >= std::pow(2, pow_)) {
				std::cout << "Iteration : " << iteration_counter_ << std::endl;
				++pow_;
			}*/
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


void PrintSolution(const DataModel& data, const RoutingIndexManager& manager,
	const RoutingModel& routing, const Assignment& solution) {

	int64 max_route_distance{ 0 };
	int64 totalcout = 0;

	cout << endl;
	cout << "Best solution found" << endl;
	for (int vehicle_id = 0; vehicle_id < data.num_vehicles; ++vehicle_id) {
		int64 index = routing.Start(vehicle_id);
		LOG(INFO) << "Route for Vehicle " << vehicle_id << ":";
		int64 route_distance{ 0 };
		std::stringstream route;
		int total_quantity = 0;
		while (routing.IsEnd(index) == false) {
			int numero_noeud = manager.IndexToNode(index).value();
			int quantity = data.demands[numero_noeud];
			total_quantity = total_quantity + quantity;
			route << manager.IndexToNode(index).value() << " (" << quantity << ") -> ";
			int64 previous_index = index;
			index = solution.Value(routing.NextVar(index));
			route_distance += const_cast<RoutingModel&>(routing).GetArcCostForVehicle(
				previous_index, index, int64{ vehicle_id });
		}
		LOG(INFO) << route.str() << manager.IndexToNode(index).value();
		LOG(INFO) << "Distance of the route: " << route_distance;
		LOG(INFO) << "Quantity of the route: " << total_quantity;

		max_route_distance = std::max(route_distance, max_route_distance);
		totalcout = totalcout + route_distance;
	}

	cout << "Problem solved in " << routing.solver()->wall_time() << "ms" << endl;
	cout << "Cout total: " << totalcout << endl;
	cout << endl;
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


	// Add Distance constraint.
	routing.AddDimension(transit_callback_index,
		0,
		300000,		 // vehicle maximal trip
		true,		// start cumul to zero
		"Distance");
	const RoutingDimension& distance_dimension =
		routing.GetDimensionOrDie("Distance");
	const_cast<RoutingDimension&>(distance_dimension).SetSpanCostCoefficientForAllVehicles(1);

	// 
	RoutingSearchParameters searchParameters = DefaultRoutingSearchParameters();

	// Setting first solution heuristic.
	// to obtain one basic initial solution use the following line
	searchParameters.set_first_solution_strategy(
		FirstSolutionStrategy::PATH_CHEAPEST_ARC);
	searchParameters.set_local_search_metaheuristic(
		LocalSearchMetaheuristic::GUIDED_LOCAL_SEARCH
	);

	int FLAGS_time_limit_in_ms = 120000; // ms
	CHECK_OK(util_time::EncodeGoogleApiProto(absl::Milliseconds(FLAGS_time_limit_in_ms),
		searchParameters.mutable_time_limit())
	);

	const int demand_callback_index = routing.RegisterUnaryTransitCallback(
		[&data, &manager](int64 from_index) -> int64 {
			// Convert from routing variable Index to demand NodeIndex.
			int from_node = manager.IndexToNode(from_index).value();
			return data.demands[from_node];
		});

	routing.AddDimensionWithVehicleCapacity(
		demand_callback_index,    // transit callback index
		int64{ 0 },                 // null capacity slack
		data.vehicle_capacities,  // vehicle maximum capacities
		true,                     // start cumul to zero
		"Capacity");



	const RoutingDimension& capacity_dimension =
		routing.GetDimensionOrDie("Capacity");


	routing.CloseModelWithParameters(searchParameters);

	//Add Intermediate solution monitor
	LoggerMonitor* const logger =
		MakeLoggerMonitor(data, &routing, &manager);

	routing.AddSearchMonitor(logger);


	// Solve the problem.
	const Assignment* solution = routing.SolveWithParameters(searchParameters);

	// Print solution on console.
	PrintSolution(data, manager, routing, *solution);
}


//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//

int main(void) {

	VrpGlobalSpan();

	cout << "press a key and enter next" << endl;
	char i;
	cin >> i;

	return EXIT_SUCCESS;
}
