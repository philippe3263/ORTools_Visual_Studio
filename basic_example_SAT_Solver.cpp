
// Authors : Ph. Lacomme (placomme@isima.fr)
//
// Date : 2019, July 27th - saturday
//
// Validation on Visual Studio 2017
//
//
// Show how to use the SAT solver.
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

// solver PPC Sat
#include "ortools/sat/cp_model.h"

using namespace operations_research;
using namespace sat;

	void demo_CP()
     {
		CpModelBuilder cp_model;

		const Domain domain(0, 10);
		const IntVar x = cp_model.NewIntVar(domain).WithName("x");
		const IntVar y = cp_model.NewIntVar(domain).WithName("y");
		const IntVar z = cp_model.NewIntVar(domain).WithName("z");

		// x + 2y <= 14
		LinearExpr partie_gauche = LinearExpr::ScalProd({ x, y }, {1, 2 });
		cp_model.AddLessOrEqual(partie_gauche, 14);

		// 3x - y >= 0
		LinearExpr partie_gauche2 = LinearExpr::ScalProd({ x, y }, { 3, -1 });
		cp_model.AddGreaterOrEqual(partie_gauche2, 0);

		//x-y <= 2
		LinearExpr partie_gauche3 = LinearExpr::ScalProd({ x, y }, { 1, -1 });
		cp_model.AddLessOrEqual(partie_gauche3, 2);

		// objective = max 3x + 4y
		LinearExpr Obj = LinearExpr::ScalProd({ x, y }, { 3, 4 });
		cp_model.Maximize(Obj);

		Model model;

		// Sets a time limit of 10 seconds.
		SatParameters parameters;
		parameters.set_max_time_in_seconds(10.0);
		model.Add(NewSatParameters(parameters));

		const CpSolverResponse response = SolveCpModel(cp_model.Build(), &model);
		cout << CpSolverResponseStats(response) << endl;
		
		if (response.status() == CpSolverStatus::OPTIMAL) {

			const int64 valeur_Obj = SolutionIntegerValue(response, Obj);
			cout << "Obj= " << valeur_Obj << endl;

			const int64 valeur_x = SolutionIntegerValue(response, x);
			cout << "x= " << valeur_x << endl;

			const int64 valeur_y = SolutionIntegerValue(response, y);
			cout << "y= " << valeur_y << endl;
		}
	}
	

	void demo_CP_2()
	{
		CpModelBuilder cp_model;

		const Domain domain(0, 2);
		const IntVar x = cp_model.NewIntVar(domain).WithName("x");
		const IntVar y = cp_model.NewIntVar(domain).WithName("y");
		const IntVar z = cp_model.NewIntVar(domain).WithName("z");

		cp_model.AddNotEqual(x, y);

		// Solving part.
		Model model;

		// Sets a time limit of 10 seconds.
		SatParameters parameters;
		parameters.set_max_time_in_seconds(10.0);
		model.Add(NewSatParameters(parameters));

		// Solve.
		const CpSolverResponse response = SolveCpModel(cp_model.Build(), &model);
		cout << CpSolverResponseStats(response) << endl;

		if (response.status() == CpSolverStatus::FEASIBLE) {
			cout << "x = " << SolutionIntegerValue(response, x) << endl;
			cout << "y = " << SolutionIntegerValue(response, y) << endl;
			cout << "z = " << SolutionIntegerValue(response, z) << endl;
		}
	}


//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//

 int main(int argc, char** argv) {

	// Example 1
	cout << endl;
	cout << "Resolution with the SAT solver " << endl;
	demo_CP();

	// Example 2
	cout << endl;
	cout << "Resolution with the SAT solver " << endl;
	demo_CP_2();
	
	
	return EXIT_SUCCESS;
}
