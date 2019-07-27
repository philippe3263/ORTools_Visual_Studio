
// Authors : Ph. Lacomme (placomme@isima.fr)
//
// Date : 2019, July 27th - saturday
//
// Validation on Visual Studio 2017
//
//
// Show how to use the SAT solver for the N-Queens problem
//
//


#include <iostream>
using namespace std;

#define _SECURE_SCL 0
#define _ALLOW_ITERATOR_DEBUG_LEVEL_MISMATCH
#define NOMINMAX

#define _SILENCE_CXX17_OLD_ALLOCATOR_MEMBERS_DEPRECATION_WARNING
#define _SILENCE_ALL_CXX17_DEPRECATION_WARNINGS


// solver PPC Sat
#include "ortools/sat/cp_model.h"

using namespace operations_research;
using namespace sat;

    void demo_N_reine()
	{
		const int n = 4;  // size of the problem

		CpModelBuilder cp_model;

		const Domain domain(0, n-1);

		std::vector<IntVar> Q;
		for (int i = 0; i < n; ++i) {
			Q.push_back(
				cp_model.NewIntVar(domain).WithName(absl::StrCat("var_", i)));
		}

       	// constraint 1. All Q have different values		
		cp_model.AddAllDifferent({Q});

		// constraint 2.
		for (int i = 0; i < n - 1; i++)
		{
			for (int j = i + 1; j < n; j++)
			{
				LinearExpr partie_gauche = LinearExpr::ScalProd({ Q[i], Q[j] }, { 1, -1 });
				cp_model.AddNotEqual(partie_gauche, (j-i));
			}
		}

		// constraint 3.
		for (int i = 0; i < n - 1; i++)
		{
			for (int j = i + 1; j < n; j++)
			{
				LinearExpr partie_gauche = LinearExpr::ScalProd({ Q[i], Q[j] }, { 1, -1 });
				cp_model.AddNotEqual(partie_gauche, -(j - i));
			}
		}

		Model model;

		// Sets a time limit of 10 seconds.
		SatParameters parameters;
		parameters.set_max_time_in_seconds(10.0);
		model.Add(NewSatParameters(parameters));

		const CpSolverResponse response = SolveCpModel(cp_model.Build(), &model);
		cout << CpSolverResponseStats(response) << endl;

		if (response.status() == CpSolverStatus::FEASIBLE) {

			for (int i = 0; i < n; i++)
			{
				const int64 valeur_Q = SolutionIntegerValue(response, Q[i]);

				stringstream ss;
				ss << "Q_" << i;
				string str = ss.str();

				cout << str << " = " << valeur_Q << endl;
			}
		}

	}


//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//

 int main(int argc, char** argv) {

    // the N_Queens
	demo_N_reine();

	
	return EXIT_SUCCESS;
}
