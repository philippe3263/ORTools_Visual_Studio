
// Authors : Ph. Lacomme
// Date : 2019, July 27th
//
// Validation on Visual Studio 2017

#include <iostream>
using namespace std;

#define _SECURE_SCL 0
#define _ALLOW_ITERATOR_DEBUG_LEVEL_MISMATCH
#define NOMINMAX

#define _SILENCE_CXX17_OLD_ALLOCATOR_MEMBERS_DEPRECATION_WARNING
#define _SILENCE_ALL_CXX17_DEPRECATION_WARNINGS


#include "ortools/base/logging.h"

// PPC Solveur
#include "ortools/constraint_solver/constraint_solver.h"


using namespace operations_research;


	void N_Reines()
	{
		const int n = 4;  // size of the problem

		Solver solver("N_reines");

		IntVar **Q;
		Q = solver.MakeIntVarArray(n, 0, n-1, "Q");
		
		// définition des variables et de leur domaine
		Constraint *C0 = solver.MakeLessOrEqual(Q[0], n-1);
		solver.AddConstraint(C0);
		Constraint *C1 = solver.MakeLessOrEqual(Q[1], n - 1);
		solver.AddConstraint(C1);
		Constraint *C2 = solver.MakeLessOrEqual(Q[2], n - 1);
		solver.AddConstraint(C2);
		Constraint *C3 = solver.MakeLessOrEqual(Q[3], n - 1);
		solver.AddConstraint(C3);

		// Constraint 1.
		std::vector<IntVar*> vars;
		for (int i = 0; i < n; i++)
		{
			vars.push_back(Q[i]);
		}
		Constraint *C4 = solver.MakeAllDifferent(vars, true);
		solver.AddConstraint(C4);

		// Constraint 2.
		for (int i = 0 ; i < n-1; i++)
		{
			for (int j = i+1 ; j < n; j++)
			{
				IntExpr* pg = solver.MakeDifference(Q[i], Q[j]);
				Constraint *C = solver.MakeNonEquality(pg, j - i);
				solver.AddConstraint(C);
			}
		}

		// Constraint 3.
		for (int i = 0; i < n-1; i++)
		{
			for (int j = i+1; j < n; j++)
			{
				IntExpr* pg = solver.MakeDifference(Q[i], Q[j]);
				Constraint *C = solver.MakeNonEquality(pg, -(j - i));
				solver.AddConstraint(C);
			}
		}

		DecisionBuilder* const db = solver.MakePhase(vars, Solver::CHOOSE_FIRST_UNBOUND, Solver::ASSIGN_MIN_VALUE);
		solver.NewSearch(db);

		bool search_for_a_solution = solver.NextSolution();

		if (search_for_a_solution == true)
		{
			std::cout << "Solution : ";
			for (int j = 0; j < n; j++)
			{
				cout << "Q[" << j << "]= " << Q[j]->Value() << " ";
			}
			cout << endl;

		}


		solver.EndSearch();

		cout << "--------------------" << endl;
		cout << "Number of solutions: " << solver.solutions() << endl;
		cout << "" << endl;
		cout << "Advanced usage:" << endl;
		cout << "Problem solved in " << solver.wall_time() << "ms" << endl;
		cout << "Memory usage: " << Solver::MemoryUsage() << " bytes" << endl;


	}



//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//

 int main(int argc, char** argv) {
	google::InitGoogleLogging(argv[0]);
	FLAGS_logtostderr = 1;

	

	cout << endl;
	cout << "Example of the N queens" << endl;
	N_Reines();

	return EXIT_SUCCESS;
}
