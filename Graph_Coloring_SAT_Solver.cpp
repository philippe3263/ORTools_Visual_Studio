
// Authors : Ph. Lacomme (placomme@isima.fr)
//
// Date : 2019, august 11th - wenesday
//
// Validation on Visual Studio 2017
//
//
// Show how to use the SAT solver for the Graph Coloring Problem
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
    
    int nb_max_color = 10;  // number of colors available
    
	void Graph_Coloring()
	{

		const int n = 10;             // size of the graph = number of nodes

		CpModelBuilder cp_model;

		// Graph definition
		
		int x[n][n] = { 0 }; // basic static definition with 0

        // x[i][j]=1 --> there is an arc from i to j
		x[0][2] = 1;		x[1][0] = 1; 		x[3][0] = 1;
		x[0][1] = 1; 		x[1][4] = 1; 		x[3][5] = 1;
		x[0][3] = 1; 		x[1][8] = 1; 		x[3][9] = 1;

		x[2][6] = 1; 		x[4][5] = 1; 		x[5][4] = 1;
		x[2][7] = 1; 		x[4][7] = 1; 		x[5][6] = 1;

		x[6][2] = 1; 		x[7][4] = 1;
		x[6][5] = 1; 		x[7][2] = 1;

		x[8][1] = 1; 		x[9][8] = 1;
		x[8][6] = 1; 		x[9][7] = 1;
		x[8][9] = 1; 		x[9][3] = 1;


		const Domain domain(1, nb_max_color);

		// variables
		std::vector<IntVar> C;
		

		// constraint 1. each node has one and only one color
		for (int i = 0; i < n; ++i) {
			C.push_back(
					cp_model.NewIntVar(domain).WithName(absl::StrCat("C_", i)));
		}

       	// constraint 2. if there is an arc from i to j then i and j must have different color		
		for (int i = 0; i < n; i++)
		{
			for (int j = 0; j < n; j++)
			{
				if (x[i][j] == 1)
				{

					LinearExpr Left_Part = LinearExpr::ScalProd({ C[i] }, { 1 });
					LinearExpr Right_Part = LinearExpr::ScalProd({ C[j] }, { 1 });

					cp_model.AddNotEqual(Left_Part, Right_Part);
				}
			}
		}

		

		Model model;

		// Sets a time limit of 10 seconds.
		SatParameters parameters;
		parameters.set_max_time_in_seconds(10.0);
		model.Add(NewSatParameters(parameters));

		const CpSolverResponse response = SolveCpModel(cp_model.Build(), &model);
		std::cout << CpSolverResponseStats(response) << std::endl;

		if (response.status() == CpSolverStatus::FEASIBLE)
		{
			cout << "solution found..." << endl;
			for (int i = 0; i < n; i++)
			{
				const int64 valeur_C = SolutionIntegerValue(response, C[i]);

				stringstream ss;
				ss << "C_" << i << "  =  ";
				string str = ss.str();
				cout << str << " = " << valeur_C << endl;
			}
			cout << endl;
		}
		else
			cout << "sorry, no solution" << endl;

	}

	


//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//

 int main(int argc, char** argv) {

     // Graph_Coloring resolution
	 nb_max_color = 10;
	 cout << "check if a solution with 10 colors exists" << endl;
	 Graph_Coloring(); 

	 // Graph_Coloring resolution
	 nb_max_color = 4;
	 cout << "check if a solution with 4 colors exists" << endl;
	 Graph_Coloring(); 

	 // Graph_Coloring resolution
	 nb_max_color = 3;
	 cout << "check if a solution with 3 colors exists" << endl;
	 Graph_Coloring();

	return EXIT_SUCCESS;
}
