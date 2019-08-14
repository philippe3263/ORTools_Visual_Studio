
// Authors : Ph. Lacomme (placomme@isima.fr)
//
// Date : 2019, August 14th - Wenesday
//
// Validation on Visual Studio 2017
//
//
// Show how to use the SAT solver with a non linear constraint
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

		// contrainte C1
		// x + 2y <= 14
		LinearExpr Left_Part_C1 = LinearExpr::ScalProd({ x, y }, {1, 2 });
		cp_model.AddLessOrEqual(Left_Part_C1, 14);

		// contrainte C2
		// x*y+z^2 <= 2.
			const Domain domain2(0, 100);
			IntVar produit = cp_model.NewIntVar(domain2).WithName("produit");
			IntVar produit2 = cp_model.NewIntVar(domain2).WithName("produit2");
			// part 1
			{
				std::vector<IntVar> liste_variables;
				liste_variables.push_back(x);
				liste_variables.push_back(y);
				auto span_variable = absl::Span<const IntVar>(liste_variables);
				// produit = x*y
				cp_model.AddProductEquality(produit, span_variable);
			}


			// part 2.
			{
			
				std::vector<IntVar> liste_variables;
				liste_variables.push_back(z);
				liste_variables.push_back(z);
				auto span_variable = absl::Span<const IntVar>(liste_variables);
				// produit2 =  z*z
				cp_model.AddProductEquality(produit2, span_variable);
			}

			// part 3 : Left_Part_C2 = produit + produit2
			LinearExpr Left_Part_C2 = LinearExpr::ScalProd({produit, produit2}, {1, 1});
			// partie 4. partie_gauche<=2
			cp_model.AddLessOrEqual(Left_Part_C2, 2);
	
		// contrainte C3
		//x-y <= 2
		LinearExpr Left_Part_C3 = LinearExpr::ScalProd({ x, y }, { 1, -1 });
		cp_model.AddLessOrEqual(Left_Part_C3, 2);

		// objective = max 3x + 4y + z
		LinearExpr Obj = LinearExpr::ScalProd({ x, y, z }, { 3, 4, 1 });
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

			const int64 valeur_z = SolutionIntegerValue(response, z);
			cout << "z= " << valeur_z << endl;
		}
	}
	

	

//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//
//-------------------------------------------------------------------------------//

 int main(int argc, char** argv) {


	cout << endl;
	cout << "Resolution with the SAT solver " << endl;
	demo_CP();


	
	return EXIT_SUCCESS;
}
