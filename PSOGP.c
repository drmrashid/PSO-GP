/*
Parameters
S := swarm size
K := maximum number of particles _informed_ by a given one
T := topology of the information links
w := first cognitive/confidence coefficient
c := second cognitive/confidence coefficient
R := random distribution of c
B := rule "to keep the particle in the box"

  Equations
  For each particle and each dimension
  v(t+1) = w*v(t) + R(c)*(p(t)-x(t)) + R(c)*(g(t)-x(t))
  x(t+1) = x(t) + v(t+1)
  where
  v(t) := velocity at time t
  x(t) := position at time t
  p(t) := best previous position of the particle
  g(t) := best previous position of the informants of the particle
  
	Default values
	S = 10+2*sqrt(D) where D is the dimension of the search space
	K = 3
	T := randomly modified after each step if there has been no improvement
	w = 1/(2*ln(2))
	c = 0.5 + ln(2)
	R = U(0..c), i.e. uniform distribution on [0, c]
	B := set the position to the min. (max.) value and the velocity to zero
	
	  Some results with the standard values
	  You may want to recode this program in another language. Also you may want to modify it
	  for your own purposes. Here are some results on classical test functions to help you to
	  check your code.
	  Dimension D=30
	  Acceptable error eps=0
	  Objective value f_min=0
	  Number of runs n_exec_max=50
	  Number of evaluations for each run eval_max=30000
	  
		Problem                            Mean best value    Standard deviation
		Parabola/Sphere on [-100, 100]^D        0                  0
		Griewank on [-600, 600]^D               0.018              0.024
		Rosenbrock/Banana on [-30, 30]^D       50.16              36.9
		Rastrigin on [-5.12, 5.12]^D           48.35              14.43
		Ackley on [-32, 32]^D                   1.12               0.85
		
		  Last updates
		  2006-02-27 Fixed a bug about minimal best value over several runs
		  2006-02-16 Fixed a bug (S_max for P, V, X, instead of D_max), thanks to Manfred Stickel
		  2006-02-16 replaced k by i x by xs (in perf()), because of possible confusion with K and X
		  2006-02-13  added De Jong's f4
*/
#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <float.h>

#define MAX_PROG_SIZE    25


#define	D_max 100  // Max number of dimensions of the search space
#define	S_max 100 // Max swarm size
#define R_max 200 // Max number of runs

struct position
{
	char string [MAX_PROG_SIZE+1];
	double x[D_max];
	double v[D_max];
	double f;
	int b;
};



// Sub-programs
double alea( double a, double b );
double perf( int s, int function ); // Fitness evaluation

// Global variables
int best; // Best of the best position (rank in the swarm)
int D; // Search space dimension
double E; // exp(1). Useful for some test functions
double f_min; // Objective(s) to reach
int nb_eval; // Total number of evaluations
double pi; // Useful for some test functions
struct position P[S_max]; // Best positions found by each particle
int S; // Swarm size
struct position X[S_max]; // Positions
double xmin[D_max], xmax[D_max]; // Intervals defining the search space

// File(s)
FILE * f_run;
FILE * f_run_combined;
// ***************************************************
// GP CODE
#define population X
#define STACK_SIZE       25
#define PCROSS            0.9
#define LINE_WIDTH      200

struct position new_population[S_max]; // Positions

double random_number()  /* single precision ok */
{
	double r;
	
	for (; (r = alea(0,1) ) >= 1.0; );
	
	return ( r );
	
}/* end random_number()*/

int random_point ( char string[] )
{
/*return a random point in the string, ie from pos zero to length of string -1
	*/
	return  ((int) (random_number() * (float) (strlen(string) )  ));
	
}/*end random_point ()*/


int matching_point ( char string[], int subtree )
/*Return: Point in string immediately after subtree starting at subtree*/
{
	int i;
	int dangling_limbs;
	
	if ( string[subtree] == '\0' )
		dangling_limbs = 0;         /*already at end of tree */
	else
		dangling_limbs = 1;
	
	for (i = subtree; dangling_limbs > 0; i++ )
	{
		switch (string [i])
		{
        case '+':
        case '-':
        case '*':
        case '/':         dangling_limbs++; /*function (all have two limbs)*/
			break;
			
			//        case '\0':        assert (1 == 0);  /*oh dear*/
			//                          break;
			
        default :         dangling_limbs--; /*terminal*/
			break;
		}
	}/*end for*/
	
	return ( i );
	
}/*end matching_point()*/



int random_function()
{
#define N_FUNCTIONS 4
	int function [ N_FUNCTIONS ] = { '+', '-', '*', '/'};
	
	return ( function [ (int) (random_number() * N_FUNCTIONS)] );
	
}/*end random_function()*/


int random_terminal()
{
#define N_TERMINALS 5
	int terminal [ N_TERMINALS ] = { 'x', 'v', 'p', 'g', 'c'};
	
	return ( terminal [ (int) (random_number() * N_TERMINALS)] );
	
	//   return ( 'x' );
	
}/*end random_terminal()*/


int random_tree (char buff[], int size)
/*generate random program, place in buff
//
//Inputs: size of buff
//
//Returns: length of tree
*/
{
	int dangling_limbs = 1;
	int i;
	
	for ( i = 0; (dangling_limbs > 0) && (i <= size) ; i++ )
	{  /*chose function or terminal at random*/
		
		if( random_number() > (float)(dangling_limbs*dangling_limbs+1)/(float)(size-i) )
		{
			buff[i] = random_function();
			dangling_limbs++;                 /*all operators have two limbs*/
		}
		else
		{
			buff[i] = random_terminal();
			dangling_limbs--;
		}
		
	}/*end for*/
	
	//  assert ( dangling_limbs == 0 ); /*Opps...*/
	
	return (i);
	
}/*end random_tree()*/

int splice  ( char output[], int outsize,
			 char buff1[],  int end1,
			 char buff2[],  int end2,
			 char buff3[],  int end3 )
			 /*returns: 0 if ok*/
{
	if (( end1 + end2 + end3 ) >= outsize ) return ( 1 );
	
	memcpy ( output,             buff1, end1 );
	memcpy ( &output[end1],      buff2, end2 );
	memcpy ( &output[end1+end2], buff3, end3 );
	
	output [end1+end2+end3] = '\0'; /*terminate string*/
	
	return ( 0 ); /*ie ok*/
	
}/*end splice()*/


mutate(int mum, int child)
/*make a single random change to mum from old population and store
//child in new_population */
{
	int mum_end1;
	int mum_start2, mum_end2;
	int mut_length;
	
	int sanity = 0;
	
	char buffer [MAX_PROG_SIZE];
	
	do {
		//  assert (sanity++ < 1000);
		
		mum_end1   = random_point ( population[mum].string );
		mum_start2 = matching_point ( population[mum].string, mum_end1 ); 
		mum_end2   = strlen ( population[mum].string );
		
		mut_length = random_tree ( buffer, MAX_PROG_SIZE );
		
	} while (splice ( 
		new_population[child].string, MAX_PROG_SIZE+1,
		population[mum].string, mum_end1,
		buffer, mut_length,
		&population[mum].string[mum_start2], mum_end2 - mum_start2 ) != 0 );
	
	/*display data */
	
	//parents[child].mum       = mum;
	//parents[child].mumcross  = mum_end1;
	//parents[child].dad       = MUTATE;
	//parents[child].dadcross  = mut_length;
	
	
}/*end mutate()*/


int   stack;
double  value_stack [STACK_SIZE][D_max];
char      op_stack [STACK_SIZE];
char  output_stack [STACK_SIZE][LINE_WIDTH];


push_operator ( char op )
{
	int d;
	op_stack [stack++]      = op;
	for( d = 0; d < D; d++ )
		value_stack [stack][d]     = 0.0;   /* keep it clean */
	//  output_stack [stack][0] = '\0';  /* and tidy      */
	
}/*end push_operator()*/


push_value ( double *value )
{
	int d;
	double a[D_max];
	double result[D_max];
	
	if ( (stack <= 0) || (op_stack[stack-1] != 0) )  /* operator on top of stack */
	{                                              /* or stack empty           */
		op_stack [ stack ]    = 0; /* operand on top of stack */
		for( d = 0; d < D; d++ )
			value_stack [stack][d] = value[d];
		stack++;
	}
	else
	{
		--stack;
		for( d = 0; d < D; d++ )
			a[d] = value_stack[stack][d];  /* pop first operand */
		switch (op_stack[--stack])   /* pop operator */
		{
        case '+':  for( d = 0; d < D; d++ )
					   result[d] = a[d] + value[d];
			break;
			
        case '-':  for( d = 0; d < D; d++ )
					   result[d] = a[d] - value[d];
			break;
			
        case '*':  for( d = 0; d < D; d++ )
					   result[d] = a[d] * value[d];
			break;
			
        case '/':  for( d = 0; d < D; d++ )
					   if (value[d] == 0.0)
						   result[d] = 1.0;
					   else
						   result[d] = a[d] / value[d];
					   break;
					   
					   //        default:
					   //                   assert (10 == 0 ); /* opps */
					   //                   break;
		}
		
		push_value ( result );
	}
	
}/*end push_value()*/

void prog_value (char string[], double *v, double *x, double *p, double *g, double c, double *output )
/* return value of program child in new_population with input*/
{
	int i, d;
	double c_array[D_max];
	
	stack = 0;
	
	for ( i = 0; string[i] != 0; i++ )
	{
		switch (string [i])
		{
        case '+':
        case '-':
        case '*':
        case '/':         push_operator(string[i]);
			break;
		case 'v':         push_value ( v );
			break;
		case 'x':         push_value ( x );
			break;
		case 'p':         push_value ( p );
			break;
		case 'g':         push_value ( g );
			break;
			/*		case 'w':         push_value ( w );
			break;*/
		case 'c':         for( d = 0; d < D; d++ )
							  c_array[d] = alea(0, c);
			push_value ( c_array );
			break;
			/*			
			default:          push_value ( input );
			break;*/
		}
	}/*end for*/
	
	//assert (stack == 1);
	
	/*printf("prog_value: %s = %e, input = %e\n", string, value_stack[0], input );
	*/
	--stack;
	for( d = 0; d < D; d++ )
		output[d] = value_stack[stack][d];
	//return (value_stack[--stack]); /*pop value*/
	
} /*end prog_value()*/



replace_old_population()
{
	int i;
	
	//  total_fitness  = new_sumfitness;
	/* best_prog - retain current value until new generation*/
	
	for (i = 0; i < S/* POPULATION_SIZE*/; i++ )
	{
		strcpy (population[i].string, new_population[i].string);
		//         population[i].fitness = new_population[i].fitness;
		//         population[i].f = new_population[i].f;
		//         population[i].hits    = new_population[i].hits;
	}
	
}/*end replace_old_population()*/

replace_with_best()
{
	int i;
	
	//  total_fitness  = new_sumfitness;
	/* best_prog - retain current value until new generation*/
	
	for (i = 0; i < S/* POPULATION_SIZE*/; i++ )
	{
		strcpy (population[i].string, P[i].string);
		//         population[i].fitness = new_population[i].fitness;
		//         population[i].f = new_population[i].f;
		//         population[i].hits    = new_population[i].hits;
	}
	
}/*end replace_old_population()*/


initialise_population()
{
	int i;
	
	for ( i=0; i < S/*POPULATION_SIZE*/; i++ )
    {
		population[i].string[0] = '\0';
		mutate (i,i);
		//       test_fitness(i);
    }
	
	//  display_stats();
	
	replace_old_population();
	
} /*end initialise_population() */


int select_parent()
/* return index or parent in old population*/
{
	/*consider binary chop if POPULATION_SIZE becomes big*/
	
	int i;
	
	double cumlative_fitness = 0.0;
	double r;
	double total_fitness = 0.0;
	
	for (i = 0; i < S/*POPULATION_SIZE*/; i++ )
    {
        total_fitness += S/(population[i].f+S);
		//        if ( r <= cumlative_fitness ) return (i);
    }
	
	r = total_fitness * random_number();
	
	for (i = 0; i < S/*POPULATION_SIZE*/; i++ )
    {
        cumlative_fitness += S/(population[i].f+S);
        if ( r <= cumlative_fitness ) return (i);
    }
	
	return ( S - 1 );
	
}/*end select_parent() */


crossover ( int mum, int dad, int child )

/*choose a random point in program from old population and another
//also from old population to produce a child which is stored in the new
//population */
{ 
	int mum_end1;
	int mum_start2, mum_end2;
	int dad_start, dad_end;
	
	int sanity = 0;
	
	do {
		//  assert (sanity++ < 1000);
		
		mum_end1   = random_point ( population[mum].string );
		mum_start2 = matching_point ( population[mum].string, mum_end1 ); 
		mum_end2   = strlen ( population[mum].string );
		
		dad_start = random_point ( population[dad].string );
		dad_end   = matching_point ( population[dad].string, dad_start );
		
	} while (splice ( 
		new_population[child].string, MAX_PROG_SIZE+1,
		population[mum].string, mum_end1,
		&population[dad].string[dad_start], dad_end - dad_start,
		&population[mum].string[mum_start2], mum_end2 - mum_start2 ) != 0 );
	
	/*display data */
	//parents[child].mum       = mum;
	//parents[child].mumcross  = mum_end1;
	//parents[child].dad       = dad;
	//parents[child].dadcross  = dad_start;
	
}/*end crossover ()*/

crossover_best ( int mum, int child )

/*choose a random point in program from old population and another
//also from old population to produce a child which is stored in the new
//population */
{ 
	int mum_end1;
	int mum_start2, mum_end2;
	int dad_start, dad_end;
	
	int sanity = 0;
	do {
		//  assert (sanity++ < 1000);
		
		mum_end1   = random_point ( population[mum].string );
		mum_start2 = matching_point ( population[mum].string, mum_end1 ); 
		mum_end2   = strlen ( population[mum].string );
		
		dad_start = random_point ( P[best].string );
		dad_end   = matching_point ( P[best].string, dad_start );
		
	} while (splice ( 
		new_population[child].string, MAX_PROG_SIZE+1,
		population[mum].string, mum_end1,
		&P[best].string[dad_start], dad_end - dad_start,
		&population[mum].string[mum_start2], mum_end2 - mum_start2 ) != 0 );
	
	/*display data */
	//parents[child].mum       = mum;
	//parents[child].mumcross  = mum_end1;
	//parents[child].dad       = dad;
	//parents[child].dadcross  = dad_start;
	
}/*end crossover ()*/

copy (int mum, int child)
/*copy from old population to new_population, including test_fitness*/

{
	strcpy (new_population[child].string, population[mum].string);
	
	/*display data */
	//parents[child].mum       = mum;
	//parents[child].mumcross  = COPY_MUM;
	
	//  update_hits_etc (population[mum].fitness, population[mum].hits, child );
	
}/*end copy()*/



push_string ( char value[] )
{
	char a[LINE_WIDTH];
	char result[LINE_WIDTH];
	
	if ( (stack <= 0) || (op_stack[stack-1] != 0) ) /*operator on top of stack*/
	{                                             /*or stack empty          */
		op_stack [ stack ]  = 0;                /*operand on top of stack*/
		strcpy (output_stack[stack], value);
		stack++;
	}
	else
	{
		--stack;
		strcpy (a, output_stack[stack]);      /*pop first operand*/
		switch (op_stack[--stack])            /*pop operator*/
		{
        case '+':  sprintf (result, "%s+%s", a, value);
			break;
			
        case '-':  sprintf (result, "(%s)-(%s)", a, value);
			break;
			
        case '*':  sprintf (result, "(%s)*(%s)", a, value);
			break;
			
        case '/':  sprintf (result, "div(%s,%s)", a, value);
			break;
			
        default:
			//                   assert (11 == 0 ); /* opps!*/
			break;
		}
		
		push_string ( result );
	}
	
}/*end push_string()*/


output_program (char string[] )
/* Convert string to c format*/
{
	char buff [] = " ";
	int i;
	FILE *stream;
	
	stack = 0;
	
	for ( i = 0; string[i] != 0; i++ )
	{
		switch (string [i])
		{
        case '+':
        case '-':
        case '*':
        case '/':         push_operator(string[i]);
			break;
			
        default:          buff [ 0 ] = string [i];
			push_string( buff );
			break;
		}
	}/*end for*/
	 /*
	 assert (stack == 1);
	 
	   if ((stream=fopen(output_file,"w"))==NULL)
	   {printf("Failed to open file %s for output! Stopping!\n", output_file);
	   exit (EXIT_FAILURE);}
	   
		 fprintf (stream, "\nfloat div ( float top, float bot )\n");
		 fprintf (stream, "{if (bot == 0.0)\n");
		 fprintf (stream, "   return (1.0);\n");
		 fprintf (stream, " else\n");
		 fprintf (stream, "   return ( top/bot );\n");
		 fprintf (stream, "}\n");
		 
		   fprintf (stream, "\nfloat gp( float x )\n{\n");
		   fprintf (stream, "  return (%s);\n}\n", output_stack[--stack] );
		   
			 fclose (stream);
	*/
}/*end output_program()*/



double dist(int a, int b)
{
	int i;
	double d = 0;
	for (i = 0; i < D; i++)
		d += pow(P[a].x[i] - P[b].x[i],2);
	d = sqrt(d);
	return d;
}

// ***************************************************

// =================================================
int main()
{
	double c; // Second onfidence coefficient
	int d; // Current dimension
	double eps; // Admissible error
	double eps_mean; // Average error
	double eps_normalized_mean;
	double error; // Error for a given position
	double error_prev; // Error after previous iteration
	int error_count;
	int eval_max; // Max number of evaluations
	double eval_mean; // Mean number of evaluations
	int function; // Code of the objective function
//	int g; // Rank of the best informant
	//  int init_links; // Flag to (re)init or not the information links
	int i;
	int j;
	//  int K; // Max number of particles informed by a given one
	int m;
	double mean_best[R_max];
	double min; // Best result through several runs
	double max;
	int n_exec, n_exec_max; // Nbs of executions
	int n_failure; // Number of failures
	int n_optimum;
	int s; // Rank of the current particle
	double t1, t2;
	double variance;
	double w; // First confidence coefficient
	int mum, dad;
	double a[D_max]; // acceleration
	//  double c_array[D_max];
	//  double w_array[D_max];
	unsigned seed;
	double pcross;
	//  unsigned id;
	char f_run_name[50];
	int reinitialize;
	int f_sort[S_max];
	int temp;
	double r;
	/* Seed the random-number generator with current time so that
    * the numbers will be different every time we run.
    */
	seed = (unsigned)time(NULL);
	srand( seed );
	//	id = alea_integer(0,1000);
	sprintf(f_run_name,"f_run_%d.txt",seed);
	f_run = fopen( f_run_name, "w" );
	f_run_combined = fopen( "f_run_combined.txt", "a" );
	E = exp( 1 );
	pi = acos( -1 );
	pcross = 0.9;
	
	//----------------------------------------------- PROBLEM
//	function = 3; //Function code
	function = 22; //Function code
				  /*
				  0 Parabola (Sphere) *
				  1 De Jong' f4
				  2 Griewank *
				  3 Rosenbrock (Banana) *
				  4 Step
				  6 Foxholes 2D
				  7 Polynomial fitting problem 9D
				  8 Alpine
				  9 Rastrigin *
				  10 Ackley *
				  13 Tripod 2D
				  17 KrishnaKumar
				  18 Eason 2D
				  19 F1
				  20 F2
				  21 F3
				  22 F4
				  23 F5

	*/
//	D = 2; // Search space dimension
	D = 1; // Search space dimension
	
	// D-cube data
	for ( d = 0; d < D; d++ )
	{
//		xmin[d] = -100; xmax[d] = 100;
		xmin[d] = 0; xmax[d] = 1;
		//	w_array[d] = w;
		//	c_array[d] = c;
	}
	r = 0.05;

	w = 1 / ( 2 * log( 2 ) ); c = 0.5 + log( 2 );
	
	eps = 0.9; // Acceptable error
	f_min = 0; // Objective value
	n_exec_max = 100; // Numbers of runs
	eval_max = 4000; // Max number of evaluations for each run
	
	if(n_exec_max>R_max) n_exec_max=R_max;
	//-----------------------------------------------------  PARAMETERS
	S = 10+( int )(2*sqrt(D)); if (S>S_max) S=S_max;
	//  S = 100;
	//  K = 3;
	S=30;
	
	printf("\n Swarm size %i", S);
	printf("\n coefficients %f %f \n",w,c);
	
	//----------------------------------------------------- INITIALISATION
	t1 = clock(); // Init time
	// Initialisation of information variables
	n_exec = 0; eval_mean = 0; eps_mean = 0; eps_normalized_mean = 0; n_failure = 0; n_optimum = 0;
	
init:
	n_exec = n_exec + 1;
	initialise_population();
	for ( s = 0; s < S; s++ )  // Positions and velocities
	{
		for ( d = 0; d < D; d++ )
		{
			X[s].x[d] = alea( xmin[d], xmax[d] );
			X[s].v[d] = (alea( xmin[d], xmax[d] ) - X[s].x[d])/2; // Non uniform
		}
	}
	
    // First evaluations
    nb_eval = 0;
    for ( s = 0; s < S; s++ )
    {
		X[s].f = fabs( perf( s, function ) - f_min );
		P[s] = X[s]; // Best position = current one
    }
	
    // Find the best
    best = 0;
	//	worst = 0;
    for ( s = 1; s < S; s++ )
	{
		if ( P[s].f < P[best].f ) best = s;
	}
	
    error =  P[best].f ; // Current min error
	error_prev = error;
    if(n_exec==1) max=min=error;
	error_count = 0;
	reinitialize = 2;
    //---------------------------------------------- ITERATIONS
loop:
	for (s = 0; s < S; s++)
	{
		f_sort[s] = s;
		X[s].b = -1;
	}
	for (i = 0; i < S - 1; i++)
		for (j = i + 1; j < S; j++)
		{
			if(P[f_sort[i]].f > P[f_sort[j]].f)
			{
				temp = f_sort[i];
				f_sort[i] = f_sort[j];
				f_sort[j] = temp;
			}
		}
	for (s = 0; s < S - 1; s++)
	{
		if(X[f_sort[s]].b < 0)
		{
			for (i = s + 1; i < S; i++)
				if(X[f_sort[i]].b < 0 && dist(f_sort[s],f_sort[i]) < r)
					X[f_sort[i]].b = f_sort[s];
		}
	}
	for (s = 0; s < S; s++)
		if(X[s].b < 0)
			X[s].b = s;
	//printf("%f ",X[f_sort[s]].f);
	//printf("\n");

	// **************************************
	// Evolve function here
//	if( nb_eval % 2 == 0 )
	{
		for (i = 0; i < S/*POPULATION_SIZE*/; i++)
		{
			mum = select_parent();
//			if (random_number() < PCROSS)
			if (random_number() < pcross)
			{
				dad = select_parent();
				crossover (mum, dad, i);
			}
			else //if (random_number() < PMUT)
			{
				mutate(mum,i);
				//			 test_fitness(i);
			}
		}/*end for - create new_population */
		
		//display_stats();
		
		replace_old_population();
	}
	
	// **************************************
    // The swarm MOVES
    for ( s = 0; s < S; s++ ) // For each particle ...
    {
		//prog_value(X[s].string, X[s].v, X[s].x, P[s].x, P[best].x, c, a);
		prog_value(X[s].string, X[s].v, X[s].x, P[s].x, P[X[s].b].x, c, a);
		// ... compute the new velocity, and move
		for ( d = 0; d < D; d++ )
		{
			X[s].v[d] = w * X[s].v[d] + a[d];
            X[s].x[d] = X[s].x[d] + X[s].v[d];
		}
		
		// ... interval confinement (keep in the box)
		for ( d = 0; d < D; d++ )
		{
			if ( X[s].x[d] < xmin[d] )
			{
				X[s].x[d] = xmin[d]; X[s].v[d] = 0;
			}
			if ( X[s].x[d] > xmax[d] )
			{
				X[s].x[d] = xmax[d]; X[s].v[d] = 0;
			}
		}
		
		
		// ... evaluate the new position
        X[s].f = fabs( perf( s, function ) - f_min );
		
		
		// ... update the best previous position
		if ( X[s].f<P[s].f )
		{
			P[s] = X[s];
			// ... update the best of the bests
			if (  P[s].f<P[best].f  ) best = s;
		}
    }
    // Check if finished
    // If no improvement, information links will be reinitialized
	if(function == 19)
	{
		double peaks[] = {0.1, 0.3, 0.5, 0.7, 0.9};
		double mind;
		int closestpeak = 0;
		error = 0;
		for(i = 0; i < 5; i++)
		{
			mind = DBL_MAX;
			for(j = 0; j < S; j++)
				if(fabs(peaks[i] - P[j].x[0]) < mind)
				{
					closestpeak = j;
					mind = fabs(peaks[i] - P[j].x[0]);
				}
			//printf("%e ",P[closestpeak].f);
			error += P[closestpeak].f;
		}
		//printf("\n");
		error /= 5.0;
				;
	}
	else if (function == 21)
	{
		double peaks[] = {0.079699,0.246660,0.450630,0.681430,0.933900};
		double mind;
		int closestpeak = 0;
		error = 0;
		for(i = 0; i < 5; i++)
		{
			mind = DBL_MAX;
			for(j = 0; j < S; j++)
				if(fabs(peaks[i] - P[j].x[0]) < mind)
				{
					closestpeak = j;
					mind = fabs(peaks[i] - P[j].x[0]);
				}
			error += P[closestpeak].f;
		}
		error /= 5.0;
	}
	else if (function == 23)
	{            
		double peaks[] = {3.58,-1.86,3.0,2.0,-2.815,3.125,-3.78,-3.28};
		double mind;
		int closestpeak = 0;
		error = 0;
		for(i = 0; i < 8; i+=2)
		{
			mind = DBL_MAX;
			for(j = 0; j < S; j++)
				if(sqrt(pow(peaks[i] - P[j].x[0],2) + pow(peaks[i+1] - P[j].x[1],2)) < mind)
				{
					closestpeak = j;
					mind = sqrt(pow(peaks[i] - P[j].x[0],2) + pow(peaks[i+1] - P[j].x[1],2));
				}
			error += P[closestpeak].f;
		}
		error /= 4.0;

	}
	else
		error=P[best].f;
/*	if ( error >= error_prev )
		error_count++;
	else
		error_count = 0;*/
/*	if ((error == error_prev) || (error / (error_prev - error) > (eval_max - nb_eval)))
		error_count++;
	else
		error_count = 0;*/
//		printf("\nSuspect1 (%d) Error %f", n_exec,error);
	//pcross = error_count / eval_max;
/*	if ( error_count > 10 )
	{
		printf("\nSuspect (%d) Error %f Iteration %d", n_exec,error,nb_eval);*/
/*		if ( nb_eval > 50 )
		{
			if (reinitialize > 0)
			{
				initialise_population();
				//replace_with_best();
				reinitialize = 0;
				pcross = 0.9;
			}
			error_count = 0;
			pcross = pcross - 0.2;
		}
		else*/ /*if ( nb_eval > 20 )
		{
			if (reinitialize > 0)
			{
				initialise_population();
				//replace_with_best();
				reinitialize = reinitialize - 1;;
//				pcross = 0.9;
			}
			//initialise_population();
			error_count = 0;
			pcross = pcross - 0.15;
		}*/
		//replace_with_best();
/*	for ( s = 0; s < S; s++ )  // Positions and velocities
	{
		for ( d = 0; d < D; d++ )
		{
			X[s].x[d] = alea( xmin[d], xmax[d] );
			X[s].v[d] = (alea( xmin[d], xmax[d] ) - X[s].x[d])/2; // Non uniform
		}
	}
	
    // First evaluations
//    nb_eval = 0;
    for ( s = 0; s < S; s++ )
    {
		X[s].f = fabs( perf( s, function ) - f_min );
		P[s] = X[s]; // Best position = current one
    }
	
    // Find the best
    best = 0;
	//	worst = 0;
    for ( s = 1; s < S; s++ )
	{
		if ( P[s].f < P[best].f ) best = s;
	}
	
    error =  P[best].f ; // Current min error
//	error_prev = error;*/
//	}
	error_prev = error;
	nb_eval = nb_eval + 1;
    if ( error > 0 && nb_eval < eval_max ) goto loop;
    if ( error > eps ) n_failure = n_failure + 1;
	if ( error <= 0 ) n_optimum = n_optimum + 1;
    // Save result
    fprintf( f_run, "\n%i\t%i\t%.10f ", n_exec, nb_eval,error );
    for (s = 0; s < S - 1; s++)
		if(X[s].b == s)
		{
			fprintf( f_run, "[ " );
			for ( d = 0; d < D; d++ ) fprintf( f_run, "\t%f", P[s].x[d] );
			fprintf( f_run, " ]" );
		}
	output_program(P[best].string);
	fprintf( f_run, "\t%s", output_stack[--stack]/*P[best].string*/);
    // Compute some statistical information
    if ( error < min ) min = error;
	if ( error > max ) max = error;
    eval_mean = eval_mean + nb_eval;
    eps_mean = eps_mean + error;
    mean_best[n_exec - 1] = error;
	for (s = 0; s < S - 1; s++)
		if(X[s].b == s)
			printf("*");
	printf("\n");
	
    if ( n_exec < n_exec_max ) goto init;
	
    // END. Display some statistical information
    t2 = clock();
    eval_mean = eval_mean / ( double )n_exec;
    eps_mean = eps_mean / ( double )n_exec;
    // Variance
    variance = 0;
    for ( d = 0; d < n_exec_max; d++ ) 
	{
		eps_normalized_mean = eps_normalized_mean + mean_best[d] / max;
		variance = variance + ( mean_best[d] - eps_mean ) * ( mean_best[d] - eps_mean );
	}
    variance = sqrt( variance / n_exec_max );
	
	eps_normalized_mean = eps_normalized_mean / ( double )n_exec;
	output_program(P[best].string);
	
	printf( "\n Seed:\t\t%d", seed);
    printf( "\n Total clocks:\t%.0f", t2 - t1 );
    printf( "\n Eval. (mean):\t%f", eval_mean );
    printf( "\n Error (mean):\t%f", eps_mean );
    printf( "\n Error (norm mean):\t%f", eps_normalized_mean );
    printf( "\n Std. dev.:\t%f", variance );
    printf( "\n Success rate:\t%.2f%%", 100 * ( 1 - n_failure / ( double )n_exec ) );
	printf( "\n Optimum rate:\t%.2f", 100 * ( n_optimum / ( double )n_exec ) );
    printf( "\n Best min value:\t%e", min );
	printf( "\n Best fubction:\t%s", output_stack[--stack]);
	
	fprintf( f_run_combined, "\n%d", seed);
	fprintf( f_run_combined, "\t%.0f", t2 - t1 );
	fprintf( f_run_combined, "\t%f", eval_mean );
	fprintf( f_run_combined, "\t%f", eps_mean );
	fprintf( f_run_combined, "\t%f", variance );
	fprintf( f_run_combined, "\t%.2f", 100 * ( 1 - n_failure / ( double )n_exec ) );
	fprintf( f_run_combined, "\t%.2f", 100 * ( n_optimum / ( double )n_exec ) );
	fprintf( f_run_combined, "\t%e", min);
	fprintf( f_run_combined, "\t%s", output_stack[stack]);
end:;
	fclose( f_run );
	fclose( f_run_combined );
    return 0;
  }
  
  //===========================================================
  double alea( double a, double b )
  { // random number (uniform distribution) in [a b]
	  double r;
	  r=(double)rand(); r=r/RAND_MAX;
	  return a + r * ( b - a );
  }
  
  //===========================================================
  double perf( int s, int function )
  { // Evaluate the fitness value for the particle of rank s
	  double c;
	  int d, d1;
	  int i, j, k;
	  double f, f1, p, xd, x1, x2, x3, x4;
	  double min;
	  double sum1, sum2;
	  double t0, tt, t1;
	  struct position xs;
	  
	  // For Foxholes problem
	  static int a[2] [25] =
	  {
		  {
			  -32, -16, 0, 16, 32, -32, -16, 0, 16, 32, -32, -16, 0, 16, 32, -32, -16, 0, 16, 32, -32, -16, 0, 16, 32
		  },
		  {
				  -32, -32, -32, -32, -32, -16, -16, -16, -16, -16, 16, 16, 16, 16, 16, 32, 32, 32, 32, 32
			  }
	  };
	  // For polynomial fitting problem
	  int const M = 60;
	  double py, y = -1, dx = ( double )M;
	  
	  //    nb_eval = nb_eval + 1;
	  xs = X[s];
	  
	  switch ( function )
	  {
      case 0: // Parabola (Sphere)
		  f = 0;
		  p = 0; // Shift
		  for ( d = 0; d < D; d++ )
		  {
			  xd = xs.x[d] - p;
			  f = f + xd * xd;
		  }
		  break;
		  
      case 1: // De Jong's f4
		  f = 0;
		  p = 0; // Shift
		  for ( d = 0; d < D; d++ )
		  {
			  xd = xs.x[d] - p;
			  f = f + (d+1)*xd*xd*xd*xd;
		  }
		  break;
		  
		  
      case 2: // Griewank
		  f = 0;
		  p = 1;
		  for ( d = 0; d < D; d++ )
		  {
			  xd = xs.x[d];
			  f = f + xd * xd;
			  p = p * cos( xd / sqrt( d + 1 ) );
		  }
		  f = f / 4000 - p + 1;
		  break;
		  
      case 3: // Rosenbrock
		  f = 0;
		  t0 = xs.x[0];
		  for ( d = 1; d < D; d++ )
		  {
			  t1 = xs.x[d];
			  tt = 1 - t0;
			  f += tt * tt;
			  tt = t1 - t0 * t0;
			  f += 100 * tt * tt;
			  t0 = t1;
		  }
		  break;
		  
      case 4: // Step
		  f = 0;
		  for ( d = 0; d < D; d++ ) f = f + ( int )xs.x[d];
		  break;
		  
		  
      case 6: //Foxholes 2D
		  f = 0;
		  for ( j = 0; j < 25; j++ )
		  {
			  sum1 = 0;
			  for ( d = 0; d < 2; d++ )
			  {
				  sum1 = sum1 + pow( xs.x[d] - a[d] [j], 6 );
			  }
			  f = f + 1 / ( j + 1 + sum1 );
		  }
		  f = 1 / ( 0.002 + f );
		  break;
		  
      case 7: // Polynomial fitting problem
		  // on [-100 100]^9
		  f = 0;
		  dx = 2 / dx;
		  for ( i = 0; i <= M; i++ )
		  {
			  py = xs.x[0];
			  for ( d = 1; d < D; d++ )
			  {
				  py = y * py + xs.x[d];
			  }
			  if ( py < -1 || py > 1 ) f += ( 1 - py ) * ( 1 - py );
			  y += dx;
		  }
		  py = xs.x[0];
		  for ( d = 1; d < D; d++ ) py = 1.2 * py + xs.x[d];
		  py = py - 72.661;
		  if ( py < 0 ) f += py * py;
		  py = xs.x[0];
		  for ( d = 1; d < D; d++ ) py = -1.2 * py + xs.x[d];
		  py = py - 72.661;
		  if ( py < 0 ) f += py * py;
		  break;
		  
      case 8: // Clerc's f1, Alpine function, min 0
		  f = 0;
		  for ( d = 0; d < D; d++ )
		  {
			  xd = xs.x[d];
			  f += fabs( xd * sin( xd ) + 0.1 * xd );
		  }
		  break;
		  
      case 9: // Rastrigin. Minimum value 0. Solution (0,0 ...0)
		  k = 10;
		  f = 0;
		  for ( d = 0; d < D; d++ )
		  {
			  xd = xs.x[d];
			  f += xd * xd - k * cos( 2 * pi * xd );
		  }
		  f += D * k;
		  break;
		  
      case 10: // Ackley
		  sum1 = 0;
		  sum2 = 0;
		  for ( d = 0; d < D; d++ )
		  {
			  xd = xs.x[d];
			  sum1 += xd * xd;
			  sum2 += cos( 2 * pi * xd );
		  }
		  y = D;
		  f = ( -20 * exp( -0.2 * sqrt( sum1 / y ) ) - exp( sum2 / y ) + 20 + E );
		  break;
		  
		  
      case 13: // 2D Tripod function (Louis Gacogne)
		  // Search [-100, 100]^2. min 0 on (0  -50)
		  x1 = xs.x[0];
		  x2 = xs.x[1];
		  if ( x2 < 0 )
		  {
			  f = fabs( x1 ) + fabs( x2 + 50 );
		  }
		  else
		  {
			  if ( x1 < 0 )
				  f = 1 + fabs( x1 + 50 ) + fabs( x2 - 50 );
			  else
				  f = 2 + fabs( x1 - 50 ) + fabs( x2 - 50 );
		  }
		  break;
		  
      case 17: // KrishnaKumar
		  f = 0;
		  for ( d = 0; d < D - 1; d++ )
		  {
			  f = f + sin( xs.x[d] + xs.x[d + 1] ) + sin( 2 * xs.x[d] * xs.x[d + 1] / 3 );
		  }
		  break;
		  
      case 18: // Eason 2D (usually on [-100,100]
		  // Minimum -1  on (pi,pi)
		  x1 = xs.x[0]; x2 = xs.x[1];
		  f = -cos( x1 ) * cos( x2 ) / exp( ( x1 - pi ) * ( x1 - pi ) + ( x2 - pi ) * ( x2 - pi ) );
		  break;

	  case 19: // F1
		  f = 1 - pow(sin(5*pi*xs.x[0]),6);
		  break;
	  case 20: // F2
		  f = 1 - exp(-2*log(2)*pow((xs.x[0]-0.1)/0.8,2))*pow(sin(5*pi*xs.x[0]),6);
		  break;
	  case 21:// F3
		  f = 1 - pow(sin(5*pi*(pow(xs.x[0],3.0/4.0)-0.05)),6);
		  break;
	  case 22: // F4
		  f = 1 - exp(-2*log(2)*pow((xs.x[0]-0.08)/0.854,2))*pow(sin(5*pi*(pow(xs.x[0],3.0/4.0)-0.05)),6);
		  break;
	  case 23: // F5
		  f = pow(pow(xs.x[0],2)+xs.x[1]-11,2) - pow(xs.x[0]+pow(xs.x[1],2)-7,2);
		  break;


    }
    return f;
  }
  
