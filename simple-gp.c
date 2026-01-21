/*
// Simple Genetic Program
//
// W. B. Langdon, cwi.nl, 21 February 1999
//
// Modifications:
// Author:  WBL
// Date  :  21 Feb 1999
// Change:  Increase portability by replacing drand48() by park-miller, 
//          and renaming functions to avoid name clashes

// Author:  WBL
// Date  :  18 Feb 1994, 21 April 1994
// Change:  Replace rand() with drand48(),
//          reduce POPULATION_SIZE from 500 to 16
*/
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <time.h>
#include <float.h>
#include <assert.h>

/* SUNos v4 */
#define EXIT_FAILURE 1
#define FILENAME_MAX 80

#define POPULATION_SIZE  16
#define PCROSS            0.6
#define PMUT               .01
#define MAX_GEN          50
#define MAX_PROG_SIZE    25
#define STACK_SIZE       25
#define LINE_WIDTH      200
#define THRESHOLD          0.01

#define MAX_TEST_POINTS   10

float x[MAX_TEST_POINTS];
float y[MAX_TEST_POINTS];
int   num_x;
char output_file[FILENAME_MAX];

struct prog
{
  char string [MAX_PROG_SIZE+1];
  float fitness;
  int  hits;
};

struct prog     population [POPULATION_SIZE];
struct prog new_population [POPULATION_SIZE];

/*Data for display purposes only */
#define COPY_MUM -1
#define MUTATE   -1
struct par
{
  int mum, mumcross;
  int dad, dadcross;
};
struct par parents [POPULATION_SIZE];
int num_tests  =  0;

int best_prog, max_hits, required_hits;

float new_sumfitness;
float total_fitness;

int generation;


/* start code */

int    seed;

read_inputs()
/*read pairs of numbers from stdin
//
//outputs:    required_hits
//            x, y, num_x
*/
{
int i;
time_t now;

  printf ("Enter up to %d x y pairs of numbers> ", MAX_TEST_POINTS );
  fflush(stdout);

  for (i = 0; i < MAX_TEST_POINTS; i++ )
    { if ( scanf("%e %e", &x[i], &y[i]) != 2 ) break; }

  if (i <= 0) {printf ("\nNo data pairs! Stopping!\n"); exit (EXIT_FAILURE);}

  num_x = i;
  required_hits = num_x;
  strcpy (output_file, "gp.c");


  printf ("\nGP regression on %d points\n", num_x);
  for( i=0; i < num_x; i++ )
  {
    printf("(%e,%e) ",x[i],y[i]);
    if ( (i%2) == 1 ) printf("\n");
  }

  time (&now);
  seed = now;

  printf ("\nPop = %d, PCross %.5f, PMutate %.5f, Max gens %d, seed %d\n",
          POPULATION_SIZE, PCROSS, PMUT, MAX_GEN, seed );

  printf ("\nGP starting\n");

} /*end read_inputs() */


/*park-miller.cc   Park-Miller random number generator
 W. Langdon cs.ucl.ac.uk 5 May 1994*/
int intrnd () /* 1<=seed<=m */
{
double const a    = 16807;      /* ie 7**5 */
double const m    = 2147483647; /* ie 2**31-1 */

        double temp = seed * a;
        seed = (int) (temp - m * floor ( temp / m ));
        return seed;
}
float rand_0to1() { return (float)(intrnd()) / 2147483647.0; }

float random_number()  /* single precision ok */
{
float r;

for (; (r = rand_0to1() ) >= 1.0; )
{printf("random number >=1.0 %e\n",r);} /* ensure we dont return 1.0 */

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
      
        case '\0':        assert (1 == 0);  /*oh dear*/
                          break;

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
   return ( 'x' );

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

  assert ( dangling_limbs == 0 ); /*Opps...*/

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
  assert (sanity++ < 1000);

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

parents[child].mum       = mum;
parents[child].mumcross  = mum_end1;
parents[child].dad       = MUTATE;
parents[child].dadcross  = mut_length;


}/*end mutate()*/


int   stack;
float  value_stack [STACK_SIZE];
char      op_stack [STACK_SIZE];
char  output_stack [STACK_SIZE][LINE_WIDTH];


push_operator ( char op )
{
  op_stack [stack++]      = op;
  value_stack [stack]     = 0.0;   /* keep it clean */
  output_stack [stack][0] = '\0';  /* and tidy      */

}/*end push_operator()*/


push_value ( float value )
{
float a;
float result;

if ( (stack <= 0) || (op_stack[stack-1] != 0) )  /* operator on top of stack */
  {                                              /* or stack empty           */
    op_stack [ stack ]    = 0; /* operand on top of stack */
    value_stack [stack++] = value;
  }
else
  {
    a = value_stack[--stack];  /* pop first operand */
    switch (op_stack[--stack])   /* pop operator */
      {
        case '+':  result = a + value;
                   break;

        case '-':  result = a - value;
                   break;

        case '*':  result = a * value;
                   break;

        case '/':  if (value == 0.0)
                     result = 1.0;
                   else
                     result = a / value;
                   break;

        default:
                   assert (10 == 0 ); /* opps */
                   break;
      }

    push_value ( result );
  }

}/*end push_value()*/

float prog_value (char string[], float input )
/* return value of program child in new_population with input*/
{
int i;

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
      
        default:          push_value ( input );
                          break;
      }
  }/*end for*/

assert (stack == 1);

/*printf("prog_value: %s = %e, input = %e\n", string, value_stack[0], input );
*/

return (value_stack[--stack]); /*pop value*/

} /*end prog_value()*/



update_hits_etc ( float fit, int n_hits, int child )
/*
//store fitness and hits of child in new_population
//update best program statistics.
//
//Nb best program is defined to be one with highest number of hits
//regardless of fitness
*/
{
  new_population[child].fitness = fit;

  new_sumfitness += new_population[child].fitness;

  new_population[child].hits    = n_hits;

  if (max_hits < new_population[child].hits)
    {
       max_hits  = new_population[child].hits;
       best_prog = child;
    }

}/*end update_hits_etc()*/

test_fitness (int child )
/*evaluate test_fitness of child in new_population, store answer with it.*/
{
int i;
int test_hits = 0;
float error;
float total_error = 0.0;

  for ( i=0; i < num_x; i++ )
  {
     error = fabs ( y[i] - prog_value( new_population[child].string, x[i] ) );

     if (error <= THRESHOLD || error <= THRESHOLD * fabs(y[i]) ) test_hits++;

     total_error += error;

  }/*end for each test switch*/

  num_tests++;

  update_hits_etc(num_x/(total_error+num_x), test_hits, child);
/*
  update_hits_etc(1.0/(total_error+1.0), test_hits, child);
*/
}/*end test_fitness()*/

display_stats()
/*display info on new_population */
{
int i;
time_t now;

float min_fitness = FLT_MAX;
float max_fitness = -FLT_MAX;

int mi_hits  = num_x;
int mx_hits  = 0;
int sum_hits = 0;

float sum_fitness = 0.0;
float sum_squared = 0.0;
float mean;


time (&now);
printf ("\n Generation %d on %s\n", generation, ctime(&now));

for ( i=0; i < POPULATION_SIZE; i++ )
  {
    sum_fitness += new_population[i].fitness;
    sum_squared += new_population[i].fitness*new_population[i].fitness;

    if (min_fitness > new_population[i].fitness)
      min_fitness = new_population[i].fitness;

    if (max_fitness < new_population[i].fitness)
      max_fitness = new_population[i].fitness;

    if (mi_hits > new_population[i].hits)
      mi_hits = new_population[i].hits;

    if (mx_hits < new_population[i].hits)
      mx_hits = new_population[i].hits;

    sum_hits += new_population[i].hits;

  }/*end for*/

mean = sum_fitness / POPULATION_SIZE;


for ( i=0; i < POPULATION_SIZE; i++ )
  {
    if      ( parents[i].mumcross == COPY_MUM )
      printf ("copy     [%3d]=%3d             ", 
               i, parents[i].mum) ;
    else if ( parents[i].dad      == MUTATE )
      printf ("mutate   [%3d]=%3d(%2d)+(%2d)    ",
               i, parents[i].mum, parents[i].mumcross, 
                  parents[i].dadcross );
    else
      printf ("crossover[%3d]=%3d(%2d)*%3d(%2d) ",
               i, parents[i].mum, parents[i].mumcross, 
                  parents[i].dad, parents[i].dadcross );

   printf ("fit = %.5f hits = %2d pselect = %.3f %s\n",
           new_population[i].fitness,
           new_population[i].hits,
           new_population[i].fitness/mean,
           new_population[i].string );
  }

printf ("Generation %d, new_sumfitness %e %s",
  generation, new_sumfitness, ctime(&now));

printf ("Mean fitness = %.5f, variance = %.5f, min = %.5f, max = %.5f \n",
  mean,
  (sum_squared - POPULATION_SIZE*mean*mean )/POPULATION_SIZE,
  min_fitness,
  max_fitness );

printf (
"Min hits = %2d, max = %2d, best_prog = %3d, fitness = %.5f hits = %2d %s\n",
  mi_hits,
  mx_hits,
  best_prog,
  new_population[best_prog].fitness,
  new_population[best_prog].hits,  
  new_population[best_prog].string    ); 

}/*end display_stats()*/


replace_old_population()
{
int i;

  total_fitness  = new_sumfitness;
/* best_prog - retain current value until new generation*/

   for (i = 0; i < POPULATION_SIZE; i++ )
     {
         strcpy (population[i].string, new_population[i].string);
         population[i].fitness = new_population[i].fitness;
         population[i].hits    = new_population[i].hits;
     }

}/*end replace_old_population()*/



initialise_population()
{
int i;

  for ( i=0; i < POPULATION_SIZE; i++ )
    {
       population[i].string[0] = '\0';
       mutate (i,i);
       test_fitness(i);
    }

  display_stats();

  replace_old_population();

} /*end initialise_population() */


int select_parent()
/* return index or parent in old population*/
{
/*consider binary chop if POPULATION_SIZE becomes big*/

int i;

float cumlative_fitness = 0.0;
float r;

  r = total_fitness * random_number();

  for (i = 0; i < POPULATION_SIZE; i++ )
    {
        cumlative_fitness += population[i].fitness;
        if ( r <= cumlative_fitness ) return (i);
    }

  return ( POPULATION_SIZE - 1 );

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
  assert (sanity++ < 1000);

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
parents[child].mum       = mum;
parents[child].mumcross  = mum_end1;
parents[child].dad       = dad;
parents[child].dadcross  = dad_start;

}/*end crossover ()*/


copy (int mum, int child)
/*copy from old population to new_population, including test_fitness*/

{
  strcpy (new_population[child].string, population[mum].string);

/*display data */
parents[child].mum       = mum;
parents[child].mumcross  = COPY_MUM;

  update_hits_etc (population[mum].fitness, population[mum].hits, child );

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
                   assert (11 == 0 ); /* opps!*/
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

}/*end output_program()*/



int main()
{
int i, mum, dad;

  read_inputs();

  generation = 0;

  new_sumfitness = 0.0;
  max_hits       = -1;

  initialise_population();

  while ((++generation <= MAX_GEN) && (max_hits < required_hits))
  {
    new_sumfitness = 0.0;
    max_hits       = -1;

    for (i = 0; i < POPULATION_SIZE; i++)
    {
       mum = select_parent();
       if (random_number() < PCROSS)
       {
         dad = select_parent();
         crossover (mum, dad, i);
         test_fitness(i);
         }
       else if (random_number() < PMUT)
         {
         mutate(mum,i);
         test_fitness(i);
         }
       else
         {
         copy (mum,i);
         };
    }/*end for - create new_population */
  
    display_stats();

    replace_old_population();

  } /*end while */

  output_program( population[best_prog].string );

  printf("GP done. %d tests completed\n", num_tests );

  return (0);

}/*end main() */


/*end program GP*/

