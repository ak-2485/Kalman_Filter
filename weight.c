/*
  To run: ./weight < sensor_data
*/
#include <stdio.h>

/*
  i - the current iteration
  g - the current estimate
  m - the new measurement to incorporate
*/
double filter_step(int i, double g, double m) {
  return g + (1.0 / (double)i * (m - g));
}

/*
On step 1 we have:
  filter_step(1, initial_guess, input) ==
  initial_guess + (1.0 / (double)1 * (input - initial_guess)) ==
  initial_guess + input - initial_guess ==
  input
So our initial guess doesn't really matter here.
*/

/*
  Start with a guess as current estimate
  Read "sensor" (double from stdin) and incorporate it into the current estimate
  Print the current estimate
  Loop

  There are two pieces of state:
  * i    - the current iteration (starts from 1)
  * curr - the current estimate
*/
int main() {
  double input, curr = 1000; // start by guessing
  int i = 0;
  while(scanf("%lf", &input) != EOF) {
    i++;
    curr = filter_step(i, curr, input);
    printf("%8.3lf\n", curr);
  }
  return 0;
}
