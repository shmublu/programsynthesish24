This is an html page that creates boolean or integer SyGuS queries and transforms the solutions to those queries into valid JS code.
To use, click on index.html. Follow the on screen prompts in the first two text boxes to enter the parameters to your query. It will give you a SyGuS 2.0 query,
which can be used in SyGuS solver.

It also connects with the API at https://ffjjhx2ybe.execute-api.us-east-1.amazonaws.com/cvc5 to send the query directly to a synthesizer; if it receives a response,
it will print the result directly as Javascript code. If not, it will give the SyGuS query for the user to paste into their own synthesizer.


