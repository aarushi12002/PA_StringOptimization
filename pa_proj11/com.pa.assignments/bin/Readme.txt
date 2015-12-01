The analysis consists of finding if the variables are redefined or not.

It involves 3 classes : driver class, Analysis class which extends body transformer, q2 Analyzer class which extends forwardAnalysis class

In the merge function, we take the union of the two sets(may analysis) and to find out which of the variables maybe redefined, i take the difference of the two sets, if the difference is 'phi' then i take their intersection(must analysis) and if differnce of the sets diff1 = A-B or diff2 = B-A contain some variables then they are put in the maylist of they were previously redefined earlier.
The gen function is - gen(x=e) : x. 
