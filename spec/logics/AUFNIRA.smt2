(logic AUFNIRA

 :smt-lib-version 2.6
 :smt-lib-release "2017-11-24"
 :written-by "Cesare Tinelli and Clark Barrett"
 :date "2010-05-12"
 :last-updated "2015-04-25"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2015-04-25 Updated to Version 2.5.
  2012-09-26 Clarified in :notes in what way AUFNIRA extendes AUFLIRA.
 "

 :theories (Reals_Ints ArraysEx)

 :language
 "Closed formulas built over arbitrary expansions of the Reals_Ints and
  ArraysEx signatures with free sort and function symbols.
 "

 :extensions
 "For every operator op with declaration (op Real Real s) for some sort s,
  and every term t1, t2 of sort Int and t of sort Real, the expression 
  - (op t1 t) is syntactic sugar for (op (to_real t1) t)
  - (op t t1) is syntactic sugar for (op t (to_real t1))
  - (/ t1 t2) is syntactic sugar for (/ (to_real t1) (to_real t2))
 "

 :notes
 "This logic properly extends the logic AUFLIRA by allowing 
  - non-linear (integer/real) operators such as  *, /, div, mod, and abs, and
  - allowing terms with an arbitrary array sort (as opposed to just
    (Array Int Real) and (Array Int (Array Int Real)) ).
 "
)
