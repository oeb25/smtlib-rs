(logic LIA

 :smt-lib-version 2.6
 :smt-lib-release "2017-11-24"
 :written-by "Cesare Tinelli"
 :date "2016-02-07"
 :update-history
 "Note: history only accounts for content changes, not release changes.
 "
 :theories (Ints)

 :language 
 "Closed formulas built over an arbitrary expansion of the
  Ints signature with free constant symbols, but whose terms of sort Int 
  are all linear, that is, have no occurrences of the function symbols
  *, /, div, mod, and abs, except as specified the :extensions attribute.
 "

 :extensions
 "Terms with _concrete_ coefficients are also allowed, that is, terms
  of the form c, (* c x), or (* x c)  where x is a free constant and 
  c is a term of the form n or (- n) for some numeral n.
 "
)


