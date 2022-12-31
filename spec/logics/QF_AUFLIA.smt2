(logic QF_AUFLIA

 :smt-lib-version 2.6
 :smt-lib-release "2017-11-24"
 :written-by "Cesare Tinelli"
 :date "2010-04-30"
 :last-updated "2015-04-25"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2015-04-25 Updated to Version 2.5.
  2011-06-03 Allowed x to be more than a free constants in terms of the form 
             (* c x) or (*x c)   in :extensions.
 "

 :theories (Ints ArraysEx)

 :language 
 "Closed quantifier-free formulas built over arbitrary expansions of the
  Ints and ArraysEx signatures with free sort and function symbols, but
  with the following restrictions:
  - all terms of sort Int are linear, that is, have no occurrences of the
    function symbols *, /, div, mod, and abs, except as specified in the 
    :extensions attributes;
  - all array terms have sort (Array Int Int).
 "

 :extensions
 "Terms with _concrete_ integer coefficients are also allowed, that is, terms
  of the form c, (* c x), or (* x c)  where 
  - x is a free constant or a term with top symbol not in Ints, and 
  - c is a term of the form n or (- n) for some numeral n.
 ")

