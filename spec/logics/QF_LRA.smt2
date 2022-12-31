(logic QF_LRA

 :smt-lib-version 2.6
 :smt-lib-release "2017-11-24"
 :written-by "Cesare Tinelli"
 :date "2010-04-14"
 :last-updated "2015-04-25"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2015-04-25 Updated to Version 2.5. 
  2011-06-03 Replaced ''(* c x), or (* x c)'' with ''c, (* c x), or (* x c)'' 
             in :extensions. (The missing case had been left out unintentionally.)
 "

 :theories (Reals)

 :language 
 "Closed quantifier-free formulas built over arbitrary expansions of 
  the Reals signature with free constant symbols, but containing only
  linear atoms, that is, atoms with no occurrences of the function
  symbols * and /, except as specified the :extensions attribute.
 "

 :extensions
 "Terms with _concrete_ coefficients are also allowed, that is, terms
  of the form c, (* c x), or (* x c)  where x is a free constant and 
  c is an integer or rational coefficient. 
  - An integer coefficient is a term of the form m or (- m) for some
    numeral m.
  - A rational coefficient is a term of the form d, (- d) or (/ c n) 
    for some decimal d, integer coefficient c and numeral n other than 0.
 "
)


