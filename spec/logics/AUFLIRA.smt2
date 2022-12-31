(logic AUFLIRA

 :smt-lib-version 2.6
 :smt-lib-release "2017-11-24"
 :written-by "Cesare Tinelli and Clark Barrett"
 :date "2010-05-05"
 :last-updated "2015-04-25"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2015-04-25 Updated to Version 2.5.
  2011-06-03 Replaced ""(* c x), or (* x c)"" with ""c, (* c x), or (* x c)""
             in :extensions.
             (The missing case was had been left out unintentionally.)
 "

 :theories (Reals_Ints ArraysEx)

:language
 "Closed formulas built over arbitrary expansions of the Reals_Ints and
  ArraysEx signatures with free sort and function symbols, but with the
  following restrictions:
  - all terms of sort Int are linear, that is, have no occurrences of the
    function symbols *, /, div, mod, and abs, except as specified in the
    :extensions attributes;
  - all terms of sort Real are linear, that is, have no occurrences of the
    function symbols * and /, except as specified in the
    :extensions attribute;
  - all array terms have sort
    (Array Int Real) or
    (Array Int (Array Int Real)).
 "

:extensions
 "For every operator op with declaration (op Real Real s) for some sort s,
  and every term t1, t2 of sort Int and t of sort Real, the expression
  - (op t1 t) is syntactic sugar for (op (to_real t1) t)
  - (op t t1) is syntactic sugar for (op t (to_real t1))
  - (/ t1 t2) is syntactic sugar for (/ (to_real t1) (to_real t2))
 "

 :extensions
 "Real or Int terms with _concrete_ coefficients are also allowed, that is,
  terms of the form c, (* c x), or (* x c) where
  x is a free constant of sort Int or Real and
  c is an integer or rational coefficient, respectively.
  - An integer coefficient is a term of the form m or (- m) for some
    numeral m.
  - A rational coefficient is a term of the form d, (- d) or (/ c n)
    for some decimal d, integer coefficient c and numeral n other than 0.
 "
)
