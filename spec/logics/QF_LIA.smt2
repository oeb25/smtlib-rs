(logic QF_LIA

 :smt-lib-version 2.6
 :smt-lib-release "2017-11-24"
 :written-by "Cesare Tinelli"
 :date "2010-04-30"
 :last-updated "2015-04-25"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2021-01-21 Clarified wording around what terms are included in extensions.
  2015-04-25 Updated to Version 2.5.
 "

 :theories (Ints)

 :language 
 "Closed quantifier-free formulas built over an arbitrary expansion of the
  Ints signature with free constant symbols, but whose terms of sort Int 
  are all linear, that is, have no occurrences of the function symbols
  /, div, mod, and abs, and no occurrences of the function symbol *,
  except as specified in the :extensions attribute.
 "

 :extensions
 "Terms containing * with _concrete_ coefficients are also allowed, that
  is, terms of the form c, (* c x), or (* x c)  where x is a free constant
  and c is a term of the form n or (- n) for some numeral n.
 "
)


