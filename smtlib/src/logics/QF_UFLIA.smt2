(logic QF_UFLIA

 :smt-lib-version 2.6
 :smt-lib-release "2017-11-24"
 :written-by "Cesare Tinelli"
 :date "2011-06-11"
 :last-updated "2015-04-25"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2015-04-25 Updated to Version 2.5.
 "

 :theories ( Ints )

 :language 
 "Closed quantifier-free formulas built over arbitrary expansions of the
  Ints signatures with free sort and function symbols, but with the 
  following restrictions:
  - all terms of sort Int are linear, that is, have no occurrences of the
    function symbols *, /, div, mod, and abs, except as specified in the 
    :extensions attributes;
 "

 :extensions
 "As in the logic QF_LIA."
)

