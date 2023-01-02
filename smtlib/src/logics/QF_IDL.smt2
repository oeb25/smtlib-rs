(logic QF_IDL

 :smt-lib-version 2.6
 :smt-lib-release "2017-11-24"
 :written-by "Cesare Tinelli"
 :date "2010-04-30"
 :last-updated "2015-04-25"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2015-04-25 Updated to Version 2.5.
 "

 :theories ( Ints )

 :language
 "Closed quantifier-free formulas with atoms of the form:
  - q
  - (op (- x y) n),
  - (op (- x y) (- n)), or
  - (op x y)
  where
    - q is a variable or free constant symbol of sort Bool,
    - op is <, <=, >, >=, =, or distinct,
    - x, y are free constant symbols of sort Int, 
    - n is a numeral. 
 "
)


