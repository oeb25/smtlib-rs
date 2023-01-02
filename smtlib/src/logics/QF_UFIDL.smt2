(logic QF_UFIDL

 :smt-lib-version 2.6
 :smt-lib-release "2017-11-24"
 :written-by "Clark Barrett, Cesare Tinelli"
 :date "2010-05-12"
 :last-updated "2015-04-25"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2015-04-25 Updated to Version 2.5.
  2011-06-03 Added :note field."

 :theories (Ints)

 :language
 "Closed quantifier-free formulas built over an arbitrary expansion with 
  free sort and function symbols of the signature consisting of 
  - all the sort and function symbols of Core and
  - the following symbols of Int:

    :sorts ((Int 0))
    :funs ((NUMERAL Int) 
           (- Int Int Int)
           (+ Int Int Int) 
           (<= Int Int Bool)
           (< Int Int Bool)
           (>= Int Int Bool)
           (> Int Int Bool)
          )

  Additionally, for every term of the form (op t1 t2) with op in {+, -}, 
  at least one of t1 and t2 is a numeral. 
 "

 :note 
 "For historical reasons, the syntax of this logic is *not* an extension 
  of QF_IDL's syntax. However, any formula in this logic with no free sorts 
  and no free function symbol of arity > 0 can be converted into an 
  equisatisfiable formula in QF_IDL.
 "
)


