# coq-hol-light-Logic1
Translation of the HOL-Light [Logic library](https://github.com/jrh13/hol-light/tree/master/Logic) using [hol2dk](https://github.com/Deducteam/hol2dk).

mappings only go up to (and not including) unify. The full library will be available as coq-hol-light-Logic2 and use results from this translation to define unify

Currently depending on https://github.com/agontard/coq-hol-light-real-with-N/tree/with_mathcomp for mathcomp integration, and temporarily provides its own updated version of the mappings of the [coq-hol-light](https://github.com/Deducteam/coq-hol-light) library to adapt to this integration and map set theory to mathcomp-classical set theory.
