open Linear

val transform : prog -> prog
(**[transform prog] transforms the program [prog] into an equivalent
   simplified program. At this time, only one simplification rule is
   used: when we find a [let] binding of the form [let xs = ys in e],
   we suppress this binding and substitute [ys] for [xs] in [e]. *)
