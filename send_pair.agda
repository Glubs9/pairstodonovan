module pair2 where

data _==_ {a} {A : Set a} (x : A) : A -> Set a where
	refl : x == x


-- official definition (non dependent pair)

data _x_ (A : Set) (B : Set) : Set where
	_,_ : A -> B -> A x B

infixr 4 _,_
infixr 4 _x_

proj1 : {A B : Set} -> A x B -> A
proj1 (a , b) = a

proj2 : {A B : Set} -> A x B -> B
proj2 (a , b) = b


-- function encoded definition

make_pair : {A B : Set} -> A -> B (F : Set -> Set -> Set) -> (A -> B -> F A B) -> F A B
make_pair a b F f = f a b

--used to make function definitions cleaner
typeof_pair : Set -> Set -> Set 1
typeof_pair A B = (F : Set -> Set -> Set) -> (A -> B -> F A B) -> F A B

p1 : {A B : Set} -> A -> B -> A
p1 x y = x

pr1_type : Set -> Set -> Set
pr1_type A B = A

pr1 : {A B : Set} -> typeof_pair A B -> A
pr1 p = p pr1_type p1

p2 : {A B : Set} -> A -> B -. B
p2 x y = y

pr2_type : Set -> Set -> Set
pr2_type A B = B

pr2 : {A B : Set} -> typeof_pair A B -> B
pr2 p = p pr2_type p2


-- proofs

p1_proof : {A B : Set} -> (a :  A) (b : B) -> proj1 (a , b) == pr1 (make_pair a b) 
p1_proof a b = refl

p2_proof : {A B : Set} -> (a : A) (b : B) -> proj2 (a , b) == pr2 (make_pair a b)
p2_proof a b = refl

proof : {A B : Set} -> (a : A) (b : B) -> proj1 (a , b) == pr1 (make_pair a b) x proj2 (a , b) == pr2 (make_pair a b)
proof a b = (p1_proof a b , p2_proof a b)

-- beta proofs abbreviated for brevity

-- the following doesn't typecheck
-- the question is, as we know that the standard pair definition and this one do the same behaviour, does it matter? especially when we can write it with some extra verbosity (albeit potentially removing the value of the unicity)
-- pair_unicity : {A B : Set} (a : A) (b : B) -> (p : typeof_pair A B) -> p == make_pair (pr1 p) (pr2 p)
-- pair_unicity a b p = refl
-- the specific error this gives is "
-- p F x != x (pr1 p) (pr2 p) of type F A B
-- when checking that the expression refl has type
-- p == make pr1 p pair (pr2 p)
-- "

-- with a more verbose definition unicity holds, although the equivalence with the above is dubious
pair_unicity : {A B : Set} (a : A) (b : B) -> make_pair a b == make_pair (pr1 (make_pair a b)) (pr2 (make_pair a b))
pair_unicity a b = refl
