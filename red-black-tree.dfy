// https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#1910-binding-guards

datatype Color = Red | Black


class RBTreeRef {
	ghost var Repr : set<RBTreeRef>
	var value: int
	var left: RBTreeRef?
	var right: RBTreeRef?
	var parent: RBTreeRef?
	var color: Color
		
		
static twostate lemma ValidFix(x : RBTreeRef, y : RBTreeRef)
	requires y.parent == old(y.parent)
	requires y.Repr == old(y.Repr)
	requires y.ValidWeak()
	requires old(x.ValidWeak())
	requires old(x.Valid())
	requires old(y in x.ElemsRef())
	// requires old(y in x.ElemsRef()) && old(y.parent != null && y.parent != x && y.parent in x.ElemsRef() ==> y.parent.ValidWeak() && y.PartialNoRRP() && y.parent.PartialNoRR(x))
	requires old(y.ElemsRef()) == y.ElemsRef()
	requires forall o :: o !in y.ElemsRef() ==> unchanged(o)
	requires countBlackN(y) == old(countBlackN(y))
	requires ElemsN(y) == old(ElemsN(y))
	requires old(y.Valid())
	requires y.Valid()

	ensures x.ValidWeak()
	ensures y in x.ElemsRef()
	ensures x.Valid()
	ensures ElemsN(x) == old(ElemsN(x))
	ensures countBlackN(x) == old(countBlackN(x))
	decreases old(x.Repr)
{
	assume(false);
	// if(x==y) {
	// 	assert(x.Valid());
	// 	return;
	// }
	// if(x.left != null && old(y in x.left.ElemsRef())) {
	// 	assert(old(x.left.Valid()));
	// 	ValidFix(x.left, y);
	// }
	// else {
	// 	assert(old(x.right.Valid()));
	// 	assert(old(y in x.right.ElemsRef()));
	// 	ValidFix(x.right, y);
	// }
}


		// termination metric
		predicate ValidWeak()
			decreases Repr
  		reads this, Repr {
				this in Repr &&
					(left != null ==> left in Repr && left.Repr <= Repr && this !in left.Repr &&
					left.ValidWeak() && left.parent == this) &&
					(right != null ==> right in Repr && right.Repr <= Repr && this !in right.Repr &&
					right.ValidWeak() && right.parent == this) &&
					(left != null && right != null ==> left.Repr * right.Repr == {}) // &&
		}


		function method elems() : set<int>
			reads this, Repr
			requires ValidWeak()
			decreases Repr
		{
			{value} + (if left != null then left.elems() else {}) + (if right != null then right.elems() else {})
		}

		predicate isOrdered()
			reads this, Repr
			requires ValidWeak()
			decreases Repr
		{
			(left != null ==> left.isOrdered() && forall i :: i  in left.elems() ==> i < value) &&
				(right != null ==> right.isOrdered() && forall i :: i  in right.elems() ==> i > value)
		}

		function countBlack() : int
			reads this, Repr
			requires ValidWeak()
			decreases Repr
		{
			(if color == Black then 1 else 0) + (if left == null then 1 else left.countBlack())
				// no right. this is NOT a typo
		}


    predicate isBalanced()
			reads this, Repr
			requires ValidWeak()
		{
			countBlackN(left) == countBlackN(right) &&
				(left != null ==> left.isBalanced()) &&
				(right != null ==> right.isBalanced())
		}

		predicate isNoRedRed()
			reads this, Repr
			requires ValidWeak()
		{
			(left != null ==> left.isNoRedRed() && (color == Red ==> left.color != Red)) &&
				(right != null ==> right.isNoRedRed() && (color == Red ==> right.color != Red))
		}

		predicate isNoRedRedL()
			reads this, Repr
			requires ValidWeak()
		{
			(left != null ==> left.isNoRedRed() && (color == Red ==> left.color != Red)) &&
				(right != null ==> (color == Red ==> right.color != Red))
		}


		predicate isNoRedRedR()
			reads this, Repr
			requires ValidWeak()
		{
			(left != null ==> (color == Red ==> left.color != Red)) &&
				(right != null ==> right.isNoRedRed() && (color == Red ==> right.color != Red))
		}

		predicate isNoRedRedRP()
			reads this, Repr
			requires ValidWeak()
		{
				(right != null ==> right.isNoRedRed() && (color == Red ==> right.color != Red))
		}

		predicate isNoRedRedLP()
			reads this, Repr
			requires ValidWeak()
		{
			(left != null ==> left.isNoRedRed() && (color == Red ==> left.color != Red))
		}
		

		predicate ValidRB()
			reads this, Repr
			requires ValidWeak()
	  {
			ValidWeak() && isNoRedRed() && isBalanced() && isOrdered()
		}

		predicate Valid()
			reads this, Repr
			requires ValidWeak()
	  {
			ValidWeak() && isBalanced() && isOrdered()
		}


		// termination metric
		static function ReprN (t : RBTreeRef?) : set<RBTreeRef>
		reads t {
			if (t == null) then {} else t.Repr
		}


		static method Member(t : RBTreeRef?, v : int) returns (r : bool)
			requires t != null ==> t.ValidWeak() && t.Valid()
			ensures (t == null ==> !r) && (t != null ==> (r <==> v in t.elems()))
			decreases ReprN(t)
		{
			if (t == null) {
				r := false;
			}

			else if (v < t.value) {
				r := Member(t.left, v);
			}

			else if (v > t.value) {
				r := Member(t.right, v);
			}

			else {
				r := true;
			}
		}

		// static method getParent(t : RBTreeRef?) returns (p : RBTreeRef?) {
		// 	if (t == null) {
		// 		return null;
		// 	}

		// 	return t.parent;
		// }

		// static method getRoot(t :RBTreeRef) returns (p : RBTreeRef?) {
		// 	if (t.parent == null) {
		// 		p := t;
		// 		return;
		// 	}
		// r := getRoot(t.parent);
		// }

		static function ElemsN (t : RBTreeRef?) : set<int>
			reads t, ReprN(t)
			requires t != null ==> t.ValidWeak()
    {
			if (t == null) then {} else t.elems()
		}


		function ElemsRef () : set<RBTreeRef>
			reads this, this.Repr
			requires this.ValidWeak()
			ensures this.ElemsRef() <= this.Repr
			ensures forall i :: i in ElemsRef() ==> i.ValidWeak() && i in this.Repr && (this.Valid() ==> i.Valid()) && (this.ValidRB() ==> i.ValidRB())
			ensures forall i :: i in ElemsRef() && i != this ==> i.Repr < Repr && ReprN(i.parent) <= Repr && i.parent != null && i.parent in ElemsRef() && i.Repr < i.parent.Repr
		{
				{this} + (if left == null then {} else left.ElemsRef()) + (if right == null then {} else right.ElemsRef())
		}


		predicate PartialNoRR (root : RBTreeRef)
			reads root, root.Repr
			requires root.ValidWeak()
			requires this in root.ElemsRef()
			decreases root.Repr - this.Repr
		{
			this != root ==>
				this.parent.PartialNoRR(root) &&
				(this.parent.left == this || this.parent.right == this) &&
				(this.parent.left == this ==> this.parent.isNoRedRedR()) &&
				(this.parent.right == this ==> this.parent.isNoRedRedL())
		}

		predicate PartialNoRRP ()
			requires parent != null ==> parent.ValidWeak()
			reads this, this.parent, ReprN(this.parent)
			// requires this in root.ElemsRef()
			// decreases root.Repr - this.Repr
		{
			this.parent != null ==>
				(this.parent.left == this || this.parent.right == this) &&
				(this.parent.left == this ==> this.parent.isNoRedRedRP()) &&
				(this.parent.right == this ==> this.parent.isNoRedRedLP())
		}


		static lemma CombineNoRR(r0 : RBTreeRef, r1 : RBTreeRef)
			requires r0.ValidWeak()
			requires r1.ValidWeak()
			requires r0.ValidRB()
			requires r1.Valid()
			requires r0 in r1.ElemsRef()
			requires r0.PartialNoRR(r1)
			ensures r1.ValidRB()
			decreases r1.Repr - r0.Repr
		{
			if (r0 == r1) {
				assert(r1.ValidRB());
				return;
			}

			assert(r0.parent.ValidRB());
			assert(r0.parent.PartialNoRR(r1));
			CombineNoRR(r0.parent, r1);
		}


		static lemma ElemsRefTrans(r0 : RBTreeRef, r1 : RBTreeRef, r2 : RBTreeRef)
			requires r1.ValidWeak()
			requires r2.ValidWeak()
			// requires r1.Valid()
			// requires r2.Valid()
			requires r0 in r1.ElemsRef()
			requires r1 in r2.ElemsRef()
			decreases r2.Repr
			ensures r0 in r2.ElemsRef()
		{
			if (r1 == r2) {
				assert(r0 in r2.ElemsRef());
				return;
			}

			if (r2.left == null || r1 !in r2.left.ElemsRef()) {
				assert(r1 in r2.right.ElemsRef());
				ElemsRefTrans(r0,r1,r2.right);
				return;
			}

			ElemsRefTrans(r0,r1,r2.left);
		}

		static function countBlackN(r0:RBTreeRef?) : int
			reads r0, ReprN(r0)
			requires r0 != null ==> r0.ValidWeak()
		{
			if r0 == null then 1 else r0.countBlack()
		}

  		// // // use convert?
 		static ghost method partialNoRRTrans(r0 : RBTreeRef, r1 : RBTreeRef, r2 : RBTreeRef)
  		requires r1.ValidWeak()
  		requires r2.ValidWeak()
			decreases r1.Repr - r0.Repr
			requires r0 in r1.ElemsRef()
			requires r1 in r2.ElemsRef()
			requires r0 in r2.ElemsRef()
			requires r0.PartialNoRR(r1)
			requires r1.PartialNoRR(r2)
			ensures r0.PartialNoRR(r2)
			{
				if(r0!=r1) {
					partialNoRRTrans(r0.parent, r1, r2);
				}
			}



    // http://leino.science/papers/krml273.html
		static method insert(t : RBTreeRef?, v : int) returns (r : RBTreeRef)
			requires t != null ==> t.ValidWeak() && t.ValidRB()
			// ensures r.Valid()
			modifies if t != null then t.Repr else {}
		{
    	var n := new RBTreeRef;
			n.Repr := {n};
			n.value := v;
			n.left := null;
			n.right := null;
			n.color := Red;
			n.parent := null;

			assert(n.ValidRB());

			r := insertBST(t, n);

			
			// handle the trivial case where n is not inserted at all
			if(n == r || n.parent == null) {
				assert(r.ValidRB());
				return;
			}

			// while(true)

			// DROP r.Valid and strengthen 
			// 	invariant r.Valid()
			// 	invariant ElemsN(r) == ElemsN(t) + {v}
			// 	invariant n in r.ElemsRef()
			// 	invariant n != r ==> n.parent.PartialNoRR(r) && n.PartialNoRRP() && n.color == Red
			// 	invariant n.ValidRB()
			// 	decreases r.Repr - n.Repr
				// decreases a.Length - index
				// invariant 0 <= index <= a.Length
				// invariant forall j : nat :: j < index ==> a[j] != key
			{
				// Case 3
				if(n == r) {
					// assert(r.ValidRB());
					// break;
					return;
				}

				// Case 1
				if(n.parent.color == Black) {
					// assert(n.parent.ValidRB());
					CombineNoRR(n.parent, r);
					// assert(r.ValidRB());
					// break;
					return;
				}

				// now the parent's color is Red

				// Case 4
				if(n.parent == r) {
					n.parent.color := Black;
					assert(r.ValidRB());
					// break;
					return;
				}

				// grandparent's color must be Black
				assert(n.parent.parent.color == Black);

				var isLeft := n.parent == n.parent.parent.left;
				var uncle := if isLeft then n.parent.parent.right else n.parent.parent.left;

				// Case 2
				if(uncle != null && uncle.color == Red) {
					assert(n.parent.parent.Valid());
					assert(uncle.ValidRB());
					assert(uncle.ValidWeak());
					label L1:
					uncle.color := Black;
					n.parent.color := Black;
					assert(n.parent.ValidRB());
					assert(uncle.ValidWeak());
					assert(uncle.ValidRB());
					n.parent.parent.color := Red;
					assert(if isLeft then n.parent.parent.left == n.parent else n.parent.parent.left == uncle);

					assert(old@L1(ElemsN(n.parent))==ElemsN(n.parent));
					assert(old@L1(ElemsN(uncle))==ElemsN(uncle));
					assert(old@L1(countBlackN(n.parent)) + 1==countBlackN(n.parent));
					assert(old@L1(countBlackN(uncle)) + 1==countBlackN(uncle));

					assert(old@L1(n.parent.value)==n.parent.value);
					assert(old@L1(uncle.value)==uncle.value);

					assert(n.parent.parent.ValidRB());
					assert(n.parent.parent.Repr == old@L1(n.parent.parent.Repr));
					assert(ElemsN(n.parent.parent) == old@L1(ElemsN(n.parent.parent)));
					assert(countBlackN(n.parent.parent) == old@L1(countBlackN(n.parent.parent)));
					
					ValidFix@L1(r, n.parent.parent);
					if(n.parent.parent != r) {

						assert(n.parent.parent.ValidWeak());
						assert(old@L1(n.parent.parent.PartialNoRR(r)));
						assert(n.parent.parent.PartialNoRRP());

					}
					
					

					// fixing up the Tree Repr
					var u := n.parent.parent;
				}
				
				// break;
				return;
			}
		}

		static method insertBST(t : RBTreeRef?, n : RBTreeRef) returns (r : RBTreeRef)
			requires n.parent == null
			requires n.Repr == {n}
			requires n !in ReprN(t)
			requires t != null ==> t.ValidWeak() && t.ValidRB()
			requires n.ValidWeak()
			requires n.Valid()
			requires n.left == null && n.right == null && n.color == Red
			requires n.color == Red

 			modifies if t != null then t.Repr else {}
			modifies n`parent
				
			ensures n.Repr == old(n.Repr) && n.value == old(n.value) && n.left == null && n.right == null && n.color == Red
			ensures t != null ==> t.ValidWeak() && old(t.Repr) + {n} == r.Repr && t == r && t.color == old(t.color) && old(t.elems()) + {n.value} == t.elems()
  		ensures if t == null then r == n else r == t
			ensures n.parent == null ==> r.ValidRB()
			ensures t != null ==> t.parent == old(t.parent)
			ensures r.ValidWeak()
			ensures n.ValidWeak()
			ensures n.ValidRB()
			ensures (n.parent == null && n != r) ==> r == t && t.color == old(t.color) &&
			          t.value == old(t.value) && t.left == old(t.left) && t.right == old(t.right)
			ensures t != null ==> old(ElemsN(t)) + {n.value} == ElemsN(t)
			ensures ElemsN(r) == ElemsN(t) + {n.value}
			ensures old(countBlackN(t)) == countBlackN(r)
			ensures r.Valid()
			ensures n.parent != null ==> n.parent.ValidWeak()
			ensures n.parent != null ==> n in r.ElemsRef() && (n != r ==> n.parent.PartialNoRR(r)) && n.PartialNoRRP()
      decreases ReprN(t)
		{

		// 	if (t == null) {
		// 		r := n;
		// 		return;
		// 	}

		// 	r := t;

		// 	if (t.value == n.value) {
		// 		t.Repr := t.Repr + {n};
		// 		return;
		// 	}


		// 	// n.parent doesn't work because dafny doesn't know n remains the same

		// 	if (n.value < t.value) {
		// 		label L1:
		// 		var newLeft := insertBST(t.left, n);

		// 		r.Repr := r.Repr + {n};
		// 		r.left := newLeft;
		// 		if(newLeft == n){
		// 			n.parent := t;
		// 		}
		// 		if(n.parent != null){
		// 			ElemsRefTrans(n,newLeft,r);
		// 			if(n != newLeft) {
		// 				partialNoRRTrans(n.parent,newLeft,r);
		// 			}
		// 		}
		// 		return;
		// 	}

		// 	if (n.value > t.value) {
		// 		label L2:
		// 		var newRight := insertBST(t.right, n);
		// 		r.Repr := r.Repr + {n};
		// 		r.right := newRight;
		// 		if(newRight == n){
		// 			n.parent := t;
		// 		}
		// 		if(n.parent != null){
		// 			ElemsRefTrans(n,newRight,r);
		// 			if(n != newRight) {
		// 				partialNoRRTrans(n.parent,newRight,r);
		// 			}
		// 		}
		// 		return;
		// }
		assume(false);
		}

		// static method getGrandparent(t : RBTreeRef?) returns (g : RBTreeRef?)

}

method Testing()
{
	var t2 := new RBTreeRef;
	t2.value, t2.color, t2.right, t2.parent := 10, Black, null, null;

	var t3 := new RBTreeRef;
	t3.left := null;
	t3.right := null;
	t3.color := Red;
	t3.parent := t2;
	t3.value := 9;

	t2.Repr := {t2,t3}	;
	t3.Repr := {t3};
	t2.left := t3;

	assert(t2.Valid());


	// Methods are opaque!!
	var r := RBTreeRef.Member(t2, 9);
	// assertion would fail if Member weren't annotated
	assert(r);
}
