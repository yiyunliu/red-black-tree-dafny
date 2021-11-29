// https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#1910-binding-guards

// do imperative BST instead of full-fledged RBTree

datatype Color = Red | Black

datatype RBTree = Empty  | Node (color : Color, value : int, left : RBTree, right : RBTree)

function method elems(t : RBTree) : set<int> {
	if t == Empty then {} else {t.value} + elems(t.left) + elems(t.right)
}

method testHigher (f : int -> int)
	requires forall x :: f(x) == 1 + x
	ensures forall x :: f(x) - 1 == x
{
}


class RBTreeRef {
 	ghost var Tree : RBTree
		ghost var Repr : set<RBTreeRef>
		var value: int
		var left: RBTreeRef?
		var right: RBTreeRef?
		var parent: RBTreeRef?
		var color: Color
		predicate ValidWeak()
			decreases Repr
  		reads this, Repr {
				this in Repr &&
					// Tree.Node? &&
					// Tree.value == value &&
					// Tree.color == color &&
					// (left == null ==> Tree.left.Empty?) &&
					// (right == null ==> Tree.right.Empty?) &&
					(left != null ==> left in Repr && left.Repr <= Repr && this !in left.Repr &&
					left.ValidWeak() && left.parent == this) &&
					(right != null ==> right in Repr && right.Repr <= Repr && this !in right.Repr &&
					right.ValidWeak() && right.parent == this) &&
					(left != null && right != null ==> left.Repr * right.Repr == {}) // &&
					// isWellFormed(Tree)
					// isBalanced(Tree) &&
					// isOrdered(Tree)
		}


		predicate Valid()
			decreases Repr
			ensures Valid() ==>  ValidWeak() && isOrdered(Tree) && isBalanced(Tree)
  		reads this, Repr {
				this in Repr &&
					Tree.Node? &&
					Tree.value == value &&
					Tree.color == color &&
					(left == null ==> Tree.left.Empty?) &&
					(right == null ==> Tree.right.Empty?) &&
					(left != null ==> left in Repr && left.Repr <= Repr && this !in left.Repr &&
					left.Valid() && left.Tree == Tree.left && left.parent == this) &&
					(right != null ==> right in Repr && right.Repr <= Repr && this !in right.Repr &&
					right.Valid() && right.Tree == Tree.right && right.parent == this) &&
					(left != null && right != null ==> left.Repr * right.Repr == {}) &&
					// isWellFormed(Tree)
					isBalanced(Tree) &&
					isOrdered(Tree)
		}


		predicate ValidRB()
			decreases Repr
			ensures Valid() && noRedRed(Tree) <==> ValidRB()
			// ensures ValidRB() ==> Valid()
  		reads this, Repr {
				this in Repr &&
					Tree.Node? &&
					Tree.value == value &&
					Tree.color == color &&
					(left == null ==> Tree.left.Empty?) &&
					(right == null ==> Tree.right.Empty?) &&
					(left != null ==> left in Repr && left.Repr <= Repr && this !in left.Repr &&
					left.ValidRB() && left.Tree == Tree.left && left.parent == this) &&
					(right != null ==> right in Repr && right.Repr <= Repr && this !in right.Repr &&
					right.ValidRB() && right.Tree == Tree.right && right.parent == this) &&
					(left != null && right != null ==> left.Repr * right.Repr == {}) &&
					// isWellFormed(Tree)
					isBalanced(Tree) &&
					isOrdered(Tree) &&
					noRedRed(Tree)
		}

		// termination metric
		static function ReprN (t : RBTreeRef?) : set<RBTreeRef>
		reads t {
			if (t == null) then {} else t.Repr
		}


		static method Member(t : RBTreeRef?, v : int) returns (r : bool)
			requires t != null ==> t.Valid()
			ensures (t == null ==> !r) && (t != null ==> (r <==> v in elems(t.Tree)))
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

		static method getParent(t : RBTreeRef?) returns (p : RBTreeRef?) {
			if (t == null) {
				return null;
			}

			return t.parent;
		}

		// static method getRoot(t :RBTreeRef) returns (p : RBTreeRef?) {
		// 	if (t.parent == null) {
		// 		p := t;
		// 		return;
		// 	}
		// r := getRoot(t.parent);
		// }

		static function ElemsN (t : RBTreeRef?) : set<int>
		reads t {
			if (t == null) then {} else elems(t.Tree)
		}


		static function countBlackN (t : RBTreeRef?) : int
			reads t {
				if (t == null) then 1 else countBlack(t.Tree)
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
			// this.parent != null ==>
			this != root ==>
				this.parent.PartialNoRR(root) &&
        this.parent.Valid() &&
				(this.parent.left == this || this.parent.right == this) &&
				(this.parent.left == this ==> noRedRedR(this.parent.Tree) && (this.parent.right == null || this.parent.right.ValidRB())) &&
				(this.parent.right == this ==> noRedRedL(this.parent.Tree) && (this.parent.left == null || this.parent.left.ValidRB()))
		}


		predicate PartialNoRRP ()
			reads this.parent
			reads this
			requires this.parent != null
		{
			  this.parent.Valid() &&
			  (this.parent.left == this || this.parent.right == this) &&
				(this.parent.left == this ==> noRedRedRP(this.parent.Tree)) &&
				(this.parent.right == this ==> noRedRedLP(this.parent.Tree))
		}


		static lemma CombineNoRR(r0 : RBTreeRef, r1 : RBTreeRef)
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
			requires r1.Valid()
			requires r2.Valid()
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

		// use convert?
		static ghost method partialNoRRTrans(r0 : RBTreeRef, r1 : RBTreeRef, r2 : RBTreeRef)
			requires r1.Valid()
			requires r2.Valid()
			decreases r1.Repr - r0.Repr
			requires r0 in r1.ElemsRef()
			requires r1 in r2.ElemsRef()
			requires r0 in r2.ElemsRef()
			requires r0.PartialNoRR(r1)
			requires r1.PartialNoRR(r2)
			ensures r0.PartialNoRR(r2)
			{
				if(r0==r1) {
					assert(r0.PartialNoRR(r2));
					return;
				}

				assert(r0.parent in r1.ElemsRef());
				assert(r0.parent.PartialNoRR(r1));
				partialNoRRTrans(r0.parent, r1, r2);
			// assert(r1 != r2);
		}

    // http://leino.science/papers/krml273.html
		static method insert(t : RBTreeRef?, v : int) returns (r : RBTreeRef)
			requires t != null ==> t.ValidRB()
			// ensures r.Valid()
			modifies if t != null then t.Repr else {}
		{
    	var n := new RBTreeRef;
			n.Tree := Node(Red,v,Empty,Empty);
			n.Repr := {n};
			n.value := v;
			n.left := null;
			n.right := null;
			n.color := Red;
			n.parent := null;

			assert(n.ValidRB());

			r := insertBST(t, n);

			
			// handle the trivial case where n is not inserted at all
			if(n.parent == null || n == r) {
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
					n.parent.Tree := n.parent.Tree.(color := Black);
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
					assert(uncle.Valid());
					assert(n.parent.PartialNoRR(r));
					assert(noRedRed(uncle.Tree));
					assert(uncle.ValidRB());
					assert(uncle.Tree.Node?);
					assert(uncle != n.parent);
					assert(uncle.parent == n.parent.parent);
					assert(n.parent.parent.Valid());
					assert(n.parent.parent.Tree.Node?);
					assert(n.parent.Valid());
					assert(n.parent.Tree.Node?);
					label L1:
					uncle.color := Black;
					uncle.Tree := uncle.Tree.(color := Black);
					n.parent.color := Black;
					n.parent.Tree := n.parent.Tree.(color := Black);
					assert(n.parent.ValidRB());
					assert(uncle.ValidRB());
					n.parent.parent.color := Red;
					assert(if isLeft then n.parent.parent.left == n.parent else n.parent.parent.left == uncle);
					if isLeft {
						n.parent.parent.Tree := n.parent.parent.Tree.(color := Red,
							left := n.parent.Tree,
							right := uncle.Tree);
							// assert(n.parent.parent.value == n.parent.parent.Tree.value);
							// assert(n.parent.value == n.parent.Tree.value);
							// assert(uncle.value == uncle.Tree.value);

							// assert(n.parent.parent.value > n.parent.value);
							// assert(n.parent.parent.value < uncle.value);
							// assert(n.parent.parent.Tree.left == n.parent.Tree);
							// assert(n.parent.parent.Tree.right == uncle.Tree);
					}
					else {
						n.parent.parent.Tree := n.parent.parent.Tree.(color := Red,
							left := uncle.Tree,
							right := n.parent.Tree);
					}

					// assert(old@L1(ElemsN(n.parent))==ElemsN(n.parent));
					// assert(old@L1(ElemsN(uncle))==ElemsN(uncle));
					// assert(old@L1(n.parent.value)==n.parent.value);
					// assert(old@L1(uncle.value)==uncle.value);

					assert(n.parent.parent.ValidRB());
							// assert(isOrdered(n.parent.parent.Tree));

					
						// assume(n.parent.parent.Tree.value> n.parent.Tree.value);
						// assume(n.parent.parent.Tree.value==old(n.parent.parent.Tree.left.value));
						// assert(n.parent.)
					
					// assert(noRedRed(n.parent.parent.Tree));
					// assert(n.parent.parent.Valid());
					// assert(n.parent.parent.ValidRB());
					// assert(n.parent.Valid());
					// assert(n.parent.parent.Valid());
					// assert(n.parent.parent.color == Black);

					// assert(n.parent.parent.ValidRB());



					// fixing up the Tree Repr
					var u := n.parent.parent;
					// while(u != r)
					// 	invariant old(r.Valid())
					// 	invariant u in old(r.ElemsRef())
					// 	invariant u.Valid()
					// 	invariant 
					// {
						
					// }
				}
				
				// break;
				return;
			}
		}

		static method insertBST(t : RBTreeRef?, n : RBTreeRef) returns (r : RBTreeRef)
			requires n.parent == null
			requires n.Repr == {n}
			requires n !in ReprN(t)
			requires t != null ==> t.ValidRB()
			requires n.Valid()
			requires elems(n.Tree)=={n.value}
			requires n.color == Red

 			modifies if t != null then t.Repr else {}
			modifies n`parent
				
  		ensures if t == null then r == n else r == t
			ensures t != null ==> t.parent == old(t.parent)
			ensures n.ValidRB()
			ensures t != null ==> old(ElemsN(t)) + {n.value} == ElemsN(t)
			ensures ElemsN(r) == ElemsN(t) + {n.value}
			ensures old(countBlackN(t)) == countBlackN(r)
			ensures t != null ==> old(t.Repr) + {n} == r.Repr
			ensures r.Valid()
			ensures n.parent != null ==> n in r.ElemsRef() && (n != r ==> n.parent.PartialNoRR(r)) && n.PartialNoRRP()
			ensures t == r ==> t.color == old(t.color)
			ensures (n.parent == null && n != r) ==> r == t && t.color == old(t.color) &&
			          t.value == old(t.value) && t.left == old(t.left) && t.right == old(t.right) && t.Tree == old(t.Tree)
      decreases ReprN(t)
		{

			if (t == null) {
				r := n;
				return;
			}

			r := t;

			if (t.value == n.value) {
				t.Repr := t.Repr + {n};
				return;
			}


			// n.parent doesn't work because dafny doesn't know n remains the same

			if (n.value < t.value) {

				var newLeft := insertBST(t.left, n);

				r.Repr := r.Repr + {n};
				r.Tree := Node(t.color,t.value,newLeft.Tree,t.Tree.right);
				r.left := newLeft;
				if(newLeft == n){
					n.parent := t;
				}

				if(n.parent != null){
					ElemsRefTrans(n,newLeft,r);
					if(n != newLeft) {
						partialNoRRTrans(n.parent,newLeft,r);
					}

				assert(n.parent in r.ElemsRef());
				}
				return;
			}

			if (n.value > t.value) {
				var newRight := insertBST(t.right, n);
				r.Repr := r.Repr + {n};
				r.Tree := Node(t.color,t.value,t.Tree.left,newRight.Tree);
				r.right := newRight;
				if(newRight == n){
					n.parent := t;
				}


				if(n.parent != null){
					ElemsRefTrans(n,newRight,r);
					if(n != newRight) {
						partialNoRRTrans(n.parent,newRight,r);
					}
				}
				return;
			}
			
			assert(false);

		}

		// static method getGrandparent(t : RBTreeRef?) returns (g : RBTreeRef?)

}

method Testing()
{
	var t0 := Node(Red,10,(Node(Black,9,Empty,Empty)),Empty);
	assert(!isWellFormed(t0));
	var t1 := Node(Black,10,(Node(Red,9,Empty,Empty)),Empty);
	assert(isWellFormed(t1));

	var t2 := new RBTreeRef;
	t2.Tree := t1;
	t2.value, t2.color, t2.right, t2.parent := 10, Black, null, null;

	var t3 := new RBTreeRef;
	t3.Tree := Node(Red,9,Empty,Empty);
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


// predicate isBlack(t : RBTree) {
// 	!isRed(t)
// }

predicate method isRed(t : RBTree) {
	t.Node? && t.color == Red
}


function countBlack(t : RBTree) : nat {
	if t.Empty? then 1 else (if t.color == Red then countBlack(t.left) else 1 + countBlack(t.left))
}

predicate isBalanced(t : RBTree) {
	if t.Empty? then true else
		(countBlack(t.left) == countBlack(t.right) && isBalanced(t.left) && isBalanced(t.right))
}

predicate isOrdered(t : RBTree) {
	if t.Empty? then true else
		(forall i :: i in elems(t.left) ==> i < t.value) &&
		(forall i :: i in elems(t.right) ==> i > t.value)
}

// predicate isOrdered(t: RBTree) {
// 	if t.Empty? then true else
// 		(t.left.Node? ==> t.left.value < t.value && isOrdered(t.left)) &&
// 		(t.right.Node? ==> t.value < t.right.value && isOrdered(t.right))
// }


predicate noRedRedRP(t : RBTree) {
	(isRed(t) ==> !isRed(t.right)) &&
		(t.Node? ==> noRedRed(t.right))
}

predicate noRedRedLP(t : RBTree) {
  (isRed(t) ==> !isRed(t.left)) &&
		(t.Node? ==> noRedRed(t.left))
}


predicate noRedRedR(t : RBTree) {
	(isRed(t) ==> !isRed(t.left) && !isRed(t.right)) &&
		(t.Node? ==> noRedRed(t.right))
}

predicate noRedRedL(t : RBTree) {
  (isRed(t) ==> !isRed(t.left) && !isRed(t.right)) &&
		(t.Node? ==> noRedRed(t.left))
}

predicate noRedRed(t : RBTree) {
	(isRed(t) ==> !isRed(t.left) && ! isRed(t.right)) &&
		(t.Node? ==> noRedRed(t.left) && noRedRed(t.right))
}

predicate isWellFormed(t : RBTree) {
	isBalanced(t) && isOrdered(t) && noRedRed(t)
}


predicate noRedRedExceptTop(t : RBTree) {
	(t.Node? ==> noRedRed(t.left) && noRedRed(t.right))	
}

predicate almostWellFormed(t : RBTree) {
	isBalanced(t) && isOrdered(t) && noRedRedExceptTop(t)
}



// method ins(t : RBTree, v: int) returns (r : RBTree)
// 	requires almostWellFormed(t)
// 	ensures almostWellFormed(r)		// need to include more precise information about ordering
// 	decreases t;
// {
// 	if(t.Empty?){
// 		return Node(Red,v,Empty,Empty);
// 	}
// 	if (v < t.value) {
		
// 	}
// 	if (v > t.value) {
		
// 	}
// 	return t;
// }

// method setBlack(t : RBTree) returns (r : RBTree)
// 	requires almostWellFormed(t)
// 	ensures isWellFormed(r)
// {
// 	if (t.Empty?) {
// 		return Empty;
// 	}
// 	return Node(Black, t.value,t.left,t.right);
// }


// method balanceL(c : Color, v : int, l : RBTree, r : RBTree) returns (r : RBTree)
// 	requires 
// {
// }


// method insert(t : RBTree) returns (r : RBTree)  {
	

// 	// r := Empty;
// }

// class RBTree {
// 		ghost var Repr: set<RBTree>
// 		var value: int
// 		var left: RBTree?
// 		var right: RBTree?

// 		predicate Valid()
// 			decreases Repr + {this}
// 			reads this, Repr {
// 				this in Repr &&
// 					1 <= size &&
// 					(left == null && right == null ==> size == 1) &&
// 					(left == null && right != null ==> size == right.size + 1) &&
// 					(left != null && right == null ==> size == left.size + 1) &&
// 					(left != null && right != null ==> size == left.size + right.size + 1) &&
// 					// ordering?
// 					(left != null ==> left.Repr <= Repr && left.size < size && this !in left.Repr && left.Valid()) &&
// 					(right != null ==> right.Repr <= Repr && right.size < size && this !in right.Repr && right.Valid())
// 		}
// }


// class Node {
//   // ghost var List: seq<int>
//   ghost var Repr: set<Node>
//   var head: int
//   var next: Node? // Node? means a Node value or null
// 	var parent: Node?

//   predicate Valid()
// 		decreases Repr
//     reads this, Repr
//   {
//     this in Repr &&
//     // 1 <= |List| && List[0] == head &&
//     // (next == null ==> |List| == 1) &&
//     (next != null ==>
//       next in Repr && next.Repr <= Repr && this !in next.Repr &&
//       next.Valid() && // && next.List == List[1..] 
// 			(next.parent == this)) 
			
//   }

//   // static method Cons(x: int, tail: Node?) returns (n: Node)
//   //   requires tail == null || tail.Valid()
//   //   ensures n.Valid()
//   //   ensures if tail == null then n.List == [x]
//   //                           else n.List == [x] + tail.List
//   // {
//   //   n := new Node;
//   //   n.head, n.next := x, tail;
//   //   if (tail == null) {
//   //     n.List := [x];
//   //     n.Repr := {n};
//   //   } else {
//   //     n.List := [x] + tail.List;
//   //     n.Repr := {n} + tail.Repr;
//   //   }
//   // }
// }

