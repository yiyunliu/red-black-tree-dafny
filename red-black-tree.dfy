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
		predicate Valid()
			decreases Repr
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

		

    // http://leino.science/papers/krml273.html
		static method insertBST(t : RBTreeRef?, n : RBTreeRef) returns (r : RBTreeRef)
			requires n.parent == null
			requires n.Repr == {n}
			requires n !in ReprN(t)
			requires t != null ==> t.Valid()
			requires n.Valid()
			requires elems(n.Tree)=={n.value}
			requires n.color == Red

  		modifies if t != null then t.Repr else {}
 			modifies n
			
  		ensures if t == null then r == n else r == t
			ensures t != null ==> t.parent == old(t.parent)
			ensures n == old(n)
			ensures n.value == old(n.value)
			ensures n.color == old(n.color)
			ensures n.left == null
			ensures n.right == null
			ensures n.Repr == {n}
			ensures n.Valid()
			ensures t != null ==> old(ElemsN(t)) + {n.value} == ElemsN(t)
			ensures old(countBlackN(t)) == countBlackN(r)
			ensures t != null ==> old(t.Repr) + {n} == r.Repr
			ensures r.Valid()
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

predicate isRed(t : RBTree) {
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

