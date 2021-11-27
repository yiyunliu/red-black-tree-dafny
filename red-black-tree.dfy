datatype Color = Red | Black

datatype RBTree = Empty  | Node (color : Color, value : int, left : RBTree, right : RBTree)

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

predicate isOrdered(t: RBTree) {
	if t.Empty? then true else
		(t.left.Node? ==> t.left.value < t.value && isOrdered(t.left)) &&
		(t.right.Node? ==> t.value < t.right.value && isOrdered(t.right))
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

method Testing()
{
	var t0 := Node(Red,10,(Node(Black,9,Empty,Empty)),Empty);
	assert(!isWellFormed(t0));
	var t1 := Node(Black,10,(Node(Red,9,Empty,Empty)),Empty);
	assert(isWellFormed(t1));
}


method ins(t : RBTree, v: int) returns (r : RBTree)
	requires almostWellFormed(t)
	ensures almostWellFormed(r)		// need to include more precise information about ordering
	decreases t;
{
	if(t.Empty?){
		return Node(Red,v,Empty,Empty);
	}
	if (v < t.value) {
		
	}
	if (v > t.value) {
		
	}
	return t;
}

method setBlack(t : RBTree) returns (r : RBTree)
	requires almostWellFormed(t)
	ensures isWellFormed(r)
{
	if (t.Empty?) {
		return Empty;
	}
	return Node(Black, t.value,t.left,t.right);
}


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
// 	var right: Node?

//   predicate Valid()
//     reads this, Repr
//   {
//     this in Repr &&
//     // 1 <= |List| && List[0] == head &&
//     // (next == null ==> |List| == 1) &&
//     (next != null ==>
//       next in Repr && next.Repr <= Repr && this !in next.Repr &&
//       next.Valid() // && next.List == List[1..]
// 			)
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

