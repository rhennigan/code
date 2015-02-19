'use strict';

var curry = function (fn) {
  var args = Array.prototype.slice.call(arguments, 1);
  return function () {
    return fn.apply(this, args.concat(
      Array.prototype.slice.call(arguments, 0)));
  };
};

function List (x, xs) {
  this.head = x  || null;
  this.tail = xs || null;
}

function Tuple (left, right) {
		this.left = left || null;
		this.right = right || null;
}

List.cons = function (x) { return function (xs) { return new List(x, xs); }; };

List.prototype.isEmpty = function () {
  return this.head === null && this.tail === null;
};

List.join = function (xs) {
  return function (ys) {
    return xs.isEmpty() ? ys :
      List.cons (xs.head) (List.join (xs.tail) (ys));
  };
};

List.reverse = function (list) {
  return list.isEmpty() ? new List() :
    List.join (List.reverse (list.tail)) (List.cons (list.head) (new List ()));
};

List.map = function (f) {
  return function (list) {
    return list.isEmpty() ? new List () :
      List.cons (f (list.head)) (List.map (f) (list.tail));
  };
};

List.N = function (num) {
  var revN = function (n) { 
    return n <= 0 ? new List () :
      List.cons (n) (revN (n-1));
  };
  return List.reverse (revN (num));
};

List.iter = function (f) {
  return function (list) {
    if (!list.isEmpty()) {
      f (list.head);
      List.iter (f) (list.tail);
    }
  };
};

List.foldl = function (f) {
  return function (acc) {
    return function (list) {
      return list.isEmpty() ? acc : 
        List.foldl (f) (f (acc) (list.head)) (list.tail);
    };
  };
};

List.foldr = function (f) {
  return function (acc) {
    return function (list) {
      return list.isEmpty() ? acc : 
        f (list.head) (List.foldr (f) (acc) (list.tail));
    };
  };
};

List.fold = List.foldr;

List.count = function (list) {
  return list.isEmpty() ? 0 :
    List.count (list.tail) + 1;
};

List.total = function (list) {
  var plus = function (a) { return function (b) { return a + b; }; };
  return List.fold (plus) (0) (list); 
};

List.take = function (n) {
		return function (list) {
				return list.isEmpty() || n <= 0 ? new List() :
						List.cons (list.head) (List.take (n-1) (list.tail));
		};
};

List.tuples = function (n) {
		return function (list) {
				
		};
};
