signature ARRAY = sig
    type 'a array

    (* init_array: int -> 'a -> 'a array
     * requires: len >= 0
     * ensures:  if arr == init_array len init, and i < len, arr i
     *           is a ref cell initially set to init, but whose
     *           state is persistent across calls to arr i  *)
    val init_array : int -> 'a -> 'a array

    (* ENSURES: get a i == SOME <ith elem of a> if possible, else NONE *)
    val get        : 'a array -> int -> 'a ref option

    (* ENSURES: foldl f b a combines all elements of a using f, with b as base case *)
    val foldl      :  ('a ref * 'b -> 'b) -> 'b -> 'a array -> 'b

    (* double_len: 'a array -> 'a -> 'a array
     * requires: len >= 0, for all i. 0 <= i < len, arr i is a value
     * ensures:  if arr2 == double_len arr len init, arr2 is array of length
     *           2*len with inital values init, and the first half of arr2 is
     *           the same as arr.
     *)
    val double_len : 'a array -> 'a -> 'a array

    (* REQUIRES: a is not empty
     * ENSURES: expand a x new_len has length new_len. first len(a) elements are
     * same as those in a. if new elements are added, all of them are x *)
    val expand     : 'a array -> int -> 'a -> 'a array

    (* FOR YOUR DEBUGGING CONVENIENCE: prints all the stuff in an array *)
    val print_arr  : ('a -> string) -> 'a array -> unit
end


structure Array : ARRAY =
  struct
    datatype 'a array = A of int * (int -> 'a ref)
    exception OutOfBounds

    (* init_array: int -> 'a -> 'a array *)
    fun init_array len init = 
      case len of
        0 => A(0, fn _ => raise OutOfBounds)
      | 1 => A(1, let 
                    val v = ref init
                  in 
                     fn 0 => v
                   | _ => raise OutOfBounds
                  end)
      | _ => A(len, let
                      val i = len div 2
                      val A(n1, f1) = init_array i init
                      val A(n2, f2) = init_array (len - i) init
                    in 
                      fn y => (case (y < i, y < len) of
                        (true,_) => f1 y
                      | (_, true) => f2 (y - i)
                      | (_, _) => raise OutOfBounds
                      )
                    end
              )

    


    (* get : 'a array -> int -> 'a ref option *)
    fun  get a i =
      let 
        val A(len, f) = a
      in 
        (case (len > i, i >= 0) of
          (true, true) => SOME (f i)
        | (_, _) => NONE 
        )
      end


    (* foldl :  ('a ref * 'b -> 'b) -> 'b -> 'a array -> 'b *)
    fun foldl f b a = 
      let 
        val A(n, fa) = a
      in
       (case n of
          0 => b
        | _ => foldl f (f(fa (n-1), b)) (A(n - 1, fa))
       )
      end

    (* double_len: 'a array -> int -> 'a -> 'a array *)
    fun double_len arr  init = 
      let 
        val A(n, f) = arr
        val A(n2, f2) = init_array n init
      in 
        A(2 * n, fn x => case (x < n) of
                             true => f x
                           | false => f2 (x - n)
         )
      end

    (*  expand     : 'a array -> int -> 'a -> 'a array *)
    fun expand a i x = 
      let 
        val A(n, f) = a
      in
        (case i <= n of
          true => A(i, f)
        | false => A(i, fn k => (case (k < n) of
                                  true => f k
                                | false => let 
                                             val A(n2, f2) = init_array (i - n) x
                                            in 
                                              f2 (k - n)
                                            end)
                    )
        )
      end
   (* print_arr  : ('a -> string) -> 'a array -> unit *)
   fun print_arr toString (A(n,f)) =
       case n of
	   0 => ()
	 | _ =>(print (toString (!(f 0))); print_arr toString(A(n-1,fn i => f(i+1))))

   end


signature FIB =
  sig
    (* memo_fib: unit -> int ->  int
     * requires: n >= 0
     * ensures:  memo_fib () 0 == 0, memo_fib () 1 == 1,
     *           memo_fib () n == memo_fib () (n -1) + memo_fib () (n - 2)
     *    Less than exponential time
     *)
    val memo_fib: unit -> (int -> IntInf.int)
  end

structure Fib :> FIB =
  struct
    (* memo_fib: unit -> int -> IntInf.int *)
    fun memo_fib () = 
      let 
        val a = ref (Array.init_array 2 0)
        val SOME v1 = Array.get (!a) 1
        val () = v1 := 1 
        val size = ref 2
        fun lookup (i : int) : IntInf.int = 
          case i >= (!size) of
            true => let 
                      val result = lookup (i - 1) + lookup(i - 2)
                      val () = (case i >= (!size) of 
                                  true => let
                                            val () = a := (Array.double_len (!a) ~1)
                                            val () = size := 2 * (!size)
                                          in
                                            ()
                                          end
                                | false => ()
                               )
                      val SOME vi = Array.get (!a) i
                      val () = vi := result
                    in 
                      result
                    end
          | false => let 
                       val SOME vi = Array.get (!a) i
                     in 
                      (case (!vi) of 
                        ~1 => let
                                val result = lookup (i - 1) + lookup(i - 2)
                                val () = vi := result
                              in
                                result
                              end
                      | _ => (!vi)
                      )
                     end
      in 
        lookup
      end


  end




signature FINDS = 
  sig
    (* ENSURES: findr p A == SOME r iff exists r in A where p r == true, else NONE *)
    val findr     : ('a ref -> bool) -> 'a Array.array -> 'a ref option
    (* ENSURES: findr p A == SOME v iff exists r in A where p r == true, r = ref v, else NONE *)
    val findv     : ('a -> bool)     -> 'a Array.array -> 'a ref option
    (* ENSURES: If exists r in A, r = ref v, p v == true, then findv_imp p A out puts r in out and
     * returns true, else returns false *)
    val findv_imp : ('a -> bool)     -> 'a Array.array -> 'a ref ref -> bool
    (* ENSURES containsr x A == true iff x is in A, else false *)
    val containsr : 'a ref           -> 'a Array.array -> bool
  end

structure Finds : FINDS =
struct
(* findr     : ('a ref -> bool) -> 'a Array.array -> 'a ref option *)
  fun findr p a = 
    let 
      
      fun comp i = 
        let
          val r = Array.get a i
        in
          (case r of
            NONE => NONE
          | SOME(r') => (case p r' of
                           true => r
                         | false => comp (i + 1))
          )
        end
    in 
      comp 0
    end

  (* findv     : ('a -> bool)     -> 'a Array.array -> 'a ref option *)
  fun findv p a = 
    let 
      fun comp i = 
        let
          val r = Array.get a i
        in
          (case r of
            NONE => NONE
          | SOME(r') => (case p (!r') of
                           true => r
                         | false => comp (i + 1))
          )
        end
    in 
      comp 0
  end

  (* findv_imp : ('a -> bool)     -> 'a Array.array -> 'a ref ref -> bool *)
  fun findv_imp p a out = 
    let 
      fun comp i = 
        let
          val r = Array.get a i
        in
          (case r of
            NONE => false
          | SOME(r') => (case p (!r') of
                           true => let 
                                     val () = out := r'
                                   in 
                                     true
                                   end 
                         | false => comp (i + 1))
          )
        end
    in 
      comp 0
  end
    


  (* containsr : 'a ref -> 'a Array.array -> bool *)
  fun containsr r a = 
    let 
      fun comp i = 
        let
          val r1 = Array.get a i
        in
          (case r1 of
            NONE => false
          | SOME(r1') => (case (r = r1') of
                           true => true
                         | false => comp (i + 1))
          )
        end
    in 
      comp 0
  end


end

structure Test = 
struct
  open Array
  open Fib
  open Finds

  (* TEST *)
  (* tests for init *)
  val a = init_array 3 0 
  val SOME (ref 0) = get a 0
  val SOME (ref 0) = get a 1
  val SOME (ref 0) = get a 2
  val NONE = get a 3

  (* tests for get *)
  val SOME a1 = get (init_array 3 0) 1
  val 0 = !a1
  val NONE = get (init_array 3 0) 3
  val NONE = get (init_array 3 0) ~1

  (* tests for double_len *)
  val a1 = double_len (init_array 3 0) 1
  val SOME (ref 1) = get a1 5


  (* tests for foldl *)
  val 3 = foldl (fn (a, y) => !a + y) 0 (init_array 3 1)

  (* test for expand *)
  val a3= expand (init_array 3 0) 2 1
  val SOME(ref 0) = get a3 0
  val SOME(ref 0) = get a3 1
  val a4 = expand (init_array 3 0) 4 1
  val SOME(ref 0) = get a4 0
  val SOME(ref 0) = get a4 1
  val SOME(ref 0) = get a4 2
  val SOME(ref 1) = get a4 03

  (* tests for memo_fib *)
  val f0 : IntInf.int = memo_fib () 0
  val f1 : IntInf.int = memo_fib () 1
  val f7 : IntInf.int = memo_fib () 7
  val f50 : IntInf.int = memo_fib () 50
  val 0 = f0
  val 1 = f1
  val 13 = f7
  val 12586269025 = f50

  (* tests for findr *)
  val SOME r = findr (fn x => !x > 0) (Array.init_array 3 1)
  val 1 = !r
  val NONE = findr (fn x => !x > 1) (Array.init_array 3 1)

  (* tests for find v*)
  val SOME r1 = findv (fn x => x > 0) (Array.init_array 3 1)
  val 1 = !r1
  val NONE = findv (fn x => x > 1) (Array.init_array 3 1)

  (* tests for findv_imp *)
  val true = findv_imp (fn x => x > 0) (Array.init_array 3 1) (ref(ref 3))
  val false = findv_imp (fn x => x < 0) (Array.init_array 3 1) (ref(ref 3))

  (* tests for containsr *)
  val a1 = Array.init_array 2 0
  val SOME v0 = Array.get a1 0
  val true = containsr v0 a1
  val false = containsr (ref 0) a1



end




















