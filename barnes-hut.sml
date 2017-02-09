functor BarnesHut (A : BHArgs) : BARNESHUT =
struct

  structure Args = A

  (* helpful aliases to clean up the code below *)
  structure Seq = A.BB.Seq
  structure Plane = A.BB.Plane
  structure BB = A.BB
  structure Mech = A.Mech
  structure Scalar = A.BB.Plane.Scalar
  open A.Mech

  val ++ = Plane.++
  val ** = Plane.**
  val --> = Plane.-->
  val // = Plane.//

  infixr 3 ++
  infixr 4 **
  infixr 3 -->
  infixr 3 //

  (* this is the core idea of the barnes-hut algorithm *)
  (* a bhtree is a finitely branching tree of bodies that also
   * stores the center of mass and diameter of the bounding box
   * containing its children *)
  datatype bhtree =
      Null
    | Singleton of body
    | Box of (Plane.scalar * Plane.point) * Plane.scalar * (bhtree Seq.seq)
      (* ((mass, center), box diameter, sequence of length four
                                        representing each quadrant) *)

  exception Unimplemented

  (* scale_point : Scalar.scalar * Plane.point -> Plane.vec*)
  (* ENSURES: Scales the vector from the origin to p by the factor m. *)
  fun scale_point (m : Scalar.scalar, p : Plane.point) : Plane.vec =
      (Plane.origin --> p) ** m

  (* Task 4.1 *)
  (* barycenter : (Scalar.scalar * Plane.point) Seq.seq
                -> Scalar.scalar * Plane.point *)
  (* REQIRES: m >= 0 *)
  (* ENSURES: barycenter s computes the pair (m, c) where m is 
   * the total mass of the bodies in the sequence (i.e., the sum of 
  * the first components of the pairs) and c is the barycenter *)
  fun barycenter (s : (Scalar.scalar * Plane.point) Seq.seq) :
      Scalar.scalar * Plane.point = 
      let 
          val mSum = Seq.mapreduce (fn (a,b) => a) Scalar.zero Scalar.plus s
          val mrSum = Plane.sum scale_point  s
          val mr = Plane.head (mrSum // mSum)
      in 
        (mSum, mr)
      end


  (* Testing hint: use seqFromList and seqEq and boxEq
     to make at least one test case.
     You may find the boxes defined above to be helpful. *)

  (* Task 4.2 discused with Zihan Guo*)
  (* quadrantize : BB.box -> body Seq.seq -> body Seq.seq Seq.seq *)
  (* REQIRES: true*)
  (* ENSURES: quadrantize b s returns a sequence with 4 inner 
   * sequences of bodies. The sequence at index i should containing 
   * all the bodies in quadrant i, where the quadrants are numbered 
   * starting at 0 in the following order: top-left (nw) has number 0, 
   * top-right (ne) has number 1, bottom-left (sw) has number 2, 
   * and bottom- right (se) has number 3 *)
  fun quadrantize (b : BB.box) (s : body Seq.seq) : body Seq.seq Seq.seq =
    Seq.tabulate (fn i => (Seq.filter (fn (m,p,v) => (BB.quadrant b p) = i) s)) 4



  (* center_of_mass bhtree -> Scalar.scalar * Plane.point *)
  (* ENSURES
   * Projects the mass and center from the root node of a bhtree *)
  fun center_of_mass (T : bhtree) : Scalar.scalar * Plane.point =
      case T of
          Null => (Scalar.zero, Plane.origin)
        | Singleton (m, p, _) => (m, p)
        | Box (com, _, _) => com

  (* Task 4.3 *)
  (* compute tree : body Seq.seq -> bhtree *)
  (* REQUIRES: true *)
  (* ENSURES: compute tree s evaluates to T, 
   * where T is the tree decomposition of s *)
  fun compute_tree (s : body Seq.seq) : bhtree =
    case Seq.length s of
      0 => Null
    | 1 => Singleton (Seq.nth 0 s)
    | _ =>let 
            val positions = Seq.map (position) s
            val b = BB.hull positions
            val d = BB.diameter b

            val ss = quadrantize b s
            val sub = Seq.map compute_tree ss (*seq of bh tree*)
            val centermass = Seq.map center_of_mass sub (* m, p seq*)
            val mc = barycenter centermass
          in 
            Box(mc, d, sub)
          end
          

  (* Testing hint: write at least one test case by
     working out the answer for (compute_tree bseq bb4).
     *)

  (* Task 4.4 *)
  fun groupable (p1 : Plane.point) (p2 : Plane.point) (bd : Plane.scalar)
              (t : Scalar.scalar) : bool =
      let 
        
        val r = Plane.distance p1 p2
        val x = Scalar.divide (bd, r)
      in 
        Scalar.lte (x, t)
      end

  (* Task 3.5 *)
  fun bh_acceleration (T : bhtree) (t : Scalar.scalar) (b as (_, p, _))
      : Plane.vec =  
      case T of 
        Null => Plane.zero
      | Singleton (m, c, v) => accOnPoint (p, (m,c))
      | Box((m,c), bd, sub) => (case (groupable p c bd t) of
                                true => accOnPoint (p, (m, c))
                              | false => Plane.sum (fn i => bh_acceleration i t b) sub) 
    



  (*
     barnes_hut : Plane.scalar -> body Seq.seq -> Plane.vec Seq.seq

   * ENSURES
     Given a threshold and a sequence of bodies, compute the acceleration
     on each body using the Barnes-Hut algorithm.
   *)
  fun barnes_hut (threshold : Plane.scalar) (s : body Seq.seq)
      : Plane.vec Seq.seq =
      Seq.map (bh_acceleration (compute_tree s) threshold) s

  val accelerations : body Seq.seq -> Plane.vec Seq.seq =
      barnes_hut (Plane.Scalar.fromRatio (A.thresh))
end

structure RatTrans = Transcripts(BarnesHut(RatArgs))
structure RealTrans = Transcripts(BarnesHut(RealArgs))
