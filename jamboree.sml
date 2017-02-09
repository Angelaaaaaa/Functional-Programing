functor Jamboree (Settings : sig
                                 structure G : ESTGAME
                                 val search_depth : int
                                 val prune_percentage : real
                             end) : PLAYER =
struct

    exception NYI

    structure Game = Settings.G

    (* abbreviate Game as G, to keep the notation simple below. *)
    structure G = Game

    type edge  = G.move * G.est

    (* Implicit ordering:   NEGINF < Bound(v) < POSINF for all v *)
    datatype bound = NEGINF | Bound of G.est | POSINF
    type alphabeta = bound * bound    (* invariant: alpha < beta *)

    datatype orderAB = BELOW | INTERIOR | ABOVE

    (* the following ToString functions my be helpful in testing *)
    fun valueToString v = "Value(" ^ G.Est.toString v ^ ")"

    fun edgeToString (m, v) = "Edge(" ^ G.move_to_string m ^ ", " ^ G.Est.toString v ^ ")"

    fun boundToString NEGINF = "NEGINF"
      | boundToString POSINF = "POSINF"
      | boundToString (Bound v) = "Bound(" ^ G.Est.toString v ^ ")"

    fun abToString (a,b) = "(" ^ boundToString a ^ "," ^ boundToString b ^ ")"

    (* lesseq : G.est * G.est -> bool *)
    fun lesseq(x, y) = (x = y) orelse
                       case (x, y) of
                         (G.Est.MinnieWins, _) => true
                       | (_, G.Est.MaxieWins) => true
                       | (G.Est.Guess n, G.Est.Guess m) => (n <= m)
                       | (_, _) => false

    (* compareAB : alphabeta -> G.est -> orderAB    *)
    (* compareAB (a,b) v  ==>                       *)
    (*                 BELOW      if  v <= a        *)
    (*                 INTERIOR   if  a < v < b     *)
    (*                 ABOVE      if  v >= b        *)

    (*  COPY this function from your alpha-beta implementation. *)
    fun compareAB (a,b) v = 
      case (a, b) of 
        (NEGINF, POSINF) => INTERIOR
      | (NEGINF, Bound y) => (case G.Est.compare (v, y) of
                               LESS => INTERIOR
                             | _ => ABOVE)
      | (Bound x, POSINF) => (case G.Est.compare (x, v) of
                               LESS => INTERIOR
                             | _ => BELOW)
      | (Bound x, Bound y) => (case (G.Est.compare (x, v), 
                                     G.Est.compare (v, y)) of
                               (LESS, LESS) => INTERIOR
                             | (LESS, _) => ABOVE
                             | (_, LESS) => BELOW
                             | (_, _) => raise NYI)

      | (_, _) => raise NYI


    (* maxEdge : edge option -> edge -> edge option                       *)
    (* REQUIRES: true                                                     *)
    (* ENSURES:  maxEdge e1op e2 returns SOME of the edge with max value. *)
    fun maxEdge NONE e = SOME(e)
      | maxEdge (SOME(m1,v1)) (m2,v2) = SOME(if lesseq(v2,v1) then (m1,v1) else (m2,v2))

    (* minEdge : edge option -> edge -> edge option                       *)
    (* REQUIRES: true                                                     *)
    (* ENSURES:  minEdge e1op e2 returns SOME of the edge with min value. *)
    fun minEdge NONE e = SOME(e)
      | minEdge (SOME(m1,v1)) (m2,v2) = SOME(if lesseq(v1,v2) then (m1,v1) else (m2,v2))

    (* bestMaxEdge : edge option -> edge option Seq.seq -> edge option       *)
    (* REQUIRES: true                                                        *)
    (* ENSURES: (bestMaxEdge eop s) returns SOME(edge) for edge with maximum *)
    (*          value in the sequence s@<eop> or NONE if no edge present.    *)
    (*                                                                       *)
    fun bestMaxEdge eop =
        let
           fun maxFn (NONE,opt) = opt
             | maxFn (opt,NONE) = opt
             | maxFn (SOME(m1,v1), SOME(m2,v2)) =
                if lesseq(v1,v2) then SOME(m2,v2) else SOME(m1,v1)
        in
           Seq.reduce maxFn eop
        end

    (* bestMinEdge : edge option -> edge option Seq.seq -> edge option       *)
    (* REQUIRES: true                                                        *)
    (* ENSURES: (bestMinEdge eop s) returns SOME(edge) for edge with minimum *)
    (*          value in the sequence s@<eop> or NONE if no edge present.    *)
    fun bestMinEdge eop =
        let
           fun minFn (NONE,opt) = opt
             | minFn (opt,NONE) = opt
             | minFn (SOME(m1,v1), SOME(m2,v2)) =
                if lesseq(v2,v1) then SOME(m2,v2) else SOME(m1,v1)
        in
           Seq.reduce minFn eop
        end


    (* splitMoves : G.state -> G.move Seq.seq * G.move Seq.seq
     * REQUIRES : true
     * ENSURES  : splits a sequence of moves according to the prune_percentage
     *            that should be abmoves and those that should be mmmoves   *)
    fun splitMoves s = 
      let
        val moves = G.moves s 
        val n = Seq.length moves
        val ab = (Real.floor (Settings.prune_percentage * (real n)))
      in
        Seq.split ab moves
      end



    (* search : int -> alphabeta -> G.state -> edge option                   *)
    (* REQUIRES: d > 0, (G.moves s) is nonempty.                             *)
    (* ENSURES:  search d ab s ==> SOME(optimal outgoing edge from s),       *)
    (*           based on depth-d Jamboree,                                  *)
    (*           starting with alpha-beta interval "ab".                     *)
    (*           The percentage of moves searched with alpha-beta pruning    *)
    (*           is specified in Settings.                                   *)
    fun search d ab s = 
      let 
        val (abmoves, mmmoves) = splitMoves s
      in 
        (case (G.player s) of
          G.Maxie => maxisearch d ab s abmoves mmmoves NONE
        | G.Minnie => minisearch d ab s abmoves mmmoves NONE)
      end


    (* maxisearch : int -> alphabeta -> G.state -> G.move Seq.seq -> G.move Seq.seq -> edge option -> edge option *)
    (* REQUIRES: d > 0;                                                      *)
    (*           all moves should contain only moves that are legal at s;    *)
    (*           "s" is a Maxie state;                                       *)
    (*           "best" should not be NONE when there are no moves left.     *)
    (* ENSURES:  maxisearch d ab s abmoves mmmoves best                      *)
    (*                              ==> SOME(optimal outgoing edge from s),  *)
    (*                based on depth-d search,                               *)
    (*                first using alpha-beta pruning over "abmoves",         *)
    (*                then using minimax over "mmoves".                      *)
    (*                "ab" and "best" are accumulator arguments for the      *)
    (*                current alpha-beta interval and current best edge.     *)
    and maxisearch d (ab as (a, b)) s abmoves mmmoves best = 
      case (Seq.showl abmoves, Seq.showl abmoves) of
        (Seq.Nil, _) =>  let
                           val edges = Seq.map 
                             (fn i => SOME (i, evaluate (d - 1) ab 
                                             (G.make_move (s,i)))) mmmoves
                         in
                           bestMaxEdge best edges
                         end

      | (Seq.Cons(x, xs),_) => let 
                                 val new_s = G.make_move (s, x)
                                 val v = evaluate (d - 1) ab new_s
                                 val edge = maxEdge best (x, v)
                               in 
                                 case (compareAB (a, b) v) of
                                    BELOW => maxisearch d (a, b)
                                                       s xs mmmoves edge
                                 |  INTERIOR => maxisearch d (Bound v, b)
                                                       s xs mmmoves edge
                                 |  ABOVE => edge
                               end
    

    (* minisearch : int -> alphabeta -> G.state -> G.move Seq.seq -> G.move Seq.seq -> edge option -> edge option *)
    (* REQUIRES: d > 0;                                                      *)
    (*           all moves should contain only moves that are legal at s;    *)
    (*           "s" is a Minnie state;                                      *)
    (*           "best" should not be NONE when there are no moves left.     *)
    (* ENSURES:  minisearch d ab s abmoves mmmoves best                      *)
    (*                              ==> SOME(optimal outgoing edge from s),  *)
    (*                based on depth-d search,                               *)
    (*                first using alpha-beta pruning over "abmoves",         *)
    (*                then using minimax over "mmoves".                      *)
    (*                "ab" and "best" are accumulator arguments for the      *)
    (*                current alpha-beta interval and current best edge.     *)
    and minisearch d (ab as (a, b)) s abmoves mmmoves best = 
      case (Seq.showl abmoves, Seq.showl abmoves) of
        (Seq.Nil, _) => let
                          val edges = Seq.map 
                             (fn i => SOME (i, evaluate (d - 1) ab 
                                          (G.make_move (s,i)))) mmmoves
                       in
                         bestMinEdge best edges
                       end

      | (Seq.Cons(x, xs),_) => let 
                                 val new_s = G.make_move (s, x)
                                 val v = evaluate (d - 1) ab new_s
                                 val edge = minEdge best (x, v)
                               in 
                                 case (compareAB (a, b) v) of
                                    BELOW => edge
                                 |  INTERIOR => minisearch d (a, Bound v) 
                                                             s xs mmmoves edge
                                 |  ABOVE => minisearch d (a, b) 
                                                             s xs mmmoves edge
                               end
    

    (* evaluate : int -> alphabeta -> G.state -> G.est                     *)
    (* REQUIRES: d >= 0                                                    *)
    (* ENSURES:  evaluate d ab s ==> value attributed to state s, based on *)
    (*                               depth-d Jamboree search.              *)
    and evaluate d ab s = 
      case (G.status s) of 
        G.Over(G.Winner G.Maxie) => G.Est.MaxieWins
      | G.Over(G.Winner G.Minnie) => G.Est.MinnieWins
      | _ => (case d of
               0 => G.estimate s
             | _ => let 
                       val SOME(m, v) = search d ab s
                    in 
                       v
                    end)

    (* recall:  the signature requires that s be In_play. *)
    (* next_move : status -> move *)
    (* REQUIRES: the status is In_play *)
    (* ENSURES: next_move s evaluates to the next move 
     * the current player should take*)
    fun next_move s = 
      let 
        val SOME (m, v) = search Settings.search_depth (NEGINF, POSINF) s
      in 
        m
      end



end (* Jamboree *)
















