(* By Daniel Gratzer *)

signature LOGIC =
sig
    (* The core type of this library, a potentially infinite stream of
     * values of type 'a. This is left abstract so the only way to
     * construct one of these is with the helpful functions below.
     *)
    type 'a t

    (* map f t applies a function f to every element in t.
     * Note that since [t] may contain elements which haven't
     * been evaluated, there is no guarantee when or if [f] will
     * be run on all the elements of the list. EG,
     *
     *    map print (delay (fn () => return "Hello World"))
     *
     * Needn't print anything, but would if we ever used [observe]
     * or friends.
     *)
    val map : ('a -> 'b) -> 'a t -> 'b t

    (* The empty sequence containing no elements *)
    val empty    : 'a t

    (* Combine two sequences. The nice part of this function is that
     * any element which has a finite index in either sequence will have
     * a finite element in the output stream.
     *)
    val merge : 'a t -> 'a t -> 'a t

    (* Convert a list to a stream so that [toList o fromList]
     * is id
     *)
    val fromList : 'a list -> 'a t

    (* When tying knots in ML, it's necessary to introduce a lambda in
     * order to do so. This function facilitates that. EG
     *
     *    val fives = merge (return 5) fives
     *
     * will diverge but
     *
     *    fun fives () = merge (return 5) (delay fives)
     *    val fives = fives ()
     *
     * Will work as expected.
     *)
    val delay : (unit -> 'a t) -> 'a t

    (* Fair-sharing version of >>=. This behaves a lot like
     * mapping a function over a stream and then @-ing the results.
     *
     * However, it does this in such a way that if any component is finitely
     * reachable in any of the resulting ['b t]'s, it has a finite index
     * in the output.
     *
     * However, since merging doesn't preserve order, it isn't the case that
     * >>- follows the monad laws. If you're viewing 'a t as a nondeterministic
     * computation anyways, then this is fine. Otherwise, you can use >>=
     * proper.
     *)
    val >>- : 'a t * ('a -> 'b t) -> 'b t

    (* This will follow the monad laws together with [return]. It behaves
     * exactly like mapping a function over a stream and then appending the
     * results.
     *
     * However unlike >>- it's not guarenteed that all finitely reachable
     * elements in results of the function supplied will have a finite index
     * in the final stream.
     *)
    val >>= : 'a t * ('a -> 'b t) -> 'b t

    val shortcircuit : 'a t * ('a -> bool) * ('a -> 'b t) -> 'b t

    (* Creates a stream with a single element in it. *)
    val return : 'a -> 'a t

    (* The canonical unfolding operator streams should give rise to.
     * The idea is that you supply a seed and an unfolding operation.
     * unfold will create a stream by applying the seed to the supplied
     * function.
     *
     *   - If NONE is returned it returns empty and halts
     *   - If SOME (a, b') is returned, it returns a stream with
     *     a at the head whose tail lazily computes [unfold f b']
     *
     * This can be used to create potentially infinite streams quite
     * easily.
     *)
    val unfold   : ('b -> ('a * 'b) option) -> 'b -> 'a t

    (* A nice convience for treating streams as nondeterministic computations.
     * [ifte i t e] behaves thusly
     *
     * If [i] contains at least one element (succeeds at all) then we will
     * return [i >>- t], otherwise, we will return e. This means that the
     * results of t and e will *never* show up in the results together.
     *)
    val ifte : 'a t -> ('a -> 'b t) -> 'b t -> 'b t

    (* This truncates a stream so that it only contains one element.
     * This is useful it is being handled as a nondeterministic computation
     * and we're only interested in using one of its results.
     *)
    val once : 'a t -> 'a t

    (* This behaves like a safe version of hd and tl for streams. It will
     * return the first element of a stream and the tail of it *if* the stream
     * is non-empty. Otherwise, it will just return NONE
     *
     * This should always terminate for stream values unless one has improperly
     * used [delay] and created a stream which is just an infinite stack of
     * [delay]s. For example [fun bad () = delay bad]
     *)
    val uncons  : 'a t -> ('a * 'a t) option

    (* This has similar properties to uncons but just returns a finite prefix
     * of a stream, raising Empty if there aren't enough elements
     *)
    exception Empty
    val observe : int -> 'a t -> 'a list

    (* [toList s] will terminate with a list containing the elements of s
     * if s is finite, otherwise it will loop forever
     *)
    val toList : 'a t -> 'a list
end