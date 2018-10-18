module type Queue =
sig
    exception EMPTY_Q
    type element
    type queue
    val mptyQ: queue
    val enQ: queue * element -> queue
    val deQ: queue -> element * queue
end

module IntListQ =
struct
    exception EMPTY_Q
    type element = int list
    type queue = element list * element list
    let emptyQ = ([],[])
    let enQ ((q:queue), (e:element)) : queue =
        match q with
        |(x,y) -> ((e::x), y)

    let rec deQ (q:queue) : element * queue =
        match q with
        |(x,y) ->
                (match y with
                |(head::tail) -> (head, (x,tail))
                |[] ->
                        (match x with
                        |[] -> raise EMPTY_Q
                        |a -> ((List.hd (List.rev a)), ([],  (List.tl (List.rev a))))
                        )
                )
end
