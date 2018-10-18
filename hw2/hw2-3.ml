type rank = int
type value = int
type heap = EMPTY | NODE of rank * value * heap * heap
exception EmptyHeap

let rec rank (h: heap) : int =
    match h with
    |EMPTY -> -1
    |NODE(r,_,_,_) -> r

and insert ((x:int),(h:heap)) : heap =
    merge(h, NODE(0,x,EMPTY,EMPTY))

and findMin (h:heap) : int =
    match h with
    |EMPTY -> raise EmptyHeap
    |NODE(_,x,_,_) -> x

and deleteMin (h:heap) : heap =
    match h with
    |EMPTY -> raise EmptyHeap
    |NODE(_,x,lh,rh) -> merge(lh,rh)

and shake ((x:int),(lh:heap),(rh:heap)) : heap =
   if (rank lh) >= (rank rh) then NODE((rank rh) + 1, x, lh, rh) else NODE((rank lh) + 1, x, rh, lh)

and merge3 (hl:heap list) : heap =
    match hl with
    |(head::(head2::tail)) ->
        if tail = [] then
        (match head2 with
        |NODE(r,x,l,_) -> shake(x, l, head)
        |EMPTY -> raise EmptyHeap
        )
        else
        (match head2 with
        |NODE(r,x,l,_) -> merge3 ([shake(x, l, head)]@tail)
        |EMPTY -> raise EmptyHeap
        )
    |_ -> raise EmptyHeap

and merge2 ((h1:heap),(h2:heap),(hl:heap list)) : heap =
    if h1 = EMPTY then merge3 (h2::hl)
    else if h2 = EMPTY then merge3 (h1::hl)
    else if findMin h1 > findMin h2 then
        (match h2 with
        |EMPTY -> raise EmptyHeap
        |NODE(_,_,_,rh) -> merge2 (h1, rh, (h2::hl))
        )
    else
        (match h1 with
        |EMPTY -> raise EmptyHeap
        |NODE(_,_,_,rh) -> merge2 (h2, rh, (h1::hl))
        )

and merge ((h1:heap),(h2:heap)) : heap =
	if h1 = EMPTY && h2 = EMPTY then EMPTY
	else if h1 = EMPTY then h2
	else if h2 = EMPTY then h1
	else merge2 (h1,h2,[])

let _ = merge(NODE (1, 1, NODE (0, 5, EMPTY, EMPTY), NODE (0, 3, EMPTY, EMPTY)), NODE (0, 2, NODE (0, 4, EMPTY, EMPTY), EMPTY))