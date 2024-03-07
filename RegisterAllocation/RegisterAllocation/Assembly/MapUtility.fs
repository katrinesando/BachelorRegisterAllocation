module MapUtility

let rec lookupInMap depth (name : string) m =
    if depth >= 0 then
        match Map.tryFind depth m with
        | None -> lookupInMap (depth-1) name m
        | Some vars ->
                let rec aux rest  = 
                    match rest with
                    |[] ->  lookupInMap (depth-1) name m 
                    |(n:string)::xs -> if n.StartsWith(name) then n else aux xs
                aux vars
    else
        failwith ("variable " + name + " not declared")
   
let addToMap depth name m =
    match Map.tryFind depth m with
    |None -> Map.add depth [name] m
    |Some vars ->
        let newlst = name::vars
        Map.add depth newlst m