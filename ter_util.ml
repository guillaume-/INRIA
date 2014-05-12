let uc = Array.init 26 (fun i -> Char.chr (i+ (Char.code 'A')))
and lc = Array.init 26 (fun i -> Char.chr (i+ (Char.code 'a')))
and nums = Array.init 10 (fun i -> Char.chr (i + (Char.code '0')))
let chars = Array.concat [uc; lc; nums];;

let newStr () = Random.self_init();
	let s = String.make 5 ' '
	in for i=0 to 4 do 
		s.[i] <- chars.(Random.int (Array.length chars))
	done;
	s;;
