open Main
open Type

open OUnit

let test_parsing = "Parsing" >:::
                   [
                     "a" >:: (fun () ->
                         assert_equal 1 (1+0);
                         assert_equal 2 2
                       );

                     "b" >:: (fun () -> ()
                       )
                   ]

let _ = run_test_tt test_parsing
