open Peg;; 
open PegRuntime;;
open Batteries;;
open Termlangcanon;;
open Termlangprolog;;
open Termlangext;;
open Termlangrefl;;

Termlangcanon.global_term_reset ();;
Termlangprolog.global_reset ();;
Repl.main ();;
