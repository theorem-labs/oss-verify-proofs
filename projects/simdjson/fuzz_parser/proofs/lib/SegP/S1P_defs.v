(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.simdjson.fuzz_parser.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition S1_ranges : list (Z * nat) := [(0x27d10, 1167%nat); (0x70224, 257%nat)].
Definition S1_IT : itab := APC.mk_itab_ranges SG S1_ranges.

Definition V (n : nat) : expr := EVar n.
Definition vRA := V 0. Definition vSP := V 1. Definition vTHIS := V 16. Definition vBUF := V 17. Definition vLEN := V 18.
Definition vA1 := V 19. Definition vNCAPB := V 20.
Definition add (a b : expr) : expr := EAlu ALU_ADD a b.
Definition sub (a b : expr) : expr := EAlu ALU_SUB a b.
Definition mul (k : Z) (a : expr) : expr := EMd M_MUL (ELit k) a.

(* [comment removed for export] *)
Definition idxlen : expr := add (mul 4 vLEN) (ELit 36).
(* [comment removed for export] *)
Definition kn_glob : list kentry :=
  [ KRange vLEN 0 1048512;
    KRange vSP 0x7fff00000000 0x800000000000;
    KAlign vSP 16;
    KRange vBUF 16 0x7fffff7fffff;
    KRange (add vBUF (add vLEN (ELit 64))) 16 0x7fffff800000;
    KRange vTHIS 16 0x7fffff7fffff;
    KAlign vTHIS 16;
    KRange (add vTHIS (ELit 96)) 16 0x7fffff800000;
    KRange vA1 16 0x7fffff7fffff;
    KAlign vA1 16;
    KRange (add vA1 idxlen) 16 0x7fffff800000;
    KDisj (SA (ELit 0) 0x10000) (ELit 0x99000) (SA vBUF 0) (add vLEN (ELit 64));
    KDisj (SA (ELit 0) 0x10000) (ELit 0x99000) (SA vTHIS 0) (ELit 96);
    KDisj (SA (ELit 0) 0x10000) (ELit 0x99000) (SA vA1 0) idxlen;
    KDisj (SA vSP (-416)) (ELit 416) (SA vBUF 0) (add vLEN (ELit 64));
    KDisj (SA vSP (-416)) (ELit 416) (SA vTHIS 0) (ELit 96);
    KDisj (SA vSP (-416)) (ELit 416) (SA vA1 0) idxlen;
    KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vTHIS 0) (ELit 96);
    KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
    KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
    KWr (SA vSP (-416)) (ELit 416);
    KWr (SA vTHIS 8) (ELit 4);
    KWr (SA vTHIS 24) (ELit 4);
    KWr (SA vTHIS 72) (ELit 16);
    KWr (SA vA1 0) idxlen;
    KUnk (SA vBUF 0) (add vLEN (ELit 64));
    KImg 0x10000 0x2572c ].

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 21; V 22; V 23; V 4; V 5; V 16; V 17; V 18; ELit 0; V 24; V 25; V 26; V 27;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 28; V 29; V 30; V 31].
Definition T0 : ST.tmpl := ST.TM 0x27d10 T0_regs (KWord (SA vTHIS 16) 8 vA1 :: kn_glob) 32%nat (ELit 2097152) 100%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ovr (l : list expr) (o : list (nat * expr)) : list expr := fold_left (fun acc p => ST.set_nth acc (fst p) (snd p)) o l.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition kn_frame : list kentry :=
  [ KWord (SA vSP (-8)) 8 (V 0); KWord (SA vSP (-16)) 8 (V 4); KWord (SA vSP (-24)) 8 (V 5); KWord (SA vSP (-32)) 8 (V 6);
    KWord (SA vSP (-40)) 8 (V 7); KWord (SA vSP (-48)) 8 (V 8); KWord (SA vSP (-56)) 8 (V 9); KWord (SA vSP (-64)) 8 (V 10);
    KWord (SA vSP (-72)) 8 (V 11); KWord (SA vSP (-80)) 8 (V 12); KWord (SA vSP (-88)) 8 (V 13); KWord (SA vSP (-96)) 8 (V 14);
    KWord (SA vSP (-104)) 8 (V 15);
    KWord (SA vSP (-144)) 8 vBUF; KWord (SA vSP (-128)) 8 vTHIS; KWord (SA vSP (-120)) 4 vLEN;
    KWord (SA vSP (-112)) 4 (ELit 0); KWord (SA vSP (-108)) 4 (ELit 0);
    KUnk (SA vSP (-400)) (ELit 256);
    KWord (SA vTHIS 72) 8 vBUF; KWord (SA vTHIS 80) 8 vLEN; KWord (SA vTHIS 16) 8 vA1 ].

(* [comment removed for export] *)
Definition R_loop : list expr :=
  [ELit 0; V 25; spo (-416); V 2; V 3; ELit 92; ELit 32; V 26; V 16; V 17; V 18; V 19; V 23;
   add vLEN (ELit (-1)); add vLEN (ELit (-2)); ELit 0; add vA1 (V 22); ELit 34; ELit 0; V 18; spo (-400); ELit 160;
   ELit 18446744073709551552; ELit 244; ELit 240; ELit 30; V 21; V 31; V 27; V 28; V 29; V 30].
Definition vJ := V 21. Definition vD := V 22.
(* [comment removed for export] *)
Definition kn_loop (vj vd : expr) : list kentry :=
  [ KRange vj 0 1048512; KRange (sub vLEN vj) 1 1048512;
    KRange vd 0 4194048; KRange (sub (mul 4 vj) vd) 0 4194048; KRange (sub (mul 4 vLEN) vd) 4 4194048 ].
Definition TO : ST.tmpl := ST.TM 0x27dd0 R_loop (kn_loop vJ vD ++ kn_frame ++ kn_glob) 32%nat (sub vLEN vJ) 2%nat.

(* [comment removed for export] *)
Definition R_exit : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 22; V 23; V 24; V 4; V 5; V 21; V 25; V 26; V 27; V 28; V 29; V 30; V 31;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 32; V 33; V 34; V 35].
Definition TX : ST.tmpl := ST.TM 0x28f30 R_exit ([KWord (SA vTHIS 72) 8 vBUF; KWord (SA vTHIS 80) 8 vLEN] ++ kn_glob) 36%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition R_ws : list expr := ovr R_loop [(7%nat, add vJ (ELit 2)); (28%nat, vLEN)].
Definition TW : ST.tmpl := ST.TM 0x27de4 R_ws (kn_loop vJ vD ++ kn_frame ++ kn_glob) 32%nat (sub vLEN vJ) 1%nat.

(* [comment removed for export] *)
Definition kn_cur (vk : expr) (g s : Z) : list kentry :=
  [ KRange vk 0 1048512; KRange (sub vLEN vk) g 1048512;
    KRange vD 0 4194048; KRange (sub (mul 4 vk) vD) (4 * s) 4194048; KRange (sub (mul 4 vLEN) vD) 4 4194048 ].

(* [comment removed for export] *)
Definition R_str : list expr := ovr R_loop [(28%nat, vJ); (26%nat, V 27); (27%nat, ELit 1)].
Definition TS : ST.tmpl := ST.TM 0x27e30 R_str (kn_cur vJ 1 1 ++ kn_frame ++ kn_glob) 32%nat (sub vLEN vJ) 1%nat.

(* [comment removed for export] *)
Definition R_sin : list expr := ovr R_loop [(12%nat, vLEN); (1%nat, V 23); (27%nat, ELit 1)].
Definition TSI : ST.tmpl := ST.TM 0x27e48 R_sin (kn_cur vJ 1 1 ++ kn_frame ++ kn_glob) 32%nat (sub vLEN vJ) 0%nat.

(* [comment removed for export] *)
Definition R_prim : list expr := ovr R_loop [(7%nat, add (add vBUF vJ) (ELit 2))].
Definition TP : ST.tmpl := ST.TM 0x28094 R_prim
  ([KRange (add vLEN (ELit (-2))) 0 1048510; KRange (sub (add vLEN (ELit (-2))) vJ) 0 1048510] ++ kn_cur vJ 2 0 ++ kn_frame ++ kn_glob)
  32%nat (sub vLEN vJ) 0%nat.
