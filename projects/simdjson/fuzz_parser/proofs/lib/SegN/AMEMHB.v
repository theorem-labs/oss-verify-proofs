(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import ST.
Open Scope Z_scope.

Module AMHB.
Definition V (n : nat) : expr := EVar n.
Definition add (a b : expr) : expr := EAlu ALU_ADD a b.
Definition sub (a b : expr) : expr := EAlu ALU_SUB a b.
Definition mul (k : Z) (a : expr) : expr := EMd M_MUL (ELit k) a.
Definition SH : Z := 2147450880.
Definition vSP := V 1.
(* [comment removed for export] *)
Definition IMGW : SP.win := (ELit 0, 0x10000, ELit 0x661000).
(* [comment removed for export] *)
Definition opnd (p8 n8 h : expr) (stk : Z) : list kentry :=
  [KRange p8 0xce204 0xfffffefffff; KRange (add (mul 8 p8) (mul 8 n8)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA (mul 8 p8) 0) (mul 8 n8);
   KDisj (SA vSP (- stk)) (ELit stk) (SA (mul 8 p8) 0) (mul 8 n8);
   KZero (SA p8 SH) n8;
   KRange (sub p8 (mul 8 h)) 4 72; KRange (sub (add (mul 8 h) (ELit 72)) (add p8 n8)) 0 68;
   KWr (SA (mul 8 h) SH) (ELit 72); KUnk (SA (mul 8 h) SH) (ELit 72)].

(* [comment removed for export] *)
Definition MC_pre_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 24; V 25; V 26; V 4; V 5; V 16; V 17; V 18; V 27; V 28; V 29; V 30; V 31;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 32; V 33; V 34; V 35].
Definition MC_pre_kn (rpc : Z) : list kentry :=
  [KRange (V 0) rpc rpc; KRange (sub (V 16) (mul 8 (V 19))) 0 0; KRange (sub (V 17) (mul 8 (V 20))) 0 0;
   KRange (sub (V 18) (mul 8 (V 21))) 0 0; KRange (V 21) 0 62; KRange (V 1) (0x7ffe00000000 + 2224) 0x800000000000;
   KWr (SA vSP (-2224)) (ELit 2224); KUnk (SA vSP (-2224)) (ELit 2224);
   KUnk (SA (V 17) 0) (V 18); KWr (SA (V 16) 0) (V 18); KDisj (SA (V 17) 0) (V 18) (SA (V 16) 0) (V 18);
   KUnk (SA (V 16) 0) (V 18)]   (* [comment removed for export] *)
  ++ opnd (V 20) (V 21) (V 22) 2224 ++ opnd (V 19) (V 21) (V 23) 2224.
Definition MC_pre (rpc : Z) : tmpl := TM 0x6584c MC_pre_regs (MC_pre_kn rpc) 36%nat (ELit 0) 0%nat.
Definition MC_post_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 36; V 37; V 38; V 4; V 5; V 16; V 39; V 40; V 41; V 42; V 43; V 44; V 45;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 46; V 47; V 48; V 49].
Definition MC_post (rpc : Z) : tmpl := TM rpc MC_post_regs [KUnk (SA (V 16) 0) (V 18)] 50%nat (ELit 0) 0%nat.
Definition MC_W : list SP.win := [(vSP, -2224, ELit 2224); (V 16, 0, V 18)].
Definition MC_A : list SP.win :=
  [(vSP, -2224, ELit 2224); (V 17, 0, V 18); (V 16, 0, V 18); (mul 8 (V 22), SH, ELit 72); (mul 8 (V 23), SH, ELit 72); IMGW].
Definition MCAH (rpc : Z) : SP.summ := SP.SUMR 24 (MC_pre rpc) [MC_post rpc] MC_W (Some MC_A) None.

(* [comment removed for export] *)
Definition MS_pre_regs (c : Z) : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 21; V 22; V 23; V 4; V 5; V 16; ELit c; V 17; V 24; V 25; V 26; V 27; V 28;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 29; V 30; V 31; V 32].
Definition MS_pre_kn (rpc : Z) : list kentry :=
  [KRange (V 0) rpc rpc; KRange (sub (V 16) (mul 8 (V 18))) 0 0; KRange (sub (V 17) (mul 8 (V 19))) 0 0; KRange (V 19) 0 62;
   KRange (V 1) (0x7ffe00000000 + 2208) 0x800000000000; KWr (SA vSP (-2208)) (ELit 2208); KUnk (SA vSP (-2208)) (ELit 2208);
   KWr (SA (V 16) 0) (V 17); KUnk (SA (V 16) 0) (V 17)] ++ opnd (V 18) (V 19) (V 20) 2208.
Definition MS_pre (c rpc : Z) : tmpl := TM 0x65ce8 (MS_pre_regs c) (MS_pre_kn rpc) 33%nat (ELit 0) 0%nat.
Definition MS_post_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 33; V 34; V 35; V 4; V 5; V 16; V 36; V 37; V 38; V 39; V 40; V 41; V 42;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 43; V 44; V 45; V 46].
Definition MS_post (c rpc : Z) : tmpl :=
  TM rpc MS_post_regs [if Z.eqb c 0 then KZero (SA (V 16) 0) (V 17) else KFill (SA (V 16) 0) (V 17) c] 47%nat (ELit 0) 0%nat.
Definition MS_W : list SP.win := [(vSP, -2208, ELit 2208); (V 16, 0, V 17)].
Definition MS_A : list SP.win := [(vSP, -2208, ELit 2208); (V 16, 0, V 17); (mul 8 (V 20), SH, ELit 72); IMGW].
Definition MSAH (c rpc : Z) : SP.summ := SP.SUMR 21 (MS_pre c rpc) [MS_post c rpc] MS_W (Some MS_A) None.

(* [comment removed for export] *)
Definition MV_pre_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 23; V 24; V 25; V 4; V 5; V 16; V 17; V 18; V 26; V 27; V 28; V 29; V 30;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 31; V 32; V 33; V 34].
Definition MV_pre_kn (rpc : Z) : list kentry :=
  [KRange (V 0) rpc rpc; KRange (sub (V 16) (mul 8 (V 19))) 0 0; KRange (sub (V 17) (mul 8 (V 20))) 0 0;
   KRange (sub (V 18) (mul 8 (V 21))) 0 0; KRange (V 21) 0 62; KRange (V 1) (0x7ffe00000000 + 4096) 0x800000000000;
   KWr (SA vSP (-4096)) (ELit 4096); KUnk (SA vSP (-4096)) (ELit 4096);
   KUnk (SA (V 17) 0) (V 18); KWr (SA (V 16) 0) (V 18); KUnk (SA (V 16) 0) (V 18)]
  ++ opnd (V 20) (V 21) (V 22) 4096 ++ opnd (V 19) (V 21) (V 22) 4096.
Definition MV_pre (rpc : Z) : tmpl := TM 0x65f28 MV_pre_regs (MV_pre_kn rpc) 35%nat (ELit 0) 0%nat.
Definition MV_post_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 35; V 36; V 37; V 4; V 5; V 16; V 38; V 39; V 40; V 41; V 42; V 43; V 44;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 45; V 46; V 47; V 48].
Definition MV_post (rpc : Z) : tmpl := TM rpc MV_post_regs [KUnk (SA (V 16) 0) (V 18)] 49%nat (ELit 0) 0%nat.
Definition MV_W : list SP.win := [(vSP, -4096, ELit 4096); (V 16, 0, V 18)].
Definition MV_A : list SP.win := [(vSP, -4096, ELit 4096); (V 17, 0, V 18); (V 16, 0, V 18); (mul 8 (V 22), SH, ELit 72); IMGW].
Definition MVAH (rpc : Z) : SP.summ := SP.SUMR 23 (MV_pre rpc) [MV_post rpc] MV_W (Some MV_A) None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition opnd2 (p n p8 g h he : expr) : list kentry :=
  [KRange (sub p (mul 8 p8)) 0 7; KRange g 0 0x2000000000; KRange (sub (mul 8 g) (sub (add p n) (mul 8 p8))) 0 7;
   KZero (SA p8 SH) g;
   KRange (sub p (mul 64 h)) 0 1048576; KRange (sub (mul 64 he) (add p n)) 0 1048576; KWr (SA (mul 8 h) SH) (mul 8 (sub he h));
   KRange p 0x671000 0x7fffff800000; KRange (add p n) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA p 0) n;
   (* [comment removed for export] *)
   KRange p8 0 0x200000000000; KRange h 0 0x200000000000; KRange he 0 0x200000000000].
Definition stk2 (stk : Z) : list kentry :=
  [KRange (V 1) (0x7ffe00000000 + stk) 0x800000000000; KWr (SA vSP (- stk)) (ELit stk); KUnk (SA vSP (- stk)) (ELit stk)].
Definition hullw (h he : expr) : SP.win := (mul 8 h, SH, mul 8 (sub he h)).

(* [comment removed for export] *)
Definition MG_pre_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 27; V 28; V 29; V 4; V 5; V 16; V 17; V 18; V 30; V 31; V 32; V 33; V 34;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 35; V 36; V 37; V 38].
Definition MG_post_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 39; V 40; V 41; V 4; V 5; V 16; V 42; V 43; V 44; V 45; V 46; V 47; V 48;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 49; V 50; V 51; V 52].
Definition MCG_pre_kn (rpc : Z) : list kentry :=
  [KRange (V 0) rpc rpc] ++ stk2 2224 ++
  [KRange (V 18) 0 0x10000000000; KUnk (SA (V 17) 0) (V 18); KWr (SA (V 16) 0) (V 18); KUnk (SA (V 16) 0) (V 18);
   KDisj (SA (V 17) 0) (V 18) (SA (V 16) 0) (V 18);
   KDisj (SA vSP (-2224)) (ELit 2224) (SA (V 16) 0) (V 18); KDisj (SA vSP (-2224)) (ELit 2224) (SA (V 17) 0) (V 18)]
  ++ opnd2 (V 16) (V 18) (V 19) (V 20) (V 21) (V 22) ++ opnd2 (V 17) (V 18) (V 23) (V 24) (V 25) (V 26).
Definition MCG_pre (rpc : Z) : tmpl := TM 0x6584c MG_pre_regs (MCG_pre_kn rpc) 39%nat (ELit 0) 0%nat.
Definition MCG_post (rpc : Z) : tmpl := TM rpc MG_post_regs [KUnk (SA (V 16) 0) (V 18)] 53%nat (ELit 0) 0%nat.
Definition MCG_W : list SP.win := [(vSP, -2224, ELit 2224); (V 16, 0, V 18)].
Definition MCG_A : list SP.win := [(vSP, -2224, ELit 2224); (V 17, 0, V 18); (V 16, 0, V 18); hullw (V 21) (V 22); hullw (V 25) (V 26); IMGW].
Definition MCAG (rpc : Z) : SP.summ := SP.SUMR 27 (MCG_pre rpc) [MCG_post rpc] MCG_W (Some MCG_A) None.

(* [comment removed for export] *)
Definition MVG_pre_kn (rpc : Z) : list kentry :=
  [KRange (V 0) rpc rpc] ++ stk2 4096 ++
  [KRange (V 18) 0 0x10000000000; KUnk (SA (V 17) 0) (V 18); KWr (SA (V 16) 0) (V 18); KUnk (SA (V 16) 0) (V 18);
   KDisj (SA vSP (-4096)) (ELit 4096) (SA (V 16) 0) (V 18); KDisj (SA vSP (-4096)) (ELit 4096) (SA (V 17) 0) (V 18)]
  ++ opnd2 (V 16) (V 18) (V 19) (V 20) (V 21) (V 22) ++ opnd2 (V 17) (V 18) (V 23) (V 24) (V 25) (V 26).
Definition MVG_pre (rpc : Z) : tmpl := TM 0x65f28 MG_pre_regs (MVG_pre_kn rpc) 39%nat (ELit 0) 0%nat.
Definition MVG_post (rpc : Z) : tmpl := TM rpc MG_post_regs [KUnk (SA (V 16) 0) (V 18)] 53%nat (ELit 0) 0%nat.
Definition MVG_W : list SP.win := [(vSP, -4096, ELit 4096); (V 16, 0, V 18)].
Definition MVG_A : list SP.win := [(vSP, -4096, ELit 4096); (V 17, 0, V 18); (V 16, 0, V 18); hullw (V 21) (V 22); hullw (V 25) (V 26); IMGW].
Definition MVAG (rpc : Z) : SP.summ := SP.SUMR 27 (MVG_pre rpc) [MVG_post rpc] MVG_W (Some MVG_A) None.

(* [comment removed for export] *)
Definition MSG_pre_regs (c : Z) : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 22; V 23; V 24; V 4; V 5; V 16; ELit c; V 17; V 25; V 26; V 27; V 28; V 29;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 30; V 31; V 32; V 33].
Definition MSG_post_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 34; V 35; V 36; V 4; V 5; V 16; V 37; V 38; V 39; V 40; V 41; V 42; V 43;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 44; V 45; V 46; V 47].
Definition MSG_pre_kn (rpc : Z) : list kentry :=
  [KRange (V 0) rpc rpc] ++ stk2 2208 ++
  [KRange (V 17) 0 0x10000000000; KWr (SA (V 16) 0) (V 17); KUnk (SA (V 16) 0) (V 17); KDisj (SA vSP (-2208)) (ELit 2208) (SA (V 16) 0) (V 17)]
  ++ opnd2 (V 16) (V 17) (V 18) (V 19) (V 20) (V 21).
Definition MSG_pre (c rpc : Z) : tmpl := TM 0x65ce8 (MSG_pre_regs c) (MSG_pre_kn rpc) 34%nat (ELit 0) 0%nat.
Definition MSG_post (c rpc : Z) : tmpl :=
  TM rpc MSG_post_regs [if Z.eqb c 0 then KZero (SA (V 16) 0) (V 17) else KFill (SA (V 16) 0) (V 17) c] 48%nat (ELit 0) 0%nat.
Definition MSG_W : list SP.win := [(vSP, -2208, ELit 2208); (V 16, 0, V 17)].
Definition MSG_A : list SP.win := [(vSP, -2208, ELit 2208); (V 16, 0, V 17); hullw (V 20) (V 21); IMGW].
Definition MSAG (c rpc : Z) : SP.summ := SP.SUMR 22 (MSG_pre c rpc) [MSG_post c rpc] MSG_W (Some MSG_A) None.

(* [comment removed for export] *)
Definition opnd2p (p n p8 g h he z : expr) : list kentry :=
  [KRange (sub p (mul 8 p8)) 0 7; KRange g 0 0x2000000000; KRange (sub (add p n) (mul 8 (add p8 g))) 1 8; KRange z 0 1;
   KZero (SA p8 SH) g; KWord (SA (add p8 g) SH) 1 (sub (sub (add p n) (mul 8 (add p8 g))) (mul 8 z));
   KRange (sub p (mul 64 h)) 0 1048576; KRange (sub (mul 64 he) (add p n)) 0 1048576; KWr (SA (mul 8 h) SH) (mul 8 (sub he h));
   KRange p 0x671000 0x7fffff800000; KRange (add p n) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA p 0) n;
   (* [comment removed for export] *)
   KRange p8 0 0x200000000000; KRange h 0 0x200000000000; KRange he 0 0x200000000000;
   KRange (sub (sub (add p n) (mul 8 (add p8 g))) (mul 8 z)) 0 7].
Definition MSGP_pre_regs (c : Z) : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 23; V 24; V 25; V 4; V 5; V 16; ELit c; V 17; V 26; V 27; V 28; V 29; V 30;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 31; V 32; V 33; V 34].
Definition MSGP_post_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 35; V 36; V 37; V 4; V 5; V 16; V 38; V 39; V 40; V 41; V 42; V 43; V 44;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 45; V 46; V 47; V 48].
Definition MSGP_pre_kn (rpc : Z) : list kentry :=
  [KRange (V 0) rpc rpc] ++ stk2 2208 ++
  [KRange (V 17) 0 0x10000000000; KWr (SA (V 16) 0) (V 17); KUnk (SA (V 16) 0) (V 17); KDisj (SA vSP (-2208)) (ELit 2208) (SA (V 16) 0) (V 17)]
  ++ opnd2p (V 16) (V 17) (V 18) (V 19) (V 20) (V 21) (V 22).
Definition MSGP_pre (c rpc : Z) : tmpl := TM 0x65ce8 (MSGP_pre_regs c) (MSGP_pre_kn rpc) 35%nat (ELit 0) 0%nat.
Definition MSGP_post (c rpc : Z) : tmpl :=
  TM rpc MSGP_post_regs [if Z.eqb c 0 then KZero (SA (V 16) 0) (V 17) else KFill (SA (V 16) 0) (V 17) c] 49%nat (ELit 0) 0%nat.
Definition MSAGP (c rpc : Z) : SP.summ := SP.SUMR 23 (MSGP_pre c rpc) [MSGP_post c rpc] MSG_W (Some MSG_A) None.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RP_pre_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 20; V 21; V 22; V 4; V 5; V 16; V 17; V 23; V 24; V 25; V 26; V 27; V 28;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 29; V 30; V 31; V 32].
Definition RP_pre_kn (rpc : Z) : list kentry :=
  [KRange (V 0) rpc rpc; KRange (sub (V 16) (mul 8 (V 18))) 0 0; KRange (sub (V 17) (mul 8 (V 19))) 0 0; KRange (V 19) 0 62;
   KRange (V 1) (0x7ffe00000000 + 80) 0x800000000000; KWr (SA vSP (-80)) (ELit 80); KUnk (SA vSP (-80)) (ELit 80);
   KRange (V 18) 0xce204 0xfffffefffff; KRange (add (mul 8 (V 18)) (mul 8 (V 19))) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA (mul 8 (V 18)) 0) (mul 8 (V 19));
   KZero (SA (V 18) SH) (V 19)].
Definition RP_pre (rpc : Z) : tmpl := TM 0x69078 RP_pre_regs (RP_pre_kn rpc) 33%nat (ELit 0) 0%nat.
Definition RP_post_regs : list expr :=
  [ELit 0; V 0; V 1; V 2; V 3; V 33; V 34; V 35; V 4; V 5; ELit 0; V 36; V 37; V 38; V 39; V 40; V 41; V 42;
   V 6; V 7; V 8; V 9; V 10; V 11; V 12; V 13; V 14; V 15; V 43; V 44; V 45; V 46].
Definition RP_post (rpc : Z) : tmpl := TM rpc RP_post_regs [] 47%nat (ELit 0) 0%nat.
Definition RP_W : list SP.win := [(vSP, -80, ELit 80)].
Definition RP_A : list SP.win := [(vSP, -80, ELit 80); (V 18, SH, V 19); IMGW].
Definition RIPA (rpc : Z) : SP.summ := SP.SUMR 20 (RP_pre rpc) [RP_post rpc] RP_W (Some RP_A) None.
End AMHB.
