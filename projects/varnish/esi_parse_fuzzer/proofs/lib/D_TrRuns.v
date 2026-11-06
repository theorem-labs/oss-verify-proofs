(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec SymExec2 SymRun SymDrive SymDe08 LibK2dm D_Kn21w D_Manqc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n D_Li6dm D_Tails D_Wamxh RefMocc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Dr084 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec.
Import SX2. Import ListNotations.
Open Scope Z_scope.

Definition STOPS_X : list Z := [0x25d58; 0x22fc4; 0x22e84; 0x2ac54; 0x2299c; 0x17eec; 0x17d58]%Z.   (* [comment removed for export] *)
Definition FUEL_X : nat := 5000.
Definition runX (dirs : list bool) (ss : sym_state) := sym_exec RSEGS FUEL_X true STOPS_X (SCR dirs [] []) ss [].
Definition kn_afterX (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition sr_h : list expr := Eval vm_compute in
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_drv 9 (EVar 20)) 19 (EVar 21)) 21 (EVar 22)) 22 (EVar 13)) 23 (EVar 14).
Definition knH : list kentry := knD ++ [KRange (EVar 20) 0x1000 0x7fffff800000; KRange (EVar 21) 0 0x4000000].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cfgX : expr := EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EVar 6)) (ELit 49)) (EVar 7).
Definition payX : expr := EAlu ALU_ADD (EAlu ALU_ADD (EVar 20) cfgX) (ELit 6).
Definition plenX : expr := EAlu ALU_ADD (EAlu ALU_ADD (EVar 21) (EMd M_MUL (ELit (-1)) cfgX)) (ELit (-6)).

(* [comment removed for export] *)
Definition rS1 := Eval vm_compute in runX [true] (SS 0x17c60 sr_h [] knH 6).
Definition srS1 : list expr := Eval vm_compute in s_regs (fst (fst rS1)).
Definition knS1 : list kentry := Eval vm_compute in kn_afterX rS1 knH.
Definition resS : stdio_res := Eval vm_compute in match stdio_call 70 srS1 knS1 with Some r => r | None => no_res end.
Definition srS2_0 : list expr := Eval vm_compute in sc_sr resS.
Definition knS2_0 : list kentry := Eval vm_compute in sc_kn resS.
Definition rS2 := Eval vm_compute in runX [] (SS (sc_ret resS) srS2_0 [] knS2_0 102).
Definition srS2 : list expr := Eval vm_compute in s_regs (fst (fst rS2)).
Definition knS2 : list kentry := Eval vm_compute in kn_afterX rS2 knS2_0.

(* [comment removed for export] *)
Definition rV1 := Eval vm_compute in runX [false; true] (SS 0x17c60 sr_h [] knH 6).
Definition srV1 : list expr := Eval vm_compute in s_regs (fst (fst rV1)).
Definition knV1 : list kentry := Eval vm_compute in kn_afterX rV1 knH.
Definition resV : stdio_res := Eval vm_compute in match stdio_call 70 srV1 knV1 with Some r => r | None => no_res end.
Definition srV2_0 : list expr := Eval vm_compute in sc_sr resV.
Definition knV2_0 : list kentry := Eval vm_compute in sc_kn resV.
Definition rV2 := Eval vm_compute in runX [] (SS (sc_ret resV) srV2_0 [] knV2_0 102).
Definition srV2 : list expr := Eval vm_compute in s_regs (fst (fst rV2)).
Definition knV2 : list kentry := Eval vm_compute in kn_afterX rV2 knV2_0.

(* [comment removed for export] *)
Definition rHmm := Eval vm_compute in runX [false; false; false; false] (SS 0x17c60 sr_h [] knH 6). (* [comment removed for export] *)
Definition rHzm := Eval vm_compute in runX [false; false; true; true] (SS 0x17c60 sr_h [] knH 6).   (* [comment removed for export] *)
Definition rHmz := Eval vm_compute in runX [false; false; false; true] (SS 0x17c60 sr_h [] knH 6).  (* [comment removed for export] *)
Definition rHzz := Eval vm_compute in runX [false; false; true; false] (SS 0x17c60 sr_h [] knH 6).  (* [comment removed for export] *)
Definition srHmm : list expr := Eval vm_compute in s_regs (fst (fst rHmm)).
Definition srHzm : list expr := Eval vm_compute in s_regs (fst (fst rHzm)).
Definition srHmz : list expr := Eval vm_compute in s_regs (fst (fst rHmz)).
Definition srHzz : list expr := Eval vm_compute in s_regs (fst (fst rHzz)).
(* [comment removed for export] *)
Definition knT0 : list kentry := Eval vm_compute in kn_afterX rHmm knH.
Definition TR_PIECES : list (Z * Z) :=
  [(0x10000, 0x31698); (0x10000, 0x315a8); (0x31690, 0x31698); (0x31780, 0x317b0); (0x41801, 0x41804); (0x41805, 0x41830); (0x41840, 0x42088);
   (0x62804, 0x62858); (0x62c58, 0x63000)]%Z.   (* [comment removed for export] *)
Definition knT : list kentry := Eval vm_compute in (knT0 ++ kimg_pieces TR_PIECES).
(* [comment removed for export] *)
Definition knTm : list kentry := Eval vm_compute in (kn_keep2 knT (RS_call (-208) MALLOC_STACK) VICT ++ [kwr_data]).

(* [comment removed for export] *)
Definition LIBW : Z := 16384.
Definition RS_lib : list frange :=
  [(EVar 0, (-208 - LIBW)%Z, LIBW); (ELit 0, ERRNO_CELL, 4%Z); (ELit 0, 0x41830%Z, 16%Z); (ELit 0, 0x41804%Z, 1%Z);
   (ELit 0, STATICS_LO, (STATICS_HI - STATICS_LO)%Z); (ELit 0, HEAP_LO, (HEAP_HI - HEAP_LO)%Z);
   (EVar 0, (-8388608 - CSLACK)%Z, CSLACK);   (* [comment removed for export] *)
   (ELit 0, LOW_LO, (LOW_HI - LOW_LO)%Z); (ELit 0, 0%Z, 4096%Z)].
Definition RS_pf : list frange :=
  [(EVar 0, (-208 - 1200)%Z, 1200%Z); (ELit 0, 0x31698%Z, 232%Z); (ELit 0, 0x62858%Z, 1024%Z)].
(* [comment removed for export] *)
Definition knL : list kentry := Eval vm_compute in (kn_keep2 knTm (RS_lib ++ RS_pf) VICT ++ [kwr_data]).

(* [comment removed for export] *)
Definition sr_m : list expr := Eval vm_compute in sr_upd srHmm 21 (EVar 25).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition srB_0 : list expr := Eval vm_compute in sr_post sr_m 70.
Definition rB := Eval vm_compute in runX [false] (SS 0x17e98 srB_0 [] knTm 102).
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).

(* [comment removed for export] *)
Definition sr_le : list expr :=
  Eval cbv in [ELit 0; jx 1; spx (-208); ELit 0x10800; ELit 0x42158; jx 5; jx 6; jx 7;
   jx 8; jx 9; jx 10; jx 11; jx 12; jx 13; jx 14; jx 15; jx 16; jx 17;
   EVar 23; jx 19; jx 20; jx 21; ELit 0; jx 23; jx 24; jx 25; jx 26; jx 27; jx 28; jx 29; jx 30; jx 31].
Definition rE0 := Eval vm_compute in runX [] (SS 0x17f24 sr_le [] knL 70).
Definition srE0 : list expr := Eval vm_compute in s_regs (fst (fst rE0)).
Definition srE1_0 : list expr := Eval vm_compute in sr_post srE0 70.
Definition rE1T := Eval vm_compute in runX [true] (SS 0x17f2c srE1_0 [] knL 102).
Definition rE1F := Eval vm_compute in runX [false] (SS 0x17f2c srE1_0 [] knL 102).

(* [comment removed for export] *)
Definition sr_cc : list expr :=
  Eval cbv in [ELit 0; jx 1; spx (-128); ELit 0x10800; ELit 0x42158; jx 5; jx 6; jx 7;
   EVar 24; EVar 20; jx 10; jx 11; jx 12; jx 13; jx 14; jx 15; jx 16; jx 17;
   jx 18; jx 19; jx 20; jx 21; jx 22; jx 23; jx 24; jx 25; jx 26; jx 27; jx 28; jx 29; jx 30; jx 31].
(* [comment removed for export] *)
Definition TAIL_CUT : list frange := RS_call (-128) FREE_STACK ++ [(ELit 0, 0x315a8%Z, 232%Z); (ELit 0, 0x41800%Z, 1%Z); (ELit 0, 0x41804%Z, 1%Z); (ELit 0, 0x621a8%Z, 288%Z)].
(* [comment removed for export] *)
Definition knTL : list kentry := Eval vm_compute in (kn_keep2 knL TAIL_CUT VICT ++ [kwr_data]).
Definition TAIL_PIECES : list (Z * Z) :=
  [(0x10000, 0x315a8); (0x31690, 0x31698); (0x31780, 0x317b0); (0x317b1, 0x317f9); (0x417f9, 0x41800); (0x41801, 0x41804); (0x41805, 0x41830); (0x41840, 0x42088);
   (0x42170, 0x62160); (0x62198, 0x621a8); (0x622c8, 0x623c8); (0x62804, 0x62858); (0x62c58, 0x63000)]%Z.   (* [comment removed for export] *)
Definition knS2p : list kentry := Eval vm_compute in (knS2 ++ kimg_pieces TAIL_PIECES).
Definition knV2p : list kentry := Eval vm_compute in (knV2 ++ kimg_pieces TAIL_PIECES).
Definition rX1 := Eval vm_compute in runX [] (SS 0x17d58 sr_cc [] knTL 70).
Definition srX1 : list expr := Eval vm_compute in s_regs (fst (fst rX1)).
Definition srX2_0 : list expr := Eval vm_compute in sr_post srX1 70.
Definition rX2 := Eval vm_compute in runX [] (SS 0x17d60 srX2_0 [] knTL 102).
Definition srX2 : list expr := Eval vm_compute in s_regs (fst (fst rX2)).

(* [comment removed for export] *)
