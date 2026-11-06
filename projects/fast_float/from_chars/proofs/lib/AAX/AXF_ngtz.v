(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Module AXF_ngt.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_CA := EVar 32.
Definition e_ND := EVar 33.
Definition e_n := EVar 34.
Definition e_SB := EVar 35.
Definition e_RIB := EVar 36.
Definition e_na := EVar 37.
Definition e_cp := EVar 38.
Definition e_sz := EVar 39.
Definition e_st := EVar 40.
Definition e_g1 := EVar 41.
Definition e_g2 := EVar 42.
Definition e_g3 := EVar 43.
Definition e_g4 := EVar 44.
Definition e_g5 := EVar 45.
Definition e_g6 := EVar 46.
Definition e_g7 := EVar 47.
Definition e_g8 := EVar 48.
Definition e_g9 := EVar 49.
Definition e_g10 := EVar 50.
Definition e_g11 := EVar 51.
Definition e_c1 := EVar 52.
Definition e_c2 := EVar 53.
Definition e_c3 := EVar 54.
Definition e_c4 := EVar 55.
Definition e_c5 := EVar 56.
Definition e_cra := EVar 57.
Definition CC := EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5).
Definition REC := EAlu ALU_ADD e_CA (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition RI := EAlu ALU_ADD e_RIB (EMd M_MUL (ELit 128) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))).
Definition STK := SA (EVar 2) (-1024).
Definition sr_ngt := (sr_upd (sr_upd (sr_upd sr_id 8 (RI)) 14 (e_n)) 19 (ELit 2305843009213693952)).
Definition kn_ngt : list kentry :=
  [ KRange e_CA 1 (2^47);
    KAlign e_CA 16;
    KRange e_ND 33 512;
    KRange (EVar 2) (2^46) (2^47);
    KRange e_RIB 1 (2^47);
    KAlign e_RIB 128;
    KWord (SA RI 72) 8 e_na;
    KWr (SA RI 72) (ELit 8);
    KWord (SA RI 0) 8 (ELit 1152921504606846976);
    KWr (SA RI 0) (ELit 8);
    KWord (SA (EVar 2) 120) 8 (ELit 279672);
    KWord (SA (EVar 2) 112) 8 REC;
    KWord (SA (EVar 2) 104) 8 e_n;
    KWord (SA (EVar 2) 96) 8 (ELit 8);
    KWord (SA (EVar 2) 88) 8 e_CA;
    KWord (SA (EVar 2) 80) 8 (ELit 923480);
    KWord (SA (EVar 2) 72) 8 e_g5;
    KWord (SA (EVar 2) 64) 8 e_g6;
    KWord (SA (EVar 2) 56) 8 e_g7;
    KWord (SA (EVar 2) 48) 8 e_g8;
    KWord (SA (EVar 2) 40) 8 e_g9;
    KWord (SA (EVar 2) 32) 8 e_g10;
    KWord (SA (EVar 2) 24) 8 e_g11;
    KWord (SA (EVar 2) 136) 8 REC;
    KWord (SA (EVar 2) 144) 8 CC;
    KWord (SA (EVar 2) 152) 8 (ELit 278424);
    KWord (SA (EVar 2) 160) 8 e_c4;
    KWord (SA (EVar 2) 168) 8 e_c3;
    KWord (SA (EVar 2) 176) 8 e_c2;
    KWord (SA (EVar 2) 184) 8 e_c1;
    KWord (SA (EVar 2) 192) 8 e_c5;
    KWord (SA (EVar 2) 200) 8 e_cra;
    KWr (SA REC 0) (ELit 4);
    KWord (SA REC 8) 8 e_sz;
    KWord (SA (EAlu ALU_ADD e_CA (EAlu ALU_ADD (EMd M_MUL (ELit 80) (EAlu ALU_SRL (EAlu ALU_ADD e_ND (ELit 31)) (ELit 5))) (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 4294967296) (EExt true 0 4 e_n)) (ELit (-4294967296))) (ELit 30)))) 16) 4 e_cp;
    KWord (SA (ELit 0) 923512) 8 e_SB;
    KWord (SA e_CA 2576) 8 e_st;
    KWr (SA e_CA 2576) (ELit 8);
    KImg 65536 143360;
    KWr STK (ELit 1024) ].
Definition scr_ngt : scripts := SCR [false; false; false; false; false; false; false; false] [] [].
Definition ss_ngt := SS 0x446c0 sr_ngt [] kn_ngt 58.
Definition RUN_ngt := sym_exec SEGS 120 true [0x43f08] scr_ngt ss_ngt [].

Definition scr_pngt : scripts := SCR [false; false; false; false; false; false; false; false] [] [].
Definition RES_pngt := Eval vm_compute in sym_exec SEGS 120 true [0x43f08] scr_pngt ss_ngt [].
Lemma RES_pngt_ok : sym_exec SEGS 120 true [0x43f08] scr_pngt (SS 0x446c0 sr_ngt [] kn_ngt 58) [] = RES_pngt.
Proof. vm_compute. reflexivity. Qed.
End AXF_ngt.


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section NGT.
Context {fx : FPState}.

Definition VALS_ngt (CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra : Z) : list Z := [CA; ND; n; SB; RIB; na; cp; sz; st; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11; c1; c2; c3; c4; c5; cra].

Record ngt_pre (regs : bvmap 5 word) (m : word -> option byte) (CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra : Z) : Prop := {
  ngt_R8 : getr regs 8 = wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5)) ;
  ngt_R14 : getr regs 14 = wa n ;
  ngt_R19 : getr regs 19 = wa 2305843009213693952 ;
  ngt_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  ngt_rng_CA : 1 <= CA <= 2^47 ;
  ngt_rng_ND : 33 <= ND <= 512 ;
  ngt_rng_n : 1 <= n <= 8 ;
  ngt_rng_SB : 0 <= SB <= 2^64-1 ;
  ngt_rng_RIB : 1 <= RIB <= 2^47 ;
  ngt_rng_na : 0 <= na <= 2^64-1 ;
  ngt_rng_cp : 0 <= cp <= 2^32-1 ;
  ngt_rng_sz : 0 <= sz <= 2^64-1 ;
  ngt_rng_st : 0 <= st <= 2^64-1 ;
  ngt_rng_g1 : 0 <= g1 <= 2^64-1 ;
  ngt_rng_g2 : 0 <= g2 <= 2^64-1 ;
  ngt_rng_g3 : 0 <= g3 <= 2^64-1 ;
  ngt_rng_g4 : 0 <= g4 <= 2^64-1 ;
  ngt_rng_g5 : 0 <= g5 <= 2^64-1 ;
  ngt_rng_g6 : 0 <= g6 <= 2^64-1 ;
  ngt_rng_g7 : 0 <= g7 <= 2^64-1 ;
  ngt_rng_g8 : 0 <= g8 <= 2^64-1 ;
  ngt_rng_g9 : 0 <= g9 <= 2^64-1 ;
  ngt_rng_g10 : 0 <= g10 <= 2^64-1 ;
  ngt_rng_g11 : 0 <= g11 <= 2^64-1 ;
  ngt_rng_c1 : 0 <= c1 <= 2^64-1 ;
  ngt_rng_c2 : 0 <= c2 <= 2^64-1 ;
  ngt_rng_c3 : 0 <= c3 <= 2^64-1 ;
  ngt_rng_c4 : 0 <= c4 <= 2^64-1 ;
  ngt_rng_c5 : 0 <= c5 <= 2^64-1 ;
  ngt_rng_cra : 0 <= cra <= 2^64-1 ;
  ngt_ka1 : CA mod 16 = 0 ;
  ngt_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  ngt_ka5 : RIB mod 128 = 0 ;
  ngt_kw6 : rdn SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 72)) 8 = Some (word_to_le_bytes 8 (wa na)) ;
  ngt_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 72 + d)) k = true ;
  ngt_kw8 : rdn SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) 8 = Some (word_to_le_bytes 8 (wa 1152921504606846976)) ;
  ngt_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0 + d)) k = true ;
  ngt_kw10 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 120)) 8 = Some (word_to_le_bytes 8 (wa 279672)) ;
  ngt_kw11 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 112)) 8 = Some (word_to_le_bytes 8 (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)))) ;
  ngt_kw12 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 104)) 8 = Some (word_to_le_bytes 8 (wa n)) ;
  ngt_kw13 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 96)) 8 = Some (word_to_le_bytes 8 (wa 8)) ;
  ngt_kw14 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 88)) 8 = Some (word_to_le_bytes 8 (wa CA)) ;
  ngt_kw15 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 80)) 8 = Some (word_to_le_bytes 8 (wa 923480)) ;
  ngt_kw16 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 72)) 8 = Some (word_to_le_bytes 8 (wa g5)) ;
  ngt_kw17 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 64)) 8 = Some (word_to_le_bytes 8 (wa g6)) ;
  ngt_kw18 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 56)) 8 = Some (word_to_le_bytes 8 (wa g7)) ;
  ngt_kw19 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48)) 8 = Some (word_to_le_bytes 8 (wa g8)) ;
  ngt_kw20 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 40)) 8 = Some (word_to_le_bytes 8 (wa g9)) ;
  ngt_kw21 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32)) 8 = Some (word_to_le_bytes 8 (wa g10)) ;
  ngt_kw22 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa g11)) ;
  ngt_kw23 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 136)) 8 = Some (word_to_le_bytes 8 (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5)))) ;
  ngt_kw24 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 144)) 8 = Some (word_to_le_bytes 8 (wa (Z.shiftr (((ND + 31)) mod 2^64) 5))) ;
  ngt_kw25 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 152)) 8 = Some (word_to_le_bytes 8 (wa 278424)) ;
  ngt_kw26 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 160)) 8 = Some (word_to_le_bytes 8 (wa c4)) ;
  ngt_kw27 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 168)) 8 = Some (word_to_le_bytes 8 (wa c3)) ;
  ngt_kw28 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 176)) 8 = Some (word_to_le_bytes 8 (wa c2)) ;
  ngt_kw29 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 184)) 8 = Some (word_to_le_bytes 8 (wa c1)) ;
  ngt_kw30 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 192)) 8 = Some (word_to_le_bytes 8 (wa c5)) ;
  ngt_kw31 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 200)) 8 = Some (word_to_le_bytes 8 (wa cra)) ;
  ngt_kwr32 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0 + d)) k = true ;
  ngt_kw33 : rdn SEGS m (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 8)) 8 = Some (word_to_le_bytes 8 (wa sz)) ;
  ngt_kw34 : rdn SEGS m (wa (CA + ((80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + Z.shiftr ((((4294967296 * ext_Z true 0 4 n) + -4294967296)) mod 2^64) 30) + 16)) 4 = Some (word_to_le_bytes 4 (wa cp)) ;
  ngt_kw35 : rdn SEGS m (wa (0 + 923512)) 8 = Some (word_to_le_bytes 8 (wa SB)) ;
  ngt_kw36 : rdn SEGS m (wa (CA + 2576)) 8 = Some (word_to_le_bytes 8 (wa st)) ;
  ngt_kwr37 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (CA + 2576 + d)) k = true ;
  ngt_kimg38 : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None
}.


#[using="Type"] Lemma ngt_setup : forall regs m CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra, ngt_pre regs m CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra ->
  regs_ok (Ez regs (VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) AXF_ngt.sr_ngt regs /\ know_ok SEGS (Ez regs (VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) m AXF_ngt.kn_ngt.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra P. destruct P as [ngt_R8 ngt_R14 ngt_R19 ngt_HSTK ngt_rng_CA ngt_rng_ND ngt_rng_n ngt_rng_SB ngt_rng_RIB ngt_rng_na ngt_rng_cp ngt_rng_sz ngt_rng_st ngt_rng_g1 ngt_rng_g2 ngt_rng_g3 ngt_rng_g4 ngt_rng_g5 ngt_rng_g6 ngt_rng_g7 ngt_rng_g8 ngt_rng_g9 ngt_rng_g10 ngt_rng_g11 ngt_rng_c1 ngt_rng_c2 ngt_rng_c3 ngt_rng_c4 ngt_rng_c5 ngt_rng_cra ngt_ka1 ngt_kr3 ngt_ka5 ngt_kw6 ngt_kwr7 ngt_kw8 ngt_kwr9 ngt_kw10 ngt_kw11 ngt_kw12 ngt_kw13 ngt_kw14 ngt_kw15 ngt_kw16 ngt_kw17 ngt_kw18 ngt_kw19 ngt_kw20 ngt_kw21 ngt_kw22 ngt_kw23 ngt_kw24 ngt_kw25 ngt_kw26 ngt_kw27 ngt_kw28 ngt_kw29 ngt_kw30 ngt_kw31 ngt_kwr32 ngt_kw33 ngt_kw34 ngt_kw35 ngt_kw36 ngt_kwr37 ngt_kimg38].
  set (E := Ez regs (VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)).
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = na) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = cp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = g1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = g2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = g3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = g4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = g5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z46 : bv_unsigned (ev E 46) = g6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z47 : bv_unsigned (ev E 47) = g7) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z48 : bv_unsigned (ev E 48) = g8) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z49 : bv_unsigned (ev E 49) = g9) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z50 : bv_unsigned (ev E 50) = g10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z51 : bv_unsigned (ev E 51) = g11) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z52 : bv_unsigned (ev E 52) = c1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z53 : bv_unsigned (ev E 53) = c2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z54 : bv_unsigned (ev E 54) = c3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z55 : bv_unsigned (ev E 55) = c4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z56 : bv_unsigned (ev E 56) = c5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z57 : bv_unsigned (ev E 57) = cra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  assert (HP : 0 <= Z.shiftr ((4294967296 * ext_Z true 0 4 n + -4294967296) mod 2^64) 30 < 2^34) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.mod_pos_bound (4294967296 * ext_Z true 0 4 n + -4294967296) (2^64) ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  split.
  { unfold AXF_ngt.sr_ngt.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|].
    - rewrite ngt_R8, zeval_sound. cbn [zeval edenot AXF_ngt.e_CA AXF_ngt.e_ND AXF_ngt.e_n AXF_ngt.e_SB AXF_ngt.e_RIB AXF_ngt.e_na AXF_ngt.e_cp AXF_ngt.e_sz AXF_ngt.e_st AXF_ngt.e_g1 AXF_ngt.e_g2 AXF_ngt.e_g3 AXF_ngt.e_g4 AXF_ngt.e_g5 AXF_ngt.e_g6 AXF_ngt.e_g7 AXF_ngt.e_g8 AXF_ngt.e_g9 AXF_ngt.e_g10 AXF_ngt.e_g11 AXF_ngt.e_c1 AXF_ngt.e_c2 AXF_ngt.e_c3 AXF_ngt.e_c4 AXF_ngt.e_c5 AXF_ngt.e_cra AXF_ngt.CC AXF_ngt.REC AXF_ngt.RI AXF_ngt.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z51, ?Z52, ?Z53, ?Z54, ?Z55, ?Z56, ?Z57, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ngt_R14. reflexivity.
    - rewrite ngt_R19. reflexivity. }
  unfold know_ok, AXF_ngt.kn_ngt.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_ngt.e_CA AXF_ngt.e_ND AXF_ngt.e_n AXF_ngt.e_SB AXF_ngt.e_RIB AXF_ngt.e_na AXF_ngt.e_cp AXF_ngt.e_sz AXF_ngt.e_st AXF_ngt.e_g1 AXF_ngt.e_g2 AXF_ngt.e_g3 AXF_ngt.e_g4 AXF_ngt.e_g5 AXF_ngt.e_g6 AXF_ngt.e_g7 AXF_ngt.e_g8 AXF_ngt.e_g9 AXF_ngt.e_g10 AXF_ngt.e_g11 AXF_ngt.e_c1 AXF_ngt.e_c2 AXF_ngt.e_c3 AXF_ngt.e_c4 AXF_ngt.e_c5 AXF_ngt.e_cra AXF_ngt.CC AXF_ngt.REC AXF_ngt.RI AXF_ngt.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z51, ?Z52, ?Z53, ?Z54, ?Z55, ?Z56, ?Z57, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range CA _ _ ngt_rng_CA eq_refl eq_refl), ?(mod64_of_range ND _ _ ngt_rng_ND eq_refl eq_refl), ?(mod64_of_range n _ _ ngt_rng_n eq_refl eq_refl), ?(mod64_of_range RIB _ _ ngt_rng_RIB eq_refl eq_refl), ?(mod64_of_range cp _ _ ngt_rng_cp eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply ngt_kwr7 | apply ngt_kwr9 | apply ngt_kwr32 | apply ngt_kwr37]; assumption).
  all: try (clear - ngt_rng_CA ngt_rng_ND ngt_rng_n ngt_rng_SB ngt_rng_RIB ngt_rng_na ngt_rng_cp ngt_rng_sz ngt_rng_st ngt_rng_g1 ngt_rng_g2 ngt_rng_g3 ngt_rng_g4 ngt_rng_g5 ngt_rng_g6 ngt_rng_g7 ngt_rng_g8 ngt_rng_g9 ngt_rng_g10 ngt_rng_g11 ngt_rng_c1 ngt_rng_c2 ngt_rng_c3 ngt_rng_c4 ngt_rng_c5 ngt_rng_cra ngt_ka1 ngt_kr3 ngt_ka5 HC HP; lia).
  all: first [lia].
Qed.


Definition ngt_mem_pngt (m : word -> option byte) (regs : bvmap 5 word) (CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 72)) (word_to_le_bytes 8 (wa (n + na)))) (wa (RIB + (128 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) (word_to_le_bytes 8 (wa 0))) (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) (word_to_le_bytes 4 (wa n))) (wa (CA + (80 * Z.shiftr (((ND + 31)) mod 2^64) 5) + 0)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 n + -1)))) (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st))).

#[using="Type"] Theorem ngt_pngt : forall regs m rom CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra, ngt_pre regs m CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra ->
  scs_denot SEGS m (Ez regs (VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) (snd (fst AXF_ngt.RES_pngt)) ->
  exists R, msteps SEGS (mkst regs (wa 0x446c0) m rom) (mkst R (wa 0x43f08) (ngt_mem_pngt m regs CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra) rom) /\
    getr R 1 = wa cra /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 208) /\ getr R 5 = wa 4611686018427387904 /\ getr R 6 = wa 0 /\ getr R 7 = wa 1152921504606846976 /\ getr R 8 = wa c5 /\ getr R 9 = wa c1 /\ getr R 10 = wa (SB + ((4294967296 * Z.shiftr (((ND + 31)) mod 2^64) 5) + (16 * ext_Z false 0 4 cp))) /\ getr R 11 = wa 9 /\ getr R 12 = wa sz /\ getr R 13 = wa 8 /\ getr R 14 = wa (16 * ext_Z false 0 4 cp) /\ getr R 15 = wa 17293822569102704639 /\ getr R 16 = wa 1152920405095219200 /\ getr R 17 = wa 18446742974197923840 /\ getr R 18 = wa c2 /\ getr R 19 = wa c3 /\ getr R 20 = wa c4 /\ getr R 21 = wa g5 /\ getr R 22 = wa g6 /\ getr R 23 = wa g7 /\ getr R 24 = wa g8 /\ getr R 25 = wa g9 /\ getr R 26 = wa g10 /\ getr R 27 = wa g11 /\ getr R 28 = wa 0 /\ (forall k, In k [3; 4; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra P Hsc. destruct (ngt_setup regs m CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra P) as [HR HK].
  set (E := Ez regs (VALS_ngt CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra)) in *. destruct P as [ngt_R8 ngt_R14 ngt_R19 ngt_HSTK ngt_rng_CA ngt_rng_ND ngt_rng_n ngt_rng_SB ngt_rng_RIB ngt_rng_na ngt_rng_cp ngt_rng_sz ngt_rng_st ngt_rng_g1 ngt_rng_g2 ngt_rng_g3 ngt_rng_g4 ngt_rng_g5 ngt_rng_g6 ngt_rng_g7 ngt_rng_g8 ngt_rng_g9 ngt_rng_g10 ngt_rng_g11 ngt_rng_c1 ngt_rng_c2 ngt_rng_c3 ngt_rng_c4 ngt_rng_c5 ngt_rng_cra ngt_ka1 ngt_kr3 ngt_ka5 ngt_kw6 ngt_kwr7 ngt_kw8 ngt_kwr9 ngt_kw10 ngt_kw11 ngt_kw12 ngt_kw13 ngt_kw14 ngt_kw15 ngt_kw16 ngt_kw17 ngt_kw18 ngt_kw19 ngt_kw20 ngt_kw21 ngt_kw22 ngt_kw23 ngt_kw24 ngt_kw25 ngt_kw26 ngt_kw27 ngt_kw28 ngt_kw29 ngt_kw30 ngt_kw31 ngt_kwr32 ngt_kw33 ngt_kw34 ngt_kw35 ngt_kw36 ngt_kwr37 ngt_kimg38].
  assert (Z32 : bv_unsigned (ev E 32) = CA) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ND) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = SB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = RIB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = na) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = cp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = g1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = g2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = g3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = g4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = g5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z46 : bv_unsigned (ev E 46) = g6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z47 : bv_unsigned (ev E 47) = g7) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z48 : bv_unsigned (ev E 48) = g8) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z49 : bv_unsigned (ev E 49) = g9) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z50 : bv_unsigned (ev E 50) = g10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z51 : bv_unsigned (ev E 51) = g11) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z52 : bv_unsigned (ev E 52) = c1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z53 : bv_unsigned (ev E 53) = c2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z54 : bv_unsigned (ev E 54) = c3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z55 : bv_unsigned (ev E 55) = c4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z56 : bv_unsigned (ev E 56) = c5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z57 : bv_unsigned (ev E 57) = cra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (HC : 2 <= Z.shiftr ((ND + 31) mod 2^64) 5 <= 16) by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^5) with 32; split; [apply Z.div_le_lower_bound; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
  assert (HP : 0 <= Z.shiftr ((4294967296 * ext_Z true 0 4 n + -4294967296) mod 2^64) 30 < 2^34) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.mod_pos_bound (4294967296 * ext_Z true 0 4 n + -4294967296) (2^64) ltac:(lia)); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (run_sound SEGS 120 [0x43f08] AXF_ngt.scr_pngt 0x446c0 AXF_ngt.sr_ngt AXF_ngt.kn_ngt 58 _ _ _ E m rom regs AXF_ngt.RES_pngt_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ngt.RES_pngt fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ngt_mem_pngt m regs CA ND n SB RIB na cp sz st g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 c1 c2 c3 c4 c5 cra) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ngt_mem_pngt. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NGT.
