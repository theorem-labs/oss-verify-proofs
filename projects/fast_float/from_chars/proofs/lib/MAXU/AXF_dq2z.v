(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Module AXF_dq2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sc := EVar 33.
Definition e_sp0 := EVar 34.
Definition e_NX := EVar 35.
Definition e_PR := EVar 36.
Definition e_NMEM := EVar 37.
Definition e_AIDXB := EVar 38.
Definition e_NFR := EVar 39.
Definition STK := SA e_sp0 (-1024).
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_dq2 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_G)) 12 (e_sc)) 18 (ELit 0x97c98)).
Definition kn_dq2 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_sc 0 47;
    KRange ACT 0 376;
    KRange e_NX 1 (2^63-1);
    KAlign e_NX 8;
    KRange e_PR 1 (2^63-1);
    KRange e_NMEM 1 (2^63-1);
    KRange e_AIDXB 0 255;
    KRange e_NFR 0 (2^32-1);
    KWord (SA e_G 8) 8 e_NX;
    KWord (SA e_G 0) 8 e_PR;
    KWord (SA ACT 621800) 8 e_G;
    KWord (SA e_NX 24) 4 (ELit 0);
    KWord (SA e_NX 16) 8 e_NMEM;
    KWord (SA e_NMEM 8) 1 e_AIDXB;
    KWord (SA e_NX 28) 4 e_NFR;
    KWr (SA e_G 0) (ELit 16);
    KWr (SA e_PR 8) (ELit 8);
    KWr (SA e_NX 0) (ELit 8);
    KWr (SA ACT 621800) (ELit 8);
    KWr (SA e_NX 24) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA ACT 621800) (ELit 8);
    KDisj STK (ELit 1024) (SA e_PR 8) (ELit 8);
    KDisj STK (ELit 1024) (SA e_NX 0) (ELit 40);
    KDisj STK (ELit 1024) (SA e_NMEM 8) (ELit 1);
    KDisj (SA e_G 0) (ELit 40) (SA ACT 621800) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA e_PR 8) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA e_NX 0) (ELit 40);
    KDisj (SA ACT 621800) (ELit 8) (SA e_PR 8) (ELit 8);
    KDisj (SA ACT 621800) (ELit 8) (SA e_NX 0) (ELit 40);
    KDisj (SA e_PR 8) (ELit 8) (SA e_NX 16) (ELit 16);
    KDisj (SA e_NMEM 8) (ELit 1) (SA e_PR 8) (ELit 8);
    KDisj (SA e_NMEM 8) (ELit 1) (SA e_NX 0) (ELit 40);
    KDisj (SA e_NMEM 8) (ELit 1) (SA e_G 0) (ELit 40);
    KDisj (SA e_NMEM 8) (ELit 1) (SA ACT 621800) (ELit 8) ].
Definition scr_dq2 : scripts := SCR [] [] [].
Definition ss_dq2 := SS 0x5379c sr_dq2 [] kn_dq2 40.
Definition RUN_dq2 := sym_exec SEGS 150 true [0x538b0] scr_dq2 ss_dq2 [].

Definition scr_pdq2 : scripts := SCR [false; false; false; false; false; false; false; false] [] [].
Definition RES_pdq2 := Eval vm_compute in sym_exec SEGS 150 true [0x538b0] scr_pdq2 ss_dq2 [].
Lemma RES_pdq2_ok : sym_exec SEGS 150 true [0x538b0] scr_pdq2 (SS 0x5379c sr_dq2 [] kn_dq2 40) [] = RES_pdq2.
Proof. vm_compute. reflexivity. Qed.
End AXF_dq2.

Import ListNotations AX2 AX2S.

Module AXF_dq0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sc := EVar 33.
Definition e_sp0 := EVar 34.
Definition STK := SA e_sp0 (-1024).
Definition sr_dq0 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_G)) 12 (e_sc)) 18 (ELit 0x97c98)).
Definition kn_dq0 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_sc 0 63;
    KWord (SA e_G 8) 8 (ELit 0);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40) ].
Definition scr_dq0 : scripts := SCR [] [] [].
Definition ss_dq0 := SS 0x5379c sr_dq0 [] kn_dq0 35.
Definition RUN_dq0 := sym_exec SEGS 100 true [0x538b0] scr_dq0 ss_dq0 [].

Definition scr_pdq0 : scripts := SCR [false] [] [].
Definition RES_pdq0 := Eval vm_compute in sym_exec SEGS 100 true [0x538b0] scr_pdq0 ss_dq0 [].
Lemma RES_pdq0_ok : sym_exec SEGS 100 true [0x538b0] scr_pdq0 (SS 0x5379c sr_dq0 [] kn_dq0 35) [] = RES_pdq0.
Proof. vm_compute. reflexivity. Qed.
End AXF_dq0.

Module AXF_dq0z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section DQ0.
Context {fx : FPState}.

Definition VALS_dq0 (G sc sp0 : Z) : list Z := [G; sc; sp0].

Record dq0_pre (regs : bvmap 5 word) (m : word -> option byte) (G sc sp0 : Z) : Prop := {
  dq0_R2 : getr regs 2 = wa (sp0 + -96) ;
  dq0_R9 : getr regs 9 = wa 621568 ;
  dq0_R10 : getr regs 10 = wa G ;
  dq0_R12 : getr regs 12 = wa sc ;
  dq0_R18 : getr regs 18 = wa 621720 ;
  dq0_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  dq0_rng_G : 1 <= G <= 2^63-1 ;
  dq0_rng_sc : 0 <= sc <= 63 ;
  dq0_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  dq0_ka1 : sp0 mod 16 = 0 ;
  dq0_ka4 : G mod 8 = 0 ;
  dq0_kw6 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  dq0_kd7 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024
}.


#[using="Type"] Lemma dq0_setup : forall regs m G sc sp0, dq0_pre regs m G sc sp0 ->
  regs_ok (Ez regs (VALS_dq0 G sc sp0)) AXF_dq0.sr_dq0 regs /\ know_ok SEGS (Ez regs (VALS_dq0 G sc sp0)) m AXF_dq0.kn_dq0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sc sp0 P. destruct P as [dq0_R2 dq0_R9 dq0_R10 dq0_R12 dq0_R18 dq0_HSTK dq0_rng_G dq0_rng_sc dq0_rng_sp0 dq0_ka1 dq0_ka4 dq0_kw6 dq0_kd7].
  set (E := Ez regs (VALS_dq0 G sc sp0)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_dq0.sr_dq0.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|].
    - rewrite dq0_R2, zeval_sound. cbn [zeval edenot AXF_dq0.e_G AXF_dq0.e_sc AXF_dq0.e_sp0 AXF_dq0.STK]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite dq0_R9. reflexivity.
    - rewrite dq0_R10. reflexivity.
    - rewrite dq0_R12. reflexivity.
    - rewrite dq0_R18. reflexivity. }
  unfold know_ok, AXF_dq0.kn_dq0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_dq0.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_dq0.e_G AXF_dq0.e_sc AXF_dq0.e_sp0 AXF_dq0.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ dq0_rng_G eq_refl eq_refl), ?(mod64_of_range sc _ _ dq0_rng_sc eq_refl eq_refl), ?(mod64_of_range sp0 _ _ dq0_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - dq0_rng_G dq0_rng_sc dq0_rng_sp0 dq0_ka1 dq0_ka4; lia).
  all: first [(clear - dq0_rng_G dq0_rng_sc dq0_rng_sp0 dq0_ka1 dq0_ka4 dq0_kd7; lia) | lia].
Qed.


Definition dq0_mem_pdq0 (m : word -> option byte) (regs : bvmap 5 word) (G sc sp0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem dq0_pdq0 : forall regs m rom G sc sp0, dq0_pre regs m G sc sp0 ->
  scs_denot SEGS m (Ez regs (VALS_dq0 G sc sp0)) (snd (fst AXF_dq0.RES_pdq0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5379c) m rom) (mkst R (wa 0x538b0) (dq0_mem_pdq0 m regs G sc sp0) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 621568 /\ getr R 10 = wa G /\ getr R 12 = wa sc /\ getr R 13 = wa 0 /\ getr R 18 = wa 621720 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 11; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sc sp0 P Hsc. destruct (dq0_setup regs m G sc sp0 P) as [HR HK].
  set (E := Ez regs (VALS_dq0 G sc sp0)) in *. destruct P as [dq0_R2 dq0_R9 dq0_R10 dq0_R12 dq0_R18 dq0_HSTK dq0_rng_G dq0_rng_sc dq0_rng_sp0 dq0_ka1 dq0_ka4 dq0_kw6 dq0_kd7].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x538b0] AXF_dq0.scr_pdq0 0x5379c AXF_dq0.sr_dq0 AXF_dq0.kn_dq0 35 _ _ _ E m rom regs AXF_dq0.RES_pdq0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_dq0.RES_pdq0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (dq0_mem_pdq0 m regs G sc sp0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold dq0_mem_pdq0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End DQ0.
End AXF_dq0z.

Module AXF_dq1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sc := EVar 33.
Definition e_sp0 := EVar 34.
Definition STK := SA e_sp0 (-1024).
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_dq1 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_G)) 12 (e_sc)) 18 (ELit 0x97c98)).
Definition kn_dq1 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_sc 0 47;
    KRange ACT 0 376;
    KWord (SA e_G 8) 8 e_G;
    KWord (SA ACT 621800) 8 e_G;
    KWr (SA e_G 0) (ELit 16);
    KWr (SA ACT 621800) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA ACT 621800) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA ACT 621800) (ELit 8) ].
Definition scr_dq1 : scripts := SCR [] [] [].
Definition ss_dq1 := SS 0x5379c sr_dq1 [] kn_dq1 35.
Definition RUN_dq1 := sym_exec SEGS 100 true [0x538b0] scr_dq1 ss_dq1 [].

Definition scr_pdq1 : scripts := SCR [false; false; false] [] [].
Definition RES_pdq1 := Eval vm_compute in sym_exec SEGS 100 true [0x538b0] scr_pdq1 ss_dq1 [].
Lemma RES_pdq1_ok : sym_exec SEGS 100 true [0x538b0] scr_pdq1 (SS 0x5379c sr_dq1 [] kn_dq1 35) [] = RES_pdq1.
Proof. vm_compute. reflexivity. Qed.
End AXF_dq1.

Module AXF_dq1z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section DQ1.
Context {fx : FPState}.

Definition VALS_dq1 (G sc sp0 : Z) : list Z := [G; sc; sp0].

Record dq1_pre (regs : bvmap 5 word) (m : word -> option byte) (G sc sp0 : Z) : Prop := {
  dq1_R2 : getr regs 2 = wa (sp0 + -96) ;
  dq1_R9 : getr regs 9 = wa 621568 ;
  dq1_R10 : getr regs 10 = wa G ;
  dq1_R12 : getr regs 12 = wa sc ;
  dq1_R18 : getr regs 18 = wa 621720 ;
  dq1_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  dq1_rng_G : 1 <= G <= 2^63-1 ;
  dq1_rng_sc : 0 <= sc <= 47 ;
  dq1_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  dq1_ka1 : sp0 mod 16 = 0 ;
  dq1_ka4 : G mod 8 = 0 ;
  dq1_kr6 : 0 <= 8 * sc <= 376 ;
  dq1_kw7 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  dq1_kw8 : rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  dq1_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  dq1_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 621800 + d)) k = true ;
  dq1_kd11 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  dq1_kd12 : sp0 + -1024 + 1024 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= sp0 + -1024 ;
  dq1_kd13 : G + 0 + 40 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= G + 0
}.


#[using="Type"] Lemma dq1_setup : forall regs m G sc sp0, dq1_pre regs m G sc sp0 ->
  regs_ok (Ez regs (VALS_dq1 G sc sp0)) AXF_dq1.sr_dq1 regs /\ know_ok SEGS (Ez regs (VALS_dq1 G sc sp0)) m AXF_dq1.kn_dq1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sc sp0 P. destruct P as [dq1_R2 dq1_R9 dq1_R10 dq1_R12 dq1_R18 dq1_HSTK dq1_rng_G dq1_rng_sc dq1_rng_sp0 dq1_ka1 dq1_ka4 dq1_kr6 dq1_kw7 dq1_kw8 dq1_kwr9 dq1_kwr10 dq1_kd11 dq1_kd12 dq1_kd13].
  set (E := Ez regs (VALS_dq1 G sc sp0)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_dq1.sr_dq1.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|].
    - rewrite dq1_R2, zeval_sound. cbn [zeval edenot AXF_dq1.e_G AXF_dq1.e_sc AXF_dq1.e_sp0 AXF_dq1.STK AXF_dq1.ACT]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite dq1_R9. reflexivity.
    - rewrite dq1_R10. reflexivity.
    - rewrite dq1_R12. reflexivity.
    - rewrite dq1_R18. reflexivity. }
  unfold know_ok, AXF_dq1.kn_dq1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_dq1.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_dq1.e_G AXF_dq1.e_sc AXF_dq1.e_sp0 AXF_dq1.STK AXF_dq1.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ dq1_rng_G eq_refl eq_refl), ?(mod64_of_range sc _ _ dq1_rng_sc eq_refl eq_refl), ?(mod64_of_range sp0 _ _ dq1_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply dq1_kwr9 | apply dq1_kwr10]; assumption).
  all: try (clear - dq1_rng_G dq1_rng_sc dq1_rng_sp0 dq1_ka1 dq1_ka4 dq1_kr6; lia).
  all: first [(clear - dq1_rng_G dq1_rng_sc dq1_rng_sp0 dq1_ka1 dq1_ka4 dq1_kr6 dq1_kd11; lia) | (clear - dq1_rng_G dq1_rng_sc dq1_rng_sp0 dq1_ka1 dq1_ka4 dq1_kr6 dq1_kd12; lia) | (clear - dq1_rng_G dq1_rng_sc dq1_rng_sp0 dq1_ka1 dq1_ka4 dq1_kr6 dq1_kd13; lia) | lia].
Qed.


Definition dq1_mem_pdq1 (m : word -> option byte) (regs : bvmap 5 word) (G sc sp0 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (8 * sc + 621800)) (word_to_le_bytes 8 (wa 0))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem dq1_pdq1 : forall regs m rom G sc sp0, dq1_pre regs m G sc sp0 ->
  scs_denot SEGS m (Ez regs (VALS_dq1 G sc sp0)) (snd (fst AXF_dq1.RES_pdq1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5379c) m rom) (mkst R (wa 0x538b0) (dq1_mem_pdq1 m regs G sc sp0) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 621568 /\ getr R 10 = wa G /\ getr R 11 = wa 0 /\ getr R 12 = wa G /\ getr R 13 = wa 0 /\ getr R 18 = wa 621720 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sc sp0 P Hsc. destruct (dq1_setup regs m G sc sp0 P) as [HR HK].
  set (E := Ez regs (VALS_dq1 G sc sp0)) in *. destruct P as [dq1_R2 dq1_R9 dq1_R10 dq1_R12 dq1_R18 dq1_HSTK dq1_rng_G dq1_rng_sc dq1_rng_sp0 dq1_ka1 dq1_ka4 dq1_kr6 dq1_kw7 dq1_kw8 dq1_kwr9 dq1_kwr10 dq1_kd11 dq1_kd12 dq1_kd13].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x538b0] AXF_dq1.scr_pdq1 0x5379c AXF_dq1.sr_dq1 AXF_dq1.kn_dq1 35 _ _ _ E m rom regs AXF_dq1.RES_pdq1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_dq1.RES_pdq1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (dq1_mem_pdq1 m regs G sc sp0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold dq1_mem_pdq1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End DQ1.
End AXF_dq1z.

Module AXF_dq3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sc := EVar 33.
Definition e_sp0 := EVar 34.
Definition e_NX := EVar 35.
Definition e_PR := EVar 36.
Definition e_H := EVar 37.
Definition STK := SA e_sp0 (-1024).
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_dq3 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_G)) 12 (e_sc)) 18 (ELit 0x97c98)).
Definition kn_dq3 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_sc 0 47;
    KRange ACT 0 376;
    KRange e_NX 1 (2^63-1);
    KRange e_PR 1 (2^63-1);
    KWord (SA e_G 8) 8 e_NX;
    KWord (SA e_G 0) 8 e_PR;
    KWord (SA ACT 621800) 8 e_H;
    KWr (SA e_G 0) (ELit 16);
    KWr (SA e_PR 8) (ELit 8);
    KWr (SA e_NX 0) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA ACT 621800) (ELit 8);
    KDisj STK (ELit 1024) (SA e_PR 8) (ELit 8);
    KDisj STK (ELit 1024) (SA e_NX 0) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA ACT 621800) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA e_PR 8) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA e_NX 0) (ELit 8);
    KDisj (SA ACT 621800) (ELit 8) (SA e_PR 8) (ELit 8);
    KDisj (SA ACT 621800) (ELit 8) (SA e_NX 0) (ELit 8) ].
Definition scr_dq3 : scripts := SCR [] [] [].
Definition ss_dq3 := SS 0x5379c sr_dq3 [] kn_dq3 38.
Definition RUN_dq3 := sym_exec SEGS 100 true [0x538b0] scr_dq3 ss_dq3 [].

Definition scr_pdq3 : scripts := SCR [false; true; true] [] [].
Definition RES_pdq3 := Eval vm_compute in sym_exec SEGS 100 true [0x538b0] scr_pdq3 ss_dq3 [].
Lemma RES_pdq3_ok : sym_exec SEGS 100 true [0x538b0] scr_pdq3 (SS 0x5379c sr_dq3 [] kn_dq3 38) [] = RES_pdq3.
Proof. vm_compute. reflexivity. Qed.
End AXF_dq3.

Module AXF_dq3z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section DQ3.
Context {fx : FPState}.

Definition VALS_dq3 (G sc sp0 NX PR H : Z) : list Z := [G; sc; sp0; NX; PR; H].

Record dq3_pre (regs : bvmap 5 word) (m : word -> option byte) (G sc sp0 NX PR H : Z) : Prop := {
  dq3_R2 : getr regs 2 = wa (sp0 + -96) ;
  dq3_R9 : getr regs 9 = wa 621568 ;
  dq3_R10 : getr regs 10 = wa G ;
  dq3_R12 : getr regs 12 = wa sc ;
  dq3_R18 : getr regs 18 = wa 621720 ;
  dq3_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  dq3_rng_G : 1 <= G <= 2^63-1 ;
  dq3_rng_sc : 0 <= sc <= 47 ;
  dq3_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  dq3_rng_NX : 1 <= NX <= 2^63-1 ;
  dq3_rng_PR : 1 <= PR <= 2^63-1 ;
  dq3_rng_H : 0 <= H <= 2^64-1 ;
  dq3_ka1 : sp0 mod 16 = 0 ;
  dq3_ka4 : G mod 8 = 0 ;
  dq3_kr6 : 0 <= 8 * sc <= 376 ;
  dq3_kw9 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa NX)) ;
  dq3_kw10 : rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa PR)) ;
  dq3_kw11 : rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa H)) ;
  dq3_kwr12 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  dq3_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (PR + 8 + d)) k = true ;
  dq3_kwr14 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (NX + 0 + d)) k = true ;
  dq3_kd15 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  dq3_kd16 : sp0 + -1024 + 1024 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= sp0 + -1024 ;
  dq3_kd17 : sp0 + -1024 + 1024 <= PR + 8 \/ PR + 8 + 8 <= sp0 + -1024 ;
  dq3_kd18 : sp0 + -1024 + 1024 <= NX + 0 \/ NX + 0 + 8 <= sp0 + -1024 ;
  dq3_kd19 : G + 0 + 40 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= G + 0 ;
  dq3_kd20 : G + 0 + 40 <= PR + 8 \/ PR + 8 + 8 <= G + 0 ;
  dq3_kd21 : G + 0 + 40 <= NX + 0 \/ NX + 0 + 8 <= G + 0 ;
  dq3_kd22 : 8 * sc + 621800 + 8 <= PR + 8 \/ PR + 8 + 8 <= 8 * sc + 621800 ;
  dq3_kd23 : 8 * sc + 621800 + 8 <= NX + 0 \/ NX + 0 + 8 <= 8 * sc + 621800
}.


#[using="Type"] Lemma dq3_setup : forall regs m G sc sp0 NX PR H, dq3_pre regs m G sc sp0 NX PR H ->
  regs_ok (Ez regs (VALS_dq3 G sc sp0 NX PR H)) AXF_dq3.sr_dq3 regs /\ know_ok SEGS (Ez regs (VALS_dq3 G sc sp0 NX PR H)) m AXF_dq3.kn_dq3.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sc sp0 NX PR H P. destruct P as [dq3_R2 dq3_R9 dq3_R10 dq3_R12 dq3_R18 dq3_HSTK dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kw9 dq3_kw10 dq3_kw11 dq3_kwr12 dq3_kwr13 dq3_kwr14 dq3_kd15 dq3_kd16 dq3_kd17 dq3_kd18 dq3_kd19 dq3_kd20 dq3_kd21 dq3_kd22 dq3_kd23].
  set (E := Ez regs (VALS_dq3 G sc sp0 NX PR H)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NX) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = PR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_dq3.sr_dq3.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|].
    - rewrite dq3_R2, zeval_sound. cbn [zeval edenot AXF_dq3.e_G AXF_dq3.e_sc AXF_dq3.e_sp0 AXF_dq3.e_NX AXF_dq3.e_PR AXF_dq3.e_H AXF_dq3.STK AXF_dq3.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite dq3_R9. reflexivity.
    - rewrite dq3_R10. reflexivity.
    - rewrite dq3_R12. reflexivity.
    - rewrite dq3_R18. reflexivity. }
  unfold know_ok, AXF_dq3.kn_dq3.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_dq3.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_dq3.e_G AXF_dq3.e_sc AXF_dq3.e_sp0 AXF_dq3.e_NX AXF_dq3.e_PR AXF_dq3.e_H AXF_dq3.STK AXF_dq3.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ dq3_rng_G eq_refl eq_refl), ?(mod64_of_range sc _ _ dq3_rng_sc eq_refl eq_refl), ?(mod64_of_range sp0 _ _ dq3_rng_sp0 eq_refl eq_refl), ?(mod64_of_range NX _ _ dq3_rng_NX eq_refl eq_refl), ?(mod64_of_range PR _ _ dq3_rng_PR eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply dq3_kwr12 | apply dq3_kwr13 | apply dq3_kwr14]; assumption).
  all: try (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6; lia).
  all: first [(clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd15; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd16; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd17; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd18; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd19; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd20; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd21; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd22; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd23; lia) | lia].
Qed.


Definition dq3_mem_pdq3 (m : word -> option byte) (regs : bvmap 5 word) (G sc sp0 NX PR H : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (m) (wa (PR + 8)) (word_to_le_bytes 8 (wa NX))) (wa (NX + 0)) (word_to_le_bytes 8 (wa PR))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem dq3_pdq3 : forall regs m rom G sc sp0 NX PR H, dq3_pre regs m G sc sp0 NX PR H ->
  scs_denot SEGS m (Ez regs (VALS_dq3 G sc sp0 NX PR H)) (snd (fst AXF_dq3.RES_pdq3)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5379c) m rom) (mkst R (wa 0x538b0) (dq3_mem_pdq3 m regs G sc sp0 NX PR H) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 621568 /\ getr R 10 = wa G /\ getr R 11 = wa ((8 * sc) + 621720) /\ getr R 12 = wa H /\ getr R 13 = wa H /\ getr R 14 = wa NX /\ getr R 18 = wa 621720 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sc sp0 NX PR H P Hsc. destruct (dq3_setup regs m G sc sp0 NX PR H P) as [HR HK].
  set (E := Ez regs (VALS_dq3 G sc sp0 NX PR H)) in *. destruct P as [dq3_R2 dq3_R9 dq3_R10 dq3_R12 dq3_R18 dq3_HSTK dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kw9 dq3_kw10 dq3_kw11 dq3_kwr12 dq3_kwr13 dq3_kwr14 dq3_kd15 dq3_kd16 dq3_kd17 dq3_kd18 dq3_kd19 dq3_kd20 dq3_kd21 dq3_kd22 dq3_kd23].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NX) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = PR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x538b0] AXF_dq3.scr_pdq3 0x5379c AXF_dq3.sr_dq3 AXF_dq3.kn_dq3 38 _ _ _ E m rom regs AXF_dq3.RES_pdq3_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_dq3.RES_pdq3 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (dq3_mem_pdq3 m regs G sc sp0 NX PR H) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold dq3_mem_pdq3. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End DQ3.
End AXF_dq3z.

Module AXF_fm0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sp0 := EVar 33.
Definition e_BASE := EVar 34.
Definition e_LEN := EVar 35.
Definition e_canary := EVar 36.
Definition e_ra := EVar 40.
Definition e_s0 := EVar 41.
Definition e_s1 := EVar 42.
Definition e_s2 := EVar 43.
Definition e_s3 := EVar 44.
Definition STK := SA e_sp0 (-1024).
Definition sr_fm0 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_G)) 11 (e_LEN)) 12 (e_BASE)) 18 (ELit 0x97c98)).
Definition kn_fm0 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KWord (SA (ELit 0) 0x97ca8) 8 (ELit 0);
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWord (SA e_sp0 (-48)) 8 e_canary;
    KWord (SA (ELit 0) 0x97c00) 8 e_canary;
    KWr (SA e_G 0) (ELit 40);
    KWr (SA (ELit 0) 0x97ca8) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x97ca8) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x97c00) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x97ca8) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x97c00) (ELit 8) ].
Definition scr_fm0 : scripts := SCR [] [] [].
Definition ss_fm0 := SS 0x5396c sr_fm0 [] kn_fm0 45.
Definition RUN_fm0 := sym_exec SEGS 100 true [] scr_fm0 ss_fm0 [].

Definition scr_pfm0 : scripts := SCR [] [] [].
Definition RES_pfm0 := Eval vm_compute in sym_exec SEGS 100 true [] scr_pfm0 ss_fm0 [].
Lemma RES_pfm0_ok : sym_exec SEGS 100 true [] scr_pfm0 (SS 0x5396c sr_fm0 [] kn_fm0 45) [] = RES_pfm0.
Proof. vm_compute. reflexivity. Qed.
End AXF_fm0.

Module AXF_fm0z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section FM0.
Context {fx : FPState}.

Definition VALS_fm0 (G sp0 BASE LEN canary ra s0 s1 s2 s3 : Z) : list Z := [G; sp0; BASE; LEN; canary; 0; 0; 0; ra; s0; s1; s2; s3].

Record fm0_pre (regs : bvmap 5 word) (m : word -> option byte) (G sp0 BASE LEN canary ra s0 s1 s2 s3 : Z) : Prop := {
  fm0_R2 : getr regs 2 = wa (sp0 + -96) ;
  fm0_R9 : getr regs 9 = wa 621568 ;
  fm0_R10 : getr regs 10 = wa G ;
  fm0_R11 : getr regs 11 = wa LEN ;
  fm0_R12 : getr regs 12 = wa BASE ;
  fm0_R18 : getr regs 18 = wa 621720 ;
  fm0_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  fm0_rng_G : 1 <= G <= 2^63-1 ;
  fm0_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  fm0_rng_BASE : 0 <= BASE <= 2^64-1 ;
  fm0_rng_LEN : 0 <= LEN <= 2^64-1 ;
  fm0_rng_canary : 0 <= canary <= 2^64-1 ;
  fm0_rng_ra : 0 <= ra <= 2^64-1 ;
  fm0_rng_s0 : 0 <= s0 <= 2^64-1 ;
  fm0_rng_s1 : 0 <= s1 <= 2^64-1 ;
  fm0_rng_s2 : 0 <= s2 <= 2^64-1 ;
  fm0_rng_s3 : 0 <= s3 <= 2^64-1 ;
  fm0_ka1 : sp0 mod 16 = 0 ;
  fm0_ka4 : G mod 8 = 0 ;
  fm0_kw5 : rdn SEGS m (wa (0 + 621736)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  fm0_kw6 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  fm0_kw7 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  fm0_kw8 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  fm0_kw9 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  fm0_kw10 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  fm0_kw11 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  fm0_kw12 : rdn SEGS m (wa (0 + 621568)) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  fm0_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 40 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  fm0_kwr14 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 621736 + d)) k = true ;
  fm0_kd15 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  fm0_kd16 : sp0 + -1024 + 1024 <= 0 + 621736 \/ 0 + 621736 + 8 <= sp0 + -1024 ;
  fm0_kd17 : sp0 + -1024 + 1024 <= 0 + 621568 \/ 0 + 621568 + 8 <= sp0 + -1024 ;
  fm0_kd18 : G + 0 + 40 <= 0 + 621736 \/ 0 + 621736 + 8 <= G + 0 ;
  fm0_kd19 : G + 0 + 40 <= 0 + 621568 \/ 0 + 621568 + 8 <= G + 0
}.


#[using="Type"] Lemma fm0_setup : forall regs m G sp0 BASE LEN canary ra s0 s1 s2 s3, fm0_pre regs m G sp0 BASE LEN canary ra s0 s1 s2 s3 ->
  regs_ok (Ez regs (VALS_fm0 G sp0 BASE LEN canary ra s0 s1 s2 s3)) AXF_fm0.sr_fm0 regs /\ know_ok SEGS (Ez regs (VALS_fm0 G sp0 BASE LEN canary ra s0 s1 s2 s3)) m AXF_fm0.kn_fm0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 BASE LEN canary ra s0 s1 s2 s3 P. destruct P as [fm0_R2 fm0_R9 fm0_R10 fm0_R11 fm0_R12 fm0_R18 fm0_HSTK fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kw5 fm0_kw6 fm0_kw7 fm0_kw8 fm0_kw9 fm0_kw10 fm0_kw11 fm0_kw12 fm0_kwr13 fm0_kwr14 fm0_kd15 fm0_kd16 fm0_kd17 fm0_kd18 fm0_kd19].
  set (E := Ez regs (VALS_fm0 G sp0 BASE LEN canary ra s0 s1 s2 s3)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = canary) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_fm0.sr_fm0.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite fm0_R2, zeval_sound. cbn [zeval edenot AXF_fm0.e_G AXF_fm0.e_sp0 AXF_fm0.e_BASE AXF_fm0.e_LEN AXF_fm0.e_canary AXF_fm0.e_ra AXF_fm0.e_s0 AXF_fm0.e_s1 AXF_fm0.e_s2 AXF_fm0.e_s3 AXF_fm0.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite fm0_R9. reflexivity.
    - rewrite fm0_R10. reflexivity.
    - rewrite fm0_R11. reflexivity.
    - rewrite fm0_R12. reflexivity.
    - rewrite fm0_R18. reflexivity. }
  unfold know_ok, AXF_fm0.kn_fm0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_fm0.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_fm0.e_G AXF_fm0.e_sp0 AXF_fm0.e_BASE AXF_fm0.e_LEN AXF_fm0.e_canary AXF_fm0.e_ra AXF_fm0.e_s0 AXF_fm0.e_s1 AXF_fm0.e_s2 AXF_fm0.e_s3 AXF_fm0.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ fm0_rng_G eq_refl eq_refl), ?(mod64_of_range sp0 _ _ fm0_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply fm0_kwr13 | apply fm0_kwr14]; assumption).
  all: try (clear - fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4; lia).
  all: first [(clear - fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kd15; lia) | (clear - fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kd16; lia) | (clear - fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kd17; lia) | (clear - fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kd18; lia) | (clear - fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kd19; lia) | lia].
Qed.


Definition fm0_mem_pfm0 (m : word -> option byte) (regs : bvmap 5 word) (G sp0 BASE LEN canary ra s0 s1 s2 s3 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (sp0 + -88)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -80)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -72)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -64)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -56)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 16)) (word_to_le_bytes 8 (wa 0))) (wa (G + 24)) (word_to_le_bytes 8 (wa 0))) (wa (G + 32)) (word_to_le_bytes 8 (wa 0))) (wa (G + 0)) (word_to_le_bytes 8 (wa G))) (wa (G + 8)) (word_to_le_bytes 8 (wa G))) (wa (0 + 621736)) (word_to_le_bytes 8 (wa G)).

#[using="Type"] Theorem fm0_pfm0 : forall regs m rom G sp0 BASE LEN canary ra s0 s1 s2 s3, fm0_pre regs m G sp0 BASE LEN canary ra s0 s1 s2 s3 ->
  scs_denot SEGS m (Ez regs (VALS_fm0 G sp0 BASE LEN canary ra s0 s1 s2 s3)) (snd (fst AXF_fm0.RES_pfm0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5396c) m rom) (mkst R (wa 0x53a58) (fm0_mem_pfm0 m regs G sp0 BASE LEN canary ra s0 s1 s2 s3) rom) /\
    getr R 1 = wa ra /\ getr R 2 = wa sp0 /\ getr R 8 = wa s0 /\ getr R 9 = wa s1 /\ getr R 10 = wa BASE /\ getr R 11 = wa LEN /\ getr R 12 = wa BASE /\ getr R 13 = wa canary /\ getr R 18 = wa s2 /\ getr R 19 = wa s3 /\ (forall k, In k [3; 4; 5; 6; 7; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 BASE LEN canary ra s0 s1 s2 s3 P Hsc. destruct (fm0_setup regs m G sp0 BASE LEN canary ra s0 s1 s2 s3 P) as [HR HK].
  set (E := Ez regs (VALS_fm0 G sp0 BASE LEN canary ra s0 s1 s2 s3)) in *. destruct P as [fm0_R2 fm0_R9 fm0_R10 fm0_R11 fm0_R12 fm0_R18 fm0_HSTK fm0_rng_G fm0_rng_sp0 fm0_rng_BASE fm0_rng_LEN fm0_rng_canary fm0_rng_ra fm0_rng_s0 fm0_rng_s1 fm0_rng_s2 fm0_rng_s3 fm0_ka1 fm0_ka4 fm0_kw5 fm0_kw6 fm0_kw7 fm0_kw8 fm0_kw9 fm0_kw10 fm0_kw11 fm0_kw12 fm0_kwr13 fm0_kwr14 fm0_kd15 fm0_kd16 fm0_kd17 fm0_kd18 fm0_kd19].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = canary) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [] AXF_fm0.scr_pfm0 0x5396c AXF_fm0.sr_fm0 AXF_fm0.kn_fm0 45 _ _ _ E m rom regs AXF_fm0.RES_pfm0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_fm0.RES_pfm0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (fm0_mem_pfm0 m regs G sp0 BASE LEN canary ra s0 s1 s2 s3) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold fm0_mem_pfm0. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End FM0.
End AXF_fm0z.

Module AXF_fm1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sp0 := EVar 33.
Definition e_BASE := EVar 34.
Definition e_LEN := EVar 35.
Definition e_canary := EVar 36.
Definition e_H := EVar 37.
Definition e_HP := EVar 38.
Definition e_ra := EVar 40.
Definition e_s0 := EVar 41.
Definition e_s1 := EVar 42.
Definition e_s2 := EVar 43.
Definition e_s3 := EVar 44.
Definition STK := SA e_sp0 (-1024).
Definition sr_fm1 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_G)) 11 (e_LEN)) 12 (e_BASE)) 18 (ELit 0x97c98)).
Definition kn_fm1 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_H 1 (2^63-1);
    KRange e_HP 1 (2^63-1);
    KWord (SA (ELit 0) 0x97ca8) 8 e_H;
    KWord (SA e_H 0) 8 e_HP;
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWord (SA e_sp0 (-48)) 8 e_canary;
    KWord (SA (ELit 0) 0x97c00) 8 e_canary;
    KWr (SA e_G 0) (ELit 40);
    KWr (SA e_H 0) (ELit 8);
    KWr (SA e_HP 8) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x97ca8) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x97c00) (ELit 8);
    KDisj STK (ELit 1024) (SA e_H 0) (ELit 40);
    KDisj STK (ELit 1024) (SA e_HP 0) (ELit 40);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x97ca8) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x97c00) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA e_H 0) (ELit 40);
    KDisj (SA e_G 0) (ELit 40) (SA e_HP 0) (ELit 40);
    KDisj (SA e_H 0) (ELit 40) (SA (ELit 0) 0x97c00) (ELit 8);
    KDisj (SA e_HP 0) (ELit 40) (SA (ELit 0) 0x97c00) (ELit 8);
    KDisj (SA e_H 0) (ELit 40) (SA (ELit 0) 0x97ca8) (ELit 8);
    KDisj (SA e_HP 0) (ELit 40) (SA (ELit 0) 0x97ca8) (ELit 8) ].
Definition scr_fm1 : scripts := SCR [] [] [].
Definition ss_fm1 := SS 0x5396c sr_fm1 [] kn_fm1 45.
Definition RUN_fm1 := sym_exec SEGS 100 true [] scr_fm1 ss_fm1 [].

Definition scr_pfm1 : scripts := SCR [] [] [].
Definition RES_pfm1 := Eval vm_compute in sym_exec SEGS 100 true [] scr_pfm1 ss_fm1 [].
Lemma RES_pfm1_ok : sym_exec SEGS 100 true [] scr_pfm1 (SS 0x5396c sr_fm1 [] kn_fm1 45) [] = RES_pfm1.
Proof. vm_compute. reflexivity. Qed.
End AXF_fm1.

Module AXF_fm1z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section FM1.
Context {fx : FPState}.

Definition VALS_fm1 (G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 : Z) : list Z := [G; sp0; BASE; LEN; canary; H; HP; 0; ra; s0; s1; s2; s3].

Record fm1_pre (regs : bvmap 5 word) (m : word -> option byte) (G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 : Z) : Prop := {
  fm1_R2 : getr regs 2 = wa (sp0 + -96) ;
  fm1_R9 : getr regs 9 = wa 621568 ;
  fm1_R10 : getr regs 10 = wa G ;
  fm1_R11 : getr regs 11 = wa LEN ;
  fm1_R12 : getr regs 12 = wa BASE ;
  fm1_R18 : getr regs 18 = wa 621720 ;
  fm1_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  fm1_rng_G : 1 <= G <= 2^63-1 ;
  fm1_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  fm1_rng_BASE : 0 <= BASE <= 2^64-1 ;
  fm1_rng_LEN : 0 <= LEN <= 2^64-1 ;
  fm1_rng_canary : 0 <= canary <= 2^64-1 ;
  fm1_rng_H : 1 <= H <= 2^63-1 ;
  fm1_rng_HP : 1 <= HP <= 2^63-1 ;
  fm1_rng_ra : 0 <= ra <= 2^64-1 ;
  fm1_rng_s0 : 0 <= s0 <= 2^64-1 ;
  fm1_rng_s1 : 0 <= s1 <= 2^64-1 ;
  fm1_rng_s2 : 0 <= s2 <= 2^64-1 ;
  fm1_rng_s3 : 0 <= s3 <= 2^64-1 ;
  fm1_ka1 : sp0 mod 16 = 0 ;
  fm1_ka4 : G mod 8 = 0 ;
  fm1_kw7 : rdn SEGS m (wa (0 + 621736)) 8 = Some (word_to_le_bytes 8 (wa H)) ;
  fm1_kw8 : rdn SEGS m (wa (H + 0)) 8 = Some (word_to_le_bytes 8 (wa HP)) ;
  fm1_kw9 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  fm1_kw10 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  fm1_kw11 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  fm1_kw12 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  fm1_kw13 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  fm1_kw14 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  fm1_kw15 : rdn SEGS m (wa (0 + 621568)) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  fm1_kwr16 : forall d k, 0 <= d -> d + Z.of_nat k <= 40 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  fm1_kwr17 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (H + 0 + d)) k = true ;
  fm1_kwr18 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (HP + 8 + d)) k = true ;
  fm1_kd19 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  fm1_kd20 : sp0 + -1024 + 1024 <= 0 + 621736 \/ 0 + 621736 + 8 <= sp0 + -1024 ;
  fm1_kd21 : sp0 + -1024 + 1024 <= 0 + 621568 \/ 0 + 621568 + 8 <= sp0 + -1024 ;
  fm1_kd22 : sp0 + -1024 + 1024 <= H + 0 \/ H + 0 + 40 <= sp0 + -1024 ;
  fm1_kd23 : sp0 + -1024 + 1024 <= HP + 0 \/ HP + 0 + 40 <= sp0 + -1024 ;
  fm1_kd24 : G + 0 + 40 <= 0 + 621736 \/ 0 + 621736 + 8 <= G + 0 ;
  fm1_kd25 : G + 0 + 40 <= 0 + 621568 \/ 0 + 621568 + 8 <= G + 0 ;
  fm1_kd26 : G + 0 + 40 <= H + 0 \/ H + 0 + 40 <= G + 0 ;
  fm1_kd27 : G + 0 + 40 <= HP + 0 \/ HP + 0 + 40 <= G + 0 ;
  fm1_kd28 : H + 0 + 40 <= 0 + 621568 \/ 0 + 621568 + 8 <= H + 0 ;
  fm1_kd29 : HP + 0 + 40 <= 0 + 621568 \/ 0 + 621568 + 8 <= HP + 0 ;
  fm1_kd30 : H + 0 + 40 <= 0 + 621736 \/ 0 + 621736 + 8 <= H + 0 ;
  fm1_kd31 : HP + 0 + 40 <= 0 + 621736 \/ 0 + 621736 + 8 <= HP + 0
}.


#[using="Type"] Lemma fm1_setup : forall regs m G sp0 BASE LEN canary H HP ra s0 s1 s2 s3, fm1_pre regs m G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 ->
  regs_ok (Ez regs (VALS_fm1 G sp0 BASE LEN canary H HP ra s0 s1 s2 s3)) AXF_fm1.sr_fm1 regs /\ know_ok SEGS (Ez regs (VALS_fm1 G sp0 BASE LEN canary H HP ra s0 s1 s2 s3)) m AXF_fm1.kn_fm1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 P. destruct P as [fm1_R2 fm1_R9 fm1_R10 fm1_R11 fm1_R12 fm1_R18 fm1_HSTK fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kw7 fm1_kw8 fm1_kw9 fm1_kw10 fm1_kw11 fm1_kw12 fm1_kw13 fm1_kw14 fm1_kw15 fm1_kwr16 fm1_kwr17 fm1_kwr18 fm1_kd19 fm1_kd20 fm1_kd21 fm1_kd22 fm1_kd23 fm1_kd24 fm1_kd25 fm1_kd26 fm1_kd27 fm1_kd28 fm1_kd29 fm1_kd30 fm1_kd31].
  set (E := Ez regs (VALS_fm1 G sp0 BASE LEN canary H HP ra s0 s1 s2 s3)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = canary) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = HP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_fm1.sr_fm1.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite fm1_R2, zeval_sound. cbn [zeval edenot AXF_fm1.e_G AXF_fm1.e_sp0 AXF_fm1.e_BASE AXF_fm1.e_LEN AXF_fm1.e_canary AXF_fm1.e_H AXF_fm1.e_HP AXF_fm1.e_ra AXF_fm1.e_s0 AXF_fm1.e_s1 AXF_fm1.e_s2 AXF_fm1.e_s3 AXF_fm1.STK]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite fm1_R9. reflexivity.
    - rewrite fm1_R10. reflexivity.
    - rewrite fm1_R11. reflexivity.
    - rewrite fm1_R12. reflexivity.
    - rewrite fm1_R18. reflexivity. }
  unfold know_ok, AXF_fm1.kn_fm1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_fm1.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_fm1.e_G AXF_fm1.e_sp0 AXF_fm1.e_BASE AXF_fm1.e_LEN AXF_fm1.e_canary AXF_fm1.e_H AXF_fm1.e_HP AXF_fm1.e_ra AXF_fm1.e_s0 AXF_fm1.e_s1 AXF_fm1.e_s2 AXF_fm1.e_s3 AXF_fm1.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ fm1_rng_G eq_refl eq_refl), ?(mod64_of_range sp0 _ _ fm1_rng_sp0 eq_refl eq_refl), ?(mod64_of_range H _ _ fm1_rng_H eq_refl eq_refl), ?(mod64_of_range HP _ _ fm1_rng_HP eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply fm1_kwr16 | apply fm1_kwr17 | apply fm1_kwr18]; assumption).
  all: try (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4; lia).
  all: first [(clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd19; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd20; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd21; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd22; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd23; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd24; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd25; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd26; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd27; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd28; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd29; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd30; lia) | (clear - fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kd31; lia) | lia].
Qed.


Definition fm1_mem_pfm1 (m : word -> option byte) (regs : bvmap 5 word) (G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (sp0 + -88)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -80)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -72)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -64)) (word_to_le_bytes 8 (wa 0))) (wa (sp0 + -56)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 16)) (word_to_le_bytes 8 (wa 0))) (wa (G + 24)) (word_to_le_bytes 8 (wa 0))) (wa (G + 32)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa H))) (wa (G + 0)) (word_to_le_bytes 8 (wa HP))) (wa (HP + 8)) (word_to_le_bytes 8 (wa G))) (wa (H + 0)) (word_to_le_bytes 8 (wa G)).

#[using="Type"] Theorem fm1_pfm1 : forall regs m rom G sp0 BASE LEN canary H HP ra s0 s1 s2 s3, fm1_pre regs m G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 ->
  scs_denot SEGS m (Ez regs (VALS_fm1 G sp0 BASE LEN canary H HP ra s0 s1 s2 s3)) (snd (fst AXF_fm1.RES_pfm1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5396c) m rom) (mkst R (wa 0x53a58) (fm1_mem_pfm1 m regs G sp0 BASE LEN canary H HP ra s0 s1 s2 s3) rom) /\
    getr R 1 = wa ra /\ getr R 2 = wa sp0 /\ getr R 8 = wa s0 /\ getr R 9 = wa s1 /\ getr R 10 = wa BASE /\ getr R 11 = wa LEN /\ getr R 12 = wa BASE /\ getr R 13 = wa canary /\ getr R 18 = wa s2 /\ getr R 19 = wa s3 /\ (forall k, In k [3; 4; 5; 6; 7; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 P Hsc. destruct (fm1_setup regs m G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 P) as [HR HK].
  set (E := Ez regs (VALS_fm1 G sp0 BASE LEN canary H HP ra s0 s1 s2 s3)) in *. destruct P as [fm1_R2 fm1_R9 fm1_R10 fm1_R11 fm1_R12 fm1_R18 fm1_HSTK fm1_rng_G fm1_rng_sp0 fm1_rng_BASE fm1_rng_LEN fm1_rng_canary fm1_rng_H fm1_rng_HP fm1_rng_ra fm1_rng_s0 fm1_rng_s1 fm1_rng_s2 fm1_rng_s3 fm1_ka1 fm1_ka4 fm1_kw7 fm1_kw8 fm1_kw9 fm1_kw10 fm1_kw11 fm1_kw12 fm1_kw13 fm1_kw14 fm1_kw15 fm1_kwr16 fm1_kwr17 fm1_kwr18 fm1_kd19 fm1_kd20 fm1_kd21 fm1_kd22 fm1_kd23 fm1_kd24 fm1_kd25 fm1_kd26 fm1_kd27 fm1_kd28 fm1_kd29 fm1_kd30 fm1_kd31].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = canary) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = HP) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [] AXF_fm1.scr_pfm1 0x5396c AXF_fm1.sr_fm1 AXF_fm1.kn_fm1 45 _ _ _ E m rom regs AXF_fm1.RES_pfm1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_fm1.RES_pfm1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (fm1_mem_pfm1 m regs G sp0 BASE LEN canary H HP ra s0 s1 s2 s3) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold fm1_mem_pfm1. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End FM1.
End AXF_fm1z.

Module AXF_m1f.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G1 := EVar 33.
Definition e_freed1 := EVar 34.
Definition e_W1 := EVar 35.
Definition e_nx1 := EVar 36.
Definition e_freed2 := EVar 37.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 621800.
Definition sr_m1f := (sr_upd (sr_upd sr_id 10 (e_G1)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 621800))).
Definition kn_m1f : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G1 1 (2^63-1);
    KAlign e_G1 8;
    KRange e_freed1 0 (2^32-1);
    KRange e_W1 0 (2^63-1);
    KRange e_nx1 1 (2^63-1);
    KAlign e_nx1 8;
    KRange e_freed2 0 (2^32-1);
    KWord (SA e_G1 28) 4 e_freed1;
    KWord (SA e_G1 32) 8 e_W1;
    KWord (SA e_G1 8) 8 e_nx1;
    KWord (SA e_nx1 28) 4 e_freed2;
    KWr ACT (ELit 8);
    KDisj ACT (ELit 8) (SA e_nx1 0) (ELit 40) ].
Definition scr_m1f : scripts := SCR [false; false] [] [].
Definition ss_m1f := SS 0x54170 sr_m1f [] kn_m1f 38.
Definition RUN_m1f := sym_exec SEGS 100 true [0x5419c] scr_m1f ss_m1f [].

Definition scr_pm1f : scripts := SCR [false; false] [] [].
Definition RES_pm1f := Eval vm_compute in sym_exec SEGS 100 true [0x5419c] scr_pm1f ss_m1f [].
Lemma RES_pm1f_ok : sym_exec SEGS 100 true [0x5419c] scr_pm1f (SS 0x54170 sr_m1f [] kn_m1f 38) [] = RES_pm1f.
Proof. vm_compute. reflexivity. Qed.
End AXF_m1f.

Module AXF_m1fz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section M1F.
Context {fx : FPState}.

Definition VALS_m1f (sc G1 freed1 W1 nx1 freed2 : Z) : list Z := [sc; G1; freed1; W1; nx1; freed2].

Record m1f_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G1 freed1 W1 nx1 freed2 : Z) : Prop := {
  m1f_R10 : getr regs 10 = wa G1 ;
  m1f_R21 : getr regs 21 = wa ((8 * sc) + 621800) ;
  m1f_rng_sc : 0 <= sc <= 47 ;
  m1f_rng_G1 : 1 <= G1 <= 2^63-1 ;
  m1f_rng_freed1 : 0 <= freed1 <= 2^32-1 ;
  m1f_rng_W1 : 0 <= W1 <= 2^63-1 ;
  m1f_rng_nx1 : 1 <= nx1 <= 2^63-1 ;
  m1f_rng_freed2 : 0 <= freed2 <= 2^32-1 ;
  m1f_ka2 : G1 mod 8 = 0 ;
  m1f_ka6 : nx1 mod 8 = 0 ;
  m1f_kw8 : rdn SEGS m (wa (G1 + 28)) 4 = Some (word_to_le_bytes 4 (wa freed1)) ;
  m1f_kw9 : rdn SEGS m (wa (G1 + 32)) 8 = Some (word_to_le_bytes 8 (wa W1)) ;
  m1f_kw10 : rdn SEGS m (wa (G1 + 8)) 8 = Some (word_to_le_bytes 8 (wa nx1)) ;
  m1f_kw11 : rdn SEGS m (wa (nx1 + 28)) 4 = Some (word_to_le_bytes 4 (wa freed2)) ;
  m1f_kwr12 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 621800 + d)) k = true ;
  m1f_kd13 : 8 * sc + 621800 + 8 <= nx1 + 0 \/ nx1 + 0 + 40 <= 8 * sc + 621800
}.


#[using="Type"] Lemma m1f_setup : forall regs m sc G1 freed1 W1 nx1 freed2, m1f_pre regs m sc G1 freed1 W1 nx1 freed2 ->
  regs_ok (Ez regs (VALS_m1f sc G1 freed1 W1 nx1 freed2)) AXF_m1f.sr_m1f regs /\ know_ok SEGS (Ez regs (VALS_m1f sc G1 freed1 W1 nx1 freed2)) m AXF_m1f.kn_m1f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G1 freed1 W1 nx1 freed2 P. destruct P as [m1f_R10 m1f_R21 m1f_rng_sc m1f_rng_G1 m1f_rng_freed1 m1f_rng_W1 m1f_rng_nx1 m1f_rng_freed2 m1f_ka2 m1f_ka6 m1f_kw8 m1f_kw9 m1f_kw10 m1f_kw11 m1f_kwr12 m1f_kd13].
  set (E := Ez regs (VALS_m1f sc G1 freed1 W1 nx1 freed2)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = nx1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_m1f.sr_m1f.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|].
    - rewrite m1f_R10. reflexivity.
    - rewrite m1f_R21, zeval_sound. cbn [zeval edenot AXF_m1f.e_sc AXF_m1f.e_G1 AXF_m1f.e_freed1 AXF_m1f.e_W1 AXF_m1f.e_nx1 AXF_m1f.e_freed2 AXF_m1f.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_m1f.kn_m1f.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_m1f.e_sc AXF_m1f.e_G1 AXF_m1f.e_freed1 AXF_m1f.e_W1 AXF_m1f.e_nx1 AXF_m1f.e_freed2 AXF_m1f.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ m1f_rng_sc eq_refl eq_refl), ?(mod64_of_range G1 _ _ m1f_rng_G1 eq_refl eq_refl), ?(mod64_of_range freed1 _ _ m1f_rng_freed1 eq_refl eq_refl), ?(mod64_of_range W1 _ _ m1f_rng_W1 eq_refl eq_refl), ?(mod64_of_range nx1 _ _ m1f_rng_nx1 eq_refl eq_refl), ?(mod64_of_range freed2 _ _ m1f_rng_freed2 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply m1f_kwr12]; assumption).
  all: try (clear - m1f_rng_sc m1f_rng_G1 m1f_rng_freed1 m1f_rng_W1 m1f_rng_nx1 m1f_rng_freed2 m1f_ka2 m1f_ka6; lia).
  all: first [(clear - m1f_rng_sc m1f_rng_G1 m1f_rng_freed1 m1f_rng_W1 m1f_rng_nx1 m1f_rng_freed2 m1f_ka2 m1f_ka6 m1f_kd13; lia) | lia].
Qed.


Definition m1f_mem_pm1f (m : word -> option byte) (regs : bvmap 5 word) (sc G1 freed1 W1 nx1 freed2 : Z) : word -> option byte :=
  wbytes (m) (wa (8 * sc + 621800)) (word_to_le_bytes 8 (wa nx1)).

#[using="Type"] Theorem m1f_pm1f : forall regs m rom sc G1 freed1 W1 nx1 freed2, m1f_pre regs m sc G1 freed1 W1 nx1 freed2 ->
  scs_denot SEGS m (Ez regs (VALS_m1f sc G1 freed1 W1 nx1 freed2)) (snd (fst AXF_m1f.RES_pm1f)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54170) m rom) (mkst R (wa 0x5419c) (m1f_mem_pm1f m regs sc G1 freed1 W1 nx1 freed2) rom) /\
    getr R 10 = wa nx1 /\ getr R 12 = wa (Z.land W1 32) /\ getr R 13 = wa (ext_Z true 0 4 freed2) /\ getr R 14 = wa 2 /\ getr R 21 = wa ((8 * sc) + 621800) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G1 freed1 W1 nx1 freed2 P Hsc. destruct (m1f_setup regs m sc G1 freed1 W1 nx1 freed2 P) as [HR HK].
  set (E := Ez regs (VALS_m1f sc G1 freed1 W1 nx1 freed2)) in *. destruct P as [m1f_R10 m1f_R21 m1f_rng_sc m1f_rng_G1 m1f_rng_freed1 m1f_rng_W1 m1f_rng_nx1 m1f_rng_freed2 m1f_ka2 m1f_ka6 m1f_kw8 m1f_kw9 m1f_kw10 m1f_kw11 m1f_kwr12 m1f_kd13].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = nx1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5419c] AXF_m1f.scr_pm1f 0x54170 AXF_m1f.sr_m1f AXF_m1f.kn_m1f 38 _ _ _ E m rom regs AXF_m1f.RES_pm1f_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_m1f.RES_pm1f fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (m1f_mem_pm1f m regs sc G1 freed1 W1 nx1 freed2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold m1f_mem_pm1f. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End M1F.
End AXF_m1fz.

Module AXF_m2b.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G2 := EVar 33.
Definition e_freed2 := EVar 34.
Definition e_mem2 := EVar 35.
Definition e_hb := EVar 36.
Definition e_nx2 := EVar 37.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 621800.
Definition sr_m2b := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_G2)) 13 (EExt true 0 4 e_freed2)) 14 (ELit 2)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 621800))).
Definition kn_m2b : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G2 1 (2^63-1);
    KAlign e_G2 8;
    KRange e_freed2 0 (2^32-1);
    KRange e_mem2 1 (2^63-1);
    KRange e_hb 0 255;
    KRange e_nx2 1 (2^63-1);
    KAlign e_nx2 8;
    KWord (SA e_G2 16) 8 e_mem2;
    KWord (SA e_mem2 8) 1 e_hb;
    KWord (SA e_G2 8) 8 e_nx2;
    KWord (SA e_nx2 24) 4 (ELit 0);
    KWr ACT (ELit 8);
    KDisj ACT (ELit 8) (SA e_nx2 0) (ELit 40) ].
Definition scr_m2b : scripts := SCR [false; false] [] [].
Definition ss_m2b := SS 0x5419c sr_m2b [] kn_m2b 38.
Definition RUN_m2b := sym_exec SEGS 100 true [0x541d0] scr_m2b ss_m2b [].

Definition scr_pm2b : scripts := SCR [false; false] [] [].
Definition RES_pm2b := Eval vm_compute in sym_exec SEGS 100 true [0x541d0] scr_pm2b ss_m2b [].
Lemma RES_pm2b_ok : sym_exec SEGS 100 true [0x541d0] scr_pm2b (SS 0x5419c sr_m2b [] kn_m2b 38) [] = RES_pm2b.
Proof. vm_compute. reflexivity. Qed.
End AXF_m2b.

Module AXF_m2bz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section M2B.
Context {fx : FPState}.

Definition VALS_m2b (sc G2 freed2 mem2 hb nx2 : Z) : list Z := [sc; G2; freed2; mem2; hb; nx2].

Record m2b_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G2 freed2 mem2 hb nx2 : Z) : Prop := {
  m2b_R10 : getr regs 10 = wa G2 ;
  m2b_R13 : getr regs 13 = wa (ext_Z true 0 4 freed2) ;
  m2b_R14 : getr regs 14 = wa 2 ;
  m2b_R21 : getr regs 21 = wa ((8 * sc) + 621800) ;
  m2b_rng_sc : 0 <= sc <= 47 ;
  m2b_rng_G2 : 1 <= G2 <= 2^63-1 ;
  m2b_rng_freed2 : 0 <= freed2 <= 2^32-1 ;
  m2b_rng_mem2 : 1 <= mem2 <= 2^63-1 ;
  m2b_rng_hb : 0 <= hb <= 255 ;
  m2b_rng_nx2 : 1 <= nx2 <= 2^63-1 ;
  m2b_ka2 : G2 mod 8 = 0 ;
  m2b_ka7 : nx2 mod 8 = 0 ;
  m2b_kw8 : rdn SEGS m (wa (G2 + 16)) 8 = Some (word_to_le_bytes 8 (wa mem2)) ;
  m2b_kw9 : rdn SEGS m (wa (mem2 + 8)) 1 = Some (word_to_le_bytes 1 (wa hb)) ;
  m2b_kw10 : rdn SEGS m (wa (G2 + 8)) 8 = Some (word_to_le_bytes 8 (wa nx2)) ;
  m2b_kw11 : rdn SEGS m (wa (nx2 + 24)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  m2b_kwr12 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 621800 + d)) k = true ;
  m2b_kd13 : 8 * sc + 621800 + 8 <= nx2 + 0 \/ nx2 + 0 + 40 <= 8 * sc + 621800
}.


#[using="Type"] Lemma m2b_setup : forall regs m sc G2 freed2 mem2 hb nx2, m2b_pre regs m sc G2 freed2 mem2 hb nx2 ->
  regs_ok (Ez regs (VALS_m2b sc G2 freed2 mem2 hb nx2)) AXF_m2b.sr_m2b regs /\ know_ok SEGS (Ez regs (VALS_m2b sc G2 freed2 mem2 hb nx2)) m AXF_m2b.kn_m2b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G2 freed2 mem2 hb nx2 P. destruct P as [m2b_R10 m2b_R13 m2b_R14 m2b_R21 m2b_rng_sc m2b_rng_G2 m2b_rng_freed2 m2b_rng_mem2 m2b_rng_hb m2b_rng_nx2 m2b_ka2 m2b_ka7 m2b_kw8 m2b_kw9 m2b_kw10 m2b_kw11 m2b_kwr12 m2b_kd13].
  set (E := Ez regs (VALS_m2b sc G2 freed2 mem2 hb nx2)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = nx2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_m2b.sr_m2b.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite m2b_R10. reflexivity.
    - rewrite m2b_R13, zeval_sound. cbn [zeval edenot AXF_m2b.e_sc AXF_m2b.e_G2 AXF_m2b.e_freed2 AXF_m2b.e_mem2 AXF_m2b.e_hb AXF_m2b.e_nx2 AXF_m2b.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite m2b_R14. reflexivity.
    - rewrite m2b_R21, zeval_sound. cbn [zeval edenot AXF_m2b.e_sc AXF_m2b.e_G2 AXF_m2b.e_freed2 AXF_m2b.e_mem2 AXF_m2b.e_hb AXF_m2b.e_nx2 AXF_m2b.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_m2b.kn_m2b.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_m2b.e_sc AXF_m2b.e_G2 AXF_m2b.e_freed2 AXF_m2b.e_mem2 AXF_m2b.e_hb AXF_m2b.e_nx2 AXF_m2b.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ m2b_rng_sc eq_refl eq_refl), ?(mod64_of_range G2 _ _ m2b_rng_G2 eq_refl eq_refl), ?(mod64_of_range freed2 _ _ m2b_rng_freed2 eq_refl eq_refl), ?(mod64_of_range mem2 _ _ m2b_rng_mem2 eq_refl eq_refl), ?(mod64_of_range hb _ _ m2b_rng_hb eq_refl eq_refl), ?(mod64_of_range nx2 _ _ m2b_rng_nx2 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply m2b_kwr12]; assumption).
  all: try (clear - m2b_rng_sc m2b_rng_G2 m2b_rng_freed2 m2b_rng_mem2 m2b_rng_hb m2b_rng_nx2 m2b_ka2 m2b_ka7; lia).
  all: first [(clear - m2b_rng_sc m2b_rng_G2 m2b_rng_freed2 m2b_rng_mem2 m2b_rng_hb m2b_rng_nx2 m2b_ka2 m2b_ka7 m2b_kd13; lia) | lia].
Qed.


Definition m2b_mem_pm2b (m : word -> option byte) (regs : bvmap 5 word) (sc G2 freed2 mem2 hb nx2 : Z) : word -> option byte :=
  wbytes (m) (wa (8 * sc + 621800)) (word_to_le_bytes 8 (wa nx2)).

#[using="Type"] Theorem m2b_pm2b : forall regs m rom sc G2 freed2 mem2 hb nx2, m2b_pre regs m sc G2 freed2 mem2 hb nx2 ->
  scs_denot SEGS m (Ez regs (VALS_m2b sc G2 freed2 mem2 hb nx2)) (snd (fst AXF_m2b.RES_pm2b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5419c) m rom) (mkst R (wa 0x541d0) (m2b_mem_pm2b m regs sc G2 freed2 mem2 hb nx2) rom) /\
    getr R 10 = wa nx2 /\ getr R 11 = wa 0 /\ getr R 12 = wa hb /\ getr R 13 = wa nx2 /\ getr R 21 = wa ((8 * sc) + 621800) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G2 freed2 mem2 hb nx2 P Hsc. destruct (m2b_setup regs m sc G2 freed2 mem2 hb nx2 P) as [HR HK].
  set (E := Ez regs (VALS_m2b sc G2 freed2 mem2 hb nx2)) in *. destruct P as [m2b_R10 m2b_R13 m2b_R14 m2b_R21 m2b_rng_sc m2b_rng_G2 m2b_rng_freed2 m2b_rng_mem2 m2b_rng_hb m2b_rng_nx2 m2b_ka2 m2b_ka7 m2b_kw8 m2b_kw9 m2b_kw10 m2b_kw11 m2b_kwr12 m2b_kd13].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = nx2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x541d0] AXF_m2b.scr_pm2b 0x5419c AXF_m2b.sr_m2b AXF_m2b.kn_m2b 38 _ _ _ E m rom regs AXF_m2b.RES_pm2b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_m2b.RES_pm2b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (m2b_mem_pm2b m regs sc G2 freed2 mem2 hb nx2) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold m2b_mem_pm2b. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End M2B.
End AXF_m2bz.

Module AXF_md1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_n := EVar 32.
Definition e_res := EVar 33.
Definition e_seq := EVar 34.
Definition sr_md1 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 621712)) 10 (e_res)) 18 (ELit 18446744073709551615)) 19 (EAlu ALU_ADD e_n (ELit 20))).
Definition kn_md1 : list kentry :=
  [ KRange e_n 131052 (2^26);
    KRange e_res 4096 (2^47);
    KRange e_seq 0 255;
    KWord (SA (ELit 0) 0x97c23) 1 (ELit 0);
    KWord (SA (ELit 0) 622632) 1 e_seq;
    KWr (SA (ELit 0) 622632) (ELit 1);
    KWr (SA (ELit 0) 622568) (ELit 32) ].
Definition scr_md1 : scripts := SCR [] [] [].
Definition ss_md1 := SS 0x53dd0 sr_md1 [] kn_md1 35.
Definition RUN_md1 := sym_exec SEGS 100 true [0x53a60] scr_md1 ss_md1 [].

Definition scr_pmd1i : scripts := SCR [true] [] [].
Definition RES_pmd1i := Eval vm_compute in sym_exec SEGS 100 true [0x53a60] scr_pmd1i ss_md1 [].
Lemma RES_pmd1i_ok : sym_exec SEGS 100 true [0x53a60] scr_pmd1i (SS 0x53dd0 sr_md1 [] kn_md1 35) [] = RES_pmd1i.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmd1w : scripts := SCR [false] [] [].
Definition RES_pmd1w := Eval vm_compute in sym_exec SEGS 100 true [0x53a60] scr_pmd1w ss_md1 [].
Lemma RES_pmd1w_ok : sym_exec SEGS 100 true [0x53a60] scr_pmd1w (SS 0x53dd0 sr_md1 [] kn_md1 35) [] = RES_pmd1w.
Proof. vm_compute. reflexivity. Qed.
End AXF_md1.

Module AXF_md1z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MD1.
Context {fx : FPState}.

Definition VALS_md1 (n res seq : Z) : list Z := [n; res; seq].

Record md1_pre (regs : bvmap 5 word) (m : word -> option byte) (n res seq : Z) : Prop := {
  md1_R8 : getr regs 8 = wa n ;
  md1_R9 : getr regs 9 = wa 621712 ;
  md1_R10 : getr regs 10 = wa res ;
  md1_R18 : getr regs 18 = wa 18446744073709551615 ;
  md1_R19 : getr regs 19 = wa (n + 20) ;
  md1_rng_n : 131052 <= n <= 2^26 ;
  md1_rng_res : 4096 <= res <= 2^47 ;
  md1_rng_seq : 0 <= seq <= 255 ;
  md1_kw3 : rdn SEGS m (wa (0 + 621603)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  md1_kw4 : rdn SEGS m (wa (0 + 622632)) 1 = Some (word_to_le_bytes 1 (wa seq)) ;
  md1_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (0 + 622632 + d)) k = true ;
  md1_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (0 + 622568 + d)) k = true
}.


#[using="Type"] Lemma md1_setup : forall regs m n res seq, md1_pre regs m n res seq ->
  regs_ok (Ez regs (VALS_md1 n res seq)) AXF_md1.sr_md1 regs /\ know_ok SEGS (Ez regs (VALS_md1 n res seq)) m AXF_md1.kn_md1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n res seq P. destruct P as [md1_R8 md1_R9 md1_R10 md1_R18 md1_R19 md1_rng_n md1_rng_res md1_rng_seq md1_kw3 md1_kw4 md1_kwr5 md1_kwr6].
  set (E := Ez regs (VALS_md1 n res seq)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_md1.sr_md1.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|].
    - rewrite md1_R8. reflexivity.
    - rewrite md1_R9. reflexivity.
    - rewrite md1_R10. reflexivity.
    - rewrite md1_R18. reflexivity.
    - rewrite md1_R19, zeval_sound. cbn [zeval edenot AXF_md1.e_n AXF_md1.e_res AXF_md1.e_seq]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_md1.kn_md1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_md1.e_n AXF_md1.e_res AXF_md1.e_seq a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ md1_rng_n eq_refl eq_refl), ?(mod64_of_range res _ _ md1_rng_res eq_refl eq_refl), ?(mod64_of_range seq _ _ md1_rng_seq eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply md1_kwr5 | apply md1_kwr6]; assumption).
  all: try (clear - md1_rng_n md1_rng_res md1_rng_seq; lia).
  all: first [lia].
Qed.


Definition md1_mem_pmd1i (m : word -> option byte) (regs : bvmap 5 word) (n res seq : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 622632)) (word_to_le_bytes 1 (wa (seq + 1))).

#[using="Type"] Theorem md1_pmd1i : forall regs m rom n res seq, md1_pre regs m n res seq ->
  scs_denot SEGS m (Ez regs (VALS_md1 n res seq)) (snd (fst AXF_md1.RES_pmd1i)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53dd0) m rom) (mkst R (wa 0x53a60) (md1_mem_pmd1i m regs n res seq) rom) /\
    getr R 1 = wa 343748 /\ getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa (seq + 1) /\ getr R 11 = wa 255 /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa (n + 20) /\ getr R 20 = wa res /\ (forall k, In k [2; 3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n res seq P Hsc. destruct (md1_setup regs m n res seq P) as [HR HK].
  set (E := Ez regs (VALS_md1 n res seq)) in *. destruct P as [md1_R8 md1_R9 md1_R10 md1_R18 md1_R19 md1_rng_n md1_rng_res md1_rng_seq md1_kw3 md1_kw4 md1_kwr5 md1_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53a60] AXF_md1.scr_pmd1i 0x53dd0 AXF_md1.sr_md1 AXF_md1.kn_md1 35 _ _ _ E m rom regs AXF_md1.RES_pmd1i_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_md1.RES_pmd1i fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (md1_mem_pmd1i m regs n res seq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold md1_mem_pmd1i. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition md1_mem_pmd1w (m : word -> option byte) (regs : bvmap 5 word) (n res seq : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 622568)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622576)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622584)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622592)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622632)) (word_to_le_bytes 1 (wa 1)).

#[using="Type"] Theorem md1_pmd1w : forall regs m rom n res seq, md1_pre regs m n res seq ->
  scs_denot SEGS m (Ez regs (VALS_md1 n res seq)) (snd (fst AXF_md1.RES_pmd1w)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53dd0) m rom) (mkst R (wa 0x53a60) (md1_mem_pmd1w m regs n res seq) rom) /\
    getr R 1 = wa 343748 /\ getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa 1 /\ getr R 11 = wa 255 /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa (n + 20) /\ getr R 20 = wa res /\ (forall k, In k [2; 3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n res seq P Hsc. destruct (md1_setup regs m n res seq P) as [HR HK].
  set (E := Ez regs (VALS_md1 n res seq)) in *. destruct P as [md1_R8 md1_R9 md1_R10 md1_R18 md1_R19 md1_rng_n md1_rng_res md1_rng_seq md1_kw3 md1_kw4 md1_kwr5 md1_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53a60] AXF_md1.scr_pmd1w 0x53dd0 AXF_md1.sr_md1 AXF_md1.kn_md1 35 _ _ _ E m rom regs AXF_md1.RES_pmd1w_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_md1.RES_pmd1w fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (md1_mem_pmd1w m regs n res seq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold md1_mem_pmd1w. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MD1.
End AXF_md1z.

Module AXF_md2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_n := EVar 32.
Definition e_res := EVar 33.
Definition e_mt := EVar 34.
Definition e_ctr := EVar 35.
Definition sr_md2 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 621712)) 10 (e_mt)) 18 (ELit 18446744073709551615)) 19 (EAlu ALU_ADD e_n (ELit 20))) 20 (e_res)).
Definition kn_md2 : list kentry :=
  [ KRange e_n 131052 (2^26);
    KRange e_res 4096 (2^47);
    KAlign e_res 4096;
    KRange e_mt 1 (2^63-1);
    KAlign e_mt 8;
    KRange e_ctr 0 (2^32-1);
    KWr (SA e_mt 16) (ELit 24);
    KWr (SA e_res 0) (ELit 8);
    KDisj (SA e_mt 16) (ELit 24) (SA e_res 0) (ELit 8);
    KWord (SA (ELit 0) 621732) 4 e_ctr;
    KWr (SA (ELit 0) 621732) (ELit 4);
    KDisj (SA e_mt 16) (ELit 24) (SA (ELit 0) 621732) (ELit 4);
    KDisj (SA e_res 0) (ELit 8) (SA (ELit 0) 621732) (ELit 4) ].
Definition scr_md2 : scripts := SCR [] [] [].
Definition ss_md2 := SS 0x53ec4 sr_md2 [] kn_md2 36.
Definition RUN_md2 := sym_exec SEGS 100 true [0x5405c] scr_md2 ss_md2 [].

Definition scr_pmd2 : scripts := SCR [] [] [].
Definition RES_pmd2 := Eval vm_compute in sym_exec SEGS 100 true [0x5405c] scr_pmd2 ss_md2 [].
Lemma RES_pmd2_ok : sym_exec SEGS 100 true [0x5405c] scr_pmd2 (SS 0x53ec4 sr_md2 [] kn_md2 36) [] = RES_pmd2.
Proof. vm_compute. reflexivity. Qed.
End AXF_md2.

Module AXF_md2z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MD2.
Context {fx : FPState}.

Definition VALS_md2 (n res mt ctr : Z) : list Z := [n; res; mt; ctr].

Record md2_pre (regs : bvmap 5 word) (m : word -> option byte) (n res mt ctr : Z) : Prop := {
  md2_R8 : getr regs 8 = wa n ;
  md2_R9 : getr regs 9 = wa 621712 ;
  md2_R10 : getr regs 10 = wa mt ;
  md2_R18 : getr regs 18 = wa 18446744073709551615 ;
  md2_R19 : getr regs 19 = wa (n + 20) ;
  md2_R20 : getr regs 20 = wa res ;
  md2_rng_n : 131052 <= n <= 2^26 ;
  md2_rng_res : 4096 <= res <= 2^47 ;
  md2_rng_mt : 1 <= mt <= 2^63-1 ;
  md2_rng_ctr : 0 <= ctr <= 2^32-1 ;
  md2_ka2 : res mod 4096 = 0 ;
  md2_ka4 : mt mod 8 = 0 ;
  md2_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 24 -> store_ok SEGS m (wa (mt + 16 + d)) k = true ;
  md2_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (res + 0 + d)) k = true ;
  md2_kd8 : mt + 16 + 24 <= res + 0 \/ res + 0 + 8 <= mt + 16 ;
  md2_kw9 : rdn SEGS m (wa (0 + 621732)) 4 = Some (word_to_le_bytes 4 (wa ctr)) ;
  md2_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (0 + 621732 + d)) k = true ;
  md2_kd11 : mt + 16 + 24 <= 0 + 621732 \/ 0 + 621732 + 4 <= mt + 16 ;
  md2_kd12 : res + 0 + 8 <= 0 + 621732 \/ 0 + 621732 + 4 <= res + 0
}.


#[using="Type"] Lemma md2_setup : forall regs m n res mt ctr, md2_pre regs m n res mt ctr ->
  regs_ok (Ez regs (VALS_md2 n res mt ctr)) AXF_md2.sr_md2 regs /\ know_ok SEGS (Ez regs (VALS_md2 n res mt ctr)) m AXF_md2.kn_md2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n res mt ctr P. destruct P as [md2_R8 md2_R9 md2_R10 md2_R18 md2_R19 md2_R20 md2_rng_n md2_rng_res md2_rng_mt md2_rng_ctr md2_ka2 md2_ka4 md2_kwr6 md2_kwr7 md2_kd8 md2_kw9 md2_kwr10 md2_kd11 md2_kd12].
  set (E := Ez regs (VALS_md2 n res mt ctr)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ctr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_md2.sr_md2.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite md2_R8. reflexivity.
    - rewrite md2_R9. reflexivity.
    - rewrite md2_R10. reflexivity.
    - rewrite md2_R18. reflexivity.
    - rewrite md2_R19, zeval_sound. cbn [zeval edenot AXF_md2.e_n AXF_md2.e_res AXF_md2.e_mt AXF_md2.e_ctr]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite md2_R20. reflexivity. }
  unfold know_ok, AXF_md2.kn_md2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_md2.e_n AXF_md2.e_res AXF_md2.e_mt AXF_md2.e_ctr a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ md2_rng_n eq_refl eq_refl), ?(mod64_of_range res _ _ md2_rng_res eq_refl eq_refl), ?(mod64_of_range mt _ _ md2_rng_mt eq_refl eq_refl), ?(mod64_of_range ctr _ _ md2_rng_ctr eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply md2_kwr6 | apply md2_kwr7 | apply md2_kwr10]; assumption).
  all: try (clear - md2_rng_n md2_rng_res md2_rng_mt md2_rng_ctr md2_ka2 md2_ka4; lia).
  all: first [(clear - md2_rng_n md2_rng_res md2_rng_mt md2_rng_ctr md2_ka2 md2_ka4 md2_kd8; lia) | (clear - md2_rng_n md2_rng_res md2_rng_mt md2_rng_ctr md2_ka2 md2_ka4 md2_kd11; lia) | (clear - md2_rng_n md2_rng_res md2_rng_mt md2_rng_ctr md2_ka2 md2_ka4 md2_kd12; lia) | lia].
Qed.


Definition md2_mem_pmd2 (m : word -> option byte) (regs : bvmap 5 word) (n res mt ctr : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (mt + 16)) (word_to_le_bytes 8 (wa res))) (wa (res + 0)) (word_to_le_bytes 8 (wa mt))) (wa (mt + 32)) (word_to_le_bytes 8 (wa ((4096 * Z.shiftr (((n + 4115)) mod 2^64) 12) + 4064)))) (wa (mt + 28)) (word_to_le_bytes 4 (wa 0))) (wa (mt + 24)) (word_to_le_bytes 4 (wa 0))) (wa (0 + 621732)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 ctr + 1))).

#[using="Type"] Theorem md2_pmd2 : forall regs m rom n res mt ctr, md2_pre regs m n res mt ctr ->
  scs_denot SEGS m (Ez regs (VALS_md2 n res mt ctr)) (snd (fst AXF_md2.RES_pmd2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53ec4) m rom) (mkst R (wa 0x5405c) (md2_mem_pmd2 m regs n res mt ctr) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa (ext_Z true 0 4 ctr + 1) /\ getr R 11 = wa (2048 * Z.shiftr (((n + 4115)) mod 2^64) 11) /\ getr R 18 = wa mt /\ getr R 19 = wa 0 /\ getr R 20 = wa res /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n res mt ctr P Hsc. destruct (md2_setup regs m n res mt ctr P) as [HR HK].
  set (E := Ez regs (VALS_md2 n res mt ctr)) in *. destruct P as [md2_R8 md2_R9 md2_R10 md2_R18 md2_R19 md2_R20 md2_rng_n md2_rng_res md2_rng_mt md2_rng_ctr md2_ka2 md2_ka4 md2_kwr6 md2_kwr7 md2_kd8 md2_kw9 md2_kwr10 md2_kd11 md2_kd12].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ctr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5405c] AXF_md2.scr_pmd2 0x53ec4 AXF_md2.sr_md2 AXF_md2.kn_md2 36 _ _ _ E m rom regs AXF_md2.RES_pmd2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_md2.RES_pmd2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (md2_mem_pmd2 m regs n res mt ctr) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold md2_mem_pmd2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MD2.
End AXF_md2z.

Module AXF_mmrd.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sp0 := EVar 32.
Definition e_res := EVar 33.
Definition e_ad := EVar 34.
Definition e_s00 := EVar 35.
Definition e_s10 := EVar 36.
Definition e_s20 := EVar 37.
Definition e_s30 := EVar 38.
Definition e_s40 := EVar 39.
Definition e_s50 := EVar 40.
Definition sr_mmrd := (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-64)))) 10 (e_res)) 16 (e_ad)).
Definition kn_mmrd : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KRange e_res 4096 (2^47);
    KRange e_ad 0 (2^63-1);
    KWord (SA e_sp0 (-8)) 8 (ELit 343504);
    KWord (SA e_sp0 (-16)) 8 e_s00;
    KWord (SA e_sp0 (-24)) 8 e_s10;
    KWord (SA e_sp0 (-32)) 8 e_s20;
    KWord (SA e_sp0 (-40)) 8 e_s30;
    KWord (SA e_sp0 (-48)) 8 e_s40;
    KWord (SA e_sp0 (-56)) 8 e_s50;
    KRange e_s00 0 (2^64-1);
    KRange e_s10 0 (2^64-1);
    KRange e_s20 0 (2^64-1);
    KRange e_s30 0 (2^64-1);
    KRange e_s40 0 (2^64-1);
    KRange e_s50 0 (2^64-1) ].
Definition scr_mmrd : scripts := SCR [] [] [].
Definition ss_mmrd := SS 0x551a8 sr_mmrd [] kn_mmrd 41.
Definition RUN_mmrd := sym_exec SEGS 100 true [0x53dd0] scr_mmrd ss_mmrd [].

Definition scr_pmrd : scripts := SCR [] [] [].
Definition RES_pmrd := Eval vm_compute in sym_exec SEGS 100 true [0x53dd0] scr_pmrd ss_mmrd [].
Lemma RES_pmrd_ok : sym_exec SEGS 100 true [0x53dd0] scr_pmrd (SS 0x551a8 sr_mmrd [] kn_mmrd 41) [] = RES_pmrd.
Proof. vm_compute. reflexivity. Qed.
End AXF_mmrd.

Module AXF_mmrdz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MMRD.
Context {fx : FPState}.

Definition VALS_mmrd (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : list Z := [sp0; res; ad; s00; s10; s20; s30; s40; s50].

Record mmrd_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : Prop := {
  mmrd_R2 : getr regs 2 = wa (sp0 + -64) ;
  mmrd_R10 : getr regs 10 = wa res ;
  mmrd_R16 : getr regs 16 = wa ad ;
  mmrd_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mmrd_rng_res : 4096 <= res <= 2^47 ;
  mmrd_rng_ad : 0 <= ad <= 2^63-1 ;
  mmrd_rng_s00 : 0 <= s00 <= 2^64-1 ;
  mmrd_rng_s10 : 0 <= s10 <= 2^64-1 ;
  mmrd_rng_s20 : 0 <= s20 <= 2^64-1 ;
  mmrd_rng_s30 : 0 <= s30 <= 2^64-1 ;
  mmrd_rng_s40 : 0 <= s40 <= 2^64-1 ;
  mmrd_rng_s50 : 0 <= s50 <= 2^64-1 ;
  mmrd_ka1 : sp0 mod 16 = 0 ;
  mmrd_kw4 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 343504)) ;
  mmrd_kw5 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s00)) ;
  mmrd_kw6 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s10)) ;
  mmrd_kw7 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s20)) ;
  mmrd_kw8 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s30)) ;
  mmrd_kw9 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa s40)) ;
  mmrd_kw10 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa s50))
}.


#[using="Type"] Lemma mmrd_setup : forall regs m sp0 res ad s00 s10 s20 s30 s40 s50, mmrd_pre regs m sp0 res ad s00 s10 s20 s30 s40 s50 ->
  regs_ok (Ez regs (VALS_mmrd sp0 res ad s00 s10 s20 s30 s40 s50)) AXF_mmrd.sr_mmrd regs /\ know_ok SEGS (Ez regs (VALS_mmrd sp0 res ad s00 s10 s20 s30 s40 s50)) m AXF_mmrd.kn_mmrd.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 res ad s00 s10 s20 s30 s40 s50 P. destruct P as [mmrd_R2 mmrd_R10 mmrd_R16 mmrd_rng_sp0 mmrd_rng_res mmrd_rng_ad mmrd_rng_s00 mmrd_rng_s10 mmrd_rng_s20 mmrd_rng_s30 mmrd_rng_s40 mmrd_rng_s50 mmrd_ka1 mmrd_kw4 mmrd_kw5 mmrd_kw6 mmrd_kw7 mmrd_kw8 mmrd_kw9 mmrd_kw10].
  set (E := Ez regs (VALS_mmrd sp0 res ad s00 s10 s20 s30 s40 s50)).
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s50) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mmrd.sr_mmrd.
    apply (regs_ok_pin E _ regs 16); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|].
    - rewrite mmrd_R2, zeval_sound. cbn [zeval edenot AXF_mmrd.e_sp0 AXF_mmrd.e_res AXF_mmrd.e_ad AXF_mmrd.e_s00 AXF_mmrd.e_s10 AXF_mmrd.e_s20 AXF_mmrd.e_s30 AXF_mmrd.e_s40 AXF_mmrd.e_s50]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mmrd_R10. reflexivity.
    - rewrite mmrd_R16. reflexivity. }
  unfold know_ok, AXF_mmrd.kn_mmrd.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mmrd.e_sp0 AXF_mmrd.e_res AXF_mmrd.e_ad AXF_mmrd.e_s00 AXF_mmrd.e_s10 AXF_mmrd.e_s20 AXF_mmrd.e_s30 AXF_mmrd.e_s40 AXF_mmrd.e_s50 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ mmrd_rng_sp0 eq_refl eq_refl), ?(mod64_of_range res _ _ mmrd_rng_res eq_refl eq_refl), ?(mod64_of_range ad _ _ mmrd_rng_ad eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mmrd_rng_sp0 mmrd_rng_res mmrd_rng_ad mmrd_rng_s00 mmrd_rng_s10 mmrd_rng_s20 mmrd_rng_s30 mmrd_rng_s40 mmrd_rng_s50 mmrd_ka1; lia).
  all: first [lia].
Qed.


Definition mmrd_mem_pmrd (m : word -> option byte) (regs : bvmap 5 word) (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mmrd_pmrd : forall regs m rom sp0 res ad s00 s10 s20 s30 s40 s50, mmrd_pre regs m sp0 res ad s00 s10 s20 s30 s40 s50 ->
  scs_denot SEGS m (Ez regs (VALS_mmrd sp0 res ad s00 s10 s20 s30 s40 s50)) (snd (fst AXF_mmrd.RES_pmrd)) ->
  exists R, msteps SEGS (mkst regs (wa 0x551a8) m rom) (mkst R (wa 0x53dd0) (mmrd_mem_pmrd m regs sp0 res ad s00 s10 s20 s30 s40 s50) rom) /\
    getr R 1 = wa 343504 /\ getr R 2 = wa sp0 /\ getr R 8 = wa s00 /\ getr R 9 = wa s10 /\ getr R 10 = wa res /\ getr R 11 = wa 18446744073709547521 /\ getr R 16 = wa ad /\ getr R 18 = wa s20 /\ getr R 19 = wa s30 /\ getr R 20 = wa s40 /\ getr R 21 = wa s50 /\ (forall k, In k [3; 4; 5; 6; 7; 12; 13; 14; 15; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 res ad s00 s10 s20 s30 s40 s50 P Hsc. destruct (mmrd_setup regs m sp0 res ad s00 s10 s20 s30 s40 s50 P) as [HR HK].
  set (E := Ez regs (VALS_mmrd sp0 res ad s00 s10 s20 s30 s40 s50)) in *. destruct P as [mmrd_R2 mmrd_R10 mmrd_R16 mmrd_rng_sp0 mmrd_rng_res mmrd_rng_ad mmrd_rng_s00 mmrd_rng_s10 mmrd_rng_s20 mmrd_rng_s30 mmrd_rng_s40 mmrd_rng_s50 mmrd_ka1 mmrd_kw4 mmrd_kw5 mmrd_kw6 mmrd_kw7 mmrd_kw8 mmrd_kw9 mmrd_kw10].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s50) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53dd0] AXF_mmrd.scr_pmrd 0x551a8 AXF_mmrd.sr_mmrd AXF_mmrd.kn_mmrd 41 _ _ _ E m rom regs AXF_mmrd.RES_pmrd_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mmrd.RES_pmrd fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mmrd_mem_pmrd m regs sp0 res ad s00 s10 s20 s30 s40 s50) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mmrd_mem_pmrd. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MMRD.
End AXF_mmrdz.

Module AXF_mp63.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sp0 := EVar 33.
Definition e_W := EVar 34.
Definition e_SEQ := EVar 36.
Definition e_MEM := EVar 37.
Definition STK := SA e_sp0 (-1024).
Definition SC := EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58).
Definition sr_mp63 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_G)) 18 (ELit 0x97c98)).
Definition kn_mp63 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange SC 63 63;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA e_G 16) 8 e_MEM;
    KWord (SA (ELit 0) 0x98028) 1 e_SEQ;
    KWr (SA (ELit 0) 0x97fe8) (ELit 32);
    KWr (SA (ELit 0) 0x98028) (ELit 1);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x97fe8) (ELit 72);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x97fe8) (ELit 72) ].
Definition scr_mp63 : scripts := SCR [] [] [].
Definition ss_mp63 := SS 0x538b0 sr_mp63 [] kn_mp63 38.
Definition RUN_mp63 := sym_exec SEGS 100 true [0x5396c] scr_mp63 ss_mp63 [].

Definition scr_pm63a : scripts := SCR [true; true] [] [].
Definition RES_pm63a := Eval vm_compute in sym_exec SEGS 100 true [0x5396c] scr_pm63a ss_mp63 [].
Lemma RES_pm63a_ok : sym_exec SEGS 100 true [0x5396c] scr_pm63a (SS 0x538b0 sr_mp63 [] kn_mp63 38) [] = RES_pm63a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pm63b : scripts := SCR [true; false] [] [].
Definition RES_pm63b := Eval vm_compute in sym_exec SEGS 100 true [0x5396c] scr_pm63b ss_mp63 [].
Lemma RES_pm63b_ok : sym_exec SEGS 100 true [0x5396c] scr_pm63b (SS 0x538b0 sr_mp63 [] kn_mp63 38) [] = RES_pm63b.
Proof. vm_compute. reflexivity. Qed.
End AXF_mp63.

Module AXF_mp63z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MP63.
Context {fx : FPState}.

Definition VALS_mp63 (G sp0 W SEQ MEM : Z) : list Z := [G; sp0; W; 0; SEQ; MEM].

Record mp63_pre (regs : bvmap 5 word) (m : word -> option byte) (G sp0 W SEQ MEM : Z) : Prop := {
  mp63_R2 : getr regs 2 = wa (sp0 + -96) ;
  mp63_R9 : getr regs 9 = wa 621568 ;
  mp63_R10 : getr regs 10 = wa G ;
  mp63_R18 : getr regs 18 = wa 621720 ;
  mp63_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  mp63_rng_G : 1 <= G <= 2^63-1 ;
  mp63_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mp63_rng_W : 0 <= W <= 2^64-1 ;
  mp63_rng_SEQ : 0 <= SEQ <= 255 ;
  mp63_rng_MEM : 0 <= MEM <= 2^64-1 ;
  mp63_ka1 : sp0 mod 16 = 0 ;
  mp63_ka4 : G mod 8 = 0 ;
  mp63_kr5 : 63 <= SCW W <= 63 ;
  mp63_kw6 : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  mp63_kw7 : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa MEM)) ;
  mp63_kw8 : rdn SEGS m (wa (0 + 622632)) 1 = Some (word_to_le_bytes 1 (wa SEQ)) ;
  mp63_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (0 + 622568 + d)) k = true ;
  mp63_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (0 + 622632 + d)) k = true ;
  mp63_kd11 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  mp63_kd12 : sp0 + -1024 + 1024 <= 0 + 622568 \/ 0 + 622568 + 72 <= sp0 + -1024 ;
  mp63_kd13 : G + 0 + 40 <= 0 + 622568 \/ 0 + 622568 + 72 <= G + 0
}.


#[using="Type"] Lemma mp63_setup : forall regs m G sp0 W SEQ MEM, mp63_pre regs m G sp0 W SEQ MEM ->
  regs_ok (Ez regs (VALS_mp63 G sp0 W SEQ MEM)) AXF_mp63.sr_mp63 regs /\ know_ok SEGS (Ez regs (VALS_mp63 G sp0 W SEQ MEM)) m AXF_mp63.kn_mp63.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 W SEQ MEM P. destruct P as [mp63_R2 mp63_R9 mp63_R10 mp63_R18 mp63_HSTK mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5 mp63_kw6 mp63_kw7 mp63_kw8 mp63_kwr9 mp63_kwr10 mp63_kd11 mp63_kd12 mp63_kd13].
  set (E := Ez regs (VALS_mp63 G sp0 W SEQ MEM)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mp63.sr_mp63.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|].
    - rewrite mp63_R2, zeval_sound. cbn [zeval edenot AXF_mp63.e_G AXF_mp63.e_sp0 AXF_mp63.e_W AXF_mp63.e_SEQ AXF_mp63.e_MEM AXF_mp63.STK AXF_mp63.SC]. rewrite ?Z32, ?Z33, ?Z34, ?Z36, ?Z37. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mp63_R9. reflexivity.
    - rewrite mp63_R10. reflexivity.
    - rewrite mp63_R18. reflexivity. }
  unfold know_ok, AXF_mp63.kn_mp63.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mp63.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mp63.e_G AXF_mp63.e_sp0 AXF_mp63.e_W AXF_mp63.e_SEQ AXF_mp63.e_MEM AXF_mp63.STK AXF_mp63.SC a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z36, ?Z37.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ mp63_rng_G eq_refl eq_refl), ?(mod64_of_range sp0 _ _ mp63_rng_sp0 eq_refl eq_refl), ?(mod64_of_range SEQ _ _ mp63_rng_SEQ eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mp63_kwr9 | apply mp63_kwr10]; assumption).
  all: try (clear - mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5; lia).
  all: first [(clear - mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5 mp63_kd11; lia) | (clear - mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5 mp63_kd12; lia) | (clear - mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5 mp63_kd13; lia) | lia].
Qed.


Definition mp63_mem_pm63a (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W SEQ MEM : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 622632)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 SEQ + 1))).

#[using="Type"] Theorem mp63_pm63a : forall regs m rom G sp0 W SEQ MEM, mp63_pre regs m G sp0 W SEQ MEM ->
  scs_denot SEGS m (Ez regs (VALS_mp63 G sp0 W SEQ MEM)) (snd (fst AXF_mp63.RES_pm63a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x538b0) m rom) (mkst R (wa 0x5396c) (mp63_mem_pm63a m regs G sp0 W SEQ MEM) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 621568 /\ getr R 10 = wa G /\ getr R 11 = wa (4096 * Z.shiftr W 12) /\ getr R 12 = wa MEM /\ getr R 13 = wa 18446744073709547520 /\ getr R 18 = wa 621720 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W SEQ MEM P Hsc. destruct (mp63_setup regs m G sp0 W SEQ MEM P) as [HR HK].
  set (E := Ez regs (VALS_mp63 G sp0 W SEQ MEM)) in *. destruct P as [mp63_R2 mp63_R9 mp63_R10 mp63_R18 mp63_HSTK mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5 mp63_kw6 mp63_kw7 mp63_kw8 mp63_kwr9 mp63_kwr10 mp63_kd11 mp63_kd12 mp63_kd13].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5396c] AXF_mp63.scr_pm63a 0x538b0 AXF_mp63.sr_mp63 AXF_mp63.kn_mp63 38 _ _ _ E m rom regs AXF_mp63.RES_pm63a_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mp63.RES_pm63a fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mp63_mem_pm63a m regs G sp0 W SEQ MEM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mp63_mem_pm63a. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mp63_mem_pm63b (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W SEQ MEM : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 622568)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622576)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622584)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622592)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622632)) (word_to_le_bytes 1 (wa 1)).

#[using="Type"] Theorem mp63_pm63b : forall regs m rom G sp0 W SEQ MEM, mp63_pre regs m G sp0 W SEQ MEM ->
  scs_denot SEGS m (Ez regs (VALS_mp63 G sp0 W SEQ MEM)) (snd (fst AXF_mp63.RES_pm63b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x538b0) m rom) (mkst R (wa 0x5396c) (mp63_mem_pm63b m regs G sp0 W SEQ MEM) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 621568 /\ getr R 10 = wa G /\ getr R 11 = wa (4096 * Z.shiftr W 12) /\ getr R 12 = wa MEM /\ getr R 13 = wa 18446744073709547520 /\ getr R 18 = wa 621720 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W SEQ MEM P Hsc. destruct (mp63_setup regs m G sp0 W SEQ MEM P) as [HR HK].
  set (E := Ez regs (VALS_mp63 G sp0 W SEQ MEM)) in *. destruct P as [mp63_R2 mp63_R9 mp63_R10 mp63_R18 mp63_HSTK mp63_rng_G mp63_rng_sp0 mp63_rng_W mp63_rng_SEQ mp63_rng_MEM mp63_ka1 mp63_ka4 mp63_kr5 mp63_kw6 mp63_kw7 mp63_kw8 mp63_kwr9 mp63_kwr10 mp63_kd11 mp63_kd12 mp63_kd13].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5396c] AXF_mp63.scr_pm63b 0x538b0 AXF_mp63.sr_mp63 AXF_mp63.kn_mp63 38 _ _ _ E m rom regs AXF_mp63.RES_pm63b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mp63.RES_pm63b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mp63_mem_pm63b m regs G sp0 W SEQ MEM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mp63_mem_pm63b. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MP63.
End AXF_mp63z.

Module AXF_mps.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sp0 := EVar 33.
Definition e_W := EVar 34.
Definition e_USG := EVar 35.
Definition e_SEQ := EVar 36.
Definition e_MEM := EVar 37.
Definition STK := SA e_sp0 (-1024).
Definition SC := EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58).
Definition SC8 := EMd M_MUL (ELit 8) SC.
Definition SCM7 := EAlu ALU_ADD SC (ELit (-7)).
Definition sr_mps := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_G)) 18 (ELit 0x97c98)).
Definition kn_mps : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange SC 0 47;
    KRange SC8 0 376;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA e_G 16) 8 e_MEM;
    KWord (SA SC8 622184) 8 e_USG;
    KWord (SA (ELit 0) 0x98028) 1 e_SEQ;
    KWr (SA SC8 622184) (ELit 8);
    KWr (SA (ELit 0) 0x97fe8) (ELit 32);
    KWr (SA (ELit 0) 0x98028) (ELit 1);
    KWr (SA SC 622561) (ELit 1);
    KDisj STK (ELit 1024) (SA SC 622561) (ELit 1);
    KDisj (SA e_G 0) (ELit 40) (SA SC 622561) (ELit 1);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA SC8 622184) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x97fe8) (ELit 72);
    KDisj (SA e_G 0) (ELit 40) (SA SC8 622184) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x97fe8) (ELit 72) ].
Definition scr_mps : scripts := SCR [] [] [].
Definition ss_mps := SS 0x538b0 sr_mps [] kn_mps 38.
Definition RUN_mps := sym_exec SEGS 100 true [0x5396c] scr_mps ss_mps [].

Definition scr_pmpa : scripts := SCR [true; true; false] [] [].
Definition RES_pmpa := Eval vm_compute in sym_exec SEGS 100 true [0x5396c] scr_pmpa ss_mps [].
Lemma RES_pmpa_ok : sym_exec SEGS 100 true [0x5396c] scr_pmpa (SS 0x538b0 sr_mps [] kn_mps 38) [] = RES_pmpa.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmpb : scripts := SCR [true; true; true] [] [].
Definition RES_pmpb := Eval vm_compute in sym_exec SEGS 100 true [0x5396c] scr_pmpb ss_mps [].
Lemma RES_pmpb_ok : sym_exec SEGS 100 true [0x5396c] scr_pmpb (SS 0x538b0 sr_mps [] kn_mps 38) [] = RES_pmpb.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmpc : scripts := SCR [true; false; false] [] [].
Definition RES_pmpc := Eval vm_compute in sym_exec SEGS 100 true [0x5396c] scr_pmpc ss_mps [].
Lemma RES_pmpc_ok : sym_exec SEGS 100 true [0x5396c] scr_pmpc (SS 0x538b0 sr_mps [] kn_mps 38) [] = RES_pmpc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmpd : scripts := SCR [true; false; true] [] [].
Definition RES_pmpd := Eval vm_compute in sym_exec SEGS 100 true [0x5396c] scr_pmpd ss_mps [].
Lemma RES_pmpd_ok : sym_exec SEGS 100 true [0x5396c] scr_pmpd (SS 0x538b0 sr_mps [] kn_mps 38) [] = RES_pmpd.
Proof. vm_compute. reflexivity. Qed.
End AXF_mps.

Module AXF_mpsz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MPS.
Context {fx : FPState}.

Definition VALS_mps (G sp0 W USG SEQ MEM : Z) : list Z := [G; sp0; W; USG; SEQ; MEM].

Record mps_pre (regs : bvmap 5 word) (m : word -> option byte) (G sp0 W USG SEQ MEM : Z) : Prop := {
  mps_R2 : getr regs 2 = wa (sp0 + -96) ;
  mps_R9 : getr regs 9 = wa 621568 ;
  mps_R10 : getr regs 10 = wa G ;
  mps_R18 : getr regs 18 = wa 621720 ;
  mps_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  mps_rng_G : 1 <= G <= 2^63-1 ;
  mps_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mps_rng_W : 0 <= W <= 2^64-1 ;
  mps_rng_USG : 0 <= USG <= 2^64-1 ;
  mps_rng_SEQ : 0 <= SEQ <= 255 ;
  mps_rng_MEM : 0 <= MEM <= 2^64-1 ;
  mps_ka1 : sp0 mod 16 = 0 ;
  mps_ka4 : G mod 8 = 0 ;
  mps_kr5 : 0 <= SCW W <= 47 ;
  mps_kr6 : 0 <= 8 * SCW W <= 376 ;
  mps_kw7 : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  mps_kw8 : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa MEM)) ;
  mps_kw9 : rdn SEGS m (wa (8 * SCW W + 622184)) 8 = Some (word_to_le_bytes 8 (wa USG)) ;
  mps_kw10 : rdn SEGS m (wa (0 + 622632)) 1 = Some (word_to_le_bytes 1 (wa SEQ)) ;
  mps_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * SCW W + 622184 + d)) k = true ;
  mps_kwr12 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (0 + 622568 + d)) k = true ;
  mps_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (0 + 622632 + d)) k = true ;
  mps_kwr14 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (SCW W + 622561 + d)) k = true ;
  mps_kd15 : sp0 + -1024 + 1024 <= SCW W + 622561 \/ SCW W + 622561 + 1 <= sp0 + -1024 ;
  mps_kd16 : G + 0 + 40 <= SCW W + 622561 \/ SCW W + 622561 + 1 <= G + 0 ;
  mps_kd17 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  mps_kd18 : sp0 + -1024 + 1024 <= 8 * SCW W + 622184 \/ 8 * SCW W + 622184 + 8 <= sp0 + -1024 ;
  mps_kd19 : sp0 + -1024 + 1024 <= 0 + 622568 \/ 0 + 622568 + 72 <= sp0 + -1024 ;
  mps_kd20 : G + 0 + 40 <= 8 * SCW W + 622184 \/ 8 * SCW W + 622184 + 8 <= G + 0 ;
  mps_kd21 : G + 0 + 40 <= 0 + 622568 \/ 0 + 622568 + 72 <= G + 0
}.


#[using="Type"] Lemma mps_setup : forall regs m G sp0 W USG SEQ MEM, mps_pre regs m G sp0 W USG SEQ MEM ->
  regs_ok (Ez regs (VALS_mps G sp0 W USG SEQ MEM)) AXF_mps.sr_mps regs /\ know_ok SEGS (Ez regs (VALS_mps G sp0 W USG SEQ MEM)) m AXF_mps.kn_mps.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 W USG SEQ MEM P. destruct P as [mps_R2 mps_R9 mps_R10 mps_R18 mps_HSTK mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kw7 mps_kw8 mps_kw9 mps_kw10 mps_kwr11 mps_kwr12 mps_kwr13 mps_kwr14 mps_kd15 mps_kd16 mps_kd17 mps_kd18 mps_kd19 mps_kd20 mps_kd21].
  set (E := Ez regs (VALS_mps G sp0 W USG SEQ MEM)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mps.sr_mps.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|].
    - rewrite mps_R2, zeval_sound. cbn [zeval edenot AXF_mps.e_G AXF_mps.e_sp0 AXF_mps.e_W AXF_mps.e_USG AXF_mps.e_SEQ AXF_mps.e_MEM AXF_mps.STK AXF_mps.SC AXF_mps.SC8 AXF_mps.SCM7]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mps_R9. reflexivity.
    - rewrite mps_R10. reflexivity.
    - rewrite mps_R18. reflexivity. }
  unfold know_ok, AXF_mps.kn_mps.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mps.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mps.e_G AXF_mps.e_sp0 AXF_mps.e_W AXF_mps.e_USG AXF_mps.e_SEQ AXF_mps.e_MEM AXF_mps.STK AXF_mps.SC AXF_mps.SC8 AXF_mps.SCM7 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ mps_rng_G eq_refl eq_refl), ?(mod64_of_range sp0 _ _ mps_rng_sp0 eq_refl eq_refl), ?(mod64_of_range SEQ _ _ mps_rng_SEQ eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mps_kwr11 | apply mps_kwr12 | apply mps_kwr13 | apply mps_kwr14]; assumption).
  all: try (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6; lia).
  all: first [(clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd15; lia) | (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd16; lia) | (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd17; lia) | (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd18; lia) | (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd19; lia) | (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd20; lia) | (clear - mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kd21; lia) | lia].
Qed.


Definition mps_mem_pmpa (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W USG SEQ MEM : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (8 * SCW W + 622184)) (word_to_le_bytes 8 (wa ((USG + Z.land ((((-1 * W) + -1)) mod 2^64) 31) + -32)))) (wa (0 + 622632)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 SEQ + 1)))) (wa (SCW W + 622561)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 SEQ + 1))).

#[using="Type"] Theorem mps_pmpa : forall regs m rom G sp0 W USG SEQ MEM, mps_pre regs m G sp0 W USG SEQ MEM ->
  scs_denot SEGS m (Ez regs (VALS_mps G sp0 W USG SEQ MEM)) (snd (fst AXF_mps.RES_pmpa)) ->
  exists R, msteps SEGS (mkst regs (wa 0x538b0) m rom) (mkst R (wa 0x5396c) (mps_mem_pmpa m regs G sp0 W USG SEQ MEM) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 621568 /\ getr R 10 = wa G /\ getr R 11 = wa (4096 * Z.shiftr W 12) /\ getr R 12 = wa MEM /\ getr R 13 = wa 18446744073709547520 /\ getr R 14 = wa USG /\ getr R 18 = wa 621720 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W USG SEQ MEM P Hsc. destruct (mps_setup regs m G sp0 W USG SEQ MEM P) as [HR HK].
  set (E := Ez regs (VALS_mps G sp0 W USG SEQ MEM)) in *. destruct P as [mps_R2 mps_R9 mps_R10 mps_R18 mps_HSTK mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kw7 mps_kw8 mps_kw9 mps_kw10 mps_kwr11 mps_kwr12 mps_kwr13 mps_kwr14 mps_kd15 mps_kd16 mps_kd17 mps_kd18 mps_kd19 mps_kd20 mps_kd21].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5396c] AXF_mps.scr_pmpa 0x538b0 AXF_mps.sr_mps AXF_mps.kn_mps 38 _ _ _ E m rom regs AXF_mps.RES_pmpa_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mps.RES_pmpa fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mps_mem_pmpa m regs G sp0 W USG SEQ MEM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mps_mem_pmpa. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mps_mem_pmpb (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W USG SEQ MEM : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (8 * SCW W + 622184)) (word_to_le_bytes 8 (wa ((USG + Z.land ((((-1 * W) + -1)) mod 2^64) 31) + -32)))) (wa (0 + 622632)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 SEQ + 1))).

#[using="Type"] Theorem mps_pmpb : forall regs m rom G sp0 W USG SEQ MEM, mps_pre regs m G sp0 W USG SEQ MEM ->
  scs_denot SEGS m (Ez regs (VALS_mps G sp0 W USG SEQ MEM)) (snd (fst AXF_mps.RES_pmpb)) ->
  exists R, msteps SEGS (mkst regs (wa 0x538b0) m rom) (mkst R (wa 0x5396c) (mps_mem_pmpb m regs G sp0 W USG SEQ MEM) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 621568 /\ getr R 10 = wa G /\ getr R 11 = wa (4096 * Z.shiftr W 12) /\ getr R 12 = wa MEM /\ getr R 13 = wa 18446744073709547520 /\ getr R 14 = wa USG /\ getr R 18 = wa 621720 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W USG SEQ MEM P Hsc. destruct (mps_setup regs m G sp0 W USG SEQ MEM P) as [HR HK].
  set (E := Ez regs (VALS_mps G sp0 W USG SEQ MEM)) in *. destruct P as [mps_R2 mps_R9 mps_R10 mps_R18 mps_HSTK mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kw7 mps_kw8 mps_kw9 mps_kw10 mps_kwr11 mps_kwr12 mps_kwr13 mps_kwr14 mps_kd15 mps_kd16 mps_kd17 mps_kd18 mps_kd19 mps_kd20 mps_kd21].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5396c] AXF_mps.scr_pmpb 0x538b0 AXF_mps.sr_mps AXF_mps.kn_mps 38 _ _ _ E m rom regs AXF_mps.RES_pmpb_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mps.RES_pmpb fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mps_mem_pmpb m regs G sp0 W USG SEQ MEM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mps_mem_pmpb. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mps_mem_pmpc (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W USG SEQ MEM : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (8 * SCW W + 622184)) (word_to_le_bytes 8 (wa ((USG + Z.land ((((-1 * W) + -1)) mod 2^64) 31) + -32)))) (wa (0 + 622568)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622576)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622584)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622592)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622632)) (word_to_le_bytes 1 (wa 1))) (wa (SCW W + 622561)) (word_to_le_bytes 1 (wa 1)).

#[using="Type"] Theorem mps_pmpc : forall regs m rom G sp0 W USG SEQ MEM, mps_pre regs m G sp0 W USG SEQ MEM ->
  scs_denot SEGS m (Ez regs (VALS_mps G sp0 W USG SEQ MEM)) (snd (fst AXF_mps.RES_pmpc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x538b0) m rom) (mkst R (wa 0x5396c) (mps_mem_pmpc m regs G sp0 W USG SEQ MEM) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 621568 /\ getr R 10 = wa G /\ getr R 11 = wa (4096 * Z.shiftr W 12) /\ getr R 12 = wa MEM /\ getr R 13 = wa 18446744073709547520 /\ getr R 14 = wa USG /\ getr R 18 = wa 621720 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W USG SEQ MEM P Hsc. destruct (mps_setup regs m G sp0 W USG SEQ MEM P) as [HR HK].
  set (E := Ez regs (VALS_mps G sp0 W USG SEQ MEM)) in *. destruct P as [mps_R2 mps_R9 mps_R10 mps_R18 mps_HSTK mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kw7 mps_kw8 mps_kw9 mps_kw10 mps_kwr11 mps_kwr12 mps_kwr13 mps_kwr14 mps_kd15 mps_kd16 mps_kd17 mps_kd18 mps_kd19 mps_kd20 mps_kd21].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5396c] AXF_mps.scr_pmpc 0x538b0 AXF_mps.sr_mps AXF_mps.kn_mps 38 _ _ _ E m rom regs AXF_mps.RES_pmpc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mps.RES_pmpc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mps_mem_pmpc m regs G sp0 W USG SEQ MEM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mps_mem_pmpc. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mps_mem_pmpd (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W USG SEQ MEM : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (8 * SCW W + 622184)) (word_to_le_bytes 8 (wa ((USG + Z.land ((((-1 * W) + -1)) mod 2^64) 31) + -32)))) (wa (0 + 622568)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622576)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622584)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622592)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 622632)) (word_to_le_bytes 1 (wa 1)).

#[using="Type"] Theorem mps_pmpd : forall regs m rom G sp0 W USG SEQ MEM, mps_pre regs m G sp0 W USG SEQ MEM ->
  scs_denot SEGS m (Ez regs (VALS_mps G sp0 W USG SEQ MEM)) (snd (fst AXF_mps.RES_pmpd)) ->
  exists R, msteps SEGS (mkst regs (wa 0x538b0) m rom) (mkst R (wa 0x5396c) (mps_mem_pmpd m regs G sp0 W USG SEQ MEM) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 621568 /\ getr R 10 = wa G /\ getr R 11 = wa (4096 * Z.shiftr W 12) /\ getr R 12 = wa MEM /\ getr R 13 = wa 18446744073709547520 /\ getr R 14 = wa USG /\ getr R 18 = wa 621720 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W USG SEQ MEM P Hsc. destruct (mps_setup regs m G sp0 W USG SEQ MEM P) as [HR HK].
  set (E := Ez regs (VALS_mps G sp0 W USG SEQ MEM)) in *. destruct P as [mps_R2 mps_R9 mps_R10 mps_R18 mps_HSTK mps_rng_G mps_rng_sp0 mps_rng_W mps_rng_USG mps_rng_SEQ mps_rng_MEM mps_ka1 mps_ka4 mps_kr5 mps_kr6 mps_kw7 mps_kw8 mps_kw9 mps_kw10 mps_kwr11 mps_kwr12 mps_kwr13 mps_kwr14 mps_kd15 mps_kd16 mps_kd17 mps_kd18 mps_kd19 mps_kd20 mps_kd21].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SEQ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5396c] AXF_mps.scr_pmpd 0x538b0 AXF_mps.sr_mps AXF_mps.kn_mps 38 _ _ _ E m rom regs AXF_mps.RES_pmpd_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mps.RES_pmpd fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mps_mem_pmpd m regs G sp0 W USG SEQ MEM) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mps_mem_pmpd. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MPS.
End AXF_mpsz.

Module AXF_ns.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sp0 := EVar 33.
Definition e_W := EVar 34.
Definition e_USG := EVar 35.
Definition e_MEM := EVar 36.
Definition e_H3 := EVar 37.
Definition e_OFF := EVar 38.
Definition e_PG := EVar 39.
Definition e_PW := EVar 40.
Definition e_PAV := EVar 41.
Definition e_PFR := EVar 42.
Definition e_SEC := EVar 43.
Definition e_PCSZ := EVar 44.
Definition STK := SA e_sp0 (-1024).
Definition SC := EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58).
Definition SC8 := EMd M_MUL (ELit 8) SC.
Definition BASE := EAlu ALU_ADD e_MEM (EMd M_MUL (ELit (-16)) (EExt false 0 2 e_OFF)).
Definition PSC := EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_PW) (ELit 58).
Definition PSC2 := EMd M_MUL (ELit 2) PSC.
Definition AREA := EMd M_MUL (ELit 4096) (EAlu ALU_SRL e_PG (ELit 12)).
Definition sr_ns := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_G)) 18 (ELit 0x97c98)).
Definition kn_ns : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange SC 0 47;
    KRange SC8 0 376;
    KRange e_MEM 16 (2^63-1);
    KAlign e_MEM 16;
    KRange e_PG 1 (2^63-1);
    KAlign e_PG 8;
    KRange BASE 16 (2^63-1);
    KRange PSC 0 47;
    KRange PSC2 0 94;
    KRange AREA 1 (2^63-1);
    KWord (SA e_G 32) 8 e_W;
    KWord (SA e_G 16) 8 e_MEM;
    KWord (SA SC8 622184) 8 e_USG;
    KWord (SA e_MEM (-4)) 1 (ELit 0);
    KWord (SA e_MEM (-3)) 1 e_H3;
    KWord (SA e_MEM (-2)) 2 e_OFF;
    KWord (SA BASE (-16)) 8 e_PG;
    KWord (SA e_PG 16) 8 (EAlu ALU_ADD BASE (ELit (-16)));
    KWord (SA e_PG 32) 8 e_PW;
    KWord (SA e_PG 24) 4 e_PAV;
    KWord (SA e_PG 28) 4 e_PFR;
    KWord (SA AREA 0) 8 e_SEC;
    KWord (SA (ELit 0) 621720) 8 e_SEC;
    KWord (SA PSC2 98984) 2 e_PCSZ;
    KWr (SA SC8 622184) (ELit 8);
    KWr (SA e_MEM 0) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA SC8 622184) (ELit 8);
    KDisj STK (ELit 1024) (SA e_MEM (-4)) (ELit 12);
    KDisj (SA e_G 0) (ELit 40) (SA SC8 622184) (ELit 8);
    KDisj (SA e_MEM (-4)) (ELit 12) (SA SC8 622184) (ELit 8);
    KDisj (SA BASE (-16)) (ELit 8) (SA SC8 622184) (ELit 8);
    KDisj (SA e_PG 0) (ELit 40) (SA SC8 622184) (ELit 8);
    KDisj (SA AREA 0) (ELit 8) (SA SC8 622184) (ELit 8);
    KDisj (SA (ELit 0) 621720) (ELit 8) (SA SC8 622184) (ELit 8);
    KDisj (SA PSC2 98984) (ELit 2) (SA SC8 622184) (ELit 8) ].
Definition scr_ns : scripts := SCR [false; true; true; true; true; false; false; true] [] [].
Definition ss_ns := SS 0x538b0 sr_ns [] kn_ns 45.
Definition RUN_ns := sym_exec SEGS 150 true [0x53688] scr_ns ss_ns [].

Definition scr_pns1 : scripts := SCR [false; true; true; true; true; false; false; true] [] [].
Definition RES_pns1 := Eval vm_compute in sym_exec SEGS 150 true [0x53688] scr_pns1 ss_ns [].
Lemma RES_pns1_ok : sym_exec SEGS 150 true [0x53688] scr_pns1 (SS 0x538b0 sr_ns [] kn_ns 45) [] = RES_pns1.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pns0 : scripts := SCR [false; true; true; true; true; false; true] [] [].
Definition RES_pns0 := Eval vm_compute in sym_exec SEGS 150 true [0x53688] scr_pns0 ss_ns [].
Lemma RES_pns0_ok : sym_exec SEGS 150 true [0x53688] scr_pns0 (SS 0x538b0 sr_ns [] kn_ns 45) [] = RES_pns0.
Proof. vm_compute. reflexivity. Qed.
End AXF_ns.

Module AXF_nsz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section NS.
Context {fx : FPState}.

Definition VALS_ns (G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ : Z) : list Z := [G; sp0; W; USG; MEM; H3; OFF; PG; PW; PAV; PFR; SEC; PCSZ].

Record ns_pre (regs : bvmap 5 word) (m : word -> option byte) (G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ : Z) : Prop := {
  ns_R2 : getr regs 2 = wa (sp0 + -96) ;
  ns_R9 : getr regs 9 = wa 621568 ;
  ns_R10 : getr regs 10 = wa G ;
  ns_R18 : getr regs 18 = wa 621720 ;
  ns_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  ns_rng_G : 1 <= G <= 2^63-1 ;
  ns_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  ns_rng_W : 0 <= W <= 2^64-1 ;
  ns_rng_USG : 0 <= USG <= 2^64-1 ;
  ns_rng_MEM : 1 <= MEM <= 2^63-1 ;
  ns_rng_H3 : 0 <= H3 <= 255 ;
  ns_rng_OFF : 0 <= OFF <= 65535 ;
  ns_rng_PG : 1 <= PG <= 2^63-1 ;
  ns_rng_PW : 0 <= PW <= 2^64-1 ;
  ns_rng_PAV : 0 <= PAV <= 2^32-1 ;
  ns_rng_PFR : 0 <= PFR <= 2^32-1 ;
  ns_rng_SEC : 0 <= SEC <= 2^64-1 ;
  ns_rng_PCSZ : 0 <= PCSZ <= 65535 ;
  ns_ka1 : sp0 mod 16 = 0 ;
  ns_ka4 : G mod 8 = 0 ;
  ns_kr5 : 0 <= SCW W <= 47 ;
  ns_kr6 : 0 <= 8 * SCW W <= 376 ;
  ns_ka8 : MEM mod 16 = 0 ;
  ns_ka10 : PG mod 8 = 0 ;
  ns_kr11 : 16 <= MEM + -16 * ext_Z false 0 2 OFF <= (2^63-1) ;
  ns_kr12 : 0 <= SCW PW <= 47 ;
  ns_kr13 : 0 <= 2 * SCW PW <= 94 ;
  ns_kr14 : 1 <= 4096 * Z.shiftr PG 12 <= (2^63-1) ;
  ns_kw15 : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  ns_kw16 : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa MEM)) ;
  ns_kw17 : rdn SEGS m (wa (8 * SCW W + 622184)) 8 = Some (word_to_le_bytes 8 (wa USG)) ;
  ns_kw18 : rdn SEGS m (wa (MEM + -4)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  ns_kw19 : rdn SEGS m (wa (MEM + -3)) 1 = Some (word_to_le_bytes 1 (wa H3)) ;
  ns_kw20 : rdn SEGS m (wa (MEM + -2)) 2 = Some (word_to_le_bytes 2 (wa OFF)) ;
  ns_kw21 : rdn SEGS m (wa (MEM + -16 * ext_Z false 0 2 OFF + -16)) 8 = Some (word_to_le_bytes 8 (wa PG)) ;
  ns_kw22 : rdn SEGS m (wa (PG + 16)) 8 = Some (word_to_le_bytes 8 (wa (MEM + -16 * ext_Z false 0 2 OFF + -16))) ;
  ns_kw23 : rdn SEGS m (wa (PG + 32)) 8 = Some (word_to_le_bytes 8 (wa PW)) ;
  ns_kw24 : rdn SEGS m (wa (PG + 24)) 4 = Some (word_to_le_bytes 4 (wa PAV)) ;
  ns_kw25 : rdn SEGS m (wa (PG + 28)) 4 = Some (word_to_le_bytes 4 (wa PFR)) ;
  ns_kw26 : rdn SEGS m (wa (4096 * Z.shiftr PG 12 + 0)) 8 = Some (word_to_le_bytes 8 (wa SEC)) ;
  ns_kw27 : rdn SEGS m (wa (0 + 621720)) 8 = Some (word_to_le_bytes 8 (wa SEC)) ;
  ns_kw28 : rdn SEGS m (wa (2 * SCW PW + 98984)) 2 = Some (word_to_le_bytes 2 (wa PCSZ)) ;
  ns_kwr29 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * SCW W + 622184 + d)) k = true ;
  ns_kwr30 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (MEM + 0 + d)) k = true ;
  ns_kd31 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  ns_kd32 : sp0 + -1024 + 1024 <= 8 * SCW W + 622184 \/ 8 * SCW W + 622184 + 8 <= sp0 + -1024 ;
  ns_kd33 : sp0 + -1024 + 1024 <= MEM + -4 \/ MEM + -4 + 12 <= sp0 + -1024 ;
  ns_kd34 : G + 0 + 40 <= 8 * SCW W + 622184 \/ 8 * SCW W + 622184 + 8 <= G + 0 ;
  ns_kd35 : MEM + -4 + 12 <= 8 * SCW W + 622184 \/ 8 * SCW W + 622184 + 8 <= MEM + -4 ;
  ns_kd36 : MEM + -16 * ext_Z false 0 2 OFF + -16 + 8 <= 8 * SCW W + 622184 \/ 8 * SCW W + 622184 + 8 <= MEM + -16 * ext_Z false 0 2 OFF + -16 ;
  ns_kd37 : PG + 0 + 40 <= 8 * SCW W + 622184 \/ 8 * SCW W + 622184 + 8 <= PG + 0 ;
  ns_kd38 : 4096 * Z.shiftr PG 12 + 0 + 8 <= 8 * SCW W + 622184 \/ 8 * SCW W + 622184 + 8 <= 4096 * Z.shiftr PG 12 + 0 ;
  ns_kd39 : 0 + 621720 + 8 <= 8 * SCW W + 622184 \/ 8 * SCW W + 622184 + 8 <= 0 + 621720 ;
  ns_kd40 : 2 * SCW PW + 98984 + 2 <= 8 * SCW W + 622184 \/ 8 * SCW W + 622184 + 8 <= 2 * SCW PW + 98984
}.


#[using="Type"] Lemma ns_setup : forall regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ, ns_pre regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ ->
  regs_ok (Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) AXF_ns.sr_ns regs /\ know_ok SEGS (Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) m AXF_ns.kn_ns.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ P. destruct P as [ns_R2 ns_R9 ns_R10 ns_R18 ns_HSTK ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kw15 ns_kw16 ns_kw17 ns_kw18 ns_kw19 ns_kw20 ns_kw21 ns_kw22 ns_kw23 ns_kw24 ns_kw25 ns_kw26 ns_kw27 ns_kw28 ns_kwr29 ns_kwr30 ns_kd31 ns_kd32 ns_kd33 ns_kd34 ns_kd35 ns_kd36 ns_kd37 ns_kd38 ns_kd39 ns_kd40].
  set (E := Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = OFF) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = PW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = PAV) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = PFR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = SEC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = PCSZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ns.sr_ns.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|].
    - rewrite ns_R2, zeval_sound. cbn [zeval edenot AXF_ns.e_G AXF_ns.e_sp0 AXF_ns.e_W AXF_ns.e_USG AXF_ns.e_MEM AXF_ns.e_H3 AXF_ns.e_OFF AXF_ns.e_PG AXF_ns.e_PW AXF_ns.e_PAV AXF_ns.e_PFR AXF_ns.e_SEC AXF_ns.e_PCSZ AXF_ns.STK AXF_ns.SC AXF_ns.SC8 AXF_ns.BASE AXF_ns.PSC AXF_ns.PSC2 AXF_ns.AREA]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ns_R9. reflexivity.
    - rewrite ns_R10. reflexivity.
    - rewrite ns_R18. reflexivity. }
  unfold know_ok, AXF_ns.kn_ns.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_ns.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia]) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ns.e_G AXF_ns.e_sp0 AXF_ns.e_W AXF_ns.e_USG AXF_ns.e_MEM AXF_ns.e_H3 AXF_ns.e_OFF AXF_ns.e_PG AXF_ns.e_PW AXF_ns.e_PAV AXF_ns.e_PFR AXF_ns.e_SEC AXF_ns.e_PCSZ AXF_ns.STK AXF_ns.SC AXF_ns.SC8 AXF_ns.BASE AXF_ns.PSC AXF_ns.PSC2 AXF_ns.AREA a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ ns_rng_G eq_refl eq_refl), ?(mod64_of_range sp0 _ _ ns_rng_sp0 eq_refl eq_refl), ?(mod64_of_range MEM _ _ ns_rng_MEM eq_refl eq_refl), ?(mod64_of_range H3 _ _ ns_rng_H3 eq_refl eq_refl), ?(mod64_of_range OFF _ _ ns_rng_OFF eq_refl eq_refl), ?(mod64_of_range PG _ _ ns_rng_PG eq_refl eq_refl), ?(mod64_of_range PAV _ _ ns_rng_PAV eq_refl eq_refl), ?(mod64_of_range PFR _ _ ns_rng_PFR eq_refl eq_refl), ?(mod64_of_range PCSZ _ _ ns_rng_PCSZ eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply ns_kwr29 | apply ns_kwr30]; assumption).
  all: try (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14; lia).
  all: first [(clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd31; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd32; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd33; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd34; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd35; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd36; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd37; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd38; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd39; lia) | (clear - ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kd40; lia) | lia].
Qed.


Definition ns_mem_pns1 (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (8 * SCW W + 622184)) (word_to_le_bytes 8 (wa ((USG + Z.land ((((-1 * W) + -1)) mod 2^64) 31) + -32)))) (wa (MEM + 0)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem ns_pns1 : forall regs m rom G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ, ns_pre regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ ->
  scs_denot SEGS m (Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) (snd (fst AXF_ns.RES_pns1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x538b0) m rom) (mkst R (wa 0x53688) (ns_mem_pns1 m regs G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ) rom) /\
    getr R 1 = wa 342288 /\ getr R 2 = wa (sp0 + -96) /\ getr R 8 = wa MEM /\ getr R 9 = wa 621568 /\ getr R 10 = wa PG /\ getr R 11 = wa (Z.land ((ext_Z false 0 1 H3) mod 2^64) 31) /\ getr R 12 = wa (ext_Z false 0 1 H3) /\ getr R 13 = wa ((Z.land ((ext_Z false 0 1 H3) mod 2^64) 31 + 1) * ext_Z false 0 2 PCSZ) /\ getr R 14 = wa (ext_Z false 0 2 PCSZ) /\ getr R 15 = wa (ext_Z false 0 2 PCSZ * Z.land ((ext_Z false 0 1 H3) mod 2^64) 31) /\ getr R 18 = wa 621720 /\ getr R 19 = wa G /\ (forall k, In k [3; 4; 5; 6; 7; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ P Hsc. destruct (ns_setup regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ P) as [HR HK].
  set (E := Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) in *. destruct P as [ns_R2 ns_R9 ns_R10 ns_R18 ns_HSTK ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kw15 ns_kw16 ns_kw17 ns_kw18 ns_kw19 ns_kw20 ns_kw21 ns_kw22 ns_kw23 ns_kw24 ns_kw25 ns_kw26 ns_kw27 ns_kw28 ns_kwr29 ns_kwr30 ns_kd31 ns_kd32 ns_kd33 ns_kd34 ns_kd35 ns_kd36 ns_kd37 ns_kd38 ns_kd39 ns_kd40].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = OFF) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = PW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = PAV) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = PFR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = SEC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = PCSZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 150 [0x53688] AXF_ns.scr_pns1 0x538b0 AXF_ns.sr_ns AXF_ns.kn_ns 45 _ _ _ E m rom regs AXF_ns.RES_pns1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ns.RES_pns1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ns_mem_pns1 m regs G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ns_mem_pns1. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition ns_mem_pns0 (m : word -> option byte) (regs : bvmap 5 word) (G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (8 * SCW W + 622184)) (word_to_le_bytes 8 (wa ((USG + Z.land ((((-1 * W) + -1)) mod 2^64) 31) + -32)))) (wa (MEM + 0)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem ns_pns0 : forall regs m rom G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ, ns_pre regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ ->
  scs_denot SEGS m (Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) (snd (fst AXF_ns.RES_pns0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x538b0) m rom) (mkst R (wa 0x53688) (ns_mem_pns0 m regs G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ) rom) /\
    getr R 1 = wa 342288 /\ getr R 2 = wa (sp0 + -96) /\ getr R 8 = wa MEM /\ getr R 9 = wa 621568 /\ getr R 10 = wa PG /\ getr R 11 = wa (Z.land ((ext_Z false 0 1 H3) mod 2^64) 31) /\ getr R 12 = wa (ext_Z false 0 1 H3) /\ getr R 13 = wa ((Z.land ((ext_Z false 0 1 H3) mod 2^64) 31 + 1) * ext_Z false 0 2 PCSZ) /\ getr R 14 = wa (ext_Z false 0 2 PCSZ) /\ getr R 15 = wa (ext_Z false 0 2 PCSZ * Z.land ((ext_Z false 0 1 H3) mod 2^64) 31) /\ getr R 18 = wa 621720 /\ getr R 19 = wa G /\ (forall k, In k [3; 4; 5; 6; 7; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ P Hsc. destruct (ns_setup regs m G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ P) as [HR HK].
  set (E := Ez regs (VALS_ns G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ)) in *. destruct P as [ns_R2 ns_R9 ns_R10 ns_R18 ns_HSTK ns_rng_G ns_rng_sp0 ns_rng_W ns_rng_USG ns_rng_MEM ns_rng_H3 ns_rng_OFF ns_rng_PG ns_rng_PW ns_rng_PAV ns_rng_PFR ns_rng_SEC ns_rng_PCSZ ns_ka1 ns_ka4 ns_kr5 ns_kr6 ns_ka8 ns_ka10 ns_kr11 ns_kr12 ns_kr13 ns_kr14 ns_kw15 ns_kw16 ns_kw17 ns_kw18 ns_kw19 ns_kw20 ns_kw21 ns_kw22 ns_kw23 ns_kw24 ns_kw25 ns_kw26 ns_kw27 ns_kw28 ns_kwr29 ns_kwr30 ns_kd31 ns_kd32 ns_kd33 ns_kd34 ns_kd35 ns_kd36 ns_kd37 ns_kd38 ns_kd39 ns_kd40].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = USG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = MEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = OFF) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = PG) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = PW) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = PAV) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = PFR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = SEC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = PCSZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 150 [0x53688] AXF_ns.scr_pns0 0x538b0 AXF_ns.sr_ns AXF_ns.kn_ns 45 _ _ _ E m rom regs AXF_ns.RES_pns0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ns.RES_pns0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ns_mem_pns0 m regs G sp0 W USG MEM H3 OFF PG PW PAV PFR SEC PCSZ) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ns_mem_pns0. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NS.
End AXF_nsz.

Module AXF_t1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sp0 := EVar 33.
Definition e_BASE := EVar 34.
Definition e_LEN := EVar 35.
Definition e_ERR := EVar 36.
Definition e_ra := EVar 38.
Definition e_s0 := EVar 39.
Definition e_s1 := EVar 40.
Definition e_s2 := EVar 41.
Definition e_s3 := EVar 42.
Definition STK := SA e_sp0 (-1024).
Definition sr_t1 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 0x53520)) 2 (EAlu ALU_ADD e_sp0 (ELit (-48)))) 4 (ELit 0x77990)) 10 (e_BASE)) 11 (e_LEN)).
Definition kn_t1 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KWord (SA (ELit 0) 0x97c90) 4 (ELit 0);
    KWord (SA (ELit 0) 0x778ec) 4 e_ERR;
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KDisj STK (ELit 1024) (SA (ELit 0) 0x97c90) (ELit 4);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x778ec) (ELit 4) ].
Definition scr_t1 : scripts := SCR [true] [] [].
Definition ss_t1 := SS 0x53a58 sr_t1 [] kn_t1 43.
Definition RUN_t1 := sym_exec SEGS 120 true [0x55310] scr_t1 ss_t1 [].

Definition scr_pt1a : scripts := SCR [true] [] [].
Definition RES_pt1a := Eval vm_compute in sym_exec SEGS 120 true [0x55310] scr_pt1a ss_t1 [].
Lemma RES_pt1a_ok : sym_exec SEGS 120 true [0x55310] scr_pt1a (SS 0x53a58 sr_t1 [] kn_t1 43) [] = RES_pt1a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pt1b : scripts := SCR [false] [] [].
Definition RES_pt1b := Eval vm_compute in sym_exec SEGS 120 true [0x55310] scr_pt1b ss_t1 [].
Lemma RES_pt1b_ok : sym_exec SEGS 120 true [0x55310] scr_pt1b (SS 0x53a58 sr_t1 [] kn_t1 43) [] = RES_pt1b.
Proof. vm_compute. reflexivity. Qed.
End AXF_t1.

Module AXF_t1z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section T1.
Context {fx : FPState}.

Definition VALS_t1 (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : list Z := [0; sp0; BASE; LEN; ERR; 0; ra; s0; s1; s2; s3].

Record t1_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : Prop := {
  t1_R1 : getr regs 1 = wa 341280 ;
  t1_R2 : getr regs 2 = wa (sp0 + -48) ;
  t1_R4 : getr regs 4 = wa 489872 ;
  t1_R10 : getr regs 10 = wa BASE ;
  t1_R11 : getr regs 11 = wa LEN ;
  t1_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  t1_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  t1_rng_BASE : 0 <= BASE <= 2^64-1 ;
  t1_rng_LEN : 0 <= LEN <= 2^64-1 ;
  t1_rng_ERR : 0 <= ERR <= 2^32-1 ;
  t1_rng_ra : 0 <= ra <= 2^64-1 ;
  t1_rng_s0 : 0 <= s0 <= 2^64-1 ;
  t1_rng_s1 : 0 <= s1 <= 2^64-1 ;
  t1_rng_s2 : 0 <= s2 <= 2^64-1 ;
  t1_rng_s3 : 0 <= s3 <= 2^64-1 ;
  t1_ka1 : sp0 mod 16 = 0 ;
  t1_kw3 : rdn SEGS m (wa (0 + 621712)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  t1_kw4 : rdn SEGS m (wa (0 + 489708)) 4 = Some (word_to_le_bytes 4 (wa ERR)) ;
  t1_kw5 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  t1_kw6 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  t1_kw7 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  t1_kw8 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  t1_kw9 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  t1_kd10 : sp0 + -1024 + 1024 <= 0 + 621712 \/ 0 + 621712 + 4 <= sp0 + -1024 ;
  t1_kd11 : sp0 + -1024 + 1024 <= 0 + 489708 \/ 0 + 489708 + 4 <= sp0 + -1024
}.


#[using="Type"] Lemma t1_setup : forall regs m sp0 BASE LEN ERR ra s0 s1 s2 s3, t1_pre regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 ->
  regs_ok (Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) AXF_t1.sr_t1 regs /\ know_ok SEGS (Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) m AXF_t1.kn_t1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 P. destruct P as [t1_R1 t1_R2 t1_R4 t1_R10 t1_R11 t1_HSTK t1_rng_sp0 t1_rng_BASE t1_rng_LEN t1_rng_ERR t1_rng_ra t1_rng_s0 t1_rng_s1 t1_rng_s2 t1_rng_s3 t1_ka1 t1_kw3 t1_kw4 t1_kw5 t1_kw6 t1_kw7 t1_kw8 t1_kw9 t1_kd10 t1_kd11].
  set (E := Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = ERR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_t1.sr_t1.
    apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 4); [apply (regs_ok_pin E _ regs 2); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|]|]|].
    - rewrite t1_R1. reflexivity.
    - rewrite t1_R2, zeval_sound. cbn [zeval edenot AXF_t1.e_sp0 AXF_t1.e_BASE AXF_t1.e_LEN AXF_t1.e_ERR AXF_t1.e_ra AXF_t1.e_s0 AXF_t1.e_s1 AXF_t1.e_s2 AXF_t1.e_s3 AXF_t1.STK]. rewrite ?Z33, ?Z34, ?Z35, ?Z36, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite t1_R4. reflexivity.
    - rewrite t1_R10. reflexivity.
    - rewrite t1_R11. reflexivity. }
  unfold know_ok, AXF_t1.kn_t1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_t1.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_t1.e_sp0 AXF_t1.e_BASE AXF_t1.e_LEN AXF_t1.e_ERR AXF_t1.e_ra AXF_t1.e_s0 AXF_t1.e_s1 AXF_t1.e_s2 AXF_t1.e_s3 AXF_t1.STK a_base a_off].
  all: rewrite ?Z33, ?Z34, ?Z35, ?Z36, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ t1_rng_sp0 eq_refl eq_refl), ?(mod64_of_range ERR _ _ t1_rng_ERR eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - t1_rng_sp0 t1_rng_BASE t1_rng_LEN t1_rng_ERR t1_rng_ra t1_rng_s0 t1_rng_s1 t1_rng_s2 t1_rng_s3 t1_ka1; lia).
  all: first [(clear - t1_rng_sp0 t1_rng_BASE t1_rng_LEN t1_rng_ERR t1_rng_ra t1_rng_s0 t1_rng_s1 t1_rng_s2 t1_rng_s3 t1_ka1 t1_kd10; lia) | (clear - t1_rng_sp0 t1_rng_BASE t1_rng_LEN t1_rng_ERR t1_rng_ra t1_rng_s0 t1_rng_s1 t1_rng_s2 t1_rng_s3 t1_ka1 t1_kd11; lia) | lia].
Qed.


Definition t1_mem_pt1a (m : word -> option byte) (regs : bvmap 5 word) (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem t1_pt1a : forall regs m rom sp0 BASE LEN ERR ra s0 s1 s2 s3, t1_pre regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 ->
  scs_denot SEGS m (Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) (snd (fst AXF_t1.RES_pt1a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53a58) m rom) (mkst R (wa 0x53574) (t1_mem_pt1a m regs sp0 BASE LEN ERR ra s0 s1 s2 s3) rom) /\
    getr R 1 = wa ra /\ getr R 2 = wa sp0 /\ getr R 4 = wa 489872 /\ getr R 8 = wa s0 /\ getr R 9 = wa s1 /\ getr R 10 = wa 621712 /\ getr R 11 = wa 0 /\ getr R 18 = wa s2 /\ getr R 19 = wa s3 /\ (forall k, In k [3; 5; 6; 7; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 BASE LEN ERR ra s0 s1 s2 s3 P Hsc. destruct (t1_setup regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 P) as [HR HK].
  set (E := Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) in *. destruct P as [t1_R1 t1_R2 t1_R4 t1_R10 t1_R11 t1_HSTK t1_rng_sp0 t1_rng_BASE t1_rng_LEN t1_rng_ERR t1_rng_ra t1_rng_s0 t1_rng_s1 t1_rng_s2 t1_rng_s3 t1_ka1 t1_kw3 t1_kw4 t1_kw5 t1_kw6 t1_kw7 t1_kw8 t1_kw9 t1_kd10 t1_kd11].
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = ERR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 120 [0x55310] AXF_t1.scr_pt1a 0x53a58 AXF_t1.sr_t1 AXF_t1.kn_t1 43 _ _ _ E m rom regs AXF_t1.RES_pt1a_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_t1.RES_pt1a fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (t1_mem_pt1a m regs sp0 BASE LEN ERR ra s0 s1 s2 s3) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold t1_mem_pt1a. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition t1_mem_pt1b (m : word -> option byte) (regs : bvmap 5 word) (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (sp0 + -56)) (word_to_le_bytes 8 (wa 341328))) (wa (sp0 + -64)) (word_to_le_bytes 8 (wa BASE))) (wa (sp0 + -72)) (word_to_le_bytes 8 (wa LEN)).

#[using="Type"] Theorem t1_pt1b : forall regs m rom sp0 BASE LEN ERR ra s0 s1 s2 s3, t1_pre regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 ->
  scs_denot SEGS m (Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) (snd (fst AXF_t1.RES_pt1b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53a58) m rom) (mkst R (wa 0x55310) (t1_mem_pt1b m regs sp0 BASE LEN ERR ra s0 s1 s2 s3) rom) /\
    getr R 1 = wa 348932 /\ getr R 2 = wa (sp0 + -80) /\ getr R 4 = wa 489872 /\ getr R 8 = wa LEN /\ getr R 9 = wa BASE /\ getr R 10 = wa BASE /\ getr R 11 = wa LEN /\ getr R 17 = wa 215 /\ getr R 18 = wa 489708 /\ getr R 19 = wa (ext_Z true 0 4 ERR) /\ (forall k, In k [3; 5; 6; 7; 12; 13; 14; 15; 16; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 BASE LEN ERR ra s0 s1 s2 s3 P Hsc. destruct (t1_setup regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 P) as [HR HK].
  set (E := Ez regs (VALS_t1 sp0 BASE LEN ERR ra s0 s1 s2 s3)) in *. destruct P as [t1_R1 t1_R2 t1_R4 t1_R10 t1_R11 t1_HSTK t1_rng_sp0 t1_rng_BASE t1_rng_LEN t1_rng_ERR t1_rng_ra t1_rng_s0 t1_rng_s1 t1_rng_s2 t1_rng_s3 t1_ka1 t1_kw3 t1_kw4 t1_kw5 t1_kw6 t1_kw7 t1_kw8 t1_kw9 t1_kd10 t1_kd11].
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = ERR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 120 [0x55310] AXF_t1.scr_pt1b 0x53a58 AXF_t1.sr_t1 AXF_t1.kn_t1 43 _ _ _ E m rom regs AXF_t1.RES_pt1b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_t1.RES_pt1b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (t1_mem_pt1b m regs sp0 BASE LEN ERR ra s0 s1 s2 s3) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold t1_mem_pt1b. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End T1.
End AXF_t1z.

Module AXF_tad1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G := EVar 33.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 621800.
Definition sr_tad1 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_sc)) 12 (e_G)) 20 (ELit 621568)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 621800))) 22 (ELit 621712)) 23 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 621712))).
Definition kn_tad1 : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KWord (SA e_G 24) 4 (ELit 0);
    KWord (SA e_G 28) 4 (ELit 0);
    KWord (SA e_G 8) 8 e_G;
    KWr ACT (ELit 8);
    KWr (SA e_G 0) (ELit 16);
    KDisj ACT (ELit 8) (SA e_G 0) (ELit 40) ].
Definition scr_tad1 : scripts := SCR [] [] [].
Definition ss_tad1 := SS 0x54108 sr_tad1 [] kn_tad1 34.
Definition RUN_tad1 := sym_exec SEGS 100 true [0x54288] scr_tad1 ss_tad1 [].

Definition scr_ptad1 : scripts := SCR [] [] [].
Definition RES_ptad1 := Eval vm_compute in sym_exec SEGS 100 true [0x54288] scr_ptad1 ss_tad1 [].
Lemma RES_ptad1_ok : sym_exec SEGS 100 true [0x54288] scr_ptad1 (SS 0x54108 sr_tad1 [] kn_tad1 34) [] = RES_ptad1.
Proof. vm_compute. reflexivity. Qed.
End AXF_tad1.

Module AXF_tad1z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section TAD1.
Context {fx : FPState}.

Definition VALS_tad1 (sc G : Z) : list Z := [sc; G].

Record tad1_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G : Z) : Prop := {
  tad1_R8 : getr regs 8 = wa sc ;
  tad1_R12 : getr regs 12 = wa G ;
  tad1_R20 : getr regs 20 = wa 621568 ;
  tad1_R21 : getr regs 21 = wa ((8 * sc) + 621800) ;
  tad1_R22 : getr regs 22 = wa 621712 ;
  tad1_R23 : getr regs 23 = wa ((8 * sc) + 621712) ;
  tad1_rng_sc : 0 <= sc <= 47 ;
  tad1_rng_G : 1 <= G <= 2^63-1 ;
  tad1_ka2 : G mod 8 = 0 ;
  tad1_kw3 : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  tad1_kw4 : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  tad1_kw5 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  tad1_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 621800 + d)) k = true ;
  tad1_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  tad1_kd8 : 8 * sc + 621800 + 8 <= G + 0 \/ G + 0 + 40 <= 8 * sc + 621800
}.


#[using="Type"] Lemma tad1_setup : forall regs m sc G, tad1_pre regs m sc G ->
  regs_ok (Ez regs (VALS_tad1 sc G)) AXF_tad1.sr_tad1 regs /\ know_ok SEGS (Ez regs (VALS_tad1 sc G)) m AXF_tad1.kn_tad1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G P. destruct P as [tad1_R8 tad1_R12 tad1_R20 tad1_R21 tad1_R22 tad1_R23 tad1_rng_sc tad1_rng_G tad1_ka2 tad1_kw3 tad1_kw4 tad1_kw5 tad1_kwr6 tad1_kwr7 tad1_kd8].
  set (E := Ez regs (VALS_tad1 sc G)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_tad1.sr_tad1.
    apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite tad1_R8. reflexivity.
    - rewrite tad1_R12. reflexivity.
    - rewrite tad1_R20. reflexivity.
    - rewrite tad1_R21, zeval_sound. cbn [zeval edenot AXF_tad1.e_sc AXF_tad1.e_G AXF_tad1.ACT]. rewrite ?Z32, ?Z33. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite tad1_R22. reflexivity.
    - rewrite tad1_R23, zeval_sound. cbn [zeval edenot AXF_tad1.e_sc AXF_tad1.e_G AXF_tad1.ACT]. rewrite ?Z32, ?Z33. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_tad1.kn_tad1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_tad1.e_sc AXF_tad1.e_G AXF_tad1.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ tad1_rng_sc eq_refl eq_refl), ?(mod64_of_range G _ _ tad1_rng_G eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply tad1_kwr6 | apply tad1_kwr7]; assumption).
  all: try (clear - tad1_rng_sc tad1_rng_G tad1_ka2; lia).
  all: first [(clear - tad1_rng_sc tad1_rng_G tad1_ka2 tad1_kd8; lia) | lia].
Qed.


Definition tad1_mem_ptad1 (m : word -> option byte) (regs : bvmap 5 word) (sc G : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (8 * sc + 621800)) (word_to_le_bytes 8 (wa 0))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem tad1_ptad1 : forall regs m rom sc G, tad1_pre regs m sc G ->
  scs_denot SEGS m (Ez regs (VALS_tad1 sc G)) (snd (fst AXF_tad1.RES_ptad1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54108) m rom) (mkst R (wa 0x54288) (tad1_mem_ptad1 m regs sc G) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa 0 /\ getr R 11 = wa 0 /\ getr R 12 = wa G /\ getr R 20 = wa 621568 /\ getr R 21 = wa ((8 * sc) + 621800) /\ getr R 22 = wa 621712 /\ getr R 23 = wa ((8 * sc) + 621712) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 13; 14; 15; 16; 17; 18; 19; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G P Hsc. destruct (tad1_setup regs m sc G P) as [HR HK].
  set (E := Ez regs (VALS_tad1 sc G)) in *. destruct P as [tad1_R8 tad1_R12 tad1_R20 tad1_R21 tad1_R22 tad1_R23 tad1_rng_sc tad1_rng_G tad1_ka2 tad1_kw3 tad1_kw4 tad1_kw5 tad1_kwr6 tad1_kwr7 tad1_kd8].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x54288] AXF_tad1.scr_ptad1 0x54108 AXF_tad1.sr_tad1 AXF_tad1.kn_tad1 34 _ _ _ E m rom regs AXF_tad1.RES_ptad1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_tad1.RES_ptad1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (tad1_mem_ptad1 m regs sc G) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold tad1_mem_ptad1. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End TAD1.
End AXF_tad1z.

Module AXF_tadn.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G := EVar 33.
Definition e_nx := EVar 34.
Definition e_pv := EVar 35.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 621800.
Definition sr_tadn := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_sc)) 12 (e_G)) 20 (ELit 621568)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 621800))) 22 (ELit 621712)) 23 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 621712))).
Definition kn_tadn : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_nx 1 (2^63-1);
    KRange e_pv 1 (2^63-1);
    KWord (SA e_G 24) 4 (ELit 0);
    KWord (SA e_G 28) 4 (ELit 0);
    KWord (SA e_G 8) 8 e_nx;
    KWord (SA e_G 0) 8 e_pv;
    KWord ACT 8 e_G;
    KWr ACT (ELit 8);
    KWr (SA e_G 0) (ELit 16);
    KWr (SA e_pv 8) (ELit 8);
    KWr (SA e_nx 0) (ELit 8);
    KDisj ACT (ELit 8) (SA e_G 0) (ELit 40);
    KDisj ACT (ELit 8) (SA e_pv 8) (ELit 8);
    KDisj ACT (ELit 8) (SA e_nx 0) (ELit 8);
    KDisj (SA e_pv 8) (ELit 8) (SA e_G 0) (ELit 40);
    KDisj (SA e_nx 0) (ELit 8) (SA e_G 0) (ELit 40) ].
Definition scr_tadn : scripts := SCR [false] [] [].
Definition ss_tadn := SS 0x54108 sr_tadn [] kn_tadn 36.
Definition RUN_tadn := sym_exec SEGS 100 true [0x54170] scr_tadn ss_tadn [].

Definition scr_ptadn : scripts := SCR [false] [] [].
Definition RES_ptadn := Eval vm_compute in sym_exec SEGS 100 true [0x54170] scr_ptadn ss_tadn [].
Lemma RES_ptadn_ok : sym_exec SEGS 100 true [0x54170] scr_ptadn (SS 0x54108 sr_tadn [] kn_tadn 36) [] = RES_ptadn.
Proof. vm_compute. reflexivity. Qed.
End AXF_tadn.

Module AXF_tadnz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section TADN.
Context {fx : FPState}.

Definition VALS_tadn (sc G nx pv : Z) : list Z := [sc; G; nx; pv].

Record tadn_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G nx pv : Z) : Prop := {
  tadn_R8 : getr regs 8 = wa sc ;
  tadn_R12 : getr regs 12 = wa G ;
  tadn_R20 : getr regs 20 = wa 621568 ;
  tadn_R21 : getr regs 21 = wa ((8 * sc) + 621800) ;
  tadn_R22 : getr regs 22 = wa 621712 ;
  tadn_R23 : getr regs 23 = wa ((8 * sc) + 621712) ;
  tadn_rng_sc : 0 <= sc <= 47 ;
  tadn_rng_G : 1 <= G <= 2^63-1 ;
  tadn_rng_nx : 1 <= nx <= 2^63-1 ;
  tadn_rng_pv : 1 <= pv <= 2^63-1 ;
  tadn_ka2 : G mod 8 = 0 ;
  tadn_kw5 : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  tadn_kw6 : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  tadn_kw7 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa nx)) ;
  tadn_kw8 : rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa pv)) ;
  tadn_kw9 : rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  tadn_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 621800 + d)) k = true ;
  tadn_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  tadn_kwr12 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (pv + 8 + d)) k = true ;
  tadn_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (nx + 0 + d)) k = true ;
  tadn_kd14 : 8 * sc + 621800 + 8 <= G + 0 \/ G + 0 + 40 <= 8 * sc + 621800 ;
  tadn_kd15 : 8 * sc + 621800 + 8 <= pv + 8 \/ pv + 8 + 8 <= 8 * sc + 621800 ;
  tadn_kd16 : 8 * sc + 621800 + 8 <= nx + 0 \/ nx + 0 + 8 <= 8 * sc + 621800 ;
  tadn_kd17 : pv + 8 + 8 <= G + 0 \/ G + 0 + 40 <= pv + 8 ;
  tadn_kd18 : nx + 0 + 8 <= G + 0 \/ G + 0 + 40 <= nx + 0
}.


#[using="Type"] Lemma tadn_setup : forall regs m sc G nx pv, tadn_pre regs m sc G nx pv ->
  regs_ok (Ez regs (VALS_tadn sc G nx pv)) AXF_tadn.sr_tadn regs /\ know_ok SEGS (Ez regs (VALS_tadn sc G nx pv)) m AXF_tadn.kn_tadn.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G nx pv P. destruct P as [tadn_R8 tadn_R12 tadn_R20 tadn_R21 tadn_R22 tadn_R23 tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kw5 tadn_kw6 tadn_kw7 tadn_kw8 tadn_kw9 tadn_kwr10 tadn_kwr11 tadn_kwr12 tadn_kwr13 tadn_kd14 tadn_kd15 tadn_kd16 tadn_kd17 tadn_kd18].
  set (E := Ez regs (VALS_tadn sc G nx pv)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = pv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_tadn.sr_tadn.
    apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite tadn_R8. reflexivity.
    - rewrite tadn_R12. reflexivity.
    - rewrite tadn_R20. reflexivity.
    - rewrite tadn_R21, zeval_sound. cbn [zeval edenot AXF_tadn.e_sc AXF_tadn.e_G AXF_tadn.e_nx AXF_tadn.e_pv AXF_tadn.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite tadn_R22. reflexivity.
    - rewrite tadn_R23, zeval_sound. cbn [zeval edenot AXF_tadn.e_sc AXF_tadn.e_G AXF_tadn.e_nx AXF_tadn.e_pv AXF_tadn.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_tadn.kn_tadn.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_tadn.e_sc AXF_tadn.e_G AXF_tadn.e_nx AXF_tadn.e_pv AXF_tadn.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ tadn_rng_sc eq_refl eq_refl), ?(mod64_of_range G _ _ tadn_rng_G eq_refl eq_refl), ?(mod64_of_range nx _ _ tadn_rng_nx eq_refl eq_refl), ?(mod64_of_range pv _ _ tadn_rng_pv eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply tadn_kwr10 | apply tadn_kwr11 | apply tadn_kwr12 | apply tadn_kwr13]; assumption).
  all: try (clear - tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2; lia).
  all: first [(clear - tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kd14; lia) | (clear - tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kd15; lia) | (clear - tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kd16; lia) | (clear - tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kd17; lia) | (clear - tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kd18; lia) | lia].
Qed.


Definition tadn_mem_ptadn (m : word -> option byte) (regs : bvmap 5 word) (sc G nx pv : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (pv + 8)) (word_to_le_bytes 8 (wa nx))) (wa (nx + 0)) (word_to_le_bytes 8 (wa pv))) (wa (8 * sc + 621800)) (word_to_le_bytes 8 (wa nx))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem tadn_ptadn : forall regs m rom sc G nx pv, tadn_pre regs m sc G nx pv ->
  scs_denot SEGS m (Ez regs (VALS_tadn sc G nx pv)) (snd (fst AXF_tadn.RES_ptadn)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54108) m rom) (mkst R (wa 0x54170) (tadn_mem_ptadn m regs sc G nx pv) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa nx /\ getr R 11 = wa nx /\ getr R 12 = wa G /\ getr R 20 = wa 621568 /\ getr R 21 = wa ((8 * sc) + 621800) /\ getr R 22 = wa 621712 /\ getr R 23 = wa ((8 * sc) + 621712) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 13; 14; 15; 16; 17; 18; 19; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G nx pv P Hsc. destruct (tadn_setup regs m sc G nx pv P) as [HR HK].
  set (E := Ez regs (VALS_tadn sc G nx pv)) in *. destruct P as [tadn_R8 tadn_R12 tadn_R20 tadn_R21 tadn_R22 tadn_R23 tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kw5 tadn_kw6 tadn_kw7 tadn_kw8 tadn_kw9 tadn_kwr10 tadn_kwr11 tadn_kwr12 tadn_kwr13 tadn_kd14 tadn_kd15 tadn_kd16 tadn_kd17 tadn_kd18].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = pv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x54170] AXF_tadn.scr_ptadn 0x54108 AXF_tadn.sr_tadn AXF_tadn.kn_tadn 36 _ _ _ E m rom regs AXF_tadn.RES_ptadn_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_tadn.RES_ptadn fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (tadn_mem_ptadn m regs sc G nx pv) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold tadn_mem_ptadn. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End TADN.
End AXF_tadnz.

Module AXF_tar.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G := EVar 33.
Definition e_freed := EVar 34.
Definition e_nx := EVar 35.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 621800.
Definition sr_tar := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_sc)) 12 (e_G)) 20 (ELit 621568)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 621800))) 22 (ELit 621712)) 23 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 621712))).
Definition kn_tar : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_freed 1 (2^32-1);
    KRange e_nx 1 (2^63-1);
    KWord (SA e_G 24) 4 (ELit 0);
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 8) 8 e_nx;
    KWr ACT (ELit 8);
    KDisj ACT (ELit 8) (SA e_G 0) (ELit 40) ].
Definition scr_tar : scripts := SCR [false] [] [].
Definition ss_tar := SS 0x54108 sr_tar [] kn_tar 36.
Definition RUN_tar := sym_exec SEGS 100 true [0x54170] scr_tar ss_tar [].

Definition scr_ptar : scripts := SCR [false] [] [].
Definition RES_ptar := Eval vm_compute in sym_exec SEGS 100 true [0x54170] scr_ptar ss_tar [].
Lemma RES_ptar_ok : sym_exec SEGS 100 true [0x54170] scr_ptar (SS 0x54108 sr_tar [] kn_tar 36) [] = RES_ptar.
Proof. vm_compute. reflexivity. Qed.
End AXF_tar.

Module AXF_tarz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section TAR.
Context {fx : FPState}.

Definition VALS_tar (sc G freed nx : Z) : list Z := [sc; G; freed; nx].

Record tar_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G freed nx : Z) : Prop := {
  tar_R8 : getr regs 8 = wa sc ;
  tar_R12 : getr regs 12 = wa G ;
  tar_R20 : getr regs 20 = wa 621568 ;
  tar_R21 : getr regs 21 = wa ((8 * sc) + 621800) ;
  tar_R22 : getr regs 22 = wa 621712 ;
  tar_R23 : getr regs 23 = wa ((8 * sc) + 621712) ;
  tar_rng_sc : 0 <= sc <= 47 ;
  tar_rng_G : 1 <= G <= 2^63-1 ;
  tar_rng_freed : 1 <= freed <= 2^32-1 ;
  tar_rng_nx : 1 <= nx <= 2^63-1 ;
  tar_ka2 : G mod 8 = 0 ;
  tar_kw5 : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  tar_kw6 : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  tar_kw7 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa nx)) ;
  tar_kwr8 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 621800 + d)) k = true ;
  tar_kd9 : 8 * sc + 621800 + 8 <= G + 0 \/ G + 0 + 40 <= 8 * sc + 621800
}.


#[using="Type"] Lemma tar_setup : forall regs m sc G freed nx, tar_pre regs m sc G freed nx ->
  regs_ok (Ez regs (VALS_tar sc G freed nx)) AXF_tar.sr_tar regs /\ know_ok SEGS (Ez regs (VALS_tar sc G freed nx)) m AXF_tar.kn_tar.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G freed nx P. destruct P as [tar_R8 tar_R12 tar_R20 tar_R21 tar_R22 tar_R23 tar_rng_sc tar_rng_G tar_rng_freed tar_rng_nx tar_ka2 tar_kw5 tar_kw6 tar_kw7 tar_kwr8 tar_kd9].
  set (E := Ez regs (VALS_tar sc G freed nx)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_tar.sr_tar.
    apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite tar_R8. reflexivity.
    - rewrite tar_R12. reflexivity.
    - rewrite tar_R20. reflexivity.
    - rewrite tar_R21, zeval_sound. cbn [zeval edenot AXF_tar.e_sc AXF_tar.e_G AXF_tar.e_freed AXF_tar.e_nx AXF_tar.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite tar_R22. reflexivity.
    - rewrite tar_R23, zeval_sound. cbn [zeval edenot AXF_tar.e_sc AXF_tar.e_G AXF_tar.e_freed AXF_tar.e_nx AXF_tar.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_tar.kn_tar.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_tar.e_sc AXF_tar.e_G AXF_tar.e_freed AXF_tar.e_nx AXF_tar.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ tar_rng_sc eq_refl eq_refl), ?(mod64_of_range G _ _ tar_rng_G eq_refl eq_refl), ?(mod64_of_range freed _ _ tar_rng_freed eq_refl eq_refl), ?(mod64_of_range nx _ _ tar_rng_nx eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply tar_kwr8]; assumption).
  all: try (clear - tar_rng_sc tar_rng_G tar_rng_freed tar_rng_nx tar_ka2; lia).
  all: first [(clear - tar_rng_sc tar_rng_G tar_rng_freed tar_rng_nx tar_ka2 tar_kd9; lia) | lia].
Qed.


Definition tar_mem_ptar (m : word -> option byte) (regs : bvmap 5 word) (sc G freed nx : Z) : word -> option byte :=
  wbytes (m) (wa (8 * sc + 621800)) (word_to_le_bytes 8 (wa nx)).

#[using="Type"] Theorem tar_ptar : forall regs m rom sc G freed nx, tar_pre regs m sc G freed nx ->
  scs_denot SEGS m (Ez regs (VALS_tar sc G freed nx)) (snd (fst AXF_tar.RES_ptar)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54108) m rom) (mkst R (wa 0x54170) (tar_mem_ptar m regs sc G freed nx) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa nx /\ getr R 12 = wa G /\ getr R 20 = wa 621568 /\ getr R 21 = wa ((8 * sc) + 621800) /\ getr R 22 = wa 621712 /\ getr R 23 = wa ((8 * sc) + 621712) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 13; 14; 15; 16; 17; 18; 19; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G freed nx P Hsc. destruct (tar_setup regs m sc G freed nx P) as [HR HK].
  set (E := Ez regs (VALS_tar sc G freed nx)) in *. destruct P as [tar_R8 tar_R12 tar_R20 tar_R21 tar_R22 tar_R23 tar_rng_sc tar_rng_G tar_rng_freed tar_rng_nx tar_ka2 tar_kw5 tar_kw6 tar_kw7 tar_kwr8 tar_kd9].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x54170] AXF_tar.scr_ptar 0x54108 AXF_tar.sr_tar AXF_tar.kn_tar 36 _ _ _ E m rom regs AXF_tar.RES_ptar_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_tar.RES_ptar fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (tar_mem_ptar m regs sc G freed nx) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold tar_mem_ptar. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End TAR.
End AXF_tarz.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section DQ2.
Context {fx : FPState}.

Definition VALS_dq2 (G sc sp0 NX PR NMEM AIDXB NFR : Z) : list Z := [G; sc; sp0; NX; PR; NMEM; AIDXB; NFR].

Record dq2_pre (regs : bvmap 5 word) (m : word -> option byte) (G sc sp0 NX PR NMEM AIDXB NFR : Z) : Prop := {
  dq2_R2 : getr regs 2 = wa (sp0 + -96) ;
  dq2_R9 : getr regs 9 = wa 621568 ;
  dq2_R10 : getr regs 10 = wa G ;
  dq2_R12 : getr regs 12 = wa sc ;
  dq2_R18 : getr regs 18 = wa 621720 ;
  dq2_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  dq2_rng_G : 1 <= G <= 2^63-1 ;
  dq2_rng_sc : 0 <= sc <= 47 ;
  dq2_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  dq2_rng_NX : 1 <= NX <= 2^63-1 ;
  dq2_rng_PR : 1 <= PR <= 2^63-1 ;
  dq2_rng_NMEM : 1 <= NMEM <= 2^63-1 ;
  dq2_rng_AIDXB : 0 <= AIDXB <= 255 ;
  dq2_rng_NFR : 0 <= NFR <= 2^32-1 ;
  dq2_ka1 : sp0 mod 16 = 0 ;
  dq2_ka4 : G mod 8 = 0 ;
  dq2_kr6 : 0 <= 8 * sc <= 376 ;
  dq2_ka8 : NX mod 8 = 0 ;
  dq2_kw13 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa NX)) ;
  dq2_kw14 : rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa PR)) ;
  dq2_kw15 : rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  dq2_kw16 : rdn SEGS m (wa (NX + 24)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  dq2_kw17 : rdn SEGS m (wa (NX + 16)) 8 = Some (word_to_le_bytes 8 (wa NMEM)) ;
  dq2_kw18 : rdn SEGS m (wa (NMEM + 8)) 1 = Some (word_to_le_bytes 1 (wa AIDXB)) ;
  dq2_kw19 : rdn SEGS m (wa (NX + 28)) 4 = Some (word_to_le_bytes 4 (wa NFR)) ;
  dq2_kwr20 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  dq2_kwr21 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (PR + 8 + d)) k = true ;
  dq2_kwr22 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (NX + 0 + d)) k = true ;
  dq2_kwr23 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 621800 + d)) k = true ;
  dq2_kwr24 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (NX + 24 + d)) k = true ;
  dq2_kd25 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  dq2_kd26 : sp0 + -1024 + 1024 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= sp0 + -1024 ;
  dq2_kd27 : sp0 + -1024 + 1024 <= PR + 8 \/ PR + 8 + 8 <= sp0 + -1024 ;
  dq2_kd28 : sp0 + -1024 + 1024 <= NX + 0 \/ NX + 0 + 40 <= sp0 + -1024 ;
  dq2_kd29 : sp0 + -1024 + 1024 <= NMEM + 8 \/ NMEM + 8 + 1 <= sp0 + -1024 ;
  dq2_kd30 : G + 0 + 40 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= G + 0 ;
  dq2_kd31 : G + 0 + 40 <= PR + 8 \/ PR + 8 + 8 <= G + 0 ;
  dq2_kd32 : G + 0 + 40 <= NX + 0 \/ NX + 0 + 40 <= G + 0 ;
  dq2_kd33 : 8 * sc + 621800 + 8 <= PR + 8 \/ PR + 8 + 8 <= 8 * sc + 621800 ;
  dq2_kd34 : 8 * sc + 621800 + 8 <= NX + 0 \/ NX + 0 + 40 <= 8 * sc + 621800 ;
  dq2_kd35 : PR + 8 + 8 <= NX + 16 \/ NX + 16 + 16 <= PR + 8 ;
  dq2_kd36 : NMEM + 8 + 1 <= PR + 8 \/ PR + 8 + 8 <= NMEM + 8 ;
  dq2_kd37 : NMEM + 8 + 1 <= NX + 0 \/ NX + 0 + 40 <= NMEM + 8 ;
  dq2_kd38 : NMEM + 8 + 1 <= G + 0 \/ G + 0 + 40 <= NMEM + 8 ;
  dq2_kd39 : NMEM + 8 + 1 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= NMEM + 8
}.


#[using="Type"] Lemma dq2_setup : forall regs m G sc sp0 NX PR NMEM AIDXB NFR, dq2_pre regs m G sc sp0 NX PR NMEM AIDXB NFR ->
  regs_ok (Ez regs (VALS_dq2 G sc sp0 NX PR NMEM AIDXB NFR)) AXF_dq2.sr_dq2 regs /\ know_ok SEGS (Ez regs (VALS_dq2 G sc sp0 NX PR NMEM AIDXB NFR)) m AXF_dq2.kn_dq2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sc sp0 NX PR NMEM AIDXB NFR P. destruct P as [dq2_R2 dq2_R9 dq2_R10 dq2_R12 dq2_R18 dq2_HSTK dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kw13 dq2_kw14 dq2_kw15 dq2_kw16 dq2_kw17 dq2_kw18 dq2_kw19 dq2_kwr20 dq2_kwr21 dq2_kwr22 dq2_kwr23 dq2_kwr24 dq2_kd25 dq2_kd26 dq2_kd27 dq2_kd28 dq2_kd29 dq2_kd30 dq2_kd31 dq2_kd32 dq2_kd33 dq2_kd34 dq2_kd35 dq2_kd36 dq2_kd37 dq2_kd38 dq2_kd39].
  set (E := Ez regs (VALS_dq2 G sc sp0 NX PR NMEM AIDXB NFR)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NX) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = PR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = NMEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = AIDXB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = NFR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_dq2.sr_dq2.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|].
    - rewrite dq2_R2, zeval_sound. cbn [zeval edenot AXF_dq2.e_G AXF_dq2.e_sc AXF_dq2.e_sp0 AXF_dq2.e_NX AXF_dq2.e_PR AXF_dq2.e_NMEM AXF_dq2.e_AIDXB AXF_dq2.e_NFR AXF_dq2.STK AXF_dq2.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite dq2_R9. reflexivity.
    - rewrite dq2_R10. reflexivity.
    - rewrite dq2_R12. reflexivity.
    - rewrite dq2_R18. reflexivity. }
  unfold know_ok, AXF_dq2.kn_dq2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_dq2.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_dq2.e_G AXF_dq2.e_sc AXF_dq2.e_sp0 AXF_dq2.e_NX AXF_dq2.e_PR AXF_dq2.e_NMEM AXF_dq2.e_AIDXB AXF_dq2.e_NFR AXF_dq2.STK AXF_dq2.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ dq2_rng_G eq_refl eq_refl), ?(mod64_of_range sc _ _ dq2_rng_sc eq_refl eq_refl), ?(mod64_of_range sp0 _ _ dq2_rng_sp0 eq_refl eq_refl), ?(mod64_of_range NX _ _ dq2_rng_NX eq_refl eq_refl), ?(mod64_of_range PR _ _ dq2_rng_PR eq_refl eq_refl), ?(mod64_of_range NMEM _ _ dq2_rng_NMEM eq_refl eq_refl), ?(mod64_of_range AIDXB _ _ dq2_rng_AIDXB eq_refl eq_refl), ?(mod64_of_range NFR _ _ dq2_rng_NFR eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply dq2_kwr20 | apply dq2_kwr21 | apply dq2_kwr22 | apply dq2_kwr23 | apply dq2_kwr24]; assumption).
  all: try (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8; lia).
  all: first [(clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd25; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd26; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd27; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd28; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd29; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd30; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd31; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd32; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd33; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd34; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd35; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd36; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd37; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd38; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd39; lia) | lia].
Qed.


Definition dq2_mem_pdq2 (m : word -> option byte) (regs : bvmap 5 word) (G sc sp0 NX PR NMEM AIDXB NFR : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (PR + 8)) (word_to_le_bytes 8 (wa NX))) (wa (NX + 0)) (word_to_le_bytes 8 (wa PR))) (wa (8 * sc + 621800)) (word_to_le_bytes 8 (wa NX))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0))) (wa (NX + 28)) (word_to_le_bytes 4 (wa (Z.ldiff NFR (2 ^ (Z.land AIDXB 31 + 1) - 1))))) (wa (NX + 24)) (word_to_le_bytes 4 (wa (Z.land NFR (2 ^ (Z.land AIDXB 31 + 1) - 1)))).

#[using="Type"] Theorem dq2_pdq2 : forall regs m rom G sc sp0 NX PR NMEM AIDXB NFR, dq2_pre regs m G sc sp0 NX PR NMEM AIDXB NFR ->
  scs_denot SEGS m (Ez regs (VALS_dq2 G sc sp0 NX PR NMEM AIDXB NFR)) (snd (fst AXF_dq2.RES_pdq2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5379c) m rom) (mkst R (wa 0x538b0) (dq2_mem_pdq2 m regs G sc sp0 NX PR NMEM AIDXB NFR) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 5 = wa 0 /\ getr R 9 = wa 621568 /\ getr R 10 = wa G /\ getr R 11 = wa NX /\ getr R 13 = wa (NX + 28) /\ getr R 18 = wa 621720 /\ (forall k, In k [1; 3; 4; 6; 7; 8; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sc sp0 NX PR NMEM AIDXB NFR P Hsc. destruct (dq2_setup regs m G sc sp0 NX PR NMEM AIDXB NFR P) as [HR HK].
  set (E := Ez regs (VALS_dq2 G sc sp0 NX PR NMEM AIDXB NFR)) in *. destruct P as [dq2_R2 dq2_R9 dq2_R10 dq2_R12 dq2_R18 dq2_HSTK dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kw13 dq2_kw14 dq2_kw15 dq2_kw16 dq2_kw17 dq2_kw18 dq2_kw19 dq2_kwr20 dq2_kwr21 dq2_kwr22 dq2_kwr23 dq2_kwr24 dq2_kd25 dq2_kd26 dq2_kd27 dq2_kd28 dq2_kd29 dq2_kd30 dq2_kd31 dq2_kd32 dq2_kd33 dq2_kd34 dq2_kd35 dq2_kd36 dq2_kd37 dq2_kd38 dq2_kd39].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NX) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = PR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = NMEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = AIDXB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = NFR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 150 [0x538b0] AXF_dq2.scr_pdq2 0x5379c AXF_dq2.sr_dq2 AXF_dq2.kn_dq2 40 _ _ _ E m rom regs AXF_dq2.RES_pdq2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_dq2.RES_pdq2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (dq2_mem_pdq2 m regs G sc sp0 NX PR NMEM AIDXB NFR) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold dq2_mem_pdq2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_avail_le; assumption).
    all: try (rewrite zeval_sound; cbn [zeval edenot]; rewrite w_subw, w_sllw; unfold v_subw, v_sllw; rewrite ?u_wa; repeat dsc_rw; repeat dsc_mod; litmods; apply act_freed_le2; assumption).
  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End DQ2.
