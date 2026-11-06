(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_put AXG_np AXG_q1.

Module AXF_qt1.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Definition e_QC := EVar 32.
Definition e_qb := EVar 33.
Definition e_mx := EVar 34.
Definition sr_qt1 := (sr_upd (sr_upd sr_id 9 (e_QC)) 22 (e_mx)).
Definition kn_qt1 : list kentry :=
  [ KRange e_QC 1 (2^47);
    KWord (SA e_QC 24) 8 e_qb ].
Definition scr_qt1 : scripts := SCR [false] [] [].
Definition ss_qt1 := SS 0x43e14 sr_qt1 [] kn_qt1 35.
Definition RUN_qt1 := sym_exec SEGS 8 true [0x43d4c] scr_qt1 ss_qt1 [].

Definition scr_pt1 : scripts := SCR [false] [] [].
Definition RES_pt1 := Eval vm_compute in sym_exec SEGS 8 true [0x43d4c] scr_pt1 ss_qt1 [].
Lemma RES_pt1_ok : sym_exec SEGS 8 true [0x43d4c] scr_pt1 (SS 0x43e14 sr_qt1 [] kn_qt1 35) [] = RES_pt1.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_qt1.

Module AXF_qt1z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section QT1.
Context {fx : FPState}.

Definition VALS_qt1 (QC qb mx : Z) : list Z := [QC; qb; mx].

Record qt1_pre (regs : bvmap 5 word) (m : word -> option byte) (QC qb mx : Z) : Prop := {
  qt1_R9 : getr regs 9 = wa QC ;
  qt1_R22 : getr regs 22 = wa mx ;
  qt1_rng_QC : 1 <= QC <= 2^47 ;
  qt1_rng_qb : 0 <= qb <= 2^62 ;
  qt1_rng_mx : 0 <= mx <= 2^62 ;
  qt1_kw1 : rdn SEGS m (wa (QC + 24)) 8 = Some (word_to_le_bytes 8 (wa qb))
}.


#[using="Type"] Lemma qt1_setup : forall regs m QC qb mx, qt1_pre regs m QC qb mx ->
  regs_ok (Ez regs (VALS_qt1 QC qb mx)) AXF_qt1.sr_qt1 regs /\ know_ok SEGS (Ez regs (VALS_qt1 QC qb mx)) m AXF_qt1.kn_qt1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m QC qb mx P. destruct P as [qt1_R9 qt1_R22 qt1_rng_QC qt1_rng_qb qt1_rng_mx qt1_kw1].
  set (E := Ez regs (VALS_qt1 QC qb mx)).
  assert (Z32 : bv_unsigned (ev E 32) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = qb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mx) by (apply zatom; [reflexivity | reflexivity | zrange]).

  split.
  { unfold AXF_qt1.sr_qt1.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|]|].
    - rewrite qt1_R9. reflexivity.
    - rewrite qt1_R22. reflexivity. }
  unfold know_ok, AXF_qt1.kn_qt1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_qt1.e_QC AXF_qt1.e_qb AXF_qt1.e_mx a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range QC _ _ qt1_rng_QC eq_refl eq_refl), ?(mod64_of_range qb _ _ qt1_rng_qb eq_refl eq_refl), ?(mod64_of_range mx _ _ qt1_rng_mx eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - qt1_rng_QC qt1_rng_qb qt1_rng_mx; lia).
  all: first [lia].
Qed.


Definition qt1_mem_pt1 (m : word -> option byte) (regs : bvmap 5 word) (QC qb mx : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem qt1_pt1 : forall regs m rom QC qb mx, qt1_pre regs m QC qb mx ->
  scs_denot SEGS m (Ez regs (VALS_qt1 QC qb mx)) (snd (fst AXF_qt1.RES_pt1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43e14) m rom) (mkst R (wa 0x43d4c) (qt1_mem_pt1 m regs QC qb mx) rom) /\
    getr R 9 = wa QC /\ getr R 10 = wa qb /\ getr R 22 = wa mx /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom QC qb mx P Hsc. destruct (qt1_setup regs m QC qb mx P) as [HR HK].
  set (E := Ez regs (VALS_qt1 QC qb mx)) in *. destruct P as [qt1_R9 qt1_R22 qt1_rng_QC qt1_rng_qb qt1_rng_mx qt1_kw1].
  assert (Z32 : bv_unsigned (ev E 32) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = qb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mx) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 8 [0x43d4c] AXF_qt1.scr_pt1 0x43e14 AXF_qt1.sr_qt1 AXF_qt1.kn_qt1 35 _ _ _ E m rom regs AXF_qt1.RES_pt1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_qt1.RES_pt1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (qt1_mem_pt1 m regs QC qb mx) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold qt1_mem_pt1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End QT1.
(* [comment removed for export] *)
End AXF_qt1z.

Module AXF_qt2c.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Definition e_QC := EVar 32.
Definition e_qb := EVar 33.
Definition e_mx := EVar 34.
Definition e_B := EVar 35.
Definition e_gl0 := EVar 36.
Definition e_gsp := EVar 37.
Definition e_gb := EVar 38.
Definition e_mxs := EVar 39.
Definition e_pa2 := EVar 40.
Definition e_pa3 := EVar 41.
Definition e_gf := EVar 42.
Definition STK := SA (EVar 2) (-1024).
Definition sr_qt2c := (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 930544)) 9 (e_QC)) 22 (e_mx)).
Definition kn_qt2c : list kentry :=
  [ KRange e_QC 1 (2^47);
    KRange e_B 1 (2^47);
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA e_QC 0) 8 (ELit 1);
    KWord (SA e_QC 8) 8 e_B;
    KWord (SA e_QC 16) 8 e_B;
    KWord (SA e_QC 24) 8 e_qb;
    KWr (SA e_QC 0) (ELit 32);
    KWord (SA (EVar 2) 0) 8 e_pa2;
    KWord (SA (EVar 2) 8) 8 e_pa3;
    KWord (SA (ELit 0) 930696) 4 (ELit 0);
    KWr (SA (ELit 0) 930696) (ELit 4);
    KWord (SA (ELit 0) 930704) 8 (ELit 0);
    KWord (SA (ELit 0) 930712) 8 e_gf;
    KWord (SA (ELit 0) 930720) 8 e_gl0;
    KWord (SA (ELit 0) 930728) 8 e_gb;
    KWr (SA (ELit 0) 930704) (ELit 32);
    KWord (SA (ELit 0) 930608) 8 e_mxs;
    KWr STK (ELit 1024) ].
Definition scr_qt2c : scripts := SCR [true; false; true] [] [].
Definition ss_qt2c := SS 0x43e14 sr_qt2c [] kn_qt2c 43.
Definition RUN_qt2c := sym_exec SEGS 120 true [0x43d4c] scr_qt2c ss_qt2c [].

Definition scr_pdc : scripts := SCR [true; false; true] [] [].
Definition RES_pdc := Eval vm_compute in sym_exec SEGS 120 true [0x43d4c] scr_pdc ss_qt2c [].
Lemma RES_pdc_ok : sym_exec SEGS 120 true [0x43d4c] scr_pdc (SS 0x43e14 sr_qt2c [] kn_qt2c 43) [] = RES_pdc.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_qt2c.

Module AXF_qt2cz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section QT2C.
Context {fx : FPState}.

Definition VALS_qt2c (QC qb mx B gl0 gsp gb mxs pa2 pa3 gf : Z) : list Z := [QC; qb; mx; B; gl0; gsp; gb; mxs; pa2; pa3; gf].

Record qt2c_pre (regs : bvmap 5 word) (m : word -> option byte) (QC qb mx B gl0 gsp gb mxs pa2 pa3 gf : Z) : Prop := {
  qt2c_R8 : getr regs 8 = wa 930544 ;
  qt2c_R9 : getr regs 9 = wa QC ;
  qt2c_R22 : getr regs 22 = wa mx ;
  qt2c_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  qt2c_rng_QC : 1 <= QC <= 2^47 ;
  qt2c_rng_qb : 0 <= qb <= 2^62 ;
  qt2c_rng_mx : 0 <= mx <= 2^62 ;
  qt2c_rng_B : 1 <= B <= 2^47 ;
  qt2c_rng_gl0 : 0 <= gl0 <= 2^64-1 ;
  qt2c_rng_gsp : 0 <= gsp <= 2^64-1 ;
  qt2c_rng_gb : 0 <= gb <= 2^62 ;
  qt2c_rng_mxs : 0 <= mxs <= 2^62 ;
  qt2c_rng_pa2 : 0 <= pa2 <= 2^64-1 ;
  qt2c_rng_pa3 : 0 <= pa3 <= 2^64-1 ;
  qt2c_rng_gf : 0 <= gf <= 2^64-1 ;
  qt2c_kr2 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  qt2c_kw3 : rdn SEGS m (wa (QC + 0)) 8 = Some (word_to_le_bytes 8 (wa 1)) ;
  qt2c_kw4 : rdn SEGS m (wa (QC + 8)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  qt2c_kw5 : rdn SEGS m (wa (QC + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  qt2c_kw6 : rdn SEGS m (wa (QC + 24)) 8 = Some (word_to_le_bytes 8 (wa qb)) ;
  qt2c_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (QC + 0 + d)) k = true ;
  qt2c_kw8 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0)) 8 = Some (word_to_le_bytes 8 (wa pa2)) ;
  qt2c_kw9 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) 8 = Some (word_to_le_bytes 8 (wa pa3)) ;
  qt2c_kw10 : rdn SEGS m (wa (0 + 930696)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  qt2c_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (0 + 930696 + d)) k = true ;
  qt2c_kw12 : rdn SEGS m (wa (0 + 930704)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  qt2c_kw13 : rdn SEGS m (wa (0 + 930712)) 8 = Some (word_to_le_bytes 8 (wa gf)) ;
  qt2c_kw14 : rdn SEGS m (wa (0 + 930720)) 8 = Some (word_to_le_bytes 8 (wa gl0)) ;
  qt2c_kw15 : rdn SEGS m (wa (0 + 930728)) 8 = Some (word_to_le_bytes 8 (wa gb)) ;
  qt2c_kwr16 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (0 + 930704 + d)) k = true ;
  qt2c_kw17 : rdn SEGS m (wa (0 + 930608)) 8 = Some (word_to_le_bytes 8 (wa mxs))
}.


#[using="Type"] Lemma qt2c_setup : forall regs m QC qb mx B gl0 gsp gb mxs pa2 pa3 gf, qt2c_pre regs m QC qb mx B gl0 gsp gb mxs pa2 pa3 gf ->
  regs_ok (Ez regs (VALS_qt2c QC qb mx B gl0 gsp gb mxs pa2 pa3 gf)) AXF_qt2c.sr_qt2c regs /\ know_ok SEGS (Ez regs (VALS_qt2c QC qb mx B gl0 gsp gb mxs pa2 pa3 gf)) m AXF_qt2c.kn_qt2c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m QC qb mx B gl0 gsp gb mxs pa2 pa3 gf P. destruct P as [qt2c_R8 qt2c_R9 qt2c_R22 qt2c_HSTK qt2c_rng_QC qt2c_rng_qb qt2c_rng_mx qt2c_rng_B qt2c_rng_gl0 qt2c_rng_gsp qt2c_rng_gb qt2c_rng_mxs qt2c_rng_pa2 qt2c_rng_pa3 qt2c_rng_gf qt2c_kr2 qt2c_kw3 qt2c_kw4 qt2c_kw5 qt2c_kw6 qt2c_kwr7 qt2c_kw8 qt2c_kw9 qt2c_kw10 qt2c_kwr11 qt2c_kw12 qt2c_kw13 qt2c_kw14 qt2c_kw15 qt2c_kwr16 qt2c_kw17].
  set (E := Ez regs (VALS_qt2c QC qb mx B gl0 gsp gb mxs pa2 pa3 gf)).
  assert (Z32 : bv_unsigned (ev E 32) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = qb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = B) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = gl0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = gsp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = gb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = mxs) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = pa2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = pa3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = gf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_qt2c.sr_qt2c.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|].
    - rewrite qt2c_R8. reflexivity.
    - rewrite qt2c_R9. reflexivity.
    - rewrite qt2c_R22. reflexivity. }
  unfold know_ok, AXF_qt2c.kn_qt2c.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_qt2c.e_QC AXF_qt2c.e_qb AXF_qt2c.e_mx AXF_qt2c.e_B AXF_qt2c.e_gl0 AXF_qt2c.e_gsp AXF_qt2c.e_gb AXF_qt2c.e_mxs AXF_qt2c.e_pa2 AXF_qt2c.e_pa3 AXF_qt2c.e_gf AXF_qt2c.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range QC _ _ qt2c_rng_QC eq_refl eq_refl), ?(mod64_of_range qb _ _ qt2c_rng_qb eq_refl eq_refl), ?(mod64_of_range mx _ _ qt2c_rng_mx eq_refl eq_refl), ?(mod64_of_range B _ _ qt2c_rng_B eq_refl eq_refl), ?(mod64_of_range gb _ _ qt2c_rng_gb eq_refl eq_refl), ?(mod64_of_range mxs _ _ qt2c_rng_mxs eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply qt2c_kwr7 | apply qt2c_kwr11 | apply qt2c_kwr16]; assumption).
  all: try (clear - qt2c_rng_QC qt2c_rng_qb qt2c_rng_mx qt2c_rng_B qt2c_rng_gl0 qt2c_rng_gsp qt2c_rng_gb qt2c_rng_mxs qt2c_rng_pa2 qt2c_rng_pa3 qt2c_rng_gf qt2c_kr2; lia).
  all: first [lia].
Qed.


Definition qt2c_mem_pdc (m : word -> option byte) (regs : bvmap 5 word) (QC qb mx B gl0 gsp gb mxs pa2 pa3 gf : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 277836))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa 930544))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa QC))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (0 + 930696)) (word_to_le_bytes 4 (wa 1))) (wa (0 + 930720)) (word_to_le_bytes 8 (wa B))) (wa (0 + 930712)) (word_to_le_bytes 8 (wa B))) (wa (0 + 930704)) (word_to_le_bytes 8 (wa 1))) (wa (QC + 0)) (word_to_le_bytes 8 (wa 0))) (wa (QC + 8)) (word_to_le_bytes 8 (wa 0))) (wa (QC + 16)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 930728)) (word_to_le_bytes 8 (wa (qb + gb)))) (wa (QC + 24)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 930696)) (word_to_le_bytes 1 (wa 0)).

#[using="Type"] Theorem qt2c_pdc : forall regs m rom QC qb mx B gl0 gsp gb mxs pa2 pa3 gf, qt2c_pre regs m QC qb mx B gl0 gsp gb mxs pa2 pa3 gf ->
  scs_denot SEGS m (Ez regs (VALS_qt2c QC qb mx B gl0 gsp gb mxs pa2 pa3 gf)) (snd (fst AXF_qt2c.RES_pdc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43e14) m rom) (mkst R (wa 0x43d4c) (qt2c_mem_pdc m regs QC qb mx B gl0 gsp gb mxs pa2 pa3 gf) rom) /\
    getr R 1 = wa 277836 /\ getr R 5 = wa 0 /\ getr R 6 = wa 0 /\ getr R 8 = wa 930544 /\ getr R 9 = wa QC /\ getr R 10 = wa 930544 /\ getr R 11 = wa (qb + gb) /\ getr R 12 = wa pa2 /\ getr R 13 = wa pa3 /\ getr R 14 = wa mxs /\ getr R 15 = wa gb /\ getr R 16 = wa 0 /\ getr R 17 = wa 1 /\ getr R 22 = wa mx /\ (forall k, In k [2; 3; 4; 7; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom QC qb mx B gl0 gsp gb mxs pa2 pa3 gf P Hsc. destruct (qt2c_setup regs m QC qb mx B gl0 gsp gb mxs pa2 pa3 gf P) as [HR HK].
  set (E := Ez regs (VALS_qt2c QC qb mx B gl0 gsp gb mxs pa2 pa3 gf)) in *. destruct P as [qt2c_R8 qt2c_R9 qt2c_R22 qt2c_HSTK qt2c_rng_QC qt2c_rng_qb qt2c_rng_mx qt2c_rng_B qt2c_rng_gl0 qt2c_rng_gsp qt2c_rng_gb qt2c_rng_mxs qt2c_rng_pa2 qt2c_rng_pa3 qt2c_rng_gf qt2c_kr2 qt2c_kw3 qt2c_kw4 qt2c_kw5 qt2c_kw6 qt2c_kwr7 qt2c_kw8 qt2c_kw9 qt2c_kw10 qt2c_kwr11 qt2c_kw12 qt2c_kw13 qt2c_kw14 qt2c_kw15 qt2c_kwr16 qt2c_kw17].
  assert (Z32 : bv_unsigned (ev E 32) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = qb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = B) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = gl0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = gsp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = gb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = mxs) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = pa2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = pa3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = gf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 120 [0x43d4c] AXF_qt2c.scr_pdc 0x43e14 AXF_qt2c.sr_qt2c AXF_qt2c.kn_qt2c 43 _ _ _ E m rom regs AXF_qt2c.RES_pdc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_qt2c.RES_pdc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (qt2c_mem_pdc m regs QC qb mx B gl0 gsp gb mxs pa2 pa3 gf) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold qt2c_mem_pdc. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End QT2C.
(* [comment removed for export] *)
End AXF_qt2cz.

Module AXF_qt2a.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Definition e_QC := EVar 32.
Definition e_qb := EVar 33.
Definition e_mx := EVar 34.
Definition e_B := EVar 35.
Definition e_gn := EVar 36.
Definition e_GLB := EVar 37.
Definition e_gb := EVar 38.
Definition e_mxs := EVar 39.
Definition e_pa2 := EVar 40.
Definition e_pa3 := EVar 41.
Definition e_gf := EVar 42.
Definition STK := SA (EVar 2) (-1024).
Definition sr_qt2a := (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 930544)) 9 (e_QC)) 22 (e_mx)).
Definition kn_qt2a : list kentry :=
  [ KRange e_QC 1 (2^47);
    KRange e_B 1 (2^47);
    KRange e_GLB 1 (2^47);
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA e_QC 0) 8 (ELit 1);
    KWord (SA e_QC 8) 8 e_B;
    KWord (SA e_QC 16) 8 e_B;
    KWord (SA e_QC 24) 8 e_qb;
    KWr (SA e_QC 0) (ELit 32);
    KWord (SA (EVar 2) 0) 8 e_pa2;
    KWord (SA (EVar 2) 8) 8 e_pa3;
    KWord (SA (ELit 0) 930696) 4 (ELit 0);
    KWr (SA (ELit 0) 930696) (ELit 4);
    KWord (SA (ELit 0) 930704) 8 e_gn;
    KWord (SA (ELit 0) 930712) 8 e_gf;
    KWord (SA (ELit 0) 930720) 8 e_GLB;
    KWord (SA (ELit 0) 930728) 8 e_gb;
    KWr (SA (ELit 0) 930704) (ELit 32);
    KWord (SA (ELit 0) 930608) 8 e_mxs;
    KWr (SA e_GLB 0) (ELit 8);
    KWr STK (ELit 1024) ].
Definition scr_qt2a : scripts := SCR [true; false; false; true] [] [].
Definition ss_qt2a := SS 0x43e14 sr_qt2a [] kn_qt2a 43.
Definition RUN_qt2a := sym_exec SEGS 120 true [0x43d4c] scr_qt2a ss_qt2a [].

Definition scr_pda : scripts := SCR [true; false; false; true] [] [].
Definition RES_pda := Eval vm_compute in sym_exec SEGS 120 true [0x43d4c] scr_pda ss_qt2a [].
Lemma RES_pda_ok : sym_exec SEGS 120 true [0x43d4c] scr_pda (SS 0x43e14 sr_qt2a [] kn_qt2a 43) [] = RES_pda.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_qt2a.

Module AXF_qt2az.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section QT2A.
Context {fx : FPState}.

Definition VALS_qt2a (QC qb mx B gn GLB gb mxs pa2 pa3 gf : Z) : list Z := [QC; qb; mx; B; gn; GLB; gb; mxs; pa2; pa3; gf].

Record qt2a_pre (regs : bvmap 5 word) (m : word -> option byte) (QC qb mx B gn GLB gb mxs pa2 pa3 gf : Z) : Prop := {
  qt2a_R8 : getr regs 8 = wa 930544 ;
  qt2a_R9 : getr regs 9 = wa QC ;
  qt2a_R22 : getr regs 22 = wa mx ;
  qt2a_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  qt2a_rng_QC : 1 <= QC <= 2^47 ;
  qt2a_rng_qb : 0 <= qb <= 2^62 ;
  qt2a_rng_mx : 0 <= mx <= 2^62 ;
  qt2a_rng_B : 1 <= B <= 2^47 ;
  qt2a_rng_gn : 1 <= gn <= 2^32 ;
  qt2a_rng_GLB : 1 <= GLB <= 2^47 ;
  qt2a_rng_gb : 0 <= gb <= 2^62 ;
  qt2a_rng_mxs : 0 <= mxs <= 2^62 ;
  qt2a_rng_pa2 : 0 <= pa2 <= 2^64-1 ;
  qt2a_rng_pa3 : 0 <= pa3 <= 2^64-1 ;
  qt2a_rng_gf : 0 <= gf <= 2^64-1 ;
  qt2a_kr3 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  qt2a_kw4 : rdn SEGS m (wa (QC + 0)) 8 = Some (word_to_le_bytes 8 (wa 1)) ;
  qt2a_kw5 : rdn SEGS m (wa (QC + 8)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  qt2a_kw6 : rdn SEGS m (wa (QC + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  qt2a_kw7 : rdn SEGS m (wa (QC + 24)) 8 = Some (word_to_le_bytes 8 (wa qb)) ;
  qt2a_kwr8 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (QC + 0 + d)) k = true ;
  qt2a_kw9 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0)) 8 = Some (word_to_le_bytes 8 (wa pa2)) ;
  qt2a_kw10 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) 8 = Some (word_to_le_bytes 8 (wa pa3)) ;
  qt2a_kw11 : rdn SEGS m (wa (0 + 930696)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  qt2a_kwr12 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (0 + 930696 + d)) k = true ;
  qt2a_kw13 : rdn SEGS m (wa (0 + 930704)) 8 = Some (word_to_le_bytes 8 (wa gn)) ;
  qt2a_kw14 : rdn SEGS m (wa (0 + 930712)) 8 = Some (word_to_le_bytes 8 (wa gf)) ;
  qt2a_kw15 : rdn SEGS m (wa (0 + 930720)) 8 = Some (word_to_le_bytes 8 (wa GLB)) ;
  qt2a_kw16 : rdn SEGS m (wa (0 + 930728)) 8 = Some (word_to_le_bytes 8 (wa gb)) ;
  qt2a_kwr17 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (0 + 930704 + d)) k = true ;
  qt2a_kw18 : rdn SEGS m (wa (0 + 930608)) 8 = Some (word_to_le_bytes 8 (wa mxs)) ;
  qt2a_kwr19 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (GLB + 0 + d)) k = true
}.


#[using="Type"] Lemma qt2a_setup : forall regs m QC qb mx B gn GLB gb mxs pa2 pa3 gf, qt2a_pre regs m QC qb mx B gn GLB gb mxs pa2 pa3 gf ->
  regs_ok (Ez regs (VALS_qt2a QC qb mx B gn GLB gb mxs pa2 pa3 gf)) AXF_qt2a.sr_qt2a regs /\ know_ok SEGS (Ez regs (VALS_qt2a QC qb mx B gn GLB gb mxs pa2 pa3 gf)) m AXF_qt2a.kn_qt2a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m QC qb mx B gn GLB gb mxs pa2 pa3 gf P. destruct P as [qt2a_R8 qt2a_R9 qt2a_R22 qt2a_HSTK qt2a_rng_QC qt2a_rng_qb qt2a_rng_mx qt2a_rng_B qt2a_rng_gn qt2a_rng_GLB qt2a_rng_gb qt2a_rng_mxs qt2a_rng_pa2 qt2a_rng_pa3 qt2a_rng_gf qt2a_kr3 qt2a_kw4 qt2a_kw5 qt2a_kw6 qt2a_kw7 qt2a_kwr8 qt2a_kw9 qt2a_kw10 qt2a_kw11 qt2a_kwr12 qt2a_kw13 qt2a_kw14 qt2a_kw15 qt2a_kw16 qt2a_kwr17 qt2a_kw18 qt2a_kwr19].
  set (E := Ez regs (VALS_qt2a QC qb mx B gn GLB gb mxs pa2 pa3 gf)).
  assert (Z32 : bv_unsigned (ev E 32) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = qb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = B) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = gn) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = GLB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = gb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = mxs) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = pa2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = pa3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = gf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_qt2a.sr_qt2a.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|].
    - rewrite qt2a_R8. reflexivity.
    - rewrite qt2a_R9. reflexivity.
    - rewrite qt2a_R22. reflexivity. }
  unfold know_ok, AXF_qt2a.kn_qt2a.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_qt2a.e_QC AXF_qt2a.e_qb AXF_qt2a.e_mx AXF_qt2a.e_B AXF_qt2a.e_gn AXF_qt2a.e_GLB AXF_qt2a.e_gb AXF_qt2a.e_mxs AXF_qt2a.e_pa2 AXF_qt2a.e_pa3 AXF_qt2a.e_gf AXF_qt2a.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range QC _ _ qt2a_rng_QC eq_refl eq_refl), ?(mod64_of_range qb _ _ qt2a_rng_qb eq_refl eq_refl), ?(mod64_of_range mx _ _ qt2a_rng_mx eq_refl eq_refl), ?(mod64_of_range B _ _ qt2a_rng_B eq_refl eq_refl), ?(mod64_of_range gn _ _ qt2a_rng_gn eq_refl eq_refl), ?(mod64_of_range GLB _ _ qt2a_rng_GLB eq_refl eq_refl), ?(mod64_of_range gb _ _ qt2a_rng_gb eq_refl eq_refl), ?(mod64_of_range mxs _ _ qt2a_rng_mxs eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply qt2a_kwr8 | apply qt2a_kwr12 | apply qt2a_kwr17 | apply qt2a_kwr19]; assumption).
  all: try (clear - qt2a_rng_QC qt2a_rng_qb qt2a_rng_mx qt2a_rng_B qt2a_rng_gn qt2a_rng_GLB qt2a_rng_gb qt2a_rng_mxs qt2a_rng_pa2 qt2a_rng_pa3 qt2a_rng_gf qt2a_kr3; lia).
  all: first [lia].
Qed.


Definition qt2a_mem_pda (m : word -> option byte) (regs : bvmap 5 word) (QC qb mx B gn GLB gb mxs pa2 pa3 gf : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 277836))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa 930544))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa QC))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (0 + 930696)) (word_to_le_bytes 4 (wa 1))) (wa (GLB + 0)) (word_to_le_bytes 8 (wa B))) (wa (0 + 930704)) (word_to_le_bytes 8 (wa (gn + 1)))) (wa (0 + 930720)) (word_to_le_bytes 8 (wa B))) (wa (QC + 0)) (word_to_le_bytes 8 (wa 0))) (wa (QC + 8)) (word_to_le_bytes 8 (wa 0))) (wa (QC + 16)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 930728)) (word_to_le_bytes 8 (wa (qb + gb)))) (wa (QC + 24)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 930696)) (word_to_le_bytes 1 (wa 0)).

#[using="Type"] Theorem qt2a_pda : forall regs m rom QC qb mx B gn GLB gb mxs pa2 pa3 gf, qt2a_pre regs m QC qb mx B gn GLB gb mxs pa2 pa3 gf ->
  scs_denot SEGS m (Ez regs (VALS_qt2a QC qb mx B gn GLB gb mxs pa2 pa3 gf)) (snd (fst AXF_qt2a.RES_pda)) ->
  exists R, msteps SEGS (mkst regs (wa 0x43e14) m rom) (mkst R (wa 0x43d4c) (qt2a_mem_pda m regs QC qb mx B gn GLB gb mxs pa2 pa3 gf) rom) /\
    getr R 1 = wa 277836 /\ getr R 5 = wa B /\ getr R 6 = wa 0 /\ getr R 8 = wa 930544 /\ getr R 9 = wa QC /\ getr R 10 = wa 930544 /\ getr R 11 = wa (qb + gb) /\ getr R 12 = wa pa2 /\ getr R 13 = wa pa3 /\ getr R 14 = wa mxs /\ getr R 15 = wa gb /\ getr R 16 = wa gn /\ getr R 17 = wa B /\ getr R 22 = wa mx /\ (forall k, In k [2; 3; 4; 7; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom QC qb mx B gn GLB gb mxs pa2 pa3 gf P Hsc. destruct (qt2a_setup regs m QC qb mx B gn GLB gb mxs pa2 pa3 gf P) as [HR HK].
  set (E := Ez regs (VALS_qt2a QC qb mx B gn GLB gb mxs pa2 pa3 gf)) in *. destruct P as [qt2a_R8 qt2a_R9 qt2a_R22 qt2a_HSTK qt2a_rng_QC qt2a_rng_qb qt2a_rng_mx qt2a_rng_B qt2a_rng_gn qt2a_rng_GLB qt2a_rng_gb qt2a_rng_mxs qt2a_rng_pa2 qt2a_rng_pa3 qt2a_rng_gf qt2a_kr3 qt2a_kw4 qt2a_kw5 qt2a_kw6 qt2a_kw7 qt2a_kwr8 qt2a_kw9 qt2a_kw10 qt2a_kw11 qt2a_kwr12 qt2a_kw13 qt2a_kw14 qt2a_kw15 qt2a_kw16 qt2a_kwr17 qt2a_kw18 qt2a_kwr19].
  assert (Z32 : bv_unsigned (ev E 32) = QC) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = qb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = mx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = B) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = gn) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = GLB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = gb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = mxs) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = pa2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = pa3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = gf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 120 [0x43d4c] AXF_qt2a.scr_pda 0x43e14 AXF_qt2a.sr_qt2a AXF_qt2a.kn_qt2a 43 _ _ _ E m rom regs AXF_qt2a.RES_pda_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_qt2a.RES_pda fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (qt2a_mem_pda m regs QC qb mx B gn GLB gb mxs pa2 pa3 gf) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold qt2a_mem_pda. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End QT2A.
(* [comment removed for export] *)
End AXF_qt2az.

Module AXG_qt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AxAsan AXG_put AXG_put2 AXG_np AXG_np2 AXG_np3 AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxBits.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_gp AXG_q1.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits.AxScChk OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp.AXG_npb OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q1.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Local Ltac lenq := rewrite ?length_N_to_le_bytes; change (Z.of_nat 1) with 1 in *; change (Z.of_nat 4) with 4 in *; change (Z.of_nat 8) with 8 in *.
Local Ltac znq := change (Z.of_nat 4) with 4 in *; change (Z.of_nat 8) with 8 in *.

Definition gq_inv (m : word -> option byte) (SB gn gl gb mxs : Z) : Prop :=
  0 <= gn < 2^32 /\ 0 <= gb < 2^62 /\ 0 <= mxs < 2^62 /\
  rd m 930696 4 0 /\ wr m 930696 4 /\ rd m 930704 8 gn /\ rd m 930728 8 gb /\ wr m 930704 32 /\ rd m 930608 8 mxs /\
  (exists gf, 0 <= gf < 2^64 /\ rd m 930712 8 gf) /\
  ((gn = 0 /\ exists g0, 0 <= g0 < 2^64 /\ rd m 930720 8 g0) \/
   (1 <= gn /\ 0 <= gl < 32 /\ rd m 930720 8 (SB + 103079215104 + 8192 * gl) /\ wr m (SB + 103079215104 + 8192 * gl) 8)).

Lemma wr_grows' : forall m m' a n, mem_grows m m' -> wr m a n -> wr m' a n.
Proof. intros m m' a n G W d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). exact (W d k Hd Hk). Qed.

(* [comment removed for export] *)
Lemma sc_geu3 : forall {fx : FPState} segs base E a b, 0 <= zeval E a < 2^64 -> 0 <= zeval E b < 2^64 -> zeval E b <= zeval E a ->
  scs_denot segs base E [SCBr true BC_GEU a b].
Proof.
  intros fx segs base E a b Ha Hb Hle. unfold scs_denot. constructor; [|constructor].
  apply sc_br_z. rewrite br_geu_z. rewrite !Z.mod_small by assumption. apply negb_true_iff. apply Z.ltb_ge. exact Hle.
Qed.

Section SCT.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte).
Variable SPa : Z.
Hypothesis HSPa : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 2))) = SPa.

#[using="Type"] Lemma sc_qt1 : forall QC qb mx, 0 <= qb <= 2^62 /\ 0 <= mx <= 2^62 /\ qb <= mx ->
  scs_denot SEGS m (Ez R (AXF_qt1z.VALS_qt1 QC qb mx)) (snd (fst AXF_qt1.RES_pt1)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros QC qb mx HH. unfold AXF_qt1z.VALS_qt1.
  sc_refl [(EVar 33, (0, 2^62)); (EVar 34, (0, 2^62))] [(EVar 34, EVar 33, 0)] R HSPa HSPa HH.
Qed.
(* [comment removed for export] *)
Definition t_geo (QC B : Z) : Prop :=
  2^46 <= SPa <= 2^47 /\ ((4176 <= QC /\ QC + 4016 <= 65536) \/ 6537296 <= QC) /\ QC + 32 + 320 <= SPa /\ 17697412710400 <= B /\ B + 8192 + 320 <= SPa /\
  (QC + 32 <= B \/ B + 8192 <= QC).
#[using="fx HSPa"] Lemma sc_qt2c : forall QC qb mx B gl0 gsp gb mxs pa2 pa3 gf, t_geo QC B ->
  0 <= qb <= 2^62 /\ 0 <= mx <= 2^62 /\ mx + 1 <= qb /\ 0 <= gb <= 2^62 /\ 0 <= mxs <= 2^62 /\ qb + gb <= mxs ->
  scs_denot SEGS m (Ez R (AXF_qt2cz.VALS_qt2c QC qb mx B gl0 gsp gb mxs pa2 pa3 gf)) (snd (fst AXF_qt2c.RES_pdc)).
Proof. LiaFast.lf_pins (fun (fx HSPa : LiaFast.U) => LiaFast.u0).
  intros QC qb mx B gl0 gsp gb mxs pa2 pa3 gf HG HH. unfold t_geo in HG. unfold AXF_qt2cz.VALS_qt2c.
  assert (HPL : (4176 <= QC /\ QC + 4016 <= 65536) \/ 6537296 <= QC) by tauto.
  assert (HND : scs_denot SEGS m (Ez R [QC; qb; mx; B; gl0; gsp; gb; mxs; pa2; pa3; gf]) [SCBr true BC_GEU (EVar 39) (EAlu ALU_ADD (EVar 33) (EVar 38))]).
  { apply sc_geu3; cbn [zeval edenot]; zat R; clear - HH; lia. }
  destruct HPL as [HPL|HPL]; assert (HH2 := conj HPL (conj HG HH)); clear HH HG HPL.
  - sc_resid [SPr; (EVar 32, (4176, 61520)); (EVar 33, (0, 2^62)); (EVar 34, (0, 2^62)); (EVar 38, (0, 2^62)); (EVar 39, (0, 2^62))]
             [(EVar 2, EVar 32, 352); (EVar 33, EVar 34, 1)] R HSPa HSPa HH2. exact HND.
  - sc_resid [SPr; (EVar 32, (6537296, 2^47)); (EVar 33, (0, 2^62)); (EVar 34, (0, 2^62)); (EVar 38, (0, 2^62)); (EVar 39, (0, 2^62))]
             [(EVar 2, EVar 32, 352); (EVar 33, EVar 34, 1)] R HSPa HSPa HH2. exact HND.
Qed.
#[using="fx HSPa"] Lemma sc_qt2a : forall QC qb mx B gn GLB gb mxs pa2 pa3 gf, t_geo QC B ->
  17697412710400 <= GLB /\ GLB + 8192 + 320 <= SPa /\ (QC + 32 <= GLB \/ GLB + 8192 <= QC) /\
  0 <= qb <= 2^62 /\ 0 <= mx <= 2^62 /\ mx + 1 <= qb /\ 1 <= gn <= 2^32 /\ 0 <= gb <= 2^62 /\ 0 <= mxs <= 2^62 /\ qb + gb <= mxs ->
  scs_denot SEGS m (Ez R (AXF_qt2az.VALS_qt2a QC qb mx B gn GLB gb mxs pa2 pa3 gf)) (snd (fst AXF_qt2a.RES_pda)).
Proof. LiaFast.lf_pins (fun (fx HSPa : LiaFast.U) => LiaFast.u0).
  intros QC qb mx B gn GLB gb mxs pa2 pa3 gf HG HH. unfold t_geo in HG. unfold AXF_qt2az.VALS_qt2a.
  assert (HPL : (4176 <= QC /\ QC + 4016 <= 65536) \/ 6537296 <= QC) by tauto.
  assert (HD : QC + 32 <= GLB \/ GLB + 8192 <= QC) by tauto.
  assert (HND : scs_denot SEGS m (Ez R [QC; qb; mx; B; gn; GLB; gb; mxs; pa2; pa3; gf]) [SCBr true BC_GEU (EVar 39) (EAlu ALU_ADD (EVar 33) (EVar 38))]).
  { apply sc_geu3; cbn [zeval edenot]; zat R; clear - HH; lia. }
  destruct HPL as [HPL|HPL].
  - assert (HD1 : QC + 32 <= GLB) by (clear - HPL HH; lia). assert (HH2 := conj HPL (conj HD1 (conj HG HH))); clear HH HG HD HD1 HPL.
    sc_resid [SPr; (EVar 32, (4176, 61520)); (EVar 33, (0, 2^62)); (EVar 34, (0, 2^62)); (EVar 36, (1, 2^32)); (EVar 37, (17697412710400, 2^47)); (EVar 38, (0, 2^62)); (EVar 39, (0, 2^62))]
             [(EVar 2, EVar 32, 352); (EVar 2, EVar 37, 8512); (EVar 37, EVar 32, 32); (EVar 33, EVar 34, 1)] R HSPa HSPa HH2. exact HND.
  - destruct HD as [HD|HD]; assert (HH2 := conj HPL (conj HD (conj HG HH))); clear HH HG HD HPL.
    + sc_resid [SPr; (EVar 32, (6537296, 2^47)); (EVar 33, (0, 2^62)); (EVar 34, (0, 2^62)); (EVar 36, (1, 2^32)); (EVar 37, (17697412710400, 2^47)); (EVar 38, (0, 2^62)); (EVar 39, (0, 2^62))]
               [(EVar 2, EVar 32, 352); (EVar 2, EVar 37, 8512); (EVar 37, EVar 32, 32); (EVar 33, EVar 34, 1)] R HSPa HSPa HH2. exact HND.
    + sc_resid [SPr; (EVar 32, (6537296, 2^47)); (EVar 33, (0, 2^62)); (EVar 34, (0, 2^62)); (EVar 36, (1, 2^32)); (EVar 37, (17697412710400, 2^47)); (EVar 38, (0, 2^62)); (EVar 39, (0, 2^62))]
               [(EVar 2, EVar 32, 352); (EVar 2, EVar 37, 8512); (EVar 32, EVar 37, 8192); (EVar 33, EVar 34, 1)] R HSPa HSPa HH2. exact HND.
Qed.
End SCT.

(* [comment removed for export] *)
Lemma wa_succ : forall a, 0 <= a -> a + 1 < 2^64 -> (wa a + 1)%bv = wa (a + 1).
Proof.
  intros a H0 H1. apply bv_eq. rewrite bv_add_unsigned. rewrite (u_wa_small a) by lia. rewrite (u_wa_small (a + 1)) by lia.
  change (bv_unsigned (1%bv : bv 64)) with 1. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). apply Z.mod_small. lia.
Qed.
Lemma rd4_zero_of_bytes : forall (mm : word -> option byte) a, 0 <= a -> a + 4 < 2^64 ->
  mm (wa a) = Some (Z_to_bv 8 0) -> mm (wa (a + 1)) = Some (Z_to_bv 8 0) -> mm (wa (a + 2)) = Some (Z_to_bv 8 0) -> mm (wa (a + 3)) = Some (Z_to_bv 8 0) ->
  rd mm a 4 0.
Proof.
  intros mm a H0 H1 P0 P1 P2 P3. unfold rd. cbn [rdn].
  rewrite (wa_succ a) by lia. rewrite (wa_succ (a + 1)) by lia. rewrite (wa_succ (a + 1 + 1)) by lia.
  replace (a + 1 + 1) with (a + 2) by ring. replace (a + 2 + 1) with (a + 3) by ring.
  rewrite P0, P1, P2, P3. reflexivity.
Qed.

(* [comment removed for export] *)
Definition KT1 : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
(* [comment removed for export] *)
Definition KT2 : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
Theorem qtail_nd : forall {fx : FPState} rom m regs QC SB qj qn qb mx,
  q_inv m QC SB qj qn qb -> getr regs 9 = wa QC -> getr regs 22 = wa mx -> 1 <= QC <= 2^47 -> 0 <= mx <= 2^62 -> qb <= mx ->
  exists R, msteps SEGS (mkst regs (wa 0x43e14) m rom) (mkst R (wa 0x43d4c) m rom) /\
    (forall k, In k KT1 -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof.
  intros fx rom m regs QC SB qj qn qb mx (Hqb & Rqb & _) H9 H22 HQC Hmx Hle.
  assert (P : AXF_qt1z.qt1_pre regs m QC qb mx) by (constructor; try assumption; lia).
  destruct (AXF_qt1z.qt1_pt1 regs m rom QC qb mx P (sc_qt1 regs m QC qb mx ltac:(lia))) as (R & Hms & A9 & _ & A22 & KK).
  exists R. split; [exact Hms|].
  intros k Hk. cbn [KT1 In] in Hk.
  repeat (destruct Hk as [<-|Hk]; [first [ apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ]
                                         | (transitivity (wa QC); [exact A9 | symmetry; exact H9])
                                         | (transitivity (wa mx); [exact A22 | symmetry; exact H22]) ]|]).
  destruct Hk.
Qed.

(* [comment removed for export] *)
Ltac rdw H := repeat first [ (apply wb_rd_hit; [clear; lia | clear - H; lia | lenq; clear - H; lia])
                           | (apply wb_rd_other; [clear - H; lia | lenq; clear - H; lia | clear - H; lia | lenq; clear - H; lia | lenq; clear - H; lia | ]) ].
Ltac wbo' H Hx := repeat (rewrite wb_other by first [exact Hx | (lenq; clear - H; lia) | (lenq; clear - H Hx; lia)]).

(* [comment removed for export] *)
Section QTDC.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (QC SB qj qn qb mx gl gb mxs SP pa2 pa3 : Z).
Hypothesis IQ : q_inv m QC SB qj qn qb.
Hypothesis Hqn : 1 <= qn.
Hypothesis IGQ : gq_inv m SB 0 gl gb mxs.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis H8 : getr regs 8 = wa 930544.
Hypothesis H9 : getr regs 9 = wa QC.
Hypothesis H22 : getr regs 22 = wa mx.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis S0 : rd m SP 8 pa2.
Hypothesis S8 : rd m (SP + 8) 8 pa3.
Hypothesis Hpa : 0 <= pa2 < 2^64 /\ 0 <= pa3 < 2^64.
Hypothesis HQC : ((4176 <= QC /\ QC + 4016 <= 65536) \/ 6537296 <= QC) /\ QC + 32 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : QC + 32 <= SB \/ SB + 137438953472 + 4096 <= QC.
Hypothesis Hmx : 0 <= mx < 2^62 /\ mx + 1 <= qb /\ qb + gb <= mxs.
Hypothesis Hwq : wr m QC 32.

#[using="qn mx gl pa2 pa3 IQ Hqn IGQ H2 H8 H9 H22 HSP HSTK S0 S8 Hpa HQC HSB HSEP Hmx Hwq"] Theorem qtail_dc :
  exists R m', msteps SEGS (mkst regs (wa 0x43e14) m rom) (mkst R (wa 0x43d4c) m' rom) /\
    getr R 1 = wa 277836 /\
    (forall k, In k KT2 -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    q_inv m' QC SB qj 0 0 /\ gq_inv m' SB 1 qj (qb + gb) mxs /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (QC <= x < QC + 32) -> ~ (930696 <= x < 930700) -> ~ (930704 <= x < 930736) ->
       m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins (fun (qn mx gl pa2 pa3 IQ Hqn IGQ H2 H8 H9 H22 HSP HSTK S0 S8 Hpa HQC HSB HSEP Hmx Hwq : LiaFast.U) => LiaFast.u0).
  destruct IQ as (Hqb & Rqb & [(Hq0 & _)|(_ & Hqj & Rsz & Rfirst & Rlast & Rbsz & Rcnt & Wb)]); [lia|].
  destruct IGQ as (Hgn & Hgb & Hmxs & Rmu & Wmu & Rgn & Rgb & Wg & Rmxs & (gf & Hgf & Rgf) & [(_ & g0 & Hg0 & Rg0)|(Hg1 & _)]); [|lia].
  set (B := SB + 103079215104 + 8192 * qj) in *.
  assert (HZ : ((4176 <= QC /\ QC + 4016 <= 65536) \/ 6537296 <= QC) /\ QC + 32 <= SP - 2048 /\ 17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 /\ (QC + 32 <= SB \/ SB + 137438953472 + 4096 <= QC) /\
               B = SB + 103079215104 + 8192 * qj /\ 0 <= qj < 32 /\ 0 <= qb < 2^62 /\ 0 <= gb < 2^62 /\ 0 <= mxs < 2^62 /\
               0 <= mx < 2^62 /\ mx + 1 <= qb /\ qb + gb <= mxs /\ 0 <= pa2 < 2^64 /\ 0 <= pa3 < 2^64 /\ 0 <= gf < 2^64 /\ 0 <= g0 < 2^64) by (unfold B; lia).
  clear HQC HSB HSEP Hmx Hqj Hqb Hgb Hmxs Hpa Hgf Hg0. clearbody B.
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  assert (P : AXF_qt2cz.qt2c_pre regs m QC qb mx B g0 0 gb mxs pa2 pa3 gf).
  { constructor; try assumption; try (zlh HZ).
    - rewrite H2. apply (stk_ok_shrink m (wa SP) 2048 1024); [lia | exact HSTK].
    - rewrite HSPa. zlh HZ.
    - rewrite Z.add_0_r. exact Rsz.
    - intros d k Hd Hk. rewrite Z.add_0_r. apply Hwq; assumption.
    - rewrite HSPa, Z.add_0_r. exact S0.
    - rewrite HSPa. exact S8. }
  destruct (AXF_qt2cz.qt2c_pdc regs m rom QC qb mx B g0 0 gb mxs pa2 pa3 gf P
              (sc_qt2c regs m SP HSPa QC qb mx B g0 0 gb mxs pa2 pa3 gf ltac:(unfold t_geo; zlh HZ) ltac:(zlh HZ)))
    as (R & Hms & A1 & _ & _ & A8 & A9 & _ & _ & _ & _ & _ & _ & _ & _ & A22 & KK).
  clear P.
  set (m' := AXF_qt2cz.qt2c_mem_pdc m regs QC qb mx B g0 0 gb mxs pa2 pa3 gf) in *.
  assert (EM : m' = wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
                 (wbytes (wbytes (wbytes (wbytes (wbytes m (wa (SP + -8)) (word_to_le_bytes 8 (wa 277836))) (wa (SP + -16)) (word_to_le_bytes 8 (wa 930544)))
                    (wa (SP + -24)) (word_to_le_bytes 8 (wa QC))) (wa (SP + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))))))
                    (wa (SP + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))))))
                 (wa 930696) (word_to_le_bytes 4 (wa 1))) (wa 930720) (word_to_le_bytes 8 (wa B))) (wa 930712) (word_to_le_bytes 8 (wa B)))
                 (wa 930704) (word_to_le_bytes 8 (wa 1))) (wa QC) (word_to_le_bytes 8 (wa 0))) (wa (QC + 8)) (word_to_le_bytes 8 (wa 0)))
                 (wa (QC + 16)) (word_to_le_bytes 8 (wa 0))) (wa 930728) (word_to_le_bytes 8 (wa (qb + gb)))) (wa (QC + 24)) (word_to_le_bytes 8 (wa 0)))
                 (wa 930696) (word_to_le_bytes 1 (wa 0))).
  { unfold m', AXF_qt2cz.qt2c_mem_pdc. rewrite HSPa, (Z.add_0_r QC). reflexivity. }
  clearbody m'.
  assert (G : mem_grows m m') by (rewrite EM; do 15 apply grows_wb; apply mem_grows_refl).
  assert (FRM : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (QC <= x < QC + 32) -> ~ (930696 <= x < 930700) -> ~ (930704 <= x < 930736) ->
                  m' (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4. rewrite EM. repeat (rewrite wb_other by first [exact Hx | (lenq; zlh HZ) | (lenq; clear - HZ Q1 Q2 Q3 Q4; lia)]). reflexivity. }
  exists R, m'. split; [exact Hms|]. split; [exact A1|].
  split.
  { intros k Hk. cbn [KT2 In] in Hk.
    repeat (destruct Hk as [<-|Hk]; [first [ apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ]
                                           | (transitivity (wa 930544); [exact A8 | symmetry; exact H8])
                                           | (transitivity (wa QC); [exact A9 | symmetry; exact H9])
                                           | (transitivity (wa mx); [exact A22 | symmetry; exact H22]) ]|]).
    destruct Hk. }
  split.
  { unfold q_inv. split; [lia|]. split; [rewrite EM; rdw HZ|]. left. split; [reflexivity|]. split; [reflexivity|]. rewrite EM. rdw HZ. }
  split.
  { unfold gq_inv. split; [lia|]. split; [zlh HZ|]. split; [zlh HZ|].
    split.
    { apply rd4_zero_of_bytes; [lia | lia | | | |].
      - rewrite EM. apply wbytes_at_wa0; [lia | lenq; lia | lenq; lia].
      - rewrite EM. rewrite wb_other by (first [lia | (lenq; lia)]).
        repeat (rewrite wb_other by first [lia | (lenq; zlh HZ)]).
        replace (930696 + 1) with (930696 + Z.of_nat 1) by reflexivity. rewrite wbytes_at_wa by (first [lia | (lenq; lia) | (rewrite length_N_to_le_bytes; lia)]). reflexivity.
      - rewrite EM. rewrite wb_other by (first [lia | (lenq; lia)]).
        repeat (rewrite wb_other by first [lia | (lenq; zlh HZ)]).
        replace (930696 + 2) with (930696 + Z.of_nat 2) by reflexivity. rewrite wbytes_at_wa by (first [lia | (lenq; lia) | (rewrite length_N_to_le_bytes; lia)]). reflexivity.
      - rewrite EM. rewrite wb_other by (first [lia | (lenq; lia)]).
        repeat (rewrite wb_other by first [lia | (lenq; zlh HZ)]).
        replace (930696 + 3) with (930696 + Z.of_nat 3) by reflexivity. rewrite wbytes_at_wa by (first [lia | (lenq; lia) | (rewrite length_N_to_le_bytes; lia)]). reflexivity. }
    split; [exact (wr_grows' m m' _ _ G Wmu)|].
    split; [rewrite EM; rdw HZ|].
    split; [rewrite EM; rdw HZ|].
    split; [exact (wr_grows' m m' _ _ G Wg)|].
    split; [apply (rd_frame m m'); [lia | lenq; lia | intros x Hx; lenq; apply FRM; clear - HZ Hx; lia | exact Rmxs]|].
    split; [exists B; split; [zlh HZ | rewrite EM; rdw HZ]|].
    right. split; [lia|]. split; [zlh HZ|]. replace (SB + 103079215104 + 8192 * qj) with B by (zlh HZ).
    split; [rewrite EM; rdw HZ|].
    intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Wb; lia. }
  split; [exact FRM | exact G].
Qed.
End QTDC.

(* [comment removed for export] *)
Section QTDA.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (QC SB qj qn qb mx gn gl gb mxs SP pa2 pa3 : Z).
Hypothesis IQ : q_inv m QC SB qj qn qb.
Hypothesis Hqn : 1 <= qn.
Hypothesis IGQ : gq_inv m SB gn gl gb mxs.
Hypothesis Hgn1 : 1 <= gn /\ gn + 1 < 2^32.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis H8 : getr regs 8 = wa 930544.
Hypothesis H9 : getr regs 9 = wa QC.
Hypothesis H22 : getr regs 22 = wa mx.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis S0 : rd m SP 8 pa2.
Hypothesis S8 : rd m (SP + 8) 8 pa3.
Hypothesis Hpa : 0 <= pa2 < 2^64 /\ 0 <= pa3 < 2^64.
Hypothesis HQC : ((4176 <= QC /\ QC + 4016 <= 65536) \/ 6537296 <= QC) /\ QC + 32 <= SP - 2048.
Hypothesis HSB : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : QC + 32 <= SB \/ SB + 137438953472 + 4096 <= QC.
Hypothesis Hmx : 0 <= mx < 2^62 /\ mx + 1 <= qb /\ qb + gb <= mxs.
Hypothesis Hwq : wr m QC 32.

#[using="qn mx pa2 pa3 IQ Hqn IGQ Hgn1 H2 H8 H9 H22 HSP HSTK S0 S8 Hpa HQC HSB HSEP Hmx Hwq"] Theorem qtail_da :
  exists R m', msteps SEGS (mkst regs (wa 0x43e14) m rom) (mkst R (wa 0x43d4c) m' rom) /\
    getr R 1 = wa 277836 /\
    (forall k, In k KT2 -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    q_inv m' QC SB qj 0 0 /\ gq_inv m' SB (gn + 1) qj (qb + gb) mxs /\ rd m' (SB + 103079215104 + 8192 * gl) 8 (SB + 103079215104 + 8192 * qj) /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (QC <= x < QC + 32) -> ~ (930696 <= x < 930700) -> ~ (930704 <= x < 930736) ->
       ~ (SB + 103079215104 + 8192 * gl <= x < SB + 103079215104 + 8192 * gl + 8) -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins (fun (qn mx pa2 pa3 IQ Hqn IGQ Hgn1 H2 H8 H9 H22 HSP HSTK S0 S8 Hpa HQC HSB HSEP Hmx Hwq : LiaFast.U) => LiaFast.u0).
  destruct IQ as (Hqb & Rqb & [(Hq0 & _)|(_ & Hqj & Rsz & Rfirst & Rlast & Rbsz & Rcnt & Wb)]); [lia|].
  destruct IGQ as (Hgn & Hgb & Hmxs & Rmu & Wmu & Rgn & Rgb & Wg & Rmxs & (gf & Hgf & Rgf) & [(Hg0 & _)|(_ & Hgl & Rgl & Wgl)]); [lia|].
  set (B := SB + 103079215104 + 8192 * qj) in *. set (GLB := SB + 103079215104 + 8192 * gl) in *.
  assert (HZ : ((4176 <= QC /\ QC + 4016 <= 65536) \/ 6537296 <= QC) /\ QC + 32 <= SP - 2048 /\ 17594333495296 <= SB /\ SB mod 4096 = 0 /\
               SB + 137438953472 + 4096 <= SP - 2048 /\ 2^46 + 4096 <= SP <= 2^47 /\ (QC + 32 <= SB \/ SB + 137438953472 + 4096 <= QC) /\
               B = SB + 103079215104 + 8192 * qj /\ 0 <= qj < 32 /\ 0 <= qb < 2^62 /\ 0 <= gb < 2^62 /\ 0 <= mxs < 2^62 /\
               0 <= mx < 2^62 /\ mx + 1 <= qb /\ qb + gb <= mxs /\ 0 <= pa2 < 2^64 /\ 0 <= pa3 < 2^64 /\ 0 <= gf < 2^64 /\
               GLB = SB + 103079215104 + 8192 * gl /\ 0 <= gl < 32 /\ 1 <= gn /\ gn + 1 < 2^32) by (unfold B, GLB; lia).
  clear HQC HSB HSEP Hmx Hqj Hqb Hgb Hmxs Hpa Hgf Hgl Hgn1 Hgn. clearbody B GLB.
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by (zlh HZ); reflexivity).
  assert (P : AXF_qt2az.qt2a_pre regs m QC qb mx B gn GLB gb mxs pa2 pa3 gf).
  { constructor; try assumption; try (zlh HZ).
    - rewrite H2. apply (stk_ok_shrink m (wa SP) 2048 1024); [lia | exact HSTK].
    - rewrite HSPa. zlh HZ.
    - rewrite Z.add_0_r. exact Rsz.
    - intros d k Hd Hk. rewrite Z.add_0_r. apply Hwq; assumption.
    - rewrite HSPa, Z.add_0_r. exact S0.
    - rewrite HSPa. exact S8.
    - intros d k Hd Hk. rewrite Z.add_0_r. apply Wgl; assumption. }
  destruct (AXF_qt2az.qt2a_pda regs m rom QC qb mx B gn GLB gb mxs pa2 pa3 gf P
              (sc_qt2a regs m SP HSPa QC qb mx B gn GLB gb mxs pa2 pa3 gf ltac:(unfold t_geo; zlh HZ) ltac:(zlh HZ)))
    as (R & Hms & A1 & _ & _ & A8 & A9 & _ & _ & _ & _ & _ & _ & _ & _ & A22 & KK).
  clear P.
  set (m' := AXF_qt2az.qt2a_mem_pda m regs QC qb mx B gn GLB gb mxs pa2 pa3 gf) in *.
  assert (EM : m' = wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
                 (wbytes (wbytes (wbytes (wbytes (wbytes m (wa (SP + -8)) (word_to_le_bytes 8 (wa 277836))) (wa (SP + -16)) (word_to_le_bytes 8 (wa 930544)))
                    (wa (SP + -24)) (word_to_le_bytes 8 (wa QC))) (wa (SP + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))))))
                    (wa (SP + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))))))
                 (wa 930696) (word_to_le_bytes 4 (wa 1))) (wa GLB) (word_to_le_bytes 8 (wa B))) (wa 930704) (word_to_le_bytes 8 (wa (gn + 1))))
                 (wa 930720) (word_to_le_bytes 8 (wa B))) (wa QC) (word_to_le_bytes 8 (wa 0))) (wa (QC + 8)) (word_to_le_bytes 8 (wa 0)))
                 (wa (QC + 16)) (word_to_le_bytes 8 (wa 0))) (wa 930728) (word_to_le_bytes 8 (wa (qb + gb)))) (wa (QC + 24)) (word_to_le_bytes 8 (wa 0)))
                 (wa 930696) (word_to_le_bytes 1 (wa 0))).
  { unfold m', AXF_qt2az.qt2a_mem_pda. rewrite HSPa, (Z.add_0_r QC), (Z.add_0_r GLB). reflexivity. }
  clearbody m'.
  assert (G : mem_grows m m') by (rewrite EM; do 15 apply grows_wb; apply mem_grows_refl).
  assert (FRM : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (QC <= x < QC + 32) -> ~ (930696 <= x < 930700) -> ~ (930704 <= x < 930736) ->
                  ~ (GLB <= x < GLB + 8) -> m' (wa x) = m (wa x)).
  { intros x Hx Q1 Q2 Q3 Q4 Q5. rewrite EM. repeat (rewrite wb_other by first [exact Hx | (lenq; zlh HZ) | (lenq; clear - HZ Q1 Q2 Q3 Q4 Q5; lia)]). reflexivity. }
  exists R, m'. split; [exact Hms|]. split; [exact A1|].
  split.
  { intros k Hk. cbn [KT2 In] in Hk.
    repeat (destruct Hk as [<-|Hk]; [first [ apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ]
                                           | (transitivity (wa 930544); [exact A8 | symmetry; exact H8])
                                           | (transitivity (wa QC); [exact A9 | symmetry; exact H9])
                                           | (transitivity (wa mx); [exact A22 | symmetry; exact H22]) ]|]).
    destruct Hk. }
  split.
  { unfold q_inv. split; [lia|]. split; [rewrite EM; rdw HZ|]. left. split; [reflexivity|]. split; [reflexivity|]. rewrite EM. rdw HZ. }
  split.
  { unfold gq_inv. split; [lia|]. split; [zlh HZ|]. split; [zlh HZ|].
    split.
    { apply rd4_zero_of_bytes; [lia | lia | | | |].
      - rewrite EM. apply wbytes_at_wa0; [lia | lenq; lia | lenq; lia].
      - rewrite EM. rewrite wb_other by (first [lia | (lenq; lia)]).
        repeat (rewrite wb_other by first [lia | (lenq; zlh HZ)]).
        replace (930696 + 1) with (930696 + Z.of_nat 1) by reflexivity. rewrite wbytes_at_wa by (first [lia | (lenq; lia) | (rewrite length_N_to_le_bytes; lia)]). reflexivity.
      - rewrite EM. rewrite wb_other by (first [lia | (lenq; lia)]).
        repeat (rewrite wb_other by first [lia | (lenq; zlh HZ)]).
        replace (930696 + 2) with (930696 + Z.of_nat 2) by reflexivity. rewrite wbytes_at_wa by (first [lia | (lenq; lia) | (rewrite length_N_to_le_bytes; lia)]). reflexivity.
      - rewrite EM. rewrite wb_other by (first [lia | (lenq; lia)]).
        repeat (rewrite wb_other by first [lia | (lenq; zlh HZ)]).
        replace (930696 + 3) with (930696 + Z.of_nat 3) by reflexivity. rewrite wbytes_at_wa by (first [lia | (lenq; lia) | (rewrite length_N_to_le_bytes; lia)]). reflexivity. }
    split; [exact (wr_grows' m m' _ _ G Wmu)|].
    split; [rewrite EM; rdw HZ|].
    split; [rewrite EM; rdw HZ|].
    split; [exact (wr_grows' m m' _ _ G Wg)|].
    split; [apply (rd_frame m m'); [lia | lenq; lia | intros x Hx; lenq; apply FRM; clear - HZ Hx; lia | exact Rmxs]|].
    split; [exists gf; split; [zlh HZ | rewrite EM; rdw HZ; exact Rgf]|].
    right. split; [lia|]. split; [zlh HZ|]. replace (SB + 103079215104 + 8192 * qj) with B by (zlh HZ).
    split; [rewrite EM; rdw HZ|].
    intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Wb; lia. }
  split; [rewrite EM; rdw HZ|].
  split; [exact FRM | exact G].
Qed.
End QTDA.
(* [comment removed for export] *)
End AXG_qt.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q1 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.NqTail.AXG_qt.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcPri.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma gq_inv_of_o : forall m SB gn gl gb mxs, gq_inv_o m SB gn gl gb -> 0 <= mxs < 2^62 -> rd m 930608 8 mxs -> gq_inv m SB gn gl gb mxs.
Proof. intros m SB gn gl gb mxs (G1 & G2 & R1 & W1 & R2 & R3 & W2 & G3 & G4) Hm Rm. unfold gq_inv. tauto. Qed.
Lemma gq_inv_to_o : forall m SB gn gl gb mxs, gq_inv m SB gn gl gb mxs -> gq_inv_o m SB gn gl gb.
Proof. intros m SB gn gl gb mxs (G1 & G2 & _ & R1 & W1 & R2 & R3 & W2 & _ & G3 & G4). unfold gq_inv_o. tauto. Qed.

Theorem qtail_d : forall {fx : FPState} rom m regs QC SB qj qn qb mx gn gl gb mxs SP pa2 pa3,
  q_inv m QC SB qj qn qb -> 1 <= qn -> gq_inv m SB gn gl gb mxs -> gn + 1 < 2^32 ->
  getr regs 2 = wa SP -> getr regs 8 = wa 930544 -> getr regs 9 = wa QC -> getr regs 22 = wa mx ->
  2^46 + 4096 <= SP <= 2^47 -> stk_ok SEGS m (wa SP) 2048 -> rd m SP 8 pa2 -> rd m (SP + 8) 8 pa3 -> 0 <= pa2 < 2^64 /\ 0 <= pa3 < 2^64 ->
  ((4176 <= QC /\ QC + 4016 <= 65536) \/ 6537296 <= QC) /\ QC + 32 <= SP - 2048 ->
  17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048 ->
  (QC + 32 <= SB \/ SB + 137438953472 + 4096 <= QC) ->
  0 <= mx < 2^62 /\ mx + 1 <= qb /\ qb + gb <= mxs -> wr m QC 32 ->
  exists R m', msteps SEGS (mkst regs (wa 0x43e14) m rom) (mkst R (wa 0x43d4c) m' rom) /\
    getr R 1 = wa 277836 /\
    (forall k, In k KT2 -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    q_inv m' QC SB qj 0 0 /\ gq_inv m' SB (gn + 1) qj (qb + gb) mxs /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (QC <= x < QC + 32) -> ~ (930696 <= x < 930736) ->
       ~ (1 <= gn /\ SB + 103079215104 + 8192 * gl <= x < SB + 103079215104 + 8192 * gl + 8) -> m' (wa x) = m (wa x)) /\
    mem_grows m m'.
Proof.
  intros fx rom m regs QC SB qj qn qb mx gn gl gb mxs SP pa2 pa3 IQ Hqn IGQ Hgn H2 H8 H9 H22 HSP HSTK S0 S8 Hpa HQC HSB HSEP Hmx Hwq.
  assert (Hgn0 : 0 <= gn) by (destruct IGQ as ((X & _) & _); exact X).
  destruct (Z.eq_dec gn 0) as [->|Hne].
  - destruct (@qtail_dc fx rom m regs QC SB qj qn qb mx gl gb mxs SP pa2 pa3 IQ Hqn IGQ H2 H8 H9 H22 HSP HSTK S0 S8 Hpa HQC HSB HSEP Hmx Hwq)
      as (R & m' & Hms & HR1 & HK & HQ' & HG' & Hfr & Hgr).
    exists R, m'. split; [exact Hms|]. split; [exact HR1|]. split; [exact HK|]. split; [exact HQ'|]. split; [exact HG'|]. split; [|exact Hgr].
    intros x Hx N0 N1 N2 _. apply Hfr; [exact Hx | exact N0 | exact N1 | clear - N2; lia | clear - N2; lia].
  - destruct (@qtail_da fx rom m regs QC SB qj qn qb mx gn gl gb mxs SP pa2 pa3 IQ Hqn IGQ ltac:(lia) H2 H8 H9 H22 HSP HSTK S0 S8 Hpa HQC HSB HSEP Hmx Hwq)
      as (R & m' & Hms & HR1 & HK & HQ' & HG' & _ & Hfr & Hgr).
    exists R, m'. split; [exact Hms|]. split; [exact HR1|]. split; [exact HK|]. split; [exact HQ'|]. split; [exact HG'|]. split; [|exact Hgr].
    intros x Hx N0 N1 N2 N3. apply Hfr; [exact Hx | exact N0 | exact N1 | clear - N2; lia | clear - N2; lia |].
    intros Hc0. apply N3. split; [clear - Hgn0 Hne; lia | exact Hc0].
Qed.
(* [comment removed for export] *)
