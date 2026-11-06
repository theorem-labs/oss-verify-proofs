(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AxAsan.

Module AXF_pt0.
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

Definition e_dmy := EVar 32.
Definition STK := SA (EVar 2) (-1024).
Definition sr_pt0 := sr_id.
Definition kn_pt0 : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange (EVar 10) 1 (2^47);
    KRange (EVar 11) 1 256;
    KImg 65536 143360 ].
Definition scr_pt0 : scripts := SCR [] [] [].
Definition ss_pt0 := SS 0x81f7c sr_pt0 [] kn_pt0 33.
Definition RUN_pt0 := sym_exec SEGS 200 true [0x8202c; 0x821c0] scr_pt0 ss_pt0 [].

Definition scr_ppt0 : scripts := SCR [] [] [].
Definition RES_ppt0 := Eval vm_compute in sym_exec SEGS 200 true [0x8202c; 0x821c0] scr_ppt0 ss_pt0 [].
Lemma RES_ppt0_ok : sym_exec SEGS 200 true [0x8202c; 0x821c0] scr_ppt0 (SS 0x81f7c sr_pt0 [] kn_pt0 33) [] = RES_ppt0.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_pt0.


Module AXF_pt0z.
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

Section PT0.
Context {fx : FPState}.

Definition VALS_pt0 (dmy : Z) : list Z := [dmy].

Record pt0_pre (regs : bvmap 5 word) (m : word -> option byte) (dmy : Z) : Prop := {
  pt0_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  pt0_rng_dmy : 0 <= dmy <= 0 ;
  pt0_kr0 : (2^20) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  pt0_ka1 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) mod 16 = 0 ;
  pt0_kr3 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) <= (2^47) ;
  pt0_kr4 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11))) <= 256 ;
  pt0_kimg5 : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None
}.


#[using="Type"] Lemma pt0_setup : forall regs m dmy, pt0_pre regs m dmy ->
  regs_ok (Ez regs (VALS_pt0 dmy)) AXF_pt0.sr_pt0 regs /\ know_ok SEGS (Ez regs (VALS_pt0 dmy)) m AXF_pt0.kn_pt0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m dmy P. destruct P as [pt0_HSTK pt0_rng_dmy pt0_kr0 pt0_ka1 pt0_kr3 pt0_kr4 pt0_kimg5].
  set (E := Ez regs (VALS_pt0 dmy)).
  assert (Z32 : bv_unsigned (ev E 32) = dmy) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  assert (Z11 : bv_unsigned (ev E 11) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11)))) by reflexivity.
  split.
  { unfold AXF_pt0.sr_pt0.
    apply regs_ok_id.
 }
  unfold know_ok, AXF_pt0.kn_pt0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pt0.e_dmy AXF_pt0.STK a_base a_off].
  all: rewrite ?Z32, ?Z2, ?Z10, ?Z11.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range dmy _ _ pt0_rng_dmy eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - pt0_rng_dmy pt0_kr0 pt0_ka1 pt0_kr3 pt0_kr4; lia).
  all: first [lia].
Qed.


Definition pt0_mem_ppt0 (m : word -> option byte) (regs : bvmap 5 word) (dmy : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -72)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -80)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -88)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -104)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -96)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11)))))).

#[using="Type"] Theorem pt0_ppt0 : forall regs m rom dmy, pt0_pre regs m dmy ->
  scs_denot SEGS m (Ez regs (VALS_pt0 dmy)) (snd (fst AXF_pt0.RES_ppt0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x81f7c) m rom) (mkst R (wa 0x8202c) (pt0_mem_ppt0 m regs dmy) rom) /\
    getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -112) /\ getr R 8 = wa 0 /\ getr R 9 = wa 1869144 /\ getr R 10 = wa 14313749767032793493 /\ getr R 11 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) /\ getr R 13 = wa 0 /\ getr R 14 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + (8 * bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11))))) /\ getr R 15 = wa (8 * bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11)))) /\ getr R 16 = wa 10900877739976798860 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom dmy P Hsc. destruct (pt0_setup regs m dmy P) as [HR HK].
  set (E := Ez regs (VALS_pt0 dmy)) in *. destruct P as [pt0_HSTK pt0_rng_dmy pt0_kr0 pt0_ka1 pt0_kr3 pt0_kr4 pt0_kimg5].
  assert (Z32 : bv_unsigned (ev E 32) = dmy) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  assert (Z11 : bv_unsigned (ev E 11) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11)))) by reflexivity.
  destruct (run_sound SEGS 200 [0x8202c; 0x821c0] AXF_pt0.scr_ppt0 0x81f7c AXF_pt0.sr_pt0 AXF_pt0.kn_pt0 33 _ _ _ E m rom regs AXF_pt0.RES_ppt0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pt0.RES_ppt0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pt0_mem_ppt0 m regs dmy) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pt0_mem_ppt0. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End PT0.
(* [comment removed for export] *)
End AXF_pt0z.


Module AXF_ph.
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

Definition e_wk := EVar 32.
Definition sr_ph := sr_id.
Definition kn_ph : list kentry :=
  [ KRange (EVar 11) 1 (2^47);
    KWord (SA (EVar 11) 0) 8 e_wk ].
Definition scr_ph : scripts := SCR [true] [] [].
Definition ss_ph := SS 0x8202c sr_ph [] kn_ph 33.
Definition RUN_ph := sym_exec SEGS 30 true [0x8202c; 0x82050] scr_ph ss_ph [].

Definition scr_phc : scripts := SCR [true] [] [].
Definition RES_phc := Eval vm_compute in sym_exec SEGS 30 true [0x8202c; 0x82050] scr_phc ss_ph [].
Lemma RES_phc_ok : sym_exec SEGS 30 true [0x8202c; 0x82050] scr_phc (SS 0x8202c sr_ph [] kn_ph 33) [] = RES_phc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_phx : scripts := SCR [false] [] [].
Definition RES_phx := Eval vm_compute in sym_exec SEGS 30 true [0x8202c; 0x82050] scr_phx ss_ph [].
Lemma RES_phx_ok : sym_exec SEGS 30 true [0x8202c; 0x82050] scr_phx (SS 0x8202c sr_ph [] kn_ph 33) [] = RES_phx.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_ph.


Module AXF_phz.
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

Section PH.
Context {fx : FPState}.

Definition VALS_ph (wk : Z) : list Z := [wk].

Record ph_pre (regs : bvmap 5 word) (m : word -> option byte) (wk : Z) : Prop := {
  ph_rng_wk : 0 <= wk <= 2^64-1 ;
  ph_kr0 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11))) <= (2^47) ;
  ph_kw1 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11))) + 0)) 8 = Some (word_to_le_bytes 8 (wa wk))
}.


#[using="Type"] Lemma ph_setup : forall regs m wk, ph_pre regs m wk ->
  regs_ok (Ez regs (VALS_ph wk)) AXF_ph.sr_ph regs /\ know_ok SEGS (Ez regs (VALS_ph wk)) m AXF_ph.kn_ph.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m wk P. destruct P as [ph_rng_wk ph_kr0 ph_kw1].
  set (E := Ez regs (VALS_ph wk)).
  assert (Z32 : bv_unsigned (ev E 32) = wk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z11 : bv_unsigned (ev E 11) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11)))) by reflexivity.
  split.
  { unfold AXF_ph.sr_ph.
    apply regs_ok_id.
 }
  unfold know_ok, AXF_ph.kn_ph.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_ph.e_wk a_base a_off].
  all: rewrite ?Z32, ?Z11.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - ph_rng_wk ph_kr0; lia).
  all: first [lia].
Qed.


Definition ph_mem_phc (m : word -> option byte) (regs : bvmap 5 word) (wk : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem ph_phc : forall regs m rom wk, ph_pre regs m wk ->
  scs_denot SEGS m (Ez regs (VALS_ph wk)) (snd (fst AXF_ph.RES_phc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x8202c) m rom) (mkst R (wa 0x8202c) (ph_mem_phc m regs wk) rom) /\
    getr R 11 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11))) + 8) /\ getr R 16 = wa (Z.shiftr (((wk * bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))))) mod 2^64) 47) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom wk P Hsc. destruct (ph_setup regs m wk P) as [HR HK].
  set (E := Ez regs (VALS_ph wk)) in *. destruct P as [ph_rng_wk ph_kr0 ph_kw1].
  assert (Z32 : bv_unsigned (ev E 32) = wk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z11 : bv_unsigned (ev E 11) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11)))) by reflexivity.
  destruct (run_sound SEGS 30 [0x8202c; 0x82050] AXF_ph.scr_phc 0x8202c AXF_ph.sr_ph AXF_ph.kn_ph 33 _ _ _ E m rom regs AXF_ph.RES_phc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ph.RES_phc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ph_mem_phc m regs wk) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ph_mem_phc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition ph_mem_phx (m : word -> option byte) (regs : bvmap 5 word) (wk : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem ph_phx : forall regs m rom wk, ph_pre regs m wk ->
  scs_denot SEGS m (Ez regs (VALS_ph wk)) (snd (fst AXF_ph.RES_phx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x8202c) m rom) (mkst R (wa 0x82050) (ph_mem_phx m regs wk) rom) /\
    getr R 11 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11))) + 8) /\ getr R 16 = wa (Z.shiftr (((wk * bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))))) mod 2^64) 47) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom wk P Hsc. destruct (ph_setup regs m wk P) as [HR HK].
  set (E := Ez regs (VALS_ph wk)) in *. destruct P as [ph_rng_wk ph_kr0 ph_kw1].
  assert (Z32 : bv_unsigned (ev E 32) = wk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z11 : bv_unsigned (ev E 11) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11)))) by reflexivity.
  destruct (run_sound SEGS 30 [0x8202c; 0x82050] AXF_ph.scr_phx 0x8202c AXF_ph.sr_ph AXF_ph.kn_ph 33 _ _ _ E m rom regs AXF_ph.RES_phx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ph.RES_phx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ph_mem_phx m regs wk) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ph_mem_phx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End PH.
(* [comment removed for export] *)
End AXF_phz.


Module AXF_pt1.
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

Definition e_dmy := EVar 32.
Definition sr_pt1 := sr_id.
Definition kn_pt1 : list kentry :=
  [  ].
Definition scr_pt1 : scripts := SCR [] [] [].
Definition ss_pt1 := SS 0x82050 sr_pt1 [] kn_pt1 33.
Definition RUN_pt1 := sym_exec SEGS 40 true [0x82090] scr_pt1 ss_pt1 [].

Definition scr_ppt1 : scripts := SCR [] [] [].
Definition RES_ppt1 := Eval vm_compute in sym_exec SEGS 40 true [0x82090] scr_ppt1 ss_pt1 [].
Lemma RES_ppt1_ok : sym_exec SEGS 40 true [0x82090] scr_ppt1 (SS 0x82050 sr_pt1 [] kn_pt1 33) [] = RES_ppt1.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_pt1.


Module AXF_pt1z.
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

Section PT1.
Context {fx : FPState}.

Definition VALS_pt1 (dmy : Z) : list Z := [dmy].

Record pt1_pre (regs : bvmap 5 word) (m : word -> option byte) (dmy : Z) : Prop := {
  pt1_rng_dmy : 0 <= dmy <= 0
}.


#[using="Type"] Lemma pt1_setup : forall regs m dmy, pt1_pre regs m dmy ->
  regs_ok (Ez regs (VALS_pt1 dmy)) AXF_pt1.sr_pt1 regs /\ know_ok SEGS (Ez regs (VALS_pt1 dmy)) m AXF_pt1.kn_pt1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m dmy P. destruct P as [pt1_rng_dmy].
  set (E := Ez regs (VALS_pt1 dmy)).
  assert (Z32 : bv_unsigned (ev E 32) = dmy) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_pt1.sr_pt1.
    apply regs_ok_id.
 }
  unfold know_ok, AXF_pt1.kn_pt1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pt1.e_dmy a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range dmy _ _ pt1_rng_dmy eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - pt1_rng_dmy; lia).
  all: first [lia].
Qed.


Definition pt1_mem_ppt1 (m : word -> option byte) (regs : bvmap 5 word) (dmy : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem pt1_ppt1 : forall regs m rom dmy, pt1_pre regs m dmy ->
  scs_denot SEGS m (Ez regs (VALS_pt1 dmy)) (snd (fst AXF_pt1.RES_ppt1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x82050) m rom) (mkst R (wa 0x82090) (pt1_mem_ppt1 m regs dmy) rom) /\
    getr R 13 = wa 4194304 /\ getr R 22 = wa 65535 /\ getr R 23 = wa 2147483647 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 20; 21; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom dmy P Hsc. destruct (pt1_setup regs m dmy P) as [HR HK].
  set (E := Ez regs (VALS_pt1 dmy)) in *. destruct P as [pt1_rng_dmy].
  assert (Z32 : bv_unsigned (ev E 32) = dmy) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 40 [0x82090] AXF_pt1.scr_ppt1 0x82050 AXF_pt1.sr_pt1 AXF_pt1.kn_pt1 33 _ _ _ E m rom regs AXF_pt1.RES_ppt1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pt1.RES_ppt1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pt1_mem_ppt1 m regs dmy) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pt1_mem_ppt1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End PT1.
(* [comment removed for export] *)
End AXF_pt1z.


Module AXF_pt2.
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

Definition e_hd := EVar 32.
Definition sr_pt2 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 9 (ELit 1869144)) 13 (ELit 4194304)) 22 (ELit 65535)) 23 (ELit 2147483647)).
Definition kn_pt2 : list kentry :=
  [ KRange (EVar 18) 1 (2^47);
    KAlign (EVar 18) 4;
    KWord (SA (EVar 18) 0) 4 e_hd ].
Definition scr_pt2 : scripts := SCR [] [] [].
Definition ss_pt2 := SS 0x8209c sr_pt2 [] kn_pt2 33.
Definition RUN_pt2 := sym_exec SEGS 20 true [0x820bc] scr_pt2 ss_pt2 [].

Definition scr_ppt2 : scripts := SCR [] [] [].
Definition RES_ppt2 := Eval vm_compute in sym_exec SEGS 20 true [0x820bc] scr_ppt2 ss_pt2 [].
Lemma RES_ppt2_ok : sym_exec SEGS 20 true [0x820bc] scr_ppt2 (SS 0x8209c sr_pt2 [] kn_pt2 33) [] = RES_ppt2.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_pt2.


Module AXF_pt2z.
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

Section PT2.
Context {fx : FPState}.

Definition VALS_pt2 (hd : Z) : list Z := [hd].

Record pt2_pre (regs : bvmap 5 word) (m : word -> option byte) (hd : Z) : Prop := {
  pt2_R9 : getr regs 9 = wa 1869144 ;
  pt2_R13 : getr regs 13 = wa 4194304 ;
  pt2_R22 : getr regs 22 = wa 65535 ;
  pt2_R23 : getr regs 23 = wa 2147483647 ;
  pt2_rng_hd : 0 <= hd <= 2^32-1 ;
  pt2_kr0 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))) <= (2^47) ;
  pt2_ka1 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))) mod 4 = 0 ;
  pt2_kw2 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))) + 0)) 4 = Some (word_to_le_bytes 4 (wa hd))
}.


#[using="Type"] Lemma pt2_setup : forall regs m hd, pt2_pre regs m hd ->
  regs_ok (Ez regs (VALS_pt2 hd)) AXF_pt2.sr_pt2 regs /\ know_ok SEGS (Ez regs (VALS_pt2 hd)) m AXF_pt2.kn_pt2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m hd P. destruct P as [pt2_R9 pt2_R13 pt2_R22 pt2_R23 pt2_rng_hd pt2_kr0 pt2_ka1 pt2_kw2].
  set (E := Ez regs (VALS_pt2 hd)).
  assert (Z32 : bv_unsigned (ev E 32) = hd) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z18 : bv_unsigned (ev E 18) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) by reflexivity.
  split.
  { unfold AXF_pt2.sr_pt2.
    apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|]|]|]|].
    - rewrite pt2_R9. reflexivity.
    - rewrite pt2_R13. reflexivity.
    - rewrite pt2_R22. reflexivity.
    - rewrite pt2_R23. reflexivity. }
  unfold know_ok, AXF_pt2.kn_pt2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pt2.e_hd a_base a_off].
  all: rewrite ?Z32, ?Z18.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range hd _ _ pt2_rng_hd eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - pt2_rng_hd pt2_kr0 pt2_ka1; lia).
  all: first [lia].
Qed.


Definition pt2_mem_ppt2 (m : word -> option byte) (regs : bvmap 5 word) (hd : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem pt2_ppt2 : forall regs m rom hd, pt2_pre regs m hd ->
  scs_denot SEGS m (Ez regs (VALS_pt2 hd)) (snd (fst AXF_pt2.RES_ppt2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x8209c) m rom) (mkst R (wa 0x820bc) (pt2_mem_ppt2 m regs hd) rom) /\
    getr R 9 = wa 1869144 /\ getr R 10 = wa (ext_Z true 0 4 hd) /\ getr R 11 = wa (Z.land ((ext_Z true 0 4 hd) mod 2^64) 2147483647) /\ getr R 13 = wa 4194312 /\ getr R 20 = wa 6063456 /\ getr R 22 = wa 65535 /\ getr R 23 = wa 2147483647 /\ getr R 24 = wa 6063464 /\ getr R 25 = wa (Z.land ((ext_Z true 0 4 hd) mod 2^64) 2147483647) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 12; 14; 15; 16; 17; 18; 19; 21; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom hd P Hsc. destruct (pt2_setup regs m hd P) as [HR HK].
  set (E := Ez regs (VALS_pt2 hd)) in *. destruct P as [pt2_R9 pt2_R13 pt2_R22 pt2_R23 pt2_rng_hd pt2_kr0 pt2_ka1 pt2_kw2].
  assert (Z32 : bv_unsigned (ev E 32) = hd) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z18 : bv_unsigned (ev E 18) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) by reflexivity.
  destruct (run_sound SEGS 20 [0x820bc] AXF_pt2.scr_ppt2 0x8209c AXF_pt2.sr_pt2 AXF_pt2.kn_pt2 33 _ _ _ E m rom regs AXF_pt2.RES_ppt2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pt2.RES_ppt2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pt2_mem_ppt2 m regs hd) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pt2_mem_ppt2. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End PT2.
(* [comment removed for export] *)
End AXF_pt2z.


Module AXF_pf.
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

Definition e_id := EVar 32.
Definition e_D1 := EVar 33.
Definition e_hv := EVar 34.
Definition e_lk := EVar 35.
Definition NODE := EAlu ALU_ADD (EMd M_MUL (ELit 16) e_id) e_D1.
Definition sr_pf := (sr_upd (sr_upd (sr_upd sr_id 11 (e_id)) 22 (ELit 65535)) 23 (ELit 2147483647)).
Definition kn_pf : list kentry :=
  [ KRange e_id 0 65535;
    KRange e_D1 1 (2^47);
    KAlign e_D1 16;
    KRange (EVar 24) 1 (2^47);
    KAlign (EVar 24) 8;
    KWord (SA (EVar 24) 0) 8 e_D1;
    KRange NODE 1 (2^48);
    KWord (SA NODE 0) 8 e_hv;
    KWord (SA NODE 8) 4 e_lk ].
Definition scr_pf : scripts := SCR [false; true] [] [].
Definition ss_pf := SS 0x820bc sr_pf [] kn_pf 36.
Definition RUN_pf := sym_exec SEGS 30 true [0x820bc; 0x82114; 0x821c0] scr_pf ss_pf [].

Definition scr_pfz : scripts := SCR [true] [] [].
Definition RES_pfz := Eval vm_compute in sym_exec SEGS 30 true [0x820bc; 0x82114; 0x821c0] scr_pfz ss_pf [].
Lemma RES_pfz_ok : sym_exec SEGS 30 true [0x820bc; 0x82114; 0x821c0] scr_pfz (SS 0x820bc sr_pf [] kn_pf 36) [] = RES_pfz.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pfc : scripts := SCR [false; true] [] [].
Definition RES_pfc := Eval vm_compute in sym_exec SEGS 30 true [0x820bc; 0x82114; 0x821c0] scr_pfc ss_pf [].
Lemma RES_pfc_ok : sym_exec SEGS 30 true [0x820bc; 0x82114; 0x821c0] scr_pfc (SS 0x820bc sr_pf [] kn_pf 36) [] = RES_pfc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pff : scripts := SCR [false; false] [] [].
Definition RES_pff := Eval vm_compute in sym_exec SEGS 30 true [0x820bc; 0x82114; 0x821c0] scr_pff ss_pf [].
Lemma RES_pff_ok : sym_exec SEGS 30 true [0x820bc; 0x82114; 0x821c0] scr_pff (SS 0x820bc sr_pf [] kn_pf 36) [] = RES_pff.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_pf.


Module AXF_pfz.
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

Section PF.
Context {fx : FPState}.

Definition VALS_pf (id D1 hv lk : Z) : list Z := [id; D1; hv; lk].

Record pf_pre (regs : bvmap 5 word) (m : word -> option byte) (id D1 hv lk : Z) : Prop := {
  pf_R11 : getr regs 11 = wa id ;
  pf_R22 : getr regs 22 = wa 65535 ;
  pf_R23 : getr regs 23 = wa 2147483647 ;
  pf_rng_id : 0 <= id <= 65535 ;
  pf_rng_D1 : 1 <= D1 <= 2^47 ;
  pf_rng_hv : 0 <= hv <= 2^64-1 ;
  pf_rng_lk : 0 <= lk <= 2^32-1 ;
  pf_ka2 : D1 mod 16 = 0 ;
  pf_kr3 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24))) <= (2^47) ;
  pf_ka4 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24))) mod 8 = 0 ;
  pf_kw5 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24))) + 0)) 8 = Some (word_to_le_bytes 8 (wa D1)) ;
  pf_kr6 : 1 <= (16 * id) + D1 <= (2^48) ;
  pf_kw7 : rdn SEGS m (wa ((16 * id) + D1 + 0)) 8 = Some (word_to_le_bytes 8 (wa hv)) ;
  pf_kw8 : rdn SEGS m (wa ((16 * id) + D1 + 8)) 4 = Some (word_to_le_bytes 4 (wa lk))
}.


#[using="Type"] Lemma pf_setup : forall regs m id D1 hv lk, pf_pre regs m id D1 hv lk ->
  regs_ok (Ez regs (VALS_pf id D1 hv lk)) AXF_pf.sr_pf regs /\ know_ok SEGS (Ez regs (VALS_pf id D1 hv lk)) m AXF_pf.kn_pf.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m id D1 hv lk P. destruct P as [pf_R11 pf_R22 pf_R23 pf_rng_id pf_rng_D1 pf_rng_hv pf_rng_lk pf_ka2 pf_kr3 pf_ka4 pf_kw5 pf_kr6 pf_kw7 pf_kw8].
  set (E := Ez regs (VALS_pf id D1 hv lk)).
  assert (Z32 : bv_unsigned (ev E 32) = id) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = D1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = lk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z24 : bv_unsigned (ev E 24) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) by reflexivity.
  split.
  { unfold AXF_pf.sr_pf.
    apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|].
    - rewrite pf_R11. reflexivity.
    - rewrite pf_R22. reflexivity.
    - rewrite pf_R23. reflexivity. }
  unfold know_ok, AXF_pf.kn_pf.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pf.e_id AXF_pf.e_D1 AXF_pf.e_hv AXF_pf.e_lk AXF_pf.NODE a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z24.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range id _ _ pf_rng_id eq_refl eq_refl), ?(mod64_of_range D1 _ _ pf_rng_D1 eq_refl eq_refl), ?(mod64_of_range lk _ _ pf_rng_lk eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - pf_rng_id pf_rng_D1 pf_rng_hv pf_rng_lk pf_ka2 pf_kr3 pf_ka4 pf_kr6; lia).
  all: first [lia].
Qed.


Definition pf_mem_pfz (m : word -> option byte) (regs : bvmap 5 word) (id D1 hv lk : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem pf_pfz : forall regs m rom id D1 hv lk, pf_pre regs m id D1 hv lk ->
  scs_denot SEGS m (Ez regs (VALS_pf id D1 hv lk)) (snd (fst AXF_pf.RES_pfz)) ->
  exists R, msteps SEGS (mkst regs (wa 0x820bc) m rom) (mkst R (wa 0x82114) (pf_mem_pfz m regs id D1 hv lk) rom) /\
    getr R 11 = wa id /\ getr R 22 = wa 65535 /\ getr R 23 = wa 2147483647 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom id D1 hv lk P Hsc. destruct (pf_setup regs m id D1 hv lk P) as [HR HK].
  set (E := Ez regs (VALS_pf id D1 hv lk)) in *. destruct P as [pf_R11 pf_R22 pf_R23 pf_rng_id pf_rng_D1 pf_rng_hv pf_rng_lk pf_ka2 pf_kr3 pf_ka4 pf_kw5 pf_kr6 pf_kw7 pf_kw8].
  assert (Z32 : bv_unsigned (ev E 32) = id) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = D1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = lk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z24 : bv_unsigned (ev E 24) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) by reflexivity.
  destruct (run_sound SEGS 30 [0x820bc; 0x82114; 0x821c0] AXF_pf.scr_pfz 0x820bc AXF_pf.sr_pf AXF_pf.kn_pf 36 _ _ _ E m rom regs AXF_pf.RES_pfz_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pf.RES_pfz fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pf_mem_pfz m regs id D1 hv lk) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pf_mem_pfz. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition pf_mem_pfc (m : word -> option byte) (regs : bvmap 5 word) (id D1 hv lk : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem pf_pfc : forall regs m rom id D1 hv lk, pf_pre regs m id D1 hv lk ->
  scs_denot SEGS m (Ez regs (VALS_pf id D1 hv lk)) (snd (fst AXF_pf.RES_pfc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x820bc) m rom) (mkst R (wa 0x820bc) (pf_mem_pfc m regs id D1 hv lk) rom) /\
    getr R 10 = wa id /\ getr R 11 = wa (ext_Z true 0 4 lk) /\ getr R 12 = wa hv /\ getr R 22 = wa 65535 /\ getr R 23 = wa 2147483647 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom id D1 hv lk P Hsc. destruct (pf_setup regs m id D1 hv lk P) as [HR HK].
  set (E := Ez regs (VALS_pf id D1 hv lk)) in *. destruct P as [pf_R11 pf_R22 pf_R23 pf_rng_id pf_rng_D1 pf_rng_hv pf_rng_lk pf_ka2 pf_kr3 pf_ka4 pf_kw5 pf_kr6 pf_kw7 pf_kw8].
  assert (Z32 : bv_unsigned (ev E 32) = id) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = D1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = lk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z24 : bv_unsigned (ev E 24) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) by reflexivity.
  destruct (run_sound SEGS 30 [0x820bc; 0x82114; 0x821c0] AXF_pf.scr_pfc 0x820bc AXF_pf.sr_pf AXF_pf.kn_pf 36 _ _ _ E m rom regs AXF_pf.RES_pfc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pf.RES_pfc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pf_mem_pfc m regs id D1 hv lk) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pf_mem_pfc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition pf_mem_pff (m : word -> option byte) (regs : bvmap 5 word) (id D1 hv lk : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem pf_pff : forall regs m rom id D1 hv lk, pf_pre regs m id D1 hv lk ->
  scs_denot SEGS m (Ez regs (VALS_pf id D1 hv lk)) (snd (fst AXF_pf.RES_pff)) ->
  exists R, msteps SEGS (mkst regs (wa 0x820bc) m rom) (mkst R (wa 0x821c0) (pf_mem_pff m regs id D1 hv lk) rom) /\
    getr R 10 = wa id /\ getr R 11 = wa (ext_Z true 0 4 lk) /\ getr R 12 = wa hv /\ getr R 22 = wa 65535 /\ getr R 23 = wa 2147483647 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom id D1 hv lk P Hsc. destruct (pf_setup regs m id D1 hv lk P) as [HR HK].
  set (E := Ez regs (VALS_pf id D1 hv lk)) in *. destruct P as [pf_R11 pf_R22 pf_R23 pf_rng_id pf_rng_D1 pf_rng_hv pf_rng_lk pf_ka2 pf_kr3 pf_ka4 pf_kw5 pf_kr6 pf_kw7 pf_kw8].
  assert (Z32 : bv_unsigned (ev E 32) = id) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = D1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = lk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z24 : bv_unsigned (ev E 24) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) by reflexivity.
  destruct (run_sound SEGS 30 [0x820bc; 0x82114; 0x821c0] AXF_pf.scr_pff 0x820bc AXF_pf.sr_pf AXF_pf.kn_pf 36 _ _ _ E m rom regs AXF_pf.RES_pff_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pf.RES_pff fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pf_mem_pff m regs id D1 hv lk) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pf_mem_pff. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End PF.
(* [comment removed for export] *)
End AXF_pfz.


Module AXF_pl.
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

Definition e_hd := EVar 32.
Definition STK := SA (EVar 2) (-1024).
Definition sr_pl := (sr_upd sr_id 25 (e_hd)).
Definition kn_pl : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange (EVar 18) 1 (2^47);
    KAlign (EVar 18) 4;
    KWord (SA (EVar 18) 0) 4 e_hd;
    KWr (SA (EVar 18) 0) (ELit 4);
    KDisj STK (ELit 1024) (SA (EVar 18) 0) (ELit 4) ].
Definition scr_pl : scripts := SCR [true; true] [] [].
Definition ss_pl := SS 0x82114 sr_pl [] kn_pl 33.
Definition RUN_pl := sym_exec SEGS 60 true [0x8214c; 0x82124] scr_pl ss_pl [].

Definition scr_ppl : scripts := SCR [true; true] [] [].
Definition RES_ppl := Eval vm_compute in sym_exec SEGS 60 true [0x8214c; 0x82124] scr_ppl ss_pl [].
Lemma RES_ppl_ok : sym_exec SEGS 60 true [0x8214c; 0x82124] scr_ppl (SS 0x82114 sr_pl [] kn_pl 33) [] = RES_ppl.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_pl.


Module AXF_plz.
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

Section PL.
Context {fx : FPState}.

Definition VALS_pl (hd : Z) : list Z := [hd].

Record pl_pre (regs : bvmap 5 word) (m : word -> option byte) (hd : Z) : Prop := {
  pl_R25 : getr regs 25 = wa hd ;
  pl_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  pl_rng_hd : 0 <= hd <= 2^31-1 ;
  pl_kr0 : (2^20) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  pl_ka1 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) mod 16 = 0 ;
  pl_kr3 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))) <= (2^47) ;
  pl_ka4 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))) mod 4 = 0 ;
  pl_kw5 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))) + 0)) 4 = Some (word_to_le_bytes 4 (wa hd)) ;
  pl_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))) + 0 + d)) k = true ;
  pl_kd7 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -1024 + 1024 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))) + 0 \/ bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))) + 0 + 4 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -1024
}.


#[using="Type"] Lemma pl_setup : forall regs m hd, pl_pre regs m hd ->
  regs_ok (Ez regs (VALS_pl hd)) AXF_pl.sr_pl regs /\ know_ok SEGS (Ez regs (VALS_pl hd)) m AXF_pl.kn_pl.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m hd P. destruct P as [pl_R25 pl_HSTK pl_rng_hd pl_kr0 pl_ka1 pl_kr3 pl_ka4 pl_kw5 pl_kwr6 pl_kd7].
  set (E := Ez regs (VALS_pl hd)).
  assert (Z32 : bv_unsigned (ev E 32) = hd) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (Z18 : bv_unsigned (ev E 18) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) by reflexivity.
  split.
  { unfold AXF_pl.sr_pl.
    apply (regs_ok_pin E _ regs 25); [apply regs_ok_id|].
    - rewrite pl_R25. reflexivity. }
  unfold know_ok, AXF_pl.kn_pl.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pl.e_hd AXF_pl.STK a_base a_off].
  all: rewrite ?Z32, ?Z2, ?Z18.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range hd _ _ pl_rng_hd eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply pl_kwr6]; assumption).
  all: try (clear - pl_rng_hd pl_kr0 pl_ka1 pl_kr3 pl_ka4; lia).
  all: first [(clear - pl_rng_hd pl_kr0 pl_ka1 pl_kr3 pl_ka4 pl_kd7; lia) | lia].
Qed.


Definition pl_mem_ppl (m : word -> option byte) (regs : bvmap 5 word) (hd : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 532764))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))) + 0)) (word_to_le_bytes 4 (wa (Z.land ((ext_Z true 0 4 hd) mod 2^64) 2147483647 + -2147483648))).

#[using="Type"] Theorem pl_ppl : forall regs m rom hd, pl_pre regs m hd ->
  scs_denot SEGS m (Ez regs (VALS_pl hd)) (snd (fst AXF_pl.RES_ppl)) ->
  exists R, msteps SEGS (mkst regs (wa 0x82114) m rom) (mkst R (wa 0x8214c) (pl_mem_ppl m regs hd) rom) /\
    getr R 1 = wa 532764 /\ getr R 10 = wa (ext_Z true 0 4 hd) /\ getr R 11 = wa 0 /\ getr R 12 = wa (Z.land ((ext_Z true 0 4 hd) mod 2^64) 2147483647 + -2147483648) /\ getr R 13 = wa (ext_Z true 0 4 hd) /\ getr R 14 = wa 0 /\ getr R 21 = wa (ext_Z true 0 4 hd) /\ getr R 25 = wa hd /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom hd P Hsc. destruct (pl_setup regs m hd P) as [HR HK].
  set (E := Ez regs (VALS_pl hd)) in *. destruct P as [pl_R25 pl_HSTK pl_rng_hd pl_kr0 pl_ka1 pl_kr3 pl_ka4 pl_kw5 pl_kwr6 pl_kd7].
  assert (Z32 : bv_unsigned (ev E 32) = hd) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  assert (Z18 : bv_unsigned (ev E 18) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) by reflexivity.
  destruct (run_sound SEGS 60 [0x8214c; 0x82124] AXF_pl.scr_ppl 0x82114 AXF_pl.sr_pl AXF_pl.kn_pl 33 _ _ _ E m rom regs AXF_pl.RES_ppl_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pl.RES_ppl fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pl_mem_ppl m regs hd) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pl_mem_ppl. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End PL.
(* [comment removed for export] *)
End AXF_plz.


Module AXF_pi0.
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

Definition e_n := EVar 32.
Definition sr_pi0 := (sr_upd sr_id 9 (ELit 1869144)).
Definition kn_pi0 : list kentry :=
  [ KWord (SA (ELit 0) 6063448) 4 e_n;
    KWr (SA (ELit 0) 6063448) (ELit 4);
    KRange e_n 0 65533 ].
Definition scr_pi0 : scripts := SCR [false] [] [].
Definition ss_pi0 := SS 0x8214c sr_pi0 [] kn_pi0 33.
Definition RUN_pi0 := sym_exec SEGS 30 true [0x8216c] scr_pi0 ss_pi0 [].

Definition scr_ppi0 : scripts := SCR [false] [] [].
Definition RES_ppi0 := Eval vm_compute in sym_exec SEGS 30 true [0x8216c] scr_ppi0 ss_pi0 [].
Lemma RES_ppi0_ok : sym_exec SEGS 30 true [0x8216c] scr_ppi0 (SS 0x8214c sr_pi0 [] kn_pi0 33) [] = RES_ppi0.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_pi0.


Module AXF_pi0z.
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

Section PI0.
Context {fx : FPState}.

Definition VALS_pi0 (n : Z) : list Z := [n].

Record pi0_pre (regs : bvmap 5 word) (m : word -> option byte) (n : Z) : Prop := {
  pi0_R9 : getr regs 9 = wa 1869144 ;
  pi0_rng_n : 0 <= n <= 65533 ;
  pi0_kw0 : rdn SEGS m (wa (0 + 6063448)) 4 = Some (word_to_le_bytes 4 (wa n)) ;
  pi0_kwr1 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (0 + 6063448 + d)) k = true
}.


#[using="Type"] Lemma pi0_setup : forall regs m n, pi0_pre regs m n ->
  regs_ok (Ez regs (VALS_pi0 n)) AXF_pi0.sr_pi0 regs /\ know_ok SEGS (Ez regs (VALS_pi0 n)) m AXF_pi0.kn_pi0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n P. destruct P as [pi0_R9 pi0_rng_n pi0_kw0 pi0_kwr1].
  set (E := Ez regs (VALS_pi0 n)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_pi0.sr_pi0.
    apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|].
    - rewrite pi0_R9. reflexivity. }
  unfold know_ok, AXF_pi0.kn_pi0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pi0.e_n a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ pi0_rng_n eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply pi0_kwr1]; assumption).
  all: try (clear - pi0_rng_n; lia).
  all: first [lia].
Qed.


Definition pi0_mem_ppi0 (m : word -> option byte) (regs : bvmap 5 word) (n : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 6063448)) (word_to_le_bytes 4 (wa (n + 1))).

#[using="Type"] Theorem pi0_ppi0 : forall regs m rom n, pi0_pre regs m n ->
  scs_denot SEGS m (Ez regs (VALS_pi0 n)) (snd (fst AXF_pi0.RES_ppi0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x8214c) m rom) (mkst R (wa 0x8216c) (pi0_mem_ppi0 m regs n) rom) /\
    getr R 9 = wa (n + 1) /\ getr R 10 = wa (n + 1) /\ getr R 11 = wa 1 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n P Hsc. destruct (pi0_setup regs m n P) as [HR HK].
  set (E := Ez regs (VALS_pi0 n)) in *. destruct P as [pi0_R9 pi0_rng_n pi0_kw0 pi0_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 30 [0x8216c] AXF_pi0.scr_ppi0 0x8214c AXF_pi0.sr_pi0 AXF_pi0.kn_pi0 33 _ _ _ E m rom regs AXF_pi0.RES_ppi0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pi0.RES_ppi0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pi0_mem_ppi0 m regs n) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pi0_mem_ppi0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End PI0.
(* [comment removed for export] *)
End AXF_pi0z.


Module AXF_pi1.
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

Definition e_id := EVar 32.
Definition e_D1 := EVar 33.
Definition e_F := EVar 34.
Definition e_B1 := EVar 35.
Definition e_tr := EVar 36.
Definition e_sz := EVar 37.
Definition STK := SA (EVar 2) (-1024).
Definition NODE := EAlu ALU_ADD e_D1 (EMd M_MUL (ELit 16) (EAlu ALU_AND e_id (ELit 65535))).
Definition BLK := EAlu ALU_ADD e_B1 (EAlu ALU_SRL (EMd M_MUL (ELit 17592186044416) e_F) (ELit 41)).
Definition sr_pi1 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 0)) 9 (e_id)) 10 (e_id)) 22 (ELit 65535)) 23 (ELit 2147483647)) 24 (ELit 6063464)).
Definition kn_pi1 : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange e_D1 1 (2^47);
    KAlign e_D1 16;
    KRange e_B1 1 (2^47);
    KAlign e_B1 8;
    KRange e_tr 1 (2^47);
    KRange (EMd M_MUL (ELit 8) (EAlu ALU_SRL e_id (ELit 16))) 0 0;
    KWord (SA (ELit 0) 6063464) 8 e_D1;
    KRange NODE 1 (2^48);
    KWr (SA NODE 0) (ELit 16);
    KRange (EMd M_MUL (ELit 16) (EAlu ALU_SRL e_F (ELit 20))) 0 0;
    KWord (SA (ELit 0) 1803592) 8 e_F;
    KWr (SA (ELit 0) 1803592) (ELit 8);
    KWord (SA (ELit 0) 1803608) 8 e_B1;
    KWord (SA (EVar 2) 8) 8 e_tr;
    KWord (SA (EVar 2) 16) 8 e_sz;
    KRange BLK 1 (2^48);
    KWr (SA BLK 0) (ELit 8);
    KDisj (SA (EVar 2) (-128)) (ELit 240) (SA NODE 0) (ELit 16);
    KDisj (SA (ELit 0) 1803592) (ELit 32) (SA (EVar 2) (-128)) (ELit 240);
    KDisj (SA (ELit 0) 1803592) (ELit 32) (SA NODE 0) (ELit 16);
    KDisj (SA BLK 0) (ELit 8) (SA (EVar 2) (-128)) (ELit 240);
    KDisj (SA BLK 0) (ELit 8) (SA NODE 0) (ELit 16);
    KDisj (SA BLK 0) (ELit 8) (SA (ELit 0) 1803592) (ELit 32) ].
Definition scr_pi1 : scripts := SCR [true; false; true; false; true; false] [] [].
Definition ss_pi1 := SS 0x8216c sr_pi1 [] kn_pi1 38.
Definition RUN_pi1 := sym_exec SEGS 200 true [0x733b8] scr_pi1 ss_pi1 [].

Definition scr_ppi1 : scripts := SCR [true; false; true; false; true; false] [] [].
Definition RES_ppi1 := Eval vm_compute in sym_exec SEGS 200 true [0x733b8] scr_ppi1 ss_pi1 [].
Lemma RES_ppi1_ok : sym_exec SEGS 200 true [0x733b8] scr_ppi1 (SS 0x8216c sr_pi1 [] kn_pi1 38) [] = RES_ppi1.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_pi1.


Module AXF_pi1z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AxAsan.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section PI1.
Context {fx : FPState}.

Definition VALS_pi1 (id D1 F B1 tr sz : Z) : list Z := [id; D1; F; B1; tr; sz].

Record pi1_pre (regs : bvmap 5 word) (m : word -> option byte) (id D1 F B1 tr sz : Z) : Prop := {
  pi1_R8 : getr regs 8 = wa 0 ;
  pi1_R9 : getr regs 9 = wa id ;
  pi1_R10 : getr regs 10 = wa id ;
  pi1_R22 : getr regs 22 = wa 65535 ;
  pi1_R23 : getr regs 23 = wa 2147483647 ;
  pi1_R24 : getr regs 24 = wa 6063464 ;
  pi1_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  pi1_rng_id : 1 <= id <= 65534 ;
  pi1_rng_D1 : 1 <= D1 <= 2^47 ;
  pi1_rng_F : 0 <= F <= 1048000 ;
  pi1_rng_B1 : 1 <= B1 <= 2^47 ;
  pi1_rng_tr : 1 <= tr <= 2^47 ;
  pi1_rng_sz : 1 <= sz <= 255 ;
  pi1_kr0 : (2^20) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  pi1_ka1 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) mod 16 = 0 ;
  pi1_ka4 : D1 mod 16 = 0 ;
  pi1_ka6 : B1 mod 8 = 0 ;
  pi1_kr8 : 0 <= 8 * Z.shiftr id 16 <= 0 ;
  pi1_kw9 : rdn SEGS m (wa (0 + 6063464)) 8 = Some (word_to_le_bytes 8 (wa D1)) ;
  pi1_kr10 : 1 <= D1 + (16 * Z.land id 65535) <= (2^48) ;
  pi1_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (D1 + (16 * Z.land id 65535) + 0 + d)) k = true ;
  pi1_kr12 : 0 <= 16 * Z.shiftr F 20 <= 0 ;
  pi1_kw13 : rdn SEGS m (wa (0 + 1803592)) 8 = Some (word_to_le_bytes 8 (wa F)) ;
  pi1_kwr14 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 1803592 + d)) k = true ;
  pi1_kw15 : rdn SEGS m (wa (0 + 1803608)) 8 = Some (word_to_le_bytes 8 (wa B1)) ;
  pi1_kw16 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) 8 = Some (word_to_le_bytes 8 (wa tr)) ;
  pi1_kw17 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 16)) 8 = Some (word_to_le_bytes 8 (wa sz)) ;
  pi1_kr18 : 1 <= B1 + Z.shiftr (((17592186044416 * F)) mod 2^64) 41 <= (2^48) ;
  pi1_kwr19 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (B1 + Z.shiftr (((17592186044416 * F)) mod 2^64) 41 + 0 + d)) k = true ;
  pi1_kd20 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -128 + 240 <= D1 + (16 * Z.land id 65535) + 0 \/ D1 + (16 * Z.land id 65535) + 0 + 16 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -128 ;
  pi1_kd21 : 0 + 1803592 + 32 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -128 \/ bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -128 + 240 <= 0 + 1803592 ;
  pi1_kd22 : 0 + 1803592 + 32 <= D1 + (16 * Z.land id 65535) + 0 \/ D1 + (16 * Z.land id 65535) + 0 + 16 <= 0 + 1803592 ;
  pi1_kd23 : B1 + Z.shiftr (((17592186044416 * F)) mod 2^64) 41 + 0 + 8 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -128 \/ bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -128 + 240 <= B1 + Z.shiftr (((17592186044416 * F)) mod 2^64) 41 + 0 ;
  pi1_kd24 : B1 + Z.shiftr (((17592186044416 * F)) mod 2^64) 41 + 0 + 8 <= D1 + (16 * Z.land id 65535) + 0 \/ D1 + (16 * Z.land id 65535) + 0 + 16 <= B1 + Z.shiftr (((17592186044416 * F)) mod 2^64) 41 + 0 ;
  pi1_kd25 : B1 + Z.shiftr (((17592186044416 * F)) mod 2^64) 41 + 0 + 8 <= 0 + 1803592 \/ 0 + 1803592 + 32 <= B1 + Z.shiftr (((17592186044416 * F)) mod 2^64) 41 + 0
}.


#[using="Type"] Lemma pi1_setup : forall regs m id D1 F B1 tr sz, pi1_pre regs m id D1 F B1 tr sz ->
  regs_ok (Ez regs (VALS_pi1 id D1 F B1 tr sz)) AXF_pi1.sr_pi1 regs /\ know_ok SEGS (Ez regs (VALS_pi1 id D1 F B1 tr sz)) m AXF_pi1.kn_pi1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m id D1 F B1 tr sz P. destruct P as [pi1_R8 pi1_R9 pi1_R10 pi1_R22 pi1_R23 pi1_R24 pi1_HSTK pi1_rng_id pi1_rng_D1 pi1_rng_F pi1_rng_B1 pi1_rng_tr pi1_rng_sz pi1_kr0 pi1_ka1 pi1_ka4 pi1_ka6 pi1_kr8 pi1_kw9 pi1_kr10 pi1_kwr11 pi1_kr12 pi1_kw13 pi1_kwr14 pi1_kw15 pi1_kw16 pi1_kw17 pi1_kr18 pi1_kwr19 pi1_kd20 pi1_kd21 pi1_kd22 pi1_kd23 pi1_kd24 pi1_kd25].
  set (E := Ez regs (VALS_pi1 id D1 F B1 tr sz)).
  assert (Z32 : bv_unsigned (ev E 32) = id) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = D1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = F) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = B1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = tr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  split.
  { unfold AXF_pi1.sr_pi1.
    apply (regs_ok_pin E _ regs 24); [apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite pi1_R8. reflexivity.
    - rewrite pi1_R9. reflexivity.
    - rewrite pi1_R10. reflexivity.
    - rewrite pi1_R22. reflexivity.
    - rewrite pi1_R23. reflexivity.
    - rewrite pi1_R24. reflexivity. }
  unfold know_ok, AXF_pi1.kn_pi1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pi1.e_id AXF_pi1.e_D1 AXF_pi1.e_F AXF_pi1.e_B1 AXF_pi1.e_tr AXF_pi1.e_sz AXF_pi1.STK AXF_pi1.NODE AXF_pi1.BLK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range id _ _ pi1_rng_id eq_refl eq_refl), ?(mod64_of_range D1 _ _ pi1_rng_D1 eq_refl eq_refl), ?(mod64_of_range F _ _ pi1_rng_F eq_refl eq_refl), ?(mod64_of_range B1 _ _ pi1_rng_B1 eq_refl eq_refl), ?(mod64_of_range tr _ _ pi1_rng_tr eq_refl eq_refl), ?(mod64_of_range sz _ _ pi1_rng_sz eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply pi1_kwr11 | apply pi1_kwr14 | apply pi1_kwr19]; assumption).
  all: try (clear - pi1_rng_id pi1_rng_D1 pi1_rng_F pi1_rng_B1 pi1_rng_tr pi1_rng_sz pi1_kr0 pi1_ka1 pi1_ka4 pi1_ka6 pi1_kr8 pi1_kr10 pi1_kr12 pi1_kr18; lia).
  all: first [(clear - pi1_rng_id pi1_rng_D1 pi1_rng_F pi1_rng_B1 pi1_rng_tr pi1_rng_sz pi1_kr0 pi1_ka1 pi1_ka4 pi1_ka6 pi1_kr8 pi1_kr10 pi1_kr12 pi1_kr18 pi1_kd20; lia) | (clear - pi1_rng_id pi1_rng_D1 pi1_rng_F pi1_rng_B1 pi1_rng_tr pi1_rng_sz pi1_kr0 pi1_ka1 pi1_ka4 pi1_ka6 pi1_kr8 pi1_kr10 pi1_kr12 pi1_kr18 pi1_kd21; lia) | (clear - pi1_rng_id pi1_rng_D1 pi1_rng_F pi1_rng_B1 pi1_rng_tr pi1_rng_sz pi1_kr0 pi1_ka1 pi1_ka4 pi1_ka6 pi1_kr8 pi1_kr10 pi1_kr12 pi1_kr18 pi1_kd22; lia) | (clear - pi1_rng_id pi1_rng_D1 pi1_rng_F pi1_rng_B1 pi1_rng_tr pi1_rng_sz pi1_kr0 pi1_ka1 pi1_ka4 pi1_ka6 pi1_kr8 pi1_kr10 pi1_kr12 pi1_kr18 pi1_kd23; lia) | (clear - pi1_rng_id pi1_rng_D1 pi1_rng_F pi1_rng_B1 pi1_rng_tr pi1_rng_sz pi1_kr0 pi1_ka1 pi1_ka4 pi1_ka6 pi1_kr8 pi1_kr10 pi1_kr12 pi1_kr18 pi1_kd24; lia) | (clear - pi1_rng_id pi1_rng_D1 pi1_rng_F pi1_rng_B1 pi1_rng_tr pi1_rng_sz pi1_kr0 pi1_ka1 pi1_ka4 pi1_ka6 pi1_kr8 pi1_kr10 pi1_kr12 pi1_kr18 pi1_kd25; lia) | lia].
Qed.


Definition pi1_mem_ppi1 (m : word -> option byte) (regs : bvmap 5 word) (id D1 F B1 tr sz : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa 532900))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa 0))) (wa (D1 + (16 * Z.land id 65535) + 0)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa 531648))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (D1 + (16 * Z.land id 65535))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (D1 + (16 * Z.land id 65535))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -72)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -80)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -88)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -96)) (word_to_le_bytes 8 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa 0))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -104)) (word_to_le_bytes 8 (wa 522744))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -112)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)))) (wa (0 + 1803592)) (word_to_le_bytes 8 (wa ((F + ext_Z true 0 4 sz) + 1)))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -96)) (word_to_le_bytes 8 (wa F))) (wa (B1 + Z.shiftr (((17592186044416 * F)) mod 2^64) 41 + 0)) (word_to_le_bytes 8 (wa sz)).

#[using="Type"] Theorem pi1_ppi1 : forall regs m rom id D1 F B1 tr sz, pi1_pre regs m id D1 F B1 tr sz ->
  scs_denot SEGS m (Ez regs (VALS_pi1 id D1 F B1 tr sz)) (snd (fst AXF_pi1.RES_ppi1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x8216c) m rom) (mkst R (wa 0x733b8) (pi1_mem_ppi1 m regs id D1 F B1 tr sz) rom) /\
    getr R 1 = wa 522776 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -96) /\ getr R 5 = wa (Z.shiftr F 20) /\ getr R 6 = wa (Z.shiftr (((F + ext_Z true 0 4 sz)) mod 2^64) 20) /\ getr R 8 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24) /\ getr R 9 = wa 1803592 /\ getr R 10 = wa ((B1 + Z.shiftr (((17592186044416 * F)) mod 2^64) 41) + 8) /\ getr R 11 = wa tr /\ getr R 12 = wa (8 * ext_Z true 0 4 sz) /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24) /\ getr R 14 = wa (F + ext_Z true 0 4 sz) /\ getr R 15 = wa (ext_Z true 0 4 sz + 1) /\ getr R 18 = wa (ext_Z true 0 4 sz + 1) /\ getr R 19 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8) /\ getr R 20 = wa (ext_Z true 0 4 sz) /\ getr R 21 = wa 0 /\ getr R 22 = wa 65535 /\ getr R 23 = wa id /\ getr R 24 = wa 6063464 /\ (forall k, In k [3; 4; 7; 16; 17; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom id D1 F B1 tr sz P Hsc. destruct (pi1_setup regs m id D1 F B1 tr sz P) as [HR HK].
  set (E := Ez regs (VALS_pi1 id D1 F B1 tr sz)) in *. destruct P as [pi1_R8 pi1_R9 pi1_R10 pi1_R22 pi1_R23 pi1_R24 pi1_HSTK pi1_rng_id pi1_rng_D1 pi1_rng_F pi1_rng_B1 pi1_rng_tr pi1_rng_sz pi1_kr0 pi1_ka1 pi1_ka4 pi1_ka6 pi1_kr8 pi1_kw9 pi1_kr10 pi1_kwr11 pi1_kr12 pi1_kw13 pi1_kwr14 pi1_kw15 pi1_kw16 pi1_kw17 pi1_kr18 pi1_kwr19 pi1_kd20 pi1_kd21 pi1_kd22 pi1_kd23 pi1_kd24 pi1_kd25].
  assert (Z32 : bv_unsigned (ev E 32) = id) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = D1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = F) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = B1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = tr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  destruct (run_sound SEGS 200 [0x733b8] AXF_pi1.scr_ppi1 0x8216c AXF_pi1.sr_pi1 AXF_pi1.kn_pi1 38 _ _ _ E m rom regs AXF_pi1.RES_ppi1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pi1.RES_ppi1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pi1_mem_ppi1 m regs id D1 F B1 tr sz) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pi1_mem_ppi1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite (hdr_frame E (EVar 37) sz) by first [lia | exact Z37]; reflexivity).
  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; cbn [edenot]; unfold ext_val; rewrite Z37; rewrite ext_Z_hi32_zero by lia; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End PI1.
(* [comment removed for export] *)
End AXF_pi1z.


Module AXF_mc0.
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

Definition e_dmy := EVar 32.
Definition sr_mc0 := sr_id.
Definition kn_mc0 : list kentry :=
  [ KRange (EVar 10) 1 (2^48);
    KRange (EVar 12) 0 (2^20) ].
Definition scr_mc0 : scripts := SCR [true] [] [].
Definition ss_mc0 := SS 0x733b8 sr_mc0 [] kn_mc0 33.
Definition RUN_mc0 := sym_exec SEGS 10 true [0x733c4; 0x733d8] scr_mc0 ss_mc0 [].

Definition scr_pmc0z : scripts := SCR [true] [] [].
Definition RES_pmc0z := Eval vm_compute in sym_exec SEGS 10 true [0x733c4; 0x733d8] scr_pmc0z ss_mc0 [].
Lemma RES_pmc0z_ok : sym_exec SEGS 10 true [0x733c4; 0x733d8] scr_pmc0z (SS 0x733b8 sr_mc0 [] kn_mc0 33) [] = RES_pmc0z.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmc0n : scripts := SCR [false] [] [].
Definition RES_pmc0n := Eval vm_compute in sym_exec SEGS 10 true [0x733c4; 0x733d8] scr_pmc0n ss_mc0 [].
Lemma RES_pmc0n_ok : sym_exec SEGS 10 true [0x733c4; 0x733d8] scr_pmc0n (SS 0x733b8 sr_mc0 [] kn_mc0 33) [] = RES_pmc0n.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_mc0.


Module AXF_mc0z.
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

Section MC0.
Context {fx : FPState}.

Definition VALS_mc0 (dmy : Z) : list Z := [dmy].

Record mc0_pre (regs : bvmap 5 word) (m : word -> option byte) (dmy : Z) : Prop := {
  mc0_rng_dmy : 0 <= dmy <= 0 ;
  mc0_kr0 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) <= (2^48) ;
  mc0_kr1 : 0 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12))) <= (2^20)
}.


#[using="Type"] Lemma mc0_setup : forall regs m dmy, mc0_pre regs m dmy ->
  regs_ok (Ez regs (VALS_mc0 dmy)) AXF_mc0.sr_mc0 regs /\ know_ok SEGS (Ez regs (VALS_mc0 dmy)) m AXF_mc0.kn_mc0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m dmy P. destruct P as [mc0_rng_dmy mc0_kr0 mc0_kr1].
  set (E := Ez regs (VALS_mc0 dmy)).
  assert (Z32 : bv_unsigned (ev E 32) = dmy) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  assert (Z12 : bv_unsigned (ev E 12) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) by reflexivity.
  split.
  { unfold AXF_mc0.sr_mc0.
    apply regs_ok_id.
 }
  unfold know_ok, AXF_mc0.kn_mc0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_mc0.e_dmy a_base a_off].
  all: rewrite ?Z32, ?Z10, ?Z12.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range dmy _ _ mc0_rng_dmy eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mc0_rng_dmy mc0_kr0 mc0_kr1; lia).
  all: first [lia].
Qed.


Definition mc0_mem_pmc0z (m : word -> option byte) (regs : bvmap 5 word) (dmy : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mc0_pmc0z : forall regs m rom dmy, mc0_pre regs m dmy ->
  scs_denot SEGS m (Ez regs (VALS_mc0 dmy)) (snd (fst AXF_mc0.RES_pmc0z)) ->
  exists R, msteps SEGS (mkst regs (wa 0x733b8) m rom) (mkst R (wa 0x733d8) (mc0_mem_pmc0z m regs dmy) rom) /\
    (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom dmy P Hsc. destruct (mc0_setup regs m dmy P) as [HR HK].
  set (E := Ez regs (VALS_mc0 dmy)) in *. destruct P as [mc0_rng_dmy mc0_kr0 mc0_kr1].
  assert (Z32 : bv_unsigned (ev E 32) = dmy) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  assert (Z12 : bv_unsigned (ev E 12) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) by reflexivity.
  destruct (run_sound SEGS 10 [0x733c4; 0x733d8] AXF_mc0.scr_pmc0z 0x733b8 AXF_mc0.sr_mc0 AXF_mc0.kn_mc0 33 _ _ _ E m rom regs AXF_mc0.RES_pmc0z_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mc0.RES_pmc0z fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mc0_mem_pmc0z m regs dmy) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mc0_mem_pmc0z. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)

    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mc0_mem_pmc0n (m : word -> option byte) (regs : bvmap 5 word) (dmy : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mc0_pmc0n : forall regs m rom dmy, mc0_pre regs m dmy ->
  scs_denot SEGS m (Ez regs (VALS_mc0 dmy)) (snd (fst AXF_mc0.RES_pmc0n)) ->
  exists R, msteps SEGS (mkst regs (wa 0x733b8) m rom) (mkst R (wa 0x733c4) (mc0_mem_pmc0n m regs dmy) rom) /\
    getr R 12 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10))) + bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom dmy P Hsc. destruct (mc0_setup regs m dmy P) as [HR HK].
  set (E := Ez regs (VALS_mc0 dmy)) in *. destruct P as [mc0_rng_dmy mc0_kr0 mc0_kr1].
  assert (Z32 : bv_unsigned (ev E 32) = dmy) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z10 : bv_unsigned (ev E 10) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) by reflexivity.
  assert (Z12 : bv_unsigned (ev E 12) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 12)))) by reflexivity.
  destruct (run_sound SEGS 10 [0x733c4; 0x733d8] AXF_mc0.scr_pmc0n 0x733b8 AXF_mc0.sr_mc0 AXF_mc0.kn_mc0 33 _ _ _ E m rom regs AXF_mc0.RES_pmc0n_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mc0.RES_pmc0n fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mc0_mem_pmc0n m regs dmy) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mc0_mem_pmc0n. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MC0.
(* [comment removed for export] *)
End AXF_mc0z.


Module AXF_mcb.
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

Definition e_b := EVar 32.
Definition sr_mcb := sr_id.
Definition kn_mcb : list kentry :=
  [ KRange (EVar 11) 1 (2^48);
    KRange (EVar 13) 1 (2^48);
    KWord (SA (EVar 11) 0) 1 e_b;
    KWr (SA (EVar 13) 0) (ELit 1) ].
Definition scr_mcb : scripts := SCR [true] [] [].
Definition ss_mcb := SS 0x733c4 sr_mcb [] kn_mcb 33.
Definition RUN_mcb := sym_exec SEGS 20 true [0x733c4; 0x733d8] scr_mcb ss_mcb [].

Definition scr_pmcc : scripts := SCR [true] [] [].
Definition RES_pmcc := Eval vm_compute in sym_exec SEGS 20 true [0x733c4; 0x733d8] scr_pmcc ss_mcb [].
Lemma RES_pmcc_ok : sym_exec SEGS 20 true [0x733c4; 0x733d8] scr_pmcc (SS 0x733c4 sr_mcb [] kn_mcb 33) [] = RES_pmcc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmcx : scripts := SCR [false] [] [].
Definition RES_pmcx := Eval vm_compute in sym_exec SEGS 20 true [0x733c4; 0x733d8] scr_pmcx ss_mcb [].
Lemma RES_pmcx_ok : sym_exec SEGS 20 true [0x733c4; 0x733d8] scr_pmcx (SS 0x733c4 sr_mcb [] kn_mcb 33) [] = RES_pmcx.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_mcb.


Module AXF_mcbz.
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

Section MCB.
Context {fx : FPState}.

Definition VALS_mcb (b : Z) : list Z := [b].

Record mcb_pre (regs : bvmap 5 word) (m : word -> option byte) (b : Z) : Prop := {
  mcb_rng_b : 0 <= b <= 255 ;
  mcb_kr0 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11))) <= (2^48) ;
  mcb_kr1 : 1 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 13))) <= (2^48) ;
  mcb_kw2 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11))) + 0)) 1 = Some (word_to_le_bytes 1 (wa b)) ;
  mcb_kwr3 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 13))) + 0 + d)) k = true
}.


#[using="Type"] Lemma mcb_setup : forall regs m b, mcb_pre regs m b ->
  regs_ok (Ez regs (VALS_mcb b)) AXF_mcb.sr_mcb regs /\ know_ok SEGS (Ez regs (VALS_mcb b)) m AXF_mcb.kn_mcb.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m b P. destruct P as [mcb_rng_b mcb_kr0 mcb_kr1 mcb_kw2 mcb_kwr3].
  set (E := Ez regs (VALS_mcb b)).
  assert (Z32 : bv_unsigned (ev E 32) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z11 : bv_unsigned (ev E 11) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11)))) by reflexivity.
  assert (Z13 : bv_unsigned (ev E 13) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 13)))) by reflexivity.
  split.
  { unfold AXF_mcb.sr_mcb.
    apply regs_ok_id.
 }
  unfold know_ok, AXF_mcb.kn_mcb.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_mcb.e_b a_base a_off].
  all: rewrite ?Z32, ?Z11, ?Z13.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range b _ _ mcb_rng_b eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mcb_kwr3]; assumption).
  all: try (clear - mcb_rng_b mcb_kr0 mcb_kr1; lia).
  all: first [lia].
Qed.


Definition mcb_mem_pmcc (m : word -> option byte) (regs : bvmap 5 word) (b : Z) : word -> option byte :=
  wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 13))) + 0)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 b))).

#[using="Type"] Theorem mcb_pmcc : forall regs m rom b, mcb_pre regs m b ->
  scs_denot SEGS m (Ez regs (VALS_mcb b)) (snd (fst AXF_mcb.RES_pmcc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x733c4) m rom) (mkst R (wa 0x733c4) (mcb_mem_pmcc m regs b) rom) /\
    getr R 11 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11))) + 1) /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 13))) + 1) /\ getr R 14 = wa (ext_Z false 0 1 b) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom b P Hsc. destruct (mcb_setup regs m b P) as [HR HK].
  set (E := Ez regs (VALS_mcb b)) in *. destruct P as [mcb_rng_b mcb_kr0 mcb_kr1 mcb_kw2 mcb_kwr3].
  assert (Z32 : bv_unsigned (ev E 32) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z11 : bv_unsigned (ev E 11) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11)))) by reflexivity.
  assert (Z13 : bv_unsigned (ev E 13) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 13)))) by reflexivity.
  destruct (run_sound SEGS 20 [0x733c4; 0x733d8] AXF_mcb.scr_pmcc 0x733c4 AXF_mcb.sr_mcb AXF_mcb.kn_mcb 33 _ _ _ E m rom regs AXF_mcb.RES_pmcc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mcb.RES_pmcc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mcb_mem_pmcc m regs b) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mcb_mem_pmcc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mcb_mem_pmcx (m : word -> option byte) (regs : bvmap 5 word) (b : Z) : word -> option byte :=
  wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 13))) + 0)) (word_to_le_bytes 1 (wa (ext_Z false 0 1 b))).

#[using="Type"] Theorem mcb_pmcx : forall regs m rom b, mcb_pre regs m b ->
  scs_denot SEGS m (Ez regs (VALS_mcb b)) (snd (fst AXF_mcb.RES_pmcx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x733c4) m rom) (mkst R (wa 0x733d8) (mcb_mem_pmcx m regs b) rom) /\
    getr R 11 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11))) + 1) /\ getr R 13 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 13))) + 1) /\ getr R 14 = wa (ext_Z false 0 1 b) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom b P Hsc. destruct (mcb_setup regs m b P) as [HR HK].
  set (E := Ez regs (VALS_mcb b)) in *. destruct P as [mcb_rng_b mcb_kr0 mcb_kr1 mcb_kw2 mcb_kwr3].
  assert (Z32 : bv_unsigned (ev E 32) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z11 : bv_unsigned (ev E 11) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11)))) by reflexivity.
  assert (Z13 : bv_unsigned (ev E 13) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 13)))) by reflexivity.
  destruct (run_sound SEGS 20 [0x733c4; 0x733d8] AXF_mcb.scr_pmcx 0x733c4 AXF_mcb.sr_mcb AXF_mcb.kn_mcb 33 _ _ _ E m rom regs AXF_mcb.RES_pmcx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mcb.RES_pmcx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mcb_mem_pmcx m regs b) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mcb_mem_pmcx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MCB.
(* [comment removed for export] *)
End AXF_mcbz.


Module AXF_ptl.
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

Definition e_F := EVar 32.
Definition e_st := EVar 33.
Definition e_node := EVar 34.
Definition e_bkt := EVar 35.
Definition e_h := EVar 36.
Definition e_hd := EVar 37.
Definition e_id := EVar 38.
Definition e_m4 := EVar 39.
Definition e_rp := EVar 40.
Definition e_v0 := EVar 41.
Definition e_v1 := EVar 42.
Definition e_v2 := EVar 43.
Definition e_v3 := EVar 44.
Definition e_v4 := EVar 45.
Definition e_v5 := EVar 46.
Definition e_v6 := EVar 47.
Definition e_v7 := EVar 48.
Definition e_v8 := EVar 49.
Definition e_v9 := EVar 50.
Definition e_sz := EVar 51.
Definition e_tr := EVar 52.
Definition P := EAlu ALU_ADD (EVar 2) (ELit 96).
Definition sr_ptl := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 0x7fa18)) 8 (EAlu ALU_ADD (EVar 2) (ELit 72))) 9 (ELit 1803592)) 18 (EAlu ALU_ADD e_sz (ELit 1))) 19 (EAlu ALU_ADD (EVar 2) (ELit 104))) 20 (e_sz)) 21 (ELit 0)) 23 (e_id)).
Definition kn_ptl : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWord (SA (EVar 2) 0) 8 e_F;
    KWord (SA (EVar 2) 56) 8 (ELit 0x81cc0);
    KWord (SA (EVar 2) 48) 8 e_node;
    KWord (SA (EVar 2) 40) 8 e_node;
    KWord (SA (EVar 2) 32) 8 e_bkt;
    KWord (SA (EVar 2) 24) 8 e_h;
    KWord (SA (EVar 2) 16) 8 e_m4;
    KWord (SA (EVar 2) 8) 8 e_hd;
    KWord (SA (EVar 2) 88) 8 (ELit 0x821a4);
    KWord (SA (EVar 2) 80) 8 (ELit 0);
    KWord (SA (EVar 2) 72) 8 (ELit 0);
    KWr (SA (EVar 2) 72) (ELit 8);
    KWord (SA (EVar 2) 200) 8 e_rp;
    KWord (SA (EVar 2) 192) 8 e_v0;
    KWord (SA (EVar 2) 184) 8 e_v1;
    KWord (SA (EVar 2) 176) 8 e_v2;
    KWord (SA (EVar 2) 168) 8 e_v3;
    KWord (SA (EVar 2) 160) 8 e_v4;
    KWord (SA (EVar 2) 152) 8 e_v5;
    KWord (SA (EVar 2) 144) 8 e_v6;
    KWord (SA (EVar 2) 136) 8 e_v7;
    KWord (SA (EVar 2) 128) 8 e_v8;
    KWord (SA (EVar 2) 120) 8 e_v9;
    KRange (EMd M_MUL (ELit 16) (EAlu ALU_SRL (EAlu ALU_SRL e_F (ELit 16)) (ELit 4))) 0 0;
    KWord (SA (ELit 0) 1803616) 4 e_st;
    KWr (SA (ELit 0) 1803616) (ELit 4);
    KRange e_node 1 (2^48);
    KAlign e_node 16;
    KWr (SA e_node 8) (ELit 8);
    KRange e_bkt 1 (2^47);
    KAlign e_bkt 4;
    KWr (SA e_bkt 0) (ELit 4);
    KDisj (SA e_node 8) (ELit 8) (SA (EVar 2) 0) (ELit 208);
    KDisj (SA e_bkt 0) (ELit 4) (SA (EVar 2) 0) (ELit 208);
    KDisj (SA e_node 8) (ELit 8) (SA e_bkt 0) (ELit 4);
    KDisj (SA (ELit 0) 1803616) (ELit 4) (SA (EVar 2) 0) (ELit 208);
    KDisj (SA (ELit 0) 1803616) (ELit 4) (SA e_node 8) (ELit 8);
    KDisj (SA (ELit 0) 1803616) (ELit 4) (SA e_bkt 0) (ELit 4) ].
Definition scr_ptl : scripts := SCR [false] [] [].
Definition ss_ptl := SS 0x733d8 sr_ptl [] kn_ptl 53.
Definition RUN_ptl := sym_exec SEGS 120 true [0x821f0] scr_ptl ss_ptl [].

Definition scr_pptl : scripts := SCR [false] [] [].
Definition RES_pptl := Eval vm_compute in sym_exec SEGS 120 true [0x821f0] scr_pptl ss_ptl [].
Lemma RES_pptl_ok : sym_exec SEGS 120 true [0x821f0] scr_pptl (SS 0x733d8 sr_ptl [] kn_ptl 53) [] = RES_pptl.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_ptl.


Module AXF_ptlz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AxAsan.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Section PTL.
Context {fx : FPState}.

Definition VALS_ptl (F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr : Z) : list Z := [F; st; node; bkt; h; hd; id; m4; rp; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; sz; tr].

Record ptl_pre (regs : bvmap 5 word) (m : word -> option byte) (F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr : Z) : Prop := {
  ptl_R1 : getr regs 1 = wa 522776 ;
  ptl_R8 : getr regs 8 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 72) ;
  ptl_R9 : getr regs 9 = wa 1803592 ;
  ptl_R18 : getr regs 18 = wa (sz + 1) ;
  ptl_R19 : getr regs 19 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 104) ;
  ptl_R20 : getr regs 20 = wa sz ;
  ptl_R21 : getr regs 21 = wa 0 ;
  ptl_R23 : getr regs 23 = wa id ;
  ptl_rng_F : 0 <= F <= 1048000 ;
  ptl_rng_st : 0 <= st <= 1048000 ;
  ptl_rng_node : 1 <= node <= 2^48 ;
  ptl_rng_bkt : 1 <= bkt <= 2^47 ;
  ptl_rng_h : 0 <= h <= 2^64-1 ;
  ptl_rng_hd : 0 <= hd <= 2^31-1 ;
  ptl_rng_id : 1 <= id <= 65534 ;
  ptl_rng_m4 : 0 <= m4 <= 2^64-1 ;
  ptl_rng_rp : 0 <= rp <= 2^64-1 ;
  ptl_rng_v0 : 0 <= v0 <= 2^64-1 ;
  ptl_rng_v1 : 0 <= v1 <= 2^64-1 ;
  ptl_rng_v2 : 0 <= v2 <= 2^64-1 ;
  ptl_rng_v3 : 0 <= v3 <= 2^64-1 ;
  ptl_rng_v4 : 0 <= v4 <= 2^64-1 ;
  ptl_rng_v5 : 0 <= v5 <= 2^64-1 ;
  ptl_rng_v6 : 0 <= v6 <= 2^64-1 ;
  ptl_rng_v7 : 0 <= v7 <= 2^64-1 ;
  ptl_rng_v8 : 0 <= v8 <= 2^64-1 ;
  ptl_rng_v9 : 0 <= v9 <= 2^64-1 ;
  ptl_rng_sz : 1 <= sz <= 255 ;
  ptl_rng_tr : 1 <= tr <= 2^47 ;
  ptl_kr0 : (2^20) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  ptl_ka1 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) mod 16 = 0 ;
  ptl_kw2 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0)) 8 = Some (word_to_le_bytes 8 (wa F)) ;
  ptl_kw3 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 56)) 8 = Some (word_to_le_bytes 8 (wa 531648)) ;
  ptl_kw4 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48)) 8 = Some (word_to_le_bytes 8 (wa node)) ;
  ptl_kw5 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 40)) 8 = Some (word_to_le_bytes 8 (wa node)) ;
  ptl_kw6 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32)) 8 = Some (word_to_le_bytes 8 (wa bkt)) ;
  ptl_kw7 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa h)) ;
  ptl_kw8 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 16)) 8 = Some (word_to_le_bytes 8 (wa m4)) ;
  ptl_kw9 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) 8 = Some (word_to_le_bytes 8 (wa hd)) ;
  ptl_kw10 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 88)) 8 = Some (word_to_le_bytes 8 (wa 532900)) ;
  ptl_kw11 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 80)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ptl_kw12 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 72)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  ptl_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 72 + d)) k = true ;
  ptl_kw14 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 200)) 8 = Some (word_to_le_bytes 8 (wa rp)) ;
  ptl_kw15 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 192)) 8 = Some (word_to_le_bytes 8 (wa v0)) ;
  ptl_kw16 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 184)) 8 = Some (word_to_le_bytes 8 (wa v1)) ;
  ptl_kw17 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 176)) 8 = Some (word_to_le_bytes 8 (wa v2)) ;
  ptl_kw18 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 168)) 8 = Some (word_to_le_bytes 8 (wa v3)) ;
  ptl_kw19 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 160)) 8 = Some (word_to_le_bytes 8 (wa v4)) ;
  ptl_kw20 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 152)) 8 = Some (word_to_le_bytes 8 (wa v5)) ;
  ptl_kw21 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 144)) 8 = Some (word_to_le_bytes 8 (wa v6)) ;
  ptl_kw22 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 136)) 8 = Some (word_to_le_bytes 8 (wa v7)) ;
  ptl_kw23 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 128)) 8 = Some (word_to_le_bytes 8 (wa v8)) ;
  ptl_kw24 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 120)) 8 = Some (word_to_le_bytes 8 (wa v9)) ;
  ptl_kr25 : 0 <= 16 * Z.shiftr ((Z.shiftr F 16) mod 2^64) 4 <= 0 ;
  ptl_kw26 : rdn SEGS m (wa (0 + 1803616)) 4 = Some (word_to_le_bytes 4 (wa st)) ;
  ptl_kwr27 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (0 + 1803616 + d)) k = true ;
  ptl_ka29 : node mod 16 = 0 ;
  ptl_kwr30 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (node + 8 + d)) k = true ;
  ptl_ka32 : bkt mod 4 = 0 ;
  ptl_kwr33 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (bkt + 0 + d)) k = true ;
  ptl_kd34 : node + 8 + 8 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0 \/ bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0 + 208 <= node + 8 ;
  ptl_kd35 : bkt + 0 + 4 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0 \/ bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0 + 208 <= bkt + 0 ;
  ptl_kd36 : node + 8 + 8 <= bkt + 0 \/ bkt + 0 + 4 <= node + 8 ;
  ptl_kd37 : 0 + 1803616 + 4 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0 \/ bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0 + 208 <= 0 + 1803616 ;
  ptl_kd38 : 0 + 1803616 + 4 <= node + 8 \/ node + 8 + 8 <= 0 + 1803616 ;
  ptl_kd39 : 0 + 1803616 + 4 <= bkt + 0 \/ bkt + 0 + 4 <= 0 + 1803616
}.


#[using="Type"] Lemma ptl_setup : forall regs m F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr, ptl_pre regs m F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr ->
  regs_ok (Ez regs (VALS_ptl F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr)) AXF_ptl.sr_ptl regs /\ know_ok SEGS (Ez regs (VALS_ptl F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr)) m AXF_ptl.kn_ptl.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr P. destruct P as [ptl_R1 ptl_R8 ptl_R9 ptl_R18 ptl_R19 ptl_R20 ptl_R21 ptl_R23 ptl_rng_F ptl_rng_st ptl_rng_node ptl_rng_bkt ptl_rng_h ptl_rng_hd ptl_rng_id ptl_rng_m4 ptl_rng_rp ptl_rng_v0 ptl_rng_v1 ptl_rng_v2 ptl_rng_v3 ptl_rng_v4 ptl_rng_v5 ptl_rng_v6 ptl_rng_v7 ptl_rng_v8 ptl_rng_v9 ptl_rng_sz ptl_rng_tr ptl_kr0 ptl_ka1 ptl_kw2 ptl_kw3 ptl_kw4 ptl_kw5 ptl_kw6 ptl_kw7 ptl_kw8 ptl_kw9 ptl_kw10 ptl_kw11 ptl_kw12 ptl_kwr13 ptl_kw14 ptl_kw15 ptl_kw16 ptl_kw17 ptl_kw18 ptl_kw19 ptl_kw20 ptl_kw21 ptl_kw22 ptl_kw23 ptl_kw24 ptl_kr25 ptl_kw26 ptl_kwr27 ptl_ka29 ptl_kwr30 ptl_ka32 ptl_kwr33 ptl_kd34 ptl_kd35 ptl_kd36 ptl_kd37 ptl_kd38 ptl_kd39].
  set (E := Ez regs (VALS_ptl F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr)).
  assert (Z32 : bv_unsigned (ev E 32) = F) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = node) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = bkt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = h) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = hd) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = id) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = m4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = rp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = v0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = v1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = v2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = v3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = v4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z46 : bv_unsigned (ev E 46) = v5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z47 : bv_unsigned (ev E 47) = v6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z48 : bv_unsigned (ev E 48) = v7) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z49 : bv_unsigned (ev E 49) = v8) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z50 : bv_unsigned (ev E 50) = v9) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z51 : bv_unsigned (ev E 51) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z52 : bv_unsigned (ev E 52) = tr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  split.
  { unfold AXF_ptl.sr_ptl.
    apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|]|]|]|]|]|].
    - rewrite ptl_R1. reflexivity.
    - rewrite ptl_R8, zeval_sound. cbn [zeval edenot AXF_ptl.e_F AXF_ptl.e_st AXF_ptl.e_node AXF_ptl.e_bkt AXF_ptl.e_h AXF_ptl.e_hd AXF_ptl.e_id AXF_ptl.e_m4 AXF_ptl.e_rp AXF_ptl.e_v0 AXF_ptl.e_v1 AXF_ptl.e_v2 AXF_ptl.e_v3 AXF_ptl.e_v4 AXF_ptl.e_v5 AXF_ptl.e_v6 AXF_ptl.e_v7 AXF_ptl.e_v8 AXF_ptl.e_v9 AXF_ptl.e_sz AXF_ptl.e_tr AXF_ptl.P]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z51, ?Z52, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ptl_R9. reflexivity.
    - rewrite ptl_R18, zeval_sound. cbn [zeval edenot AXF_ptl.e_F AXF_ptl.e_st AXF_ptl.e_node AXF_ptl.e_bkt AXF_ptl.e_h AXF_ptl.e_hd AXF_ptl.e_id AXF_ptl.e_m4 AXF_ptl.e_rp AXF_ptl.e_v0 AXF_ptl.e_v1 AXF_ptl.e_v2 AXF_ptl.e_v3 AXF_ptl.e_v4 AXF_ptl.e_v5 AXF_ptl.e_v6 AXF_ptl.e_v7 AXF_ptl.e_v8 AXF_ptl.e_v9 AXF_ptl.e_sz AXF_ptl.e_tr AXF_ptl.P]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z51, ?Z52, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ptl_R19, zeval_sound. cbn [zeval edenot AXF_ptl.e_F AXF_ptl.e_st AXF_ptl.e_node AXF_ptl.e_bkt AXF_ptl.e_h AXF_ptl.e_hd AXF_ptl.e_id AXF_ptl.e_m4 AXF_ptl.e_rp AXF_ptl.e_v0 AXF_ptl.e_v1 AXF_ptl.e_v2 AXF_ptl.e_v3 AXF_ptl.e_v4 AXF_ptl.e_v5 AXF_ptl.e_v6 AXF_ptl.e_v7 AXF_ptl.e_v8 AXF_ptl.e_v9 AXF_ptl.e_sz AXF_ptl.e_tr AXF_ptl.P]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z51, ?Z52, ?Z2. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite ptl_R20. reflexivity.
    - rewrite ptl_R21. reflexivity.
    - rewrite ptl_R23. reflexivity. }
  unfold know_ok, AXF_ptl.kn_ptl.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_ptl.e_F AXF_ptl.e_st AXF_ptl.e_node AXF_ptl.e_bkt AXF_ptl.e_h AXF_ptl.e_hd AXF_ptl.e_id AXF_ptl.e_m4 AXF_ptl.e_rp AXF_ptl.e_v0 AXF_ptl.e_v1 AXF_ptl.e_v2 AXF_ptl.e_v3 AXF_ptl.e_v4 AXF_ptl.e_v5 AXF_ptl.e_v6 AXF_ptl.e_v7 AXF_ptl.e_v8 AXF_ptl.e_v9 AXF_ptl.e_sz AXF_ptl.e_tr AXF_ptl.P a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z51, ?Z52, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range F _ _ ptl_rng_F eq_refl eq_refl), ?(mod64_of_range st _ _ ptl_rng_st eq_refl eq_refl), ?(mod64_of_range node _ _ ptl_rng_node eq_refl eq_refl), ?(mod64_of_range bkt _ _ ptl_rng_bkt eq_refl eq_refl), ?(mod64_of_range hd _ _ ptl_rng_hd eq_refl eq_refl), ?(mod64_of_range id _ _ ptl_rng_id eq_refl eq_refl), ?(mod64_of_range sz _ _ ptl_rng_sz eq_refl eq_refl), ?(mod64_of_range tr _ _ ptl_rng_tr eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply ptl_kwr13 | apply ptl_kwr27 | apply ptl_kwr30 | apply ptl_kwr33]; assumption).
  all: try (clear - ptl_rng_F ptl_rng_st ptl_rng_node ptl_rng_bkt ptl_rng_h ptl_rng_hd ptl_rng_id ptl_rng_m4 ptl_rng_rp ptl_rng_v0 ptl_rng_v1 ptl_rng_v2 ptl_rng_v3 ptl_rng_v4 ptl_rng_v5 ptl_rng_v6 ptl_rng_v7 ptl_rng_v8 ptl_rng_v9 ptl_rng_sz ptl_rng_tr ptl_kr0 ptl_ka1 ptl_kr25 ptl_ka29 ptl_ka32; lia).
  all: first [(clear - ptl_rng_F ptl_rng_st ptl_rng_node ptl_rng_bkt ptl_rng_h ptl_rng_hd ptl_rng_id ptl_rng_m4 ptl_rng_rp ptl_rng_v0 ptl_rng_v1 ptl_rng_v2 ptl_rng_v3 ptl_rng_v4 ptl_rng_v5 ptl_rng_v6 ptl_rng_v7 ptl_rng_v8 ptl_rng_v9 ptl_rng_sz ptl_rng_tr ptl_kr0 ptl_ka1 ptl_kr25 ptl_ka29 ptl_ka32 ptl_kd34; lia) | (clear - ptl_rng_F ptl_rng_st ptl_rng_node ptl_rng_bkt ptl_rng_h ptl_rng_hd ptl_rng_id ptl_rng_m4 ptl_rng_rp ptl_rng_v0 ptl_rng_v1 ptl_rng_v2 ptl_rng_v3 ptl_rng_v4 ptl_rng_v5 ptl_rng_v6 ptl_rng_v7 ptl_rng_v8 ptl_rng_v9 ptl_rng_sz ptl_rng_tr ptl_kr0 ptl_ka1 ptl_kr25 ptl_ka29 ptl_ka32 ptl_kd35; lia) | (clear - ptl_rng_F ptl_rng_st ptl_rng_node ptl_rng_bkt ptl_rng_h ptl_rng_hd ptl_rng_id ptl_rng_m4 ptl_rng_rp ptl_rng_v0 ptl_rng_v1 ptl_rng_v2 ptl_rng_v3 ptl_rng_v4 ptl_rng_v5 ptl_rng_v6 ptl_rng_v7 ptl_rng_v8 ptl_rng_v9 ptl_rng_sz ptl_rng_tr ptl_kr0 ptl_ka1 ptl_kr25 ptl_ka29 ptl_ka32 ptl_kd36; lia) | (clear - ptl_rng_F ptl_rng_st ptl_rng_node ptl_rng_bkt ptl_rng_h ptl_rng_hd ptl_rng_id ptl_rng_m4 ptl_rng_rp ptl_rng_v0 ptl_rng_v1 ptl_rng_v2 ptl_rng_v3 ptl_rng_v4 ptl_rng_v5 ptl_rng_v6 ptl_rng_v7 ptl_rng_v8 ptl_rng_v9 ptl_rng_sz ptl_rng_tr ptl_kr0 ptl_ka1 ptl_kr25 ptl_ka29 ptl_ka32 ptl_kd37; lia) | (clear - ptl_rng_F ptl_rng_st ptl_rng_node ptl_rng_bkt ptl_rng_h ptl_rng_hd ptl_rng_id ptl_rng_m4 ptl_rng_rp ptl_rng_v0 ptl_rng_v1 ptl_rng_v2 ptl_rng_v3 ptl_rng_v4 ptl_rng_v5 ptl_rng_v6 ptl_rng_v7 ptl_rng_v8 ptl_rng_v9 ptl_rng_sz ptl_rng_tr ptl_kr0 ptl_ka1 ptl_kr25 ptl_ka29 ptl_ka32 ptl_kd38; lia) | (clear - ptl_rng_F ptl_rng_st ptl_rng_node ptl_rng_bkt ptl_rng_h ptl_rng_hd ptl_rng_id ptl_rng_m4 ptl_rng_rp ptl_rng_v0 ptl_rng_v1 ptl_rng_v2 ptl_rng_v3 ptl_rng_v4 ptl_rng_v5 ptl_rng_v6 ptl_rng_v7 ptl_rng_v8 ptl_rng_v9 ptl_rng_sz ptl_rng_tr ptl_kr0 ptl_ka1 ptl_kr25 ptl_ka29 ptl_ka32 ptl_kd39; lia) | lia].
Qed.


Definition ptl_mem_pptl (m : word -> option byte) (regs : bvmap 5 word) (F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 1803616)) (word_to_le_bytes 4 (wa (st + (sz + 1))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 72)) (word_to_le_bytes 8 (wa 0))) (wa (node + 12)) (word_to_le_bytes 4 (wa (F + 1)))) (wa (node + 8)) (word_to_le_bytes 4 (wa hd))) (wa (bkt + 0)) (word_to_le_bytes 4 (wa id)).

#[using="Type"] Theorem ptl_pptl : forall regs m rom F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr, ptl_pre regs m F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr ->
  scs_denot SEGS m (Ez regs (VALS_ptl F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr)) (snd (fst AXF_ptl.RES_pptl)) ->
  exists R, msteps SEGS (mkst regs (wa 0x733d8) m rom) (mkst R (wa 0x821f0) (ptl_mem_pptl m regs F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr) rom) /\
    getr R 1 = wa rp /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 208) /\ getr R 8 = wa v0 /\ getr R 9 = wa v1 /\ getr R 10 = wa id /\ getr R 12 = wa 0 /\ getr R 18 = wa v2 /\ getr R 19 = wa v3 /\ getr R 20 = wa v4 /\ getr R 21 = wa v5 /\ getr R 22 = wa v6 /\ getr R 23 = wa v7 /\ getr R 24 = wa v8 /\ getr R 25 = wa v9 /\ (forall k, In k [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr P Hsc. destruct (ptl_setup regs m F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr P) as [HR HK].
  set (E := Ez regs (VALS_ptl F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr)) in *. destruct P as [ptl_R1 ptl_R8 ptl_R9 ptl_R18 ptl_R19 ptl_R20 ptl_R21 ptl_R23 ptl_rng_F ptl_rng_st ptl_rng_node ptl_rng_bkt ptl_rng_h ptl_rng_hd ptl_rng_id ptl_rng_m4 ptl_rng_rp ptl_rng_v0 ptl_rng_v1 ptl_rng_v2 ptl_rng_v3 ptl_rng_v4 ptl_rng_v5 ptl_rng_v6 ptl_rng_v7 ptl_rng_v8 ptl_rng_v9 ptl_rng_sz ptl_rng_tr ptl_kr0 ptl_ka1 ptl_kw2 ptl_kw3 ptl_kw4 ptl_kw5 ptl_kw6 ptl_kw7 ptl_kw8 ptl_kw9 ptl_kw10 ptl_kw11 ptl_kw12 ptl_kwr13 ptl_kw14 ptl_kw15 ptl_kw16 ptl_kw17 ptl_kw18 ptl_kw19 ptl_kw20 ptl_kw21 ptl_kw22 ptl_kw23 ptl_kw24 ptl_kr25 ptl_kw26 ptl_kwr27 ptl_ka29 ptl_kwr30 ptl_ka32 ptl_kwr33 ptl_kd34 ptl_kd35 ptl_kd36 ptl_kd37 ptl_kd38 ptl_kd39].
  assert (Z32 : bv_unsigned (ev E 32) = F) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = st) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = node) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = bkt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = h) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = hd) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = id) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = m4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = rp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = v0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = v1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = v2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = v3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = v4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z46 : bv_unsigned (ev E 46) = v5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z47 : bv_unsigned (ev E 47) = v6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z48 : bv_unsigned (ev E 48) = v7) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z49 : bv_unsigned (ev E 49) = v8) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z50 : bv_unsigned (ev E 50) = v9) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z51 : bv_unsigned (ev E 51) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z52 : bv_unsigned (ev E 52) = tr) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  destruct (run_sound SEGS 120 [0x821f0] AXF_ptl.scr_pptl 0x733d8 AXF_ptl.sr_ptl AXF_ptl.kn_ptl 53 _ _ _ E m rom regs AXF_ptl.RES_pptl_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ptl.RES_pptl fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ptl_mem_pptl m regs F st node bkt h hd id m4 rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 sz tr) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ptl_mem_pptl. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite (aluw_add_small E (EVar 33) (EAlu ALU_ADD (EVar 51) (ELit 1)) st (sz + 1)) by first [lia | exact Z33 | (apply add_lit_u; first [lia | exact Z51])]; reflexivity).
    all: try (rewrite (pack_zero E (EVar 51) (EVar 33) sz st) by first [lia | exact Z51 | exact Z33]; reflexivity).
    all: try (rewrite (aluw_add_small E (EVar 32) (ELit 1) F 1) by first [lia | exact Z32 | reflexivity]; reflexivity).
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

End PTL.
(* [comment removed for export] *)
End AXF_ptlz.


Module AXF_pe.
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

Definition e_rp := EVar 40.
Definition e_v0 := EVar 41.
Definition e_v1 := EVar 42.
Definition e_v2 := EVar 43.
Definition e_v3 := EVar 44.
Definition e_v4 := EVar 45.
Definition e_v5 := EVar 46.
Definition e_v6 := EVar 47.
Definition e_v7 := EVar 48.
Definition e_v8 := EVar 49.
Definition e_v9 := EVar 50.
Definition sr_pe := sr_id.
Definition kn_pe : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWord (SA (EVar 2) 104) 8 e_rp;
    KWord (SA (EVar 2) 96) 8 e_v0;
    KWord (SA (EVar 2) 88) 8 e_v1;
    KWord (SA (EVar 2) 80) 8 e_v2;
    KWord (SA (EVar 2) 72) 8 e_v3;
    KWord (SA (EVar 2) 64) 8 e_v4;
    KWord (SA (EVar 2) 56) 8 e_v5;
    KWord (SA (EVar 2) 48) 8 e_v6;
    KWord (SA (EVar 2) 40) 8 e_v7;
    KWord (SA (EVar 2) 32) 8 e_v8;
    KWord (SA (EVar 2) 24) 8 e_v9 ].
Definition scr_pe : scripts := SCR [] [] [].
Definition ss_pe := SS 0x821c0 sr_pe [] kn_pe 51.
Definition RUN_pe := sym_exec SEGS 20 true [0x821f0] scr_pe ss_pe [].

Definition scr_ppe : scripts := SCR [] [] [].
Definition RES_ppe := Eval vm_compute in sym_exec SEGS 20 true [0x821f0] scr_ppe ss_pe [].
Lemma RES_ppe_ok : sym_exec SEGS 20 true [0x821f0] scr_ppe (SS 0x821c0 sr_pe [] kn_pe 51) [] = RES_ppe.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
End AXF_pe.


Module AXF_pez.
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

Section PE.
Context {fx : FPState}.

Definition VALS_pe (rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : Z) : list Z := [0; 0; 0; 0; 0; 0; 0; 0; rp; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9].

Record pe_pre (regs : bvmap 5 word) (m : word -> option byte) (rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : Z) : Prop := {
  pe_rng_rp : 0 <= rp <= 2^64-1 ;
  pe_rng_v0 : 0 <= v0 <= 2^64-1 ;
  pe_rng_v1 : 0 <= v1 <= 2^64-1 ;
  pe_rng_v2 : 0 <= v2 <= 2^64-1 ;
  pe_rng_v3 : 0 <= v3 <= 2^64-1 ;
  pe_rng_v4 : 0 <= v4 <= 2^64-1 ;
  pe_rng_v5 : 0 <= v5 <= 2^64-1 ;
  pe_rng_v6 : 0 <= v6 <= 2^64-1 ;
  pe_rng_v7 : 0 <= v7 <= 2^64-1 ;
  pe_rng_v8 : 0 <= v8 <= 2^64-1 ;
  pe_rng_v9 : 0 <= v9 <= 2^64-1 ;
  pe_kr0 : (2^20) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  pe_ka1 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) mod 16 = 0 ;
  pe_kw2 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 104)) 8 = Some (word_to_le_bytes 8 (wa rp)) ;
  pe_kw3 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 96)) 8 = Some (word_to_le_bytes 8 (wa v0)) ;
  pe_kw4 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 88)) 8 = Some (word_to_le_bytes 8 (wa v1)) ;
  pe_kw5 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 80)) 8 = Some (word_to_le_bytes 8 (wa v2)) ;
  pe_kw6 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 72)) 8 = Some (word_to_le_bytes 8 (wa v3)) ;
  pe_kw7 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 64)) 8 = Some (word_to_le_bytes 8 (wa v4)) ;
  pe_kw8 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 56)) 8 = Some (word_to_le_bytes 8 (wa v5)) ;
  pe_kw9 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48)) 8 = Some (word_to_le_bytes 8 (wa v6)) ;
  pe_kw10 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 40)) 8 = Some (word_to_le_bytes 8 (wa v7)) ;
  pe_kw11 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32)) 8 = Some (word_to_le_bytes 8 (wa v8)) ;
  pe_kw12 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa v9))
}.


#[using="Type"] Lemma pe_setup : forall regs m rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9, pe_pre regs m rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ->
  regs_ok (Ez regs (VALS_pe rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9)) AXF_pe.sr_pe regs /\ know_ok SEGS (Ez regs (VALS_pe rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9)) m AXF_pe.kn_pe.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 P. destruct P as [pe_rng_rp pe_rng_v0 pe_rng_v1 pe_rng_v2 pe_rng_v3 pe_rng_v4 pe_rng_v5 pe_rng_v6 pe_rng_v7 pe_rng_v8 pe_rng_v9 pe_kr0 pe_ka1 pe_kw2 pe_kw3 pe_kw4 pe_kw5 pe_kw6 pe_kw7 pe_kw8 pe_kw9 pe_kw10 pe_kw11 pe_kw12].
  set (E := Ez regs (VALS_pe rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9)).
  assert (Z40 : bv_unsigned (ev E 40) = rp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = v0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = v1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = v2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = v3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = v4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z46 : bv_unsigned (ev E 46) = v5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z47 : bv_unsigned (ev E 47) = v6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z48 : bv_unsigned (ev E 48) = v7) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z49 : bv_unsigned (ev E 49) = v8) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z50 : bv_unsigned (ev E 50) = v9) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  split.
  { unfold AXF_pe.sr_pe.
    apply regs_ok_id.
 }
  unfold know_ok, AXF_pe.kn_pe.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pe.e_rp AXF_pe.e_v0 AXF_pe.e_v1 AXF_pe.e_v2 AXF_pe.e_v3 AXF_pe.e_v4 AXF_pe.e_v5 AXF_pe.e_v6 AXF_pe.e_v7 AXF_pe.e_v8 AXF_pe.e_v9 a_base a_off].
  all: rewrite ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z48, ?Z49, ?Z50, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - pe_rng_rp pe_rng_v0 pe_rng_v1 pe_rng_v2 pe_rng_v3 pe_rng_v4 pe_rng_v5 pe_rng_v6 pe_rng_v7 pe_rng_v8 pe_rng_v9 pe_kr0 pe_ka1; lia).
  all: first [lia].
Qed.


Definition pe_mem_ppe (m : word -> option byte) (regs : bvmap 5 word) (rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem pe_ppe : forall regs m rom rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9, pe_pre regs m rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ->
  scs_denot SEGS m (Ez regs (VALS_pe rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9)) (snd (fst AXF_pe.RES_ppe)) ->
  exists R, msteps SEGS (mkst regs (wa 0x821c0) m rom) (mkst R (wa 0x821f0) (pe_mem_ppe m regs rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9) rom) /\
    getr R 1 = wa rp /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 112) /\ getr R 8 = wa v0 /\ getr R 9 = wa v1 /\ getr R 18 = wa v2 /\ getr R 19 = wa v3 /\ getr R 20 = wa v4 /\ getr R 21 = wa v5 /\ getr R 22 = wa v6 /\ getr R 23 = wa v7 /\ getr R 24 = wa v8 /\ getr R 25 = wa v9 /\ (forall k, In k [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 P Hsc. destruct (pe_setup regs m rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 P) as [HR HK].
  set (E := Ez regs (VALS_pe rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9)) in *. destruct P as [pe_rng_rp pe_rng_v0 pe_rng_v1 pe_rng_v2 pe_rng_v3 pe_rng_v4 pe_rng_v5 pe_rng_v6 pe_rng_v7 pe_rng_v8 pe_rng_v9 pe_kr0 pe_ka1 pe_kw2 pe_kw3 pe_kw4 pe_kw5 pe_kw6 pe_kw7 pe_kw8 pe_kw9 pe_kw10 pe_kw11 pe_kw12].
  assert (Z40 : bv_unsigned (ev E 40) = rp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = v0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = v1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = v2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = v3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = v4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z46 : bv_unsigned (ev E 46) = v5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z47 : bv_unsigned (ev E 47) = v6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z48 : bv_unsigned (ev E 48) = v7) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z49 : bv_unsigned (ev E 49) = v8) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z50 : bv_unsigned (ev E 50) = v9) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  destruct (run_sound SEGS 20 [0x821f0] AXF_pe.scr_ppe 0x821c0 AXF_pe.sr_pe AXF_pe.kn_pe 51 _ _ _ E m rom regs AXF_pe.RES_ppe_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pe.RES_ppe fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pe_mem_ppe m regs rp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pe_mem_ppe. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End PE.
(* [comment removed for export] *)
End AXF_pez.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Notation TAB := 1869144 (only parsing).      (* [comment removed for export] *)
Notation NUNIQ := 6063448 (only parsing).    (* [comment removed for export] *)
Notation MAP1 := 6063464 (only parsing).     (* [comment removed for export] *)
Notation SSF := 1803592 (only parsing).      (* [comment removed for export] *)
Notation SSD := 1803608 (only parsing).      (* [comment removed for export] *)
Notation SSS := 1803616 (only parsing).      (* [comment removed for export] *)

Definition rd (m : word -> option byte) (a : Z) (w : nat) (v : Z) : Prop :=
  rdn SEGS m (wa a) w = Some (word_to_le_bytes w (wa v)).

(* [comment removed for export] *)
Fixpoint chainz (m : word -> option byte) (D1 n : Z) (k : nat) (id : Z) : Prop :=
  match k with
  | O => id = 0
  | S k' => id = 0 \/ (1 <= id <= n /\ exists hv lk, 0 <= hv < 2^64 /\ 0 <= lk < id /\
                        rd m (D1 + 16 * id) 8 hv /\ rd m (D1 + 16 * id + 8) 4 lk /\ chainz m D1 n k' lk)
  end.

(* [comment removed for export] *)
Definition downed (D1 B1 x : Z) : Prop :=
  TAB <= x < TAB + 4194304 \/ NUNIQ <= x < NUNIQ + 4 \/ MAP1 <= x < MAP1 + 8 \/ D1 <= x < D1 + 1048576 \/
  SSF <= x < SSF + 28 \/ B1 <= x < B1 + 8388608.

Record INV_D (m : word -> option byte) (D1 B1 n F st : Z) : Prop := {
  d_n : rd m NUNIQ 4 n ;
  d_nr : 0 <= n <= 65533 ;
  d_map : rd m MAP1 8 D1 ;
  d_D1 : 1 <= D1 /\ D1 + 1048576 <= 2^47 /\ D1 mod 16 = 0 ;
  d_tab : forall b, 0 <= b < 1048576 -> exists hd, 0 <= hd < 2^31 /\ rd m (TAB + 4 * b) 4 hd /\ exists k, chainz m D1 n k hd ;
  d_F : rd m SSF 8 F ;
  d_st : rd m SSS 4 st ;
  d_Fr : 0 <= st <= F /\ F <= 1048000 ;
  d_B1 : rd m SSD 8 B1 ;
  d_B1r : 1 <= B1 /\ B1 + 8388608 <= 2^47 /\ B1 mod 8 = 0 ;
  d_wr : forall x, downed D1 B1 x -> wview SEGS m (wa x) <> None ;
  d_sep : 6537216 <= D1 /\ 6537216 <= B1 /\ (D1 + 1048576 <= B1 \/ B1 + 8388608 <= D1) ;  (* [comment removed for export] *)
  d_n0 : exists hv lk, 0 <= hv < 2^64 /\ 0 <= lk < 2^32 /\ rd m D1 8 hv /\ rd m (D1 + 8) 4 lk   (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Lemma rdn_frame : forall (m m' : word -> option byte) (a : Z) n, 0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall x, a <= x < a + Z.of_nat n -> m' (wa x) = m (wa x)) -> rdn SEGS m' (wa a) n = rdn SEGS m (wa a) n.
Proof.
  intros m m' a n Ha Hn H. revert a Ha Hn H. induction n as [|n IH]; intros a Ha Hn H; [reflexivity|].
  cbn [rdn]. rewrite Nat2Z.inj_succ in Hn.
  rewrite (H a) by lia. destruct n as [|n'].
  { cbn [rdn]. reflexivity. }
  assert (Ea : (wa a + 1)%bv = wa (a + 1)).
  { apply bv_eq. rewrite bv_add_unsigned. rewrite (u_wa_small a) by lia. rewrite (u_wa_small (a + 1)) by lia.
    change (bv_unsigned 1%bv) with 1. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small; lia. }
  rewrite Ea. rewrite (IH (a + 1)) by (first [lia | intros x Hx; apply H; lia]). reflexivity.
Qed.

Lemma rd_frame : forall (m m' : word -> option byte) a w v, 0 <= a -> a + Z.of_nat w <= 2^64 ->
  (forall x, a <= x < a + Z.of_nat w -> m' (wa x) = m (wa x)) -> rd m a w v -> rd m' a w v.
Proof. intros m m' a w v H1 H2 H3 H. unfold rd in *. rewrite (rdn_frame m m') by assumption. exact H. Qed.

Lemma chainz_frame : forall m m' D1 n k id, 0 <= D1 -> D1 + 1048576 <= 2^47 -> n <= 65534 ->
  (forall x, D1 + 16 <= x < D1 + 16 * (n + 1) -> m' (wa x) = m (wa x)) ->
  chainz m D1 n k id -> chainz m' D1 n k id.
Proof.
  intros m m' D1 n k. induction k as [|k IH]; intros id H0 H1 Hn HF H; cbn [chainz] in *; [exact H|].
  destruct H as [H|(Hi & hv & lk & Hv & Hl & R1 & R2 & Hc)]; [left; exact H|]. right. split; [exact Hi|].
  exists hv, lk. split; [exact Hv|]. split; [exact Hl|].
  split; [apply (rd_frame m m'); first [lia | (intros x Hx; apply HF; cbn in Hx; lia) | exact R1]|].
  split; [apply (rd_frame m m'); first [lia | (intros x Hx; apply HF; cbn in Hx; lia) | exact R2]|].
  exact (IH lk H0 H1 Hn HF Hc).
Qed.

Lemma chainz_mono_n : forall m D1 n n' k id, n <= n' -> chainz m D1 n k id -> chainz m D1 n' k id.
Proof.
  intros m D1 n n' k. induction k as [|k IH]; intros id Hn H; cbn [chainz] in *; [exact H|].
  destruct H as [H|(Hi & hv & lk & Hv & Hl & R1 & R2 & Hc)]; [left; exact H|]. right. split; [lia|].
  exists hv, lk. split; [exact Hv|]. split; [exact Hl|]. split; [exact R1|]. split; [exact R2|]. exact (IH lk Hn Hc).
Qed.

(* [comment removed for export] *)
Section HASH.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (TR SZ : Z) (R0 : bvmap 5 word).
Hypothesis HTR : 1 <= TR /\ TR + 8 * SZ <= 2^47.
Hypothesis HSZ : 1 <= SZ <= 256.
Hypothesis HWORDS : forall i, 0 <= i < SZ -> exists w, 0 <= w < 2^64 /\ rd m (TR + 8 * i) 8 w.
Hypothesis HEND : getr R0 (Z_to_bv 5 (Z.of_nat 14)) = wa (TR + 8 * SZ).

Definition KH : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

Definition LH (i : Z) (R : bvmap 5 word) : Prop :=
  getr R 11 = wa (TR + 8 * i) /\
  (forall k, In k KH -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr R0 (Z_to_bv 5 (Z.of_nat k))).

Ltac memb := first [ AxSymRun3.memb_refl | repeat first [left; reflexivity | right] ].      (* [comment removed for export] *)

#[using="HTR HSZ HWORDS HEND"] Theorem hash_loop : forall (j : nat) i R, SZ - i = Z.of_nat j -> 0 <= i < SZ -> LH i R ->
  exists R', msteps SEGS (mkst R (wa 0x8202c) m rom) (mkst R' (wa 0x82050) m rom) /\ LH SZ R'.
Proof. LiaFast.lf_pins (fun (HTR HSZ HWORDS HEND : LiaFast.U) => LiaFast.u0).
  induction j as [|j IH]; intros i R Hj Hi (L11 & LK); [lia|].
  destruct (HWORDS i Hi) as (wk & Hwk & Rwk).
  assert (P : AXF_phz.ph_pre R m wk).
  { constructor; [lia | replace (Z_to_bv 5 (Z.of_nat 11)) with (@BV 5 11 I) by (apply bv_eq; reflexivity); rewrite L11, u_wa_small by lia; lia |].
    replace (Z_to_bv 5 (Z.of_nat 11)) with (@BV 5 11 I) by (apply bv_eq; reflexivity). rewrite L11, u_wa_small by lia. rewrite Z.add_0_r. exact Rwk. }
  assert (E14 : getr R (Z_to_bv 5 (Z.of_nat 14)) = wa (TR + 8 * SZ)) by (rewrite (LK 14%nat) by memb; exact HEND).
  destruct (Z.eq_dec (i + 1) SZ) as [Hlast|Hmore].
  - destruct (AXF_phz.ph_phx R m rom wk P) as (R1 & Hms & A11 & _ & K1).
    { cbn [AXF_ph.RES_phx fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      apply sc_br_z. rewrite br_ne_z. cbn [zeval edenot].
      rewrite (zreg R _ 11 eq_refl), (zreg R _ 14 eq_refl). replace (Z_to_bv 5 (Z.of_nat 11)) with (@BV 5 11 I) by (apply bv_eq; reflexivity). rewrite L11, E14, !u_wa_small by lia.
      apply negb_false_iff. apply Z.eqb_eq. rewrite !Z.mod_small by lia. lia. }
    exists R1. split; [exact Hms|]. split.
    + rewrite A11. replace (Z_to_bv 5 (Z.of_nat 11)) with (@BV 5 11 I) by (apply bv_eq; reflexivity). rewrite L11, u_wa_small by lia. f_equal. lia.
    + intros k Hk. rewrite (K1 k Hk). exact (LK k Hk).
  - destruct (AXF_phz.ph_phc R m rom wk P) as (R1 & Hms & A11 & _ & K1).
    { cbn [AXF_ph.RES_phc fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      apply sc_br_z. rewrite br_ne_z. cbn [zeval edenot].
      rewrite (zreg R _ 11 eq_refl), (zreg R _ 14 eq_refl). replace (Z_to_bv 5 (Z.of_nat 11)) with (@BV 5 11 I) by (apply bv_eq; reflexivity). rewrite L11, E14, !u_wa_small by lia.
      apply negb_true_iff. apply Z.eqb_neq. rewrite !Z.mod_small by lia. lia. }
    assert (LH1 : LH (i + 1) R1).
    { split; [rewrite A11; replace (Z_to_bv 5 (Z.of_nat 11)) with (@BV 5 11 I) by (apply bv_eq; reflexivity); rewrite L11, u_wa_small by lia; f_equal; lia|]. intros k Hk. rewrite (K1 k Hk). exact (LK k Hk). }
    destruct (IH (i + 1) R1 ltac:(lia) ltac:(lia) LH1) as (R' & Hms' & HL').
    exists R'. split; [exact (msteps_trans SEGS _ _ _ Hms Hms') | exact HL'].
Qed.
End HASH.

(* [comment removed for export] *)
Lemma rd_exists : forall m a w bs, (w <= 8)%nat -> rdn SEGS m (wa a) w = Some bs -> exists v, 0 <= v < 2^(8 * Z.of_nat w) /\ v < 2^64 /\ rd m a w v.
Proof.
  intros m a w bs Hw H. pose proof (rdn_length _ _ _ _ _ H) as Hl.
  exists (lez bs). pose proof (lez_bound_len bs w Hl) as B.
  assert (B64 : lez bs < 2^64) by (apply (Z.lt_le_trans _ (2 ^ (8 * Z.of_nat w))); [lia | apply Z.pow_le_mono_r; lia]).
  split; [lia|]. split; [lia|]. unfold rd. rewrite H. f_equal. unfold word_to_le_bytes. rewrite u_wa_small by lia. rewrite <- Hl. symmetry. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
Section FIND.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (D1 n h : Z) (R0 : bvmap 5 word).
Hypothesis HD1 : 1 <= D1 /\ D1 + 1048576 <= 2^47 /\ D1 mod 16 = 0.
Hypothesis Hn : 0 <= n <= 65533.
Hypothesis HMAP : rd m MAP1 8 D1.
Hypothesis HN0 : exists hv lk, 0 <= hv < 2^64 /\ 0 <= lk < 2^32 /\ rd m D1 8 hv /\ rd m (D1 + 8) 4 lk.
Hypothesis Hh : 0 <= h < 2^64.

Definition KF : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

Definition LF (id : Z) (R : bvmap 5 word) : Prop :=
  getr R 11 = wa id /\ getr R 22 = wa 65535 /\ getr R 23 = wa 2147483647 /\
  (forall k, In k KF -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr R0 (Z_to_bv 5 (Z.of_nat k))).
Hypothesis HR24 : getr R0 (Z_to_bv 5 (Z.of_nat 24)) = wa MAP1.
Hypothesis HR19 : getr R0 (Z_to_bv 5 (Z.of_nat 19)) = wa h.

Ltac memb := first [ AxSymRun3.memb_refl | repeat first [left; reflexivity | right] ].      (* [comment removed for export] *)

#[using="h HD1 HMAP Hh HR24"] Lemma pf_pre_of : forall id R hv lk, LF id R -> 0 <= id <= 65535 -> 0 <= hv < 2^64 -> 0 <= lk < 2^32 ->
  rd m (D1 + 16 * id) 8 hv -> rd m (D1 + 16 * id + 8) 4 lk -> AXF_pfz.pf_pre R m id D1 hv lk.
Proof. LiaFast.lf_pins (fun (h HD1 HMAP Hh HR24 : LiaFast.U) => LiaFast.u0).
  intros id R hv lk (L11 & L22 & L23 & LK) Hid Hv Hl R1 R2.
  assert (E24 : getr R (Z_to_bv 5 (Z.of_nat 24)) = wa MAP1) by (rewrite (LK 24%nat) by memb; exact HR24).
  idtac. constructor; try assumption; try lia; rewrite ?E24, ?u_wa_small by lia; try lia.
  - rewrite Z.add_0_r. exact HMAP.
  - rewrite Z.add_0_r, Z.add_comm. exact R1.
  - rewrite (Z.add_comm (16 * id) D1). exact R2.
Qed.

#[using="h HD1 Hn HMAP HN0 Hh HR24 HR19"] Theorem find_loop : forall (k : nat) id R, chainz m D1 n k id -> LF id R ->
  (exists R', msteps SEGS (mkst R (wa 0x820bc) m rom) (mkst R' (wa 0x82114) m rom) /\ LF 0 R') \/
  (exists R' id', 1 <= id' <= n /\ msteps SEGS (mkst R (wa 0x820bc) m rom) (mkst R' (wa 0x821c0) m rom) /\
     getr R' 10 = wa id' /\ (forall k, In k KF -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R0 (Z_to_bv 5 (Z.of_nat k)))).
Proof. LiaFast.lf_pins (fun (h HD1 Hn HMAP HN0 Hh HR24 HR19 : LiaFast.U) => LiaFast.u0).
  induction k as [|k IH]; intros id R Hc HL.
  - cbn [chainz] in Hc. subst id. left.
    destruct HN0 as (hv & lk & Hv & Hl & R1 & R2).
    assert (P : AXF_pfz.pf_pre R m 0 D1 hv lk) by (apply pf_pre_of; first [exact HL | lia | (rewrite Z.mul_0_r, Z.add_0_r; assumption)]).
    destruct (AXF_pfz.pf_pfz R m rom 0 D1 hv lk P) as (R1' & Hms & A11 & A22 & A23 & K1).
    { cbn [AXF_pf.RES_pfz fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      apply sc_br_z. rewrite br_eq_z. cbn [zeval edenot]. rewrite (zatom R (AXF_pfz.VALS_pf 0 D1 hv lk) 32 0 eq_refl eq_refl) by lia. reflexivity. }
    exists R1'. split; [exact Hms|]. destruct HL as (_ & _ & _ & LK).
    split; [exact A11|]. split; [exact A22|]. split; [exact A23|]. intros j Hj. rewrite (K1 j) by (clear - Hj; unfold KF in Hj; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in Hj |- *; tauto ]). exact (LK j Hj).
  - cbn [chainz] in Hc. destruct Hc as [->|(Hi & hv & lk & Hv & Hl & R1 & R2 & Hc)].
    + apply (IH 0 R); [destruct k; cbn; [reflexivity | left; reflexivity] | exact HL].
    + assert (P : AXF_pfz.pf_pre R m id D1 hv lk) by (apply pf_pre_of; first [exact HL | lia | assumption]).
      destruct (Z.eq_dec h hv) as [Ehv|Nhv].
      * right. destruct (AXF_pfz.pf_pff R m rom id D1 hv lk P) as (R1' & Hms & A10 & _ & _ & _ & _ & K1).
        { cbn [AXF_pf.RES_pff fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
          - apply sc_br_z. rewrite br_ne_z. cbn [zeval edenot]. rewrite (zatom R (AXF_pfz.VALS_pf id D1 hv lk) 34 hv eq_refl eq_refl) by lia.
            rewrite (zreg R _ 19 eq_refl). destruct HL as (_ & _ & _ & LK). rewrite (LK 19%nat) by memb. rewrite HR19, u_wa_small by lia. subst hv. rewrite Z.eqb_refl. reflexivity.
          - apply sc_br_z. rewrite br_eq_z. cbn [zeval edenot]. rewrite (zatom R (AXF_pfz.VALS_pf id D1 hv lk) 32 id eq_refl eq_refl) by lia.
            apply Z.eqb_neq. rewrite Z.mod_small by lia. change (0 mod 2^64) with 0. lia. }
        exists R1', id. split; [exact Hi|]. split; [exact Hms|]. split; [exact A10|].
        destruct HL as (_ & _ & _ & LK). intros j Hj. rewrite (K1 j) by (clear - Hj; unfold KF in Hj; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in Hj |- *; tauto ]). exact (LK j Hj).
      * destruct (AXF_pfz.pf_pfc R m rom id D1 hv lk P) as (R1' & Hms & A10 & A11 & A12 & A22 & A23 & K1).
        { cbn [AXF_pf.RES_pfc fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
          - apply sc_br_z. rewrite br_ne_z. cbn [zeval edenot]. rewrite (zatom R (AXF_pfz.VALS_pf id D1 hv lk) 34 hv eq_refl eq_refl) by lia.
            rewrite (zreg R _ 19 eq_refl). destruct HL as (_ & _ & _ & LK). rewrite (LK 19%nat) by memb. rewrite HR19, u_wa_small by lia.
            rewrite !Z.mod_small by lia. apply negb_true_iff. apply Z.eqb_neq. exact Nhv.
          - apply sc_br_z. rewrite br_eq_z. cbn [zeval edenot]. rewrite (zatom R (AXF_pfz.VALS_pf id D1 hv lk) 32 id eq_refl eq_refl) by lia.
            apply Z.eqb_neq. rewrite Z.mod_small by lia. change (0 mod 2^64) with 0. lia. }
        assert (HL1 : LF lk R1').
        { destruct HL as (_ & _ & _ & LK). split; [rewrite A11, ext_Z_lo32_small by lia; reflexivity|]. split; [exact A22|]. split; [exact A23|].
          intros j Hj. rewrite (K1 j) by (clear - Hj; unfold KF in Hj; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in Hj |- *; tauto ]). exact (LK j Hj). }
        destruct (IH lk R1' Hc HL1) as [(R' & Hms' & HL')|(R' & id' & Hi' & Hms' & A' & K')].
        -- left. exists R'. split; [exact (msteps_trans SEGS _ _ _ Hms Hms') | exact HL'].
        -- right. exists R', id'. split; [exact Hi'|]. split; [exact (msteps_trans SEGS _ _ _ Hms Hms')|]. split; [exact A'|]. exact K'.
Qed.
End FIND.

(* [comment removed for export] *)
Lemma rdn_byte : forall m (a : Z) n bs j, 0 <= a -> a + Z.of_nat n <= 2^64 -> rdn SEGS m (wa a) n = Some bs -> (j < n)%nat ->
  exists b, rdn SEGS m (wa (a + Z.of_nat j)) 1 = Some [b].
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a bs j Ha Hn H Hj; [lia|].
  cbn [rdn] in H. destruct (match m (wa a) with Some b => Some b | None => seg_rom SEGS (wa a) end) as [b|] eqn:Eb; [|discriminate].
  destruct j as [|j].
  - exists b. cbn [rdn]. rewrite Z.add_0_r, Eb. reflexivity.
  - destruct (rdn SEGS m (wa a + 1) n) as [rest|] eqn:Er; [|discriminate].
    assert (Ea : (wa a + 1)%bv = wa (a + 1)).
    { apply bv_eq. rewrite bv_add_unsigned. rewrite (u_wa_small a) by (rewrite Nat2Z.inj_succ in Hn; lia).
      rewrite (u_wa_small (a + 1)) by (rewrite Nat2Z.inj_succ in Hn; lia). change (bv_unsigned 1%bv) with 1.
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small; rewrite Nat2Z.inj_succ in Hn; lia. }
    rewrite Ea in Er. destruct (IH (a + 1) rest j ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in Hn; lia) Er ltac:(lia)) as (b' & Hb').
    exists b'. replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia. exact Hb'.
Qed.

Lemma rd_byte : forall m a w v j, 0 <= a -> a + Z.of_nat w <= 2^64 -> rd m a w v -> (j < w)%nat ->
  exists b, 0 <= b < 256 /\ rd m (a + Z.of_nat j) 1 b.
Proof.
  intros m a w v j Ha Hw H Hj. unfold rd in H. destruct (rdn_byte m a w _ j Ha Hw H Hj) as (b & Hb).
  destruct (rd_exists m (a + Z.of_nat j) 1 [b] ltac:(lia) Hb) as (v' & H1 & H2 & H3). exists v'. split; [exact H1 | exact H3].
Qed.

(* [comment removed for export] *)
Section MEMCPY.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (dst src n : Z) (R0 : bvmap 5 word).
Hypothesis Hd : 1 <= dst /\ dst + n <= 2^47.
Hypothesis Hs : 1 <= src /\ src + n <= 2^47.
Hypothesis Hn : 0 <= n <= 2^20.
Hypothesis Hdisj : src + n <= dst \/ dst + n <= src.

Definition KM : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

Definition LM (i : Z) (R : bvmap 5 word) : Prop :=
  getr R 11 = wa (src + i) /\ getr R 13 = wa (dst + i) /\ getr R 12 = wa (dst + n) /\
  (forall k, In k KM -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr R0 (Z_to_bv 5 (Z.of_nat k))).

Ltac memb := first [ AxSymRun3.memb_refl | repeat first [left; reflexivity | right] ].      (* [comment removed for export] *)

#[using="Hd Hs Hdisj"] Theorem memcpy_loop : forall (j : nat) i R m0 m, n - i = Z.of_nat j -> 0 <= i < n -> LM i R ->
  (forall k, 0 <= k < n -> exists b, 0 <= b < 256 /\ rd m (src + k) 1 b) ->
  (forall k, 0 <= k < n -> store_ok SEGS m (wa (dst + k)) 1 = true) ->
  (forall x, 0 <= x < 2^64 -> ~ (dst <= x < dst + i) -> m (wa x) = m0 (wa x)) -> mem_grows m0 m ->
  exists R' m', msteps SEGS (mkst R (wa 0x733c4) m rom) (mkst R' (wa 0x733d8) m' rom) /\
    (forall k, In k KM -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R0 (Z_to_bv 5 (Z.of_nat k))) /\
    (forall x, 0 <= x < 2^64 -> ~ (dst <= x < dst + n) -> m' (wa x) = m0 (wa x)) /\ mem_grows m0 m'.
Proof. LiaFast.lf_pins (fun (Hd Hs Hdisj : LiaFast.U) => LiaFast.u0).
  induction j as [|j IH]; intros i R m0 m Hj Hi (L11 & L13 & L12 & LK) HSRC HDST HFR HGR; [lia|].
  destruct (HSRC i Hi) as (b & Hb & Rb).
  assert (E11 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 11))) = src + i).
  { replace (Z_to_bv 5 (Z.of_nat 11)) with (@BV 5 11 I) by (apply bv_eq; reflexivity). rewrite L11, u_wa_small by lia. reflexivity. }
  assert (E13 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 13))) = dst + i).
  { replace (Z_to_bv 5 (Z.of_nat 13)) with (@BV 5 13 I) by (apply bv_eq; reflexivity). rewrite L13, u_wa_small by lia. reflexivity. }
  assert (P : AXF_mcbz.mcb_pre R m b).
  { constructor; [lia | rewrite E11; lia | rewrite E13; lia | rewrite E11, Z.add_0_r; exact Rb |].
    intros d k Hd0 Hk0. rewrite E13. destruct k as [|[|k]]; [reflexivity | | lia].
    assert (d = 0) by lia. subst d. rewrite !Z.add_0_r. exact (HDST i Hi). }
  assert (E12 : getr R (Z_to_bv 5 (Z.of_nat 12)) = wa (dst + n)).
  { replace (Z_to_bv 5 (Z.of_nat 12)) with (@BV 5 12 I) by (apply bv_eq; reflexivity). exact L12. }
  set (m1 := AXF_mcbz.mcb_mem_pmcc m R b).
  assert (M1 : forall x, 0 <= x < 2^64 -> x <> dst + i -> m1 (wa x) = m (wa x)).
  { intros x Hx Hne. unfold m1, AXF_mcbz.mcb_mem_pmcc. rewrite E13, Z.add_0_r. apply AX2S.wbytes_out; rewrite length_N_to_le_bytes;
    rewrite !u_wa_small by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia. }
  assert (G1 : mem_grows m m1) by (unfold m1, AXF_mcbz.mcb_mem_pmcc; apply wbytes_grows).
  destruct (Z.eq_dec (i + 1) n) as [Hlast|Hmore].
  - destruct (AXF_mcbz.mcb_pmcx R m rom b P) as (R1 & Hms & A11 & A13 & _ & K1).
    { cbn [AXF_mcb.RES_pmcx fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      apply sc_br_z. rewrite br_ne_z. cbn [zeval edenot]. rewrite (zreg R _ 13 eq_refl), (zreg R _ 12 eq_refl), E13, E12, u_wa_small by lia.
      apply negb_false_iff. apply Z.eqb_eq. rewrite !Z.mod_small by lia. lia. }
    exists R1, m1. split; [exact Hms|]. split.
    + intros k Hk. rewrite (K1 k) by (clear - Hk; unfold KM in Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in Hk |- *; tauto ]). exact (LK k Hk).
    + split; [|intros x Hx; apply G1; apply HGR; exact Hx].
      intros x Hx Hnot. rewrite M1 by (first [exact Hx | lia]). apply HFR; [exact Hx | lia].
  - destruct (AXF_mcbz.mcb_pmcc R m rom b P) as (R1 & Hms & A11 & A13 & _ & K1).
    { cbn [AXF_mcb.RES_pmcc fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      apply sc_br_z. rewrite br_ne_z. cbn [zeval edenot]. rewrite (zreg R _ 13 eq_refl), (zreg R _ 12 eq_refl), E13, E12, u_wa_small by lia.
      apply negb_true_iff. apply Z.eqb_neq. rewrite !Z.mod_small by lia. lia. }
    assert (LM1 : LM (i + 1) R1).
    { split; [rewrite A11, E11; f_equal; lia|]. split; [rewrite A13, E13; f_equal; lia|].
      split; [replace (@BV 5 12 I) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity); rewrite (K1 12%nat) by memb; exact E12|].
      intros k Hk. rewrite (K1 k) by (clear - Hk; unfold KM in Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in Hk |- *; tauto ]). exact (LK k Hk). }
    destruct (IH (i + 1) R1 m0 m1 ltac:(lia) ltac:(lia) LM1) as (R' & m' & Hms' & K' & F' & G').
    + intros k Hk. destruct (HSRC k Hk) as (b' & Hb' & Rb'). exists b'. split; [exact Hb'|].
      apply (rd_frame m m1); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | | exact Rb']. intros x Hx. apply M1; [lia|]. cbn in Hx. lia.
    + intros k Hk. apply (store_ok_mono SEGS 1 m m1 _ G1). exact (HDST k Hk).
    + intros x Hx Hnot. destruct (Z.eq_dec x (dst + i)) as [->|Hne].
      * exfalso. apply Hnot. lia.
      * rewrite M1 by (first [exact Hx | exact Hne]). apply HFR; [exact Hx | lia].
    + intros x Hx. apply G1. apply HGR. exact Hx.
    + exists R', m'. split; [exact (msteps_trans SEGS _ _ _ Hms Hms')|]. split; [exact K'|]. split; [exact F' | exact G'].
Qed.
End MEMCPY.
(* [comment removed for export] *)
