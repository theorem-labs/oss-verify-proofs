(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ MngHeap AxTry.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_ag1.

Module AXF_bnco.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_seq := EVar 33.
Definition sr_bnco := (sr_upd (sr_upd sr_id 8 (e_sc)) 22 (ELit 614096)).
Definition kn_bnco : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_seq 0 255;
    KWord (SA (ELit 0) 615016) 1 e_seq ].
Definition scr_bnco : scripts := SCR [true] [] [].
Definition ss_bnco := SS 0x525bc sr_bnco [] kn_bnco 34.
Definition RUN_bnco := sym_exec SEGS 100 true [0x52870] scr_bnco ss_bnco [].

Definition scr_pbo : scripts := SCR [true] [] [].
Definition RES_pbo := Eval vm_compute in sym_exec SEGS 100 true [0x52870] scr_pbo ss_bnco [].
Lemma RES_pbo_ok : sym_exec SEGS 100 true [0x52870] scr_pbo (SS 0x525bc sr_bnco [] kn_bnco 34) [] = RES_pbo.
Proof. vm_compute. reflexivity. Qed.
End AXF_bnco.

Module AXF_bncoz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section BNCO.
Context {fx : FPState}.

Definition VALS_bnco (sc seq : Z) : list Z := [sc; seq].

Record bnco_pre (regs : bvmap 5 word) (m : word -> option byte) (sc seq : Z) : Prop := {
  bnco_R8 : getr regs 8 = wa sc ;
  bnco_R22 : getr regs 22 = wa 614096 ;
  bnco_rng_sc : 0 <= sc <= 47 ;
  bnco_rng_seq : 0 <= seq <= 255 ;
  bnco_kw2 : rdn SEGS m (wa (0 + 615016)) 1 = Some (word_to_le_bytes 1 (wa seq))
}.


#[using="Type"] Lemma bnco_setup : forall regs m sc seq, bnco_pre regs m sc seq ->
  regs_ok (Ez regs (VALS_bnco sc seq)) AXF_bnco.sr_bnco regs /\ know_ok SEGS (Ez regs (VALS_bnco sc seq)) m AXF_bnco.kn_bnco.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc seq P. destruct P as [bnco_R8 bnco_R22 bnco_rng_sc bnco_rng_seq bnco_kw2].
  set (E := Ez regs (VALS_bnco sc seq)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_bnco.sr_bnco.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|].
    - rewrite bnco_R8. reflexivity.
    - rewrite bnco_R22. reflexivity. }
  unfold know_ok, AXF_bnco.kn_bnco.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_bnco.e_sc AXF_bnco.e_seq a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ bnco_rng_sc eq_refl eq_refl), ?(mod64_of_range seq _ _ bnco_rng_seq eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - bnco_rng_sc bnco_rng_seq; lia).
  all: first [lia].
Qed.


Definition bnco_mem_pbo (m : word -> option byte) (regs : bvmap 5 word) (sc seq : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem bnco_pbo : forall regs m rom sc seq, bnco_pre regs m sc seq ->
  scs_denot SEGS m (Ez regs (VALS_bnco sc seq)) (snd (fst AXF_bnco.RES_pbo)) ->
  exists R, msteps SEGS (mkst regs (wa 0x525bc) m rom) (mkst R (wa 0x52870) (bnco_mem_pbo m regs sc seq) rom) /\
    getr R 8 = wa sc /\ getr R 13 = wa 0 /\ getr R 15 = wa (sc + -7) /\ getr R 16 = wa seq /\ getr R 22 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 10; 11; 12; 14; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc seq P Hsc. destruct (bnco_setup regs m sc seq P) as [HR HK].
  set (E := Ez regs (VALS_bnco sc seq)) in *. destruct P as [bnco_R8 bnco_R22 bnco_rng_sc bnco_rng_seq bnco_kw2].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52870] AXF_bnco.scr_pbo 0x525bc AXF_bnco.sr_bnco AXF_bnco.kn_bnco 34 _ _ _ E m rom regs AXF_bnco.RES_pbo_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_bnco.RES_pbo fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (bnco_mem_pbo m regs sc seq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold bnco_mem_pbo. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End BNCO.
End AXF_bncoz.


Module AXF_bnci.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_b := EVar 33.
Definition e_useq := EVar 34.
Definition e_seq := EVar 35.
Definition sr_bnci := (sr_upd (sr_upd sr_id 8 (e_sc)) 22 (ELit 614096)).
Definition kn_bnci : list kentry :=
  [ KRange e_sc 7 38;
    KRange e_b 0 255;
    KRange e_useq 0 255;
    KRange e_seq 0 255;
    KWord (SA (ELit 0) 615016) 1 e_seq;
    KWord (SA e_sc 614977) 1 e_b;
    KWord (SA e_sc 614945) 1 e_useq;
    KWr (SA e_sc 614977) (ELit 1) ].
Definition scr_bnci : scripts := SCR [true] [] [].
Definition ss_bnci := SS 0x525bc sr_bnci [] kn_bnci 36.
Definition RUN_bnci := sym_exec SEGS 100 true [0x52870] scr_bnci ss_bnci [].

Definition scr_pbz : scripts := SCR [true] [] [].
Definition RES_pbz := Eval vm_compute in sym_exec SEGS 100 true [0x52870] scr_pbz ss_bnci [].
Lemma RES_pbz_ok : sym_exec SEGS 100 true [0x52870] scr_pbz (SS 0x525bc sr_bnci [] kn_bnci 36) [] = RES_pbz.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pbf : scripts := SCR [false; true] [] [].
Definition RES_pbf := Eval vm_compute in sym_exec SEGS 100 true [0x52870] scr_pbf ss_bnci [].
Lemma RES_pbf_ok : sym_exec SEGS 100 true [0x52870] scr_pbf (SS 0x525bc sr_bnci [] kn_bnci 36) [] = RES_pbf.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pbi : scripts := SCR [false; false; true] [] [].
Definition RES_pbi := Eval vm_compute in sym_exec SEGS 100 true [0x52870] scr_pbi ss_bnci [].
Lemma RES_pbi_ok : sym_exec SEGS 100 true [0x52870] scr_pbi (SS 0x525bc sr_bnci [] kn_bnci 36) [] = RES_pbi.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pbs : scripts := SCR [false; false; false] [] [].
Definition RES_pbs := Eval vm_compute in sym_exec SEGS 100 true [0x52870] scr_pbs ss_bnci [].
Lemma RES_pbs_ok : sym_exec SEGS 100 true [0x52870] scr_pbs (SS 0x525bc sr_bnci [] kn_bnci 36) [] = RES_pbs.
Proof. vm_compute. reflexivity. Qed.
End AXF_bnci.

Module AXF_bnciz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ AxTry.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section BNCI.
Context {fx : FPState}.

Definition VALS_bnci (sc b useq seq : Z) : list Z := [sc; b; useq; seq].

Record bnci_pre (regs : bvmap 5 word) (m : word -> option byte) (sc b useq seq : Z) : Prop := {
  bnci_R8 : getr regs 8 = wa sc ;
  bnci_R22 : getr regs 22 = wa 614096 ;
  bnci_rng_sc : 7 <= sc <= 38 ;
  bnci_rng_b : 0 <= b <= 255 ;
  bnci_rng_useq : 0 <= useq <= 255 ;
  bnci_rng_seq : 0 <= seq <= 255 ;
  bnci_kw4 : rdn SEGS m (wa (0 + 615016)) 1 = Some (word_to_le_bytes 1 (wa seq)) ;
  bnci_kw5 : rdn SEGS m (wa (sc + 614977)) 1 = Some (word_to_le_bytes 1 (wa b)) ;
  bnci_kw6 : rdn SEGS m (wa (sc + 614945)) 1 = Some (word_to_le_bytes 1 (wa useq)) ;
  bnci_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (sc + 614977 + d)) k = true
}.


#[using="Type"] Lemma bnci_setup : forall regs m sc b useq seq, bnci_pre regs m sc b useq seq ->
  regs_ok (Ez regs (VALS_bnci sc b useq seq)) AXF_bnci.sr_bnci regs /\ know_ok SEGS (Ez regs (VALS_bnci sc b useq seq)) m AXF_bnci.kn_bnci.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc b useq seq P. destruct P as [bnci_R8 bnci_R22 bnci_rng_sc bnci_rng_b bnci_rng_useq bnci_rng_seq bnci_kw4 bnci_kw5 bnci_kw6 bnci_kwr7].
  set (E := Ez regs (VALS_bnci sc b useq seq)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = useq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_bnci.sr_bnci.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|].
    - rewrite bnci_R8. reflexivity.
    - rewrite bnci_R22. reflexivity. }
  unfold know_ok, AXF_bnci.kn_bnci.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_bnci.e_sc AXF_bnci.e_b AXF_bnci.e_useq AXF_bnci.e_seq a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ bnci_rng_sc eq_refl eq_refl), ?(mod64_of_range b _ _ bnci_rng_b eq_refl eq_refl), ?(mod64_of_range useq _ _ bnci_rng_useq eq_refl eq_refl), ?(mod64_of_range seq _ _ bnci_rng_seq eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply bnci_kwr7]; assumption).
  all: try (clear - bnci_rng_sc bnci_rng_b bnci_rng_useq bnci_rng_seq; lia).
  all: first [lia].
Qed.


Definition bnci_mem_pbz (m : word -> option byte) (regs : bvmap 5 word) (sc b useq seq : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem bnci_pbz : forall regs m rom sc b useq seq, bnci_pre regs m sc b useq seq ->
  scs_denot SEGS m (Ez regs (VALS_bnci sc b useq seq)) (snd (fst AXF_bnci.RES_pbz)) ->
  exists R, msteps SEGS (mkst regs (wa 0x525bc) m rom) (mkst R (wa 0x52870) (bnci_mem_pbz m regs sc b useq seq) rom) /\
    getr R 5 = wa useq /\ getr R 8 = wa sc /\ getr R 13 = wa (if b <? 100 then 0 else 1) /\ getr R 15 = wa (sc + 614089) /\ getr R 16 = wa seq /\ getr R 17 = wa b /\ getr R 22 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 6; 7; 9; 10; 11; 12; 14; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc b useq seq P Hsc. destruct (bnci_setup regs m sc b useq seq P) as [HR HK].
  set (E := Ez regs (VALS_bnci sc b useq seq)) in *. destruct P as [bnci_R8 bnci_R22 bnci_rng_sc bnci_rng_b bnci_rng_useq bnci_rng_seq bnci_kw4 bnci_kw5 bnci_kw6 bnci_kwr7].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = useq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52870] AXF_bnci.scr_pbz 0x525bc AXF_bnci.sr_bnci AXF_bnci.kn_bnci 36 _ _ _ E m rom regs AXF_bnci.RES_pbz_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_bnci.RES_pbz fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (bnci_mem_pbz m regs sc b useq seq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold bnci_mem_pbz. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition bnci_mem_pbf (m : word -> option byte) (regs : bvmap 5 word) (sc b useq seq : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem bnci_pbf : forall regs m rom sc b useq seq, bnci_pre regs m sc b useq seq ->
  scs_denot SEGS m (Ez regs (VALS_bnci sc b useq seq)) (snd (fst AXF_bnci.RES_pbf)) ->
  exists R, msteps SEGS (mkst regs (wa 0x525bc) m rom) (mkst R (wa 0x52870) (bnci_mem_pbf m regs sc b useq seq) rom) /\
    getr R 5 = wa ((-1 * useq) + seq) /\ getr R 6 = wa 9 /\ getr R 8 = wa sc /\ getr R 13 = wa (if b <? 100 then 0 else 1) /\ getr R 15 = wa (sc + 614089) /\ getr R 16 = wa seq /\ getr R 17 = wa b /\ getr R 22 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 7; 9; 10; 11; 12; 14; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc b useq seq P Hsc. destruct (bnci_setup regs m sc b useq seq P) as [HR HK].
  set (E := Ez regs (VALS_bnci sc b useq seq)) in *. destruct P as [bnci_R8 bnci_R22 bnci_rng_sc bnci_rng_b bnci_rng_useq bnci_rng_seq bnci_kw4 bnci_kw5 bnci_kw6 bnci_kwr7].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = useq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52870] AXF_bnci.scr_pbf 0x525bc AXF_bnci.sr_bnci AXF_bnci.kn_bnci 36 _ _ _ E m rom regs AXF_bnci.RES_pbf_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_bnci.RES_pbf fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (bnci_mem_pbf m regs sc b useq seq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold bnci_mem_pbf. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition bnci_mem_pbi (m : word -> option byte) (regs : bvmap 5 word) (sc b useq seq : Z) : word -> option byte :=
  wbytes (m) (wa (sc + 614977)) (word_to_le_bytes 1 (wa (b + 1))).

#[using="Type"] Theorem bnci_pbi : forall regs m rom sc b useq seq, bnci_pre regs m sc b useq seq ->
  scs_denot SEGS m (Ez regs (VALS_bnci sc b useq seq)) (snd (fst AXF_bnci.RES_pbi)) ->
  exists R, msteps SEGS (mkst regs (wa 0x525bc) m rom) (mkst R (wa 0x52870) (bnci_mem_pbi m regs sc b useq seq) rom) /\
    getr R 5 = wa ((-1 * useq) + seq) /\ getr R 6 = wa 9 /\ getr R 8 = wa sc /\ getr R 13 = wa (if b <? 100 then 0 else 1) /\ getr R 15 = wa (sc + 614089) /\ getr R 16 = wa seq /\ getr R 17 = wa (b + 1) /\ getr R 22 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 7; 9; 10; 11; 12; 14; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc b useq seq P Hsc. destruct (bnci_setup regs m sc b useq seq P) as [HR HK].
  set (E := Ez regs (VALS_bnci sc b useq seq)) in *. destruct P as [bnci_R8 bnci_R22 bnci_rng_sc bnci_rng_b bnci_rng_useq bnci_rng_seq bnci_kw4 bnci_kw5 bnci_kw6 bnci_kwr7].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = useq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52870] AXF_bnci.scr_pbi 0x525bc AXF_bnci.sr_bnci AXF_bnci.kn_bnci 36 _ _ _ E m rom regs AXF_bnci.RES_pbi_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_bnci.RES_pbi fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (bnci_mem_pbi m regs sc b useq seq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold bnci_mem_pbi. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition bnci_mem_pbs (m : word -> option byte) (regs : bvmap 5 word) (sc b useq seq : Z) : word -> option byte :=
  wbytes (m) (wa (sc + 614977)) (word_to_le_bytes 1 (wa 150)).

#[using="Type"] Theorem bnci_pbs : forall regs m rom sc b useq seq, bnci_pre regs m sc b useq seq ->
  scs_denot SEGS m (Ez regs (VALS_bnci sc b useq seq)) (snd (fst AXF_bnci.RES_pbs)) ->
  exists R, msteps SEGS (mkst regs (wa 0x525bc) m rom) (mkst R (wa 0x52870) (bnci_mem_pbs m regs sc b useq seq) rom) /\
    getr R 5 = wa ((-1 * useq) + seq) /\ getr R 6 = wa 9 /\ getr R 8 = wa sc /\ getr R 13 = wa (if b <? 100 then 0 else 1) /\ getr R 15 = wa (sc + 614089) /\ getr R 16 = wa seq /\ getr R 17 = wa 150 /\ getr R 22 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 7; 9; 10; 11; 12; 14; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc b useq seq P Hsc. destruct (bnci_setup regs m sc b useq seq P) as [HR HK].
  set (E := Ez regs (VALS_bnci sc b useq seq)) in *. destruct P as [bnci_R8 bnci_R22 bnci_rng_sc bnci_rng_b bnci_rng_useq bnci_rng_seq bnci_kw4 bnci_kw5 bnci_kw6 bnci_kwr7].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = useq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52870] AXF_bnci.scr_pbs 0x525bc AXF_bnci.sr_bnci AXF_bnci.kn_bnci 36 _ _ _ E m rom regs AXF_bnci.RES_pbs_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_bnci.RES_pbs fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (bnci_mem_pbs m regs sc b useq seq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold bnci_mem_pbs. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; apply nosmall_z; [exact Z33 | assumption])]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End BNCI.
End AXF_bnciz.


Module AXF_sq.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_seq := EVar 32.
Definition sr_sq := (sr_upd (sr_upd sr_id 16 (e_seq)) 22 (ELit 614096)).
Definition kn_sq : list kentry :=
  [ KRange e_seq 0 255;
    KWr (SA (ELit 0) 614952) (ELit 32);
    KWr (SA (ELit 0) 615016) (ELit 1) ].
Definition scr_sq : scripts := SCR [true] [] [].
Definition ss_sq := SS 0x52870 sr_sq [] kn_sq 33.
Definition RUN_sq := sym_exec SEGS 100 true [0x5289c] scr_sq ss_sq [].

Definition scr_pinc : scripts := SCR [true] [] [].
Definition RES_pinc := Eval vm_compute in sym_exec SEGS 100 true [0x5289c] scr_pinc ss_sq [].
Lemma RES_pinc_ok : sym_exec SEGS 100 true [0x5289c] scr_pinc (SS 0x52870 sr_sq [] kn_sq 33) [] = RES_pinc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pres : scripts := SCR [false] [] [].
Definition RES_pres := Eval vm_compute in sym_exec SEGS 100 true [0x5289c] scr_pres ss_sq [].
Lemma RES_pres_ok : sym_exec SEGS 100 true [0x5289c] scr_pres (SS 0x52870 sr_sq [] kn_sq 33) [] = RES_pres.
Proof. vm_compute. reflexivity. Qed.
End AXF_sq.

Module AXF_sqz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section SQ.
Context {fx : FPState}.

Definition VALS_sq (seq : Z) : list Z := [seq].

Record sq_pre (regs : bvmap 5 word) (m : word -> option byte) (seq : Z) : Prop := {
  sq_R16 : getr regs 16 = wa seq ;
  sq_R22 : getr regs 22 = wa 614096 ;
  sq_rng_seq : 0 <= seq <= 255 ;
  sq_kwr1 : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (0 + 614952 + d)) k = true ;
  sq_kwr2 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (0 + 615016 + d)) k = true
}.


#[using="Type"] Lemma sq_setup : forall regs m seq, sq_pre regs m seq ->
  regs_ok (Ez regs (VALS_sq seq)) AXF_sq.sr_sq regs /\ know_ok SEGS (Ez regs (VALS_sq seq)) m AXF_sq.kn_sq.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m seq P. destruct P as [sq_R16 sq_R22 sq_rng_seq sq_kwr1 sq_kwr2].
  set (E := Ez regs (VALS_sq seq)).
  assert (Z32 : bv_unsigned (ev E 32) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_sq.sr_sq.
    apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 16); [apply regs_ok_id|]|].
    - rewrite sq_R16. reflexivity.
    - rewrite sq_R22. reflexivity. }
  unfold know_ok, AXF_sq.kn_sq.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_sq.e_seq a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range seq _ _ sq_rng_seq eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply sq_kwr1 | apply sq_kwr2]; assumption).
  all: try (clear - sq_rng_seq; lia).
  all: first [lia].
Qed.


Definition sq_mem_pinc (m : word -> option byte) (regs : bvmap 5 word) (seq : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 615016)) (word_to_le_bytes 1 (wa (seq + 1))).

#[using="Type"] Theorem sq_pinc : forall regs m rom seq, sq_pre regs m seq ->
  scs_denot SEGS m (Ez regs (VALS_sq seq)) (snd (fst AXF_sq.RES_pinc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52870) m rom) (mkst R (wa 0x5289c) (sq_mem_pinc m regs seq) rom) /\
    getr R 15 = wa 31 /\ getr R 16 = wa (seq + 1) /\ getr R 22 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom seq P Hsc. destruct (sq_setup regs m seq P) as [HR HK].
  set (E := Ez regs (VALS_sq seq)) in *. destruct P as [sq_R16 sq_R22 sq_rng_seq sq_kwr1 sq_kwr2].
  assert (Z32 : bv_unsigned (ev E 32) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5289c] AXF_sq.scr_pinc 0x52870 AXF_sq.sr_sq AXF_sq.kn_sq 33 _ _ _ E m rom regs AXF_sq.RES_pinc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_sq.RES_pinc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (sq_mem_pinc m regs seq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold sq_mem_pinc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition sq_mem_pres (m : word -> option byte) (regs : bvmap 5 word) (seq : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 614952)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614960)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614968)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614976)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1)).

#[using="Type"] Theorem sq_pres : forall regs m rom seq, sq_pre regs m seq ->
  scs_denot SEGS m (Ez regs (VALS_sq seq)) (snd (fst AXF_sq.RES_pres)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52870) m rom) (mkst R (wa 0x5289c) (sq_mem_pres m regs seq) rom) /\
    getr R 15 = wa 31 /\ getr R 16 = wa 1 /\ getr R 22 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom seq P Hsc. destruct (sq_setup regs m seq P) as [HR HK].
  set (E := Ez regs (VALS_sq seq)) in *. destruct P as [sq_R16 sq_R22 sq_rng_seq sq_kwr1 sq_kwr2].
  assert (Z32 : bv_unsigned (ev E 32) = seq) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5289c] AXF_sq.scr_pres 0x52870 AXF_sq.sr_sq AXF_sq.kn_sq 33 _ _ _ E m rom regs AXF_sq.RES_pres_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_sq.RES_pres fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (sq_mem_pres m regs seq) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold sq_mem_pres. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End SQ.
End AXF_sqz.


Module AXF_ua.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_u0 := EVar 33.
Definition e_u1 := EVar 34.
Definition sr_ua := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_sc)) 10 (e_u0)) 15 (ELit 31)) 23 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614096))).
Definition kn_ua : list kentry :=
  [ KRange e_sc 0 31;
    KRange e_u0 0 (2^60);
    KRange e_u1 0 (2^60);
    KWord (SA (EMd M_MUL (ELit 8) e_sc) 614576) 8 e_u1 ].
Definition scr_ua : scripts := SCR [true] [] [].
Definition ss_ua := SS 0x5289c sr_ua [] kn_ua 35.
Definition RUN_ua := sym_exec SEGS 100 true [0x528b0] scr_ua ss_ua [].

Definition scr_puao : scripts := SCR [true] [] [].
Definition RES_puao := Eval vm_compute in sym_exec SEGS 100 true [0x528b0] scr_puao ss_ua [].
Lemma RES_puao_ok : sym_exec SEGS 100 true [0x528b0] scr_puao (SS 0x5289c sr_ua [] kn_ua 35) [] = RES_puao.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puae : scripts := SCR [false] [] [].
Definition RES_puae := Eval vm_compute in sym_exec SEGS 100 true [0x528b0] scr_puae ss_ua [].
Lemma RES_puae_ok : sym_exec SEGS 100 true [0x528b0] scr_puae (SS 0x5289c sr_ua [] kn_ua 35) [] = RES_puae.
Proof. vm_compute. reflexivity. Qed.
End AXF_ua.

Module AXF_uaz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section UA.
Context {fx : FPState}.

Definition VALS_ua (sc u0 u1 : Z) : list Z := [sc; u0; u1].

Record ua_pre (regs : bvmap 5 word) (m : word -> option byte) (sc u0 u1 : Z) : Prop := {
  ua_R8 : getr regs 8 = wa sc ;
  ua_R10 : getr regs 10 = wa u0 ;
  ua_R15 : getr regs 15 = wa 31 ;
  ua_R23 : getr regs 23 = wa ((8 * sc) + 614096) ;
  ua_rng_sc : 0 <= sc <= 31 ;
  ua_rng_u0 : 0 <= u0 <= 2^60 ;
  ua_rng_u1 : 0 <= u1 <= 2^60 ;
  ua_kw3 : rdn SEGS m (wa (8 * sc + 614576)) 8 = Some (word_to_le_bytes 8 (wa u1))
}.


#[using="Type"] Lemma ua_setup : forall regs m sc u0 u1, ua_pre regs m sc u0 u1 ->
  regs_ok (Ez regs (VALS_ua sc u0 u1)) AXF_ua.sr_ua regs /\ know_ok SEGS (Ez regs (VALS_ua sc u0 u1)) m AXF_ua.kn_ua.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc u0 u1 P. destruct P as [ua_R8 ua_R10 ua_R15 ua_R23 ua_rng_sc ua_rng_u0 ua_rng_u1 ua_kw3].
  set (E := Ez regs (VALS_ua sc u0 u1)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = u0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ua.sr_ua.
    apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 15); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite ua_R8. reflexivity.
    - rewrite ua_R10. reflexivity.
    - rewrite ua_R15. reflexivity.
    - rewrite ua_R23, zeval_sound. cbn [zeval edenot AXF_ua.e_sc AXF_ua.e_u0 AXF_ua.e_u1]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_ua.kn_ua.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ua.e_sc AXF_ua.e_u0 AXF_ua.e_u1 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ ua_rng_sc eq_refl eq_refl), ?(mod64_of_range u0 _ _ ua_rng_u0 eq_refl eq_refl), ?(mod64_of_range u1 _ _ ua_rng_u1 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - ua_rng_sc ua_rng_u0 ua_rng_u1; lia).
  all: first [lia].
Qed.


Definition ua_mem_puao (m : word -> option byte) (regs : bvmap 5 word) (sc u0 u1 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem ua_puao : forall regs m rom sc u0 u1, ua_pre regs m sc u0 u1 ->
  scs_denot SEGS m (Ez regs (VALS_ua sc u0 u1)) (snd (fst AXF_ua.RES_puao)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5289c) m rom) (mkst R (wa 0x528b0) (ua_mem_puao m regs sc u0 u1) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa u0 /\ getr R 15 = wa (Z.land sc 1) /\ getr R 23 = wa ((8 * sc) + 614096) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 11; 12; 13; 14; 16; 17; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc u0 u1 P Hsc. destruct (ua_setup regs m sc u0 u1 P) as [HR HK].
  set (E := Ez regs (VALS_ua sc u0 u1)) in *. destruct P as [ua_R8 ua_R10 ua_R15 ua_R23 ua_rng_sc ua_rng_u0 ua_rng_u1 ua_kw3].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = u0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x528b0] AXF_ua.scr_puao 0x5289c AXF_ua.sr_ua AXF_ua.kn_ua 35 _ _ _ E m rom regs AXF_ua.RES_puao_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ua.RES_puao fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ua_mem_puao m regs sc u0 u1) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ua_mem_puao. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition ua_mem_puae (m : word -> option byte) (regs : bvmap 5 word) (sc u0 u1 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem ua_puae : forall regs m rom sc u0 u1, ua_pre regs m sc u0 u1 ->
  scs_denot SEGS m (Ez regs (VALS_ua sc u0 u1)) (snd (fst AXF_ua.RES_puae)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5289c) m rom) (mkst R (wa 0x528b0) (ua_mem_puae m regs sc u0 u1) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa (u0 + u1) /\ getr R 15 = wa u1 /\ getr R 23 = wa ((8 * sc) + 614096) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 11; 12; 13; 14; 16; 17; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc u0 u1 P Hsc. destruct (ua_setup regs m sc u0 u1 P) as [HR HK].
  set (E := Ez regs (VALS_ua sc u0 u1)) in *. destruct P as [ua_R8 ua_R10 ua_R15 ua_R23 ua_rng_sc ua_rng_u0 ua_rng_u1 ua_kw3].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = u0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = u1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x528b0] AXF_ua.scr_puae 0x5289c AXF_ua.sr_ua AXF_ua.kn_ua 35 _ _ _ E m rom regs AXF_ua.RES_puae_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ua.RES_puae fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ua_mem_puae m regs sc u0 u1) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ua_mem_puae. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End UA.
End AXF_uaz.


Module AXF_uab.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition sr_uab := (sr_upd (sr_upd sr_id 8 (e_sc)) 15 (ELit 31)).
Definition kn_uab : list kentry :=
  [ KRange e_sc 32 47 ].
Definition scr_uab : scripts := SCR [] [] [].
Definition ss_uab := SS 0x5289c sr_uab [] kn_uab 33.
Definition RUN_uab := sym_exec SEGS 100 true [0x528b0] scr_uab ss_uab [].

Definition scr_puab : scripts := SCR [] [] [].
Definition RES_puab := Eval vm_compute in sym_exec SEGS 100 true [0x528b0] scr_puab ss_uab [].
Lemma RES_puab_ok : sym_exec SEGS 100 true [0x528b0] scr_puab (SS 0x5289c sr_uab [] kn_uab 33) [] = RES_puab.
Proof. vm_compute. reflexivity. Qed.
End AXF_uab.

Module AXF_uabz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section UAB.
Context {fx : FPState}.

Definition VALS_uab (sc : Z) : list Z := [sc].

Record uab_pre (regs : bvmap 5 word) (m : word -> option byte) (sc : Z) : Prop := {
  uab_R8 : getr regs 8 = wa sc ;
  uab_R15 : getr regs 15 = wa 31 ;
  uab_rng_sc : 32 <= sc <= 47
}.


#[using="Type"] Lemma uab_setup : forall regs m sc, uab_pre regs m sc ->
  regs_ok (Ez regs (VALS_uab sc)) AXF_uab.sr_uab regs /\ know_ok SEGS (Ez regs (VALS_uab sc)) m AXF_uab.kn_uab.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc P. destruct P as [uab_R8 uab_R15 uab_rng_sc].
  set (E := Ez regs (VALS_uab sc)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_uab.sr_uab.
    apply (regs_ok_pin E _ regs 15); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|].
    - rewrite uab_R8. reflexivity.
    - rewrite uab_R15. reflexivity. }
  unfold know_ok, AXF_uab.kn_uab.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_uab.e_sc a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ uab_rng_sc eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - uab_rng_sc; lia).
  all: first [lia].
Qed.


Definition uab_mem_puab (m : word -> option byte) (regs : bvmap 5 word) (sc : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem uab_puab : forall regs m rom sc, uab_pre regs m sc ->
  scs_denot SEGS m (Ez regs (VALS_uab sc)) (snd (fst AXF_uab.RES_puab)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5289c) m rom) (mkst R (wa 0x528b0) (uab_mem_puab m regs sc) rom) /\
    getr R 8 = wa sc /\ getr R 15 = wa 31 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 10; 11; 12; 13; 14; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc P Hsc. destruct (uab_setup regs m sc P) as [HR HK].
  set (E := Ez regs (VALS_uab sc)) in *. destruct P as [uab_R8 uab_R15 uab_rng_sc].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x528b0] AXF_uab.scr_puab 0x5289c AXF_uab.sr_uab AXF_uab.kn_uab 33 _ _ _ E m rom regs AXF_uab.RES_puab_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uab.RES_puab fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uab_mem_puab m regs sc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uab_mem_puab. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End UAB.
End AXF_uabz.


Module AXF_rd.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_cnt0 := EVar 33.
Definition e_usage := EVar 34.
Definition e_ns := EVar 35.
Definition e_sz0 := EVar 36.
Definition sr_rd := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_sc)) 10 (e_usage)) 11 (ELit 4096)) 13 (e_ns)) 14 (e_sz0)) 19 (e_cnt0)).
Definition kn_rd : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_cnt0 1 32;
    KRange e_usage 0 (2^61);
    KRange e_ns 0 1;
    KRange e_sz0 16 (2^23) ].
Definition scr_rd : scripts := SCR [true] [] [].
Definition ss_rd := SS 0x528b0 sr_rd [] kn_rd 37.
Definition RUN_rd := sym_exec SEGS 100 true [0x52924] scr_rd ss_rd [].

Definition scr_prdu : scripts := SCR [true] [] [].
Definition RES_prdu := Eval vm_compute in sym_exec SEGS 100 true [0x52924] scr_prdu ss_rd [].
Lemma RES_prdu_ok : sym_exec SEGS 100 true [0x52924] scr_prdu (SS 0x528b0 sr_rd [] kn_rd 37) [] = RES_prdu.
Proof. vm_compute. reflexivity. Qed.

Definition scr_prdn : scripts := SCR [false; true] [] [].
Definition RES_prdn := Eval vm_compute in sym_exec SEGS 100 true [0x52924] scr_prdn ss_rd [].
Lemma RES_prdn_ok : sym_exec SEGS 100 true [0x52924] scr_prdn (SS 0x528b0 sr_rd [] kn_rd 37) [] = RES_prdn.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr1r : scripts := SCR [false; false; false; false] [] [].
Definition RES_pr1r := Eval vm_compute in sym_exec SEGS 100 true [0x52924] scr_pr1r ss_rd [].
Lemma RES_pr1r_ok : sym_exec SEGS 100 true [0x52924] scr_pr1r (SS 0x528b0 sr_rd [] kn_rd 37) [] = RES_pr1r.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr1k : scripts := SCR [false; false; false; true; true; false; true] [] [].
Definition RES_pr1k := Eval vm_compute in sym_exec SEGS 100 true [0x52924] scr_pr1k ss_rd [].
Lemma RES_pr1k_ok : sym_exec SEGS 100 true [0x52924] scr_pr1k (SS 0x528b0 sr_rd [] kn_rd 37) [] = RES_pr1k.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr2r : scripts := SCR [false; false; true; false; false] [] [].
Definition RES_pr2r := Eval vm_compute in sym_exec SEGS 100 true [0x52924] scr_pr2r ss_rd [].
Lemma RES_pr2r_ok : sym_exec SEGS 100 true [0x52924] scr_pr2r (SS 0x528b0 sr_rd [] kn_rd 37) [] = RES_pr2r.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr2k : scripts := SCR [false; false; true; false; true; false; true] [] [].
Definition RES_pr2k := Eval vm_compute in sym_exec SEGS 100 true [0x52924] scr_pr2k ss_rd [].
Lemma RES_pr2k_ok : sym_exec SEGS 100 true [0x52924] scr_pr2k (SS 0x528b0 sr_rd [] kn_rd 37) [] = RES_pr2k.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr0b : scripts := SCR [false; false; true; true; true; false; true] [] [].
Definition RES_pr0b := Eval vm_compute in sym_exec SEGS 100 true [0x52924] scr_pr0b ss_rd [].
Lemma RES_pr0b_ok : sym_exec SEGS 100 true [0x52924] scr_pr0b (SS 0x528b0 sr_rd [] kn_rd 37) [] = RES_pr0b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr0k : scripts := SCR [false; false; true; true; false; false; false; true] [] [].
Definition RES_pr0k := Eval vm_compute in sym_exec SEGS 100 true [0x52924] scr_pr0k ss_rd [].
Lemma RES_pr0k_ok : sym_exec SEGS 100 true [0x52924] scr_pr0k (SS 0x528b0 sr_rd [] kn_rd 37) [] = RES_pr0k.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr05 : scripts := SCR [false; false; true; true; false; false; false; false] [] [].
Definition RES_pr05 := Eval vm_compute in sym_exec SEGS 100 true [0x52924] scr_pr05 ss_rd [].
Lemma RES_pr05_ok : sym_exec SEGS 100 true [0x52924] scr_pr05 (SS 0x528b0 sr_rd [] kn_rd 37) [] = RES_pr05.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pr3 : scripts := SCR [false; false; true; true; false; true] [] [].
Definition RES_pr3 := Eval vm_compute in sym_exec SEGS 100 true [0x52924] scr_pr3 ss_rd [].
Lemma RES_pr3_ok : sym_exec SEGS 100 true [0x52924] scr_pr3 (SS 0x528b0 sr_rd [] kn_rd 37) [] = RES_pr3.
Proof. vm_compute. reflexivity. Qed.
End AXF_rd.

Module AXF_rdz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section RD.
Context {fx : FPState}.

Definition VALS_rd (sc cnt0 usage ns sz0 : Z) : list Z := [sc; cnt0; usage; ns; sz0].

Record rd_pre (regs : bvmap 5 word) (m : word -> option byte) (sc cnt0 usage ns sz0 : Z) : Prop := {
  rd_R8 : getr regs 8 = wa sc ;
  rd_R10 : getr regs 10 = wa usage ;
  rd_R11 : getr regs 11 = wa 4096 ;
  rd_R13 : getr regs 13 = wa ns ;
  rd_R14 : getr regs 14 = wa sz0 ;
  rd_R19 : getr regs 19 = wa cnt0 ;
  rd_rng_sc : 0 <= sc <= 47 ;
  rd_rng_cnt0 : 1 <= cnt0 <= 32 ;
  rd_rng_usage : 0 <= usage <= 2^61 ;
  rd_rng_ns : 0 <= ns <= 1 ;
  rd_rng_sz0 : 16 <= sz0 <= 2^23
}.


#[using="Type"] Lemma rd_setup : forall regs m sc cnt0 usage ns sz0, rd_pre regs m sc cnt0 usage ns sz0 ->
  regs_ok (Ez regs (VALS_rd sc cnt0 usage ns sz0)) AXF_rd.sr_rd regs /\ know_ok SEGS (Ez regs (VALS_rd sc cnt0 usage ns sz0)) m AXF_rd.kn_rd.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc cnt0 usage ns sz0 P. destruct P as [rd_R8 rd_R10 rd_R11 rd_R13 rd_R14 rd_R19 rd_rng_sc rd_rng_cnt0 rd_rng_usage rd_rng_ns rd_rng_sz0].
  set (E := Ez regs (VALS_rd sc cnt0 usage ns sz0)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = cnt0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sz0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_rd.sr_rd.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite rd_R8. reflexivity.
    - rewrite rd_R10. reflexivity.
    - rewrite rd_R11. reflexivity.
    - rewrite rd_R13. reflexivity.
    - rewrite rd_R14. reflexivity.
    - rewrite rd_R19. reflexivity. }
  unfold know_ok, AXF_rd.kn_rd.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_rd.e_sc AXF_rd.e_cnt0 AXF_rd.e_usage AXF_rd.e_ns AXF_rd.e_sz0 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ rd_rng_sc eq_refl eq_refl), ?(mod64_of_range cnt0 _ _ rd_rng_cnt0 eq_refl eq_refl), ?(mod64_of_range usage _ _ rd_rng_usage eq_refl eq_refl), ?(mod64_of_range ns _ _ rd_rng_ns eq_refl eq_refl), ?(mod64_of_range sz0 _ _ rd_rng_sz0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - rd_rng_sc rd_rng_cnt0 rd_rng_usage rd_rng_ns rd_rng_sz0; lia).
  all: first [lia].
Qed.


Definition rd_mem_prdu (m : word -> option byte) (regs : bvmap 5 word) (sc cnt0 usage ns sz0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem rd_prdu : forall regs m rom sc cnt0 usage ns sz0, rd_pre regs m sc cnt0 usage ns sz0 ->
  scs_denot SEGS m (Ez regs (VALS_rd sc cnt0 usage ns sz0)) (snd (fst AXF_rd.RES_prdu)) ->
  exists R, msteps SEGS (mkst regs (wa 0x528b0) m rom) (mkst R (wa 0x52924) (rd_mem_prdu m regs sc cnt0 usage ns sz0) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 13 = wa ns /\ getr R 14 = wa sz0 /\ getr R 19 = wa cnt0 /\ getr R 25 = wa cnt0 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 12; 16; 17; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc cnt0 usage ns sz0 P Hsc. destruct (rd_setup regs m sc cnt0 usage ns sz0 P) as [HR HK].
  set (E := Ez regs (VALS_rd sc cnt0 usage ns sz0)) in *. destruct P as [rd_R8 rd_R10 rd_R11 rd_R13 rd_R14 rd_R19 rd_rng_sc rd_rng_cnt0 rd_rng_usage rd_rng_ns rd_rng_sz0].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = cnt0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sz0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52924] AXF_rd.scr_prdu 0x528b0 AXF_rd.sr_rd AXF_rd.kn_rd 37 _ _ _ E m rom regs AXF_rd.RES_prdu_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_rd.RES_prdu fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (rd_mem_prdu m regs sc cnt0 usage ns sz0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold rd_mem_prdu. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition rd_mem_prdn (m : word -> option byte) (regs : bvmap 5 word) (sc cnt0 usage ns sz0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem rd_prdn : forall regs m rom sc cnt0 usage ns sz0, rd_pre regs m sc cnt0 usage ns sz0 ->
  scs_denot SEGS m (Ez regs (VALS_rd sc cnt0 usage ns sz0)) (snd (fst AXF_rd.RES_prdn)) ->
  exists R, msteps SEGS (mkst regs (wa 0x528b0) m rom) (mkst R (wa 0x52924) (rd_mem_prdn m regs sc cnt0 usage ns sz0) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 13 = wa ns /\ getr R 14 = wa sz0 /\ getr R 19 = wa cnt0 /\ getr R 25 = wa cnt0 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 12; 16; 17; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc cnt0 usage ns sz0 P Hsc. destruct (rd_setup regs m sc cnt0 usage ns sz0 P) as [HR HK].
  set (E := Ez regs (VALS_rd sc cnt0 usage ns sz0)) in *. destruct P as [rd_R8 rd_R10 rd_R11 rd_R13 rd_R14 rd_R19 rd_rng_sc rd_rng_cnt0 rd_rng_usage rd_rng_ns rd_rng_sz0].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = cnt0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sz0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52924] AXF_rd.scr_prdn 0x528b0 AXF_rd.sr_rd AXF_rd.kn_rd 37 _ _ _ E m rom regs AXF_rd.RES_prdn_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_rd.RES_prdn fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (rd_mem_prdn m regs sc cnt0 usage ns sz0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold rd_mem_prdn. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition rd_mem_pr1r (m : word -> option byte) (regs : bvmap 5 word) (sc cnt0 usage ns sz0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem rd_pr1r : forall regs m rom sc cnt0 usage ns sz0, rd_pre regs m sc cnt0 usage ns sz0 ->
  scs_denot SEGS m (Ez regs (VALS_rd sc cnt0 usage ns sz0)) (snd (fst AXF_rd.RES_pr1r)) ->
  exists R, msteps SEGS (mkst regs (wa 0x528b0) m rom) (mkst R (wa 0x52924) (rd_mem_pr1r m regs sc cnt0 usage ns sz0) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 13 = wa ns /\ getr R 14 = wa sz0 /\ getr R 15 = wa (Z.land sc 3) /\ getr R 16 = wa 32768 /\ getr R 17 = wa 1 /\ getr R 19 = wa cnt0 /\ getr R 25 = wa 2 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 12; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc cnt0 usage ns sz0 P Hsc. destruct (rd_setup regs m sc cnt0 usage ns sz0 P) as [HR HK].
  set (E := Ez regs (VALS_rd sc cnt0 usage ns sz0)) in *. destruct P as [rd_R8 rd_R10 rd_R11 rd_R13 rd_R14 rd_R19 rd_rng_sc rd_rng_cnt0 rd_rng_usage rd_rng_ns rd_rng_sz0].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = cnt0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sz0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52924] AXF_rd.scr_pr1r 0x528b0 AXF_rd.sr_rd AXF_rd.kn_rd 37 _ _ _ E m rom regs AXF_rd.RES_pr1r_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_rd.RES_pr1r fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (rd_mem_pr1r m regs sc cnt0 usage ns sz0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold rd_mem_pr1r. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition rd_mem_pr1k (m : word -> option byte) (regs : bvmap 5 word) (sc cnt0 usage ns sz0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem rd_pr1k : forall regs m rom sc cnt0 usage ns sz0, rd_pre regs m sc cnt0 usage ns sz0 ->
  scs_denot SEGS m (Ez regs (VALS_rd sc cnt0 usage ns sz0)) (snd (fst AXF_rd.RES_pr1k)) ->
  exists R, msteps SEGS (mkst regs (wa 0x528b0) m rom) (mkst R (wa 0x52924) (rd_mem_pr1k m regs sc cnt0 usage ns sz0) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 13 = wa ns /\ getr R 14 = wa sz0 /\ getr R 15 = wa (Z.land sc 3) /\ getr R 16 = wa 32768 /\ getr R 19 = wa cnt0 /\ getr R 25 = wa cnt0 /\ (forall k, In k [1; 2; 3; 4; 6; 7; 9; 12; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc cnt0 usage ns sz0 P Hsc. destruct (rd_setup regs m sc cnt0 usage ns sz0 P) as [HR HK].
  set (E := Ez regs (VALS_rd sc cnt0 usage ns sz0)) in *. destruct P as [rd_R8 rd_R10 rd_R11 rd_R13 rd_R14 rd_R19 rd_rng_sc rd_rng_cnt0 rd_rng_usage rd_rng_ns rd_rng_sz0].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = cnt0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sz0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52924] AXF_rd.scr_pr1k 0x528b0 AXF_rd.sr_rd AXF_rd.kn_rd 37 _ _ _ E m rom regs AXF_rd.RES_pr1k_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_rd.RES_pr1k fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (rd_mem_pr1k m regs sc cnt0 usage ns sz0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold rd_mem_pr1k. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition rd_mem_pr2r (m : word -> option byte) (regs : bvmap 5 word) (sc cnt0 usage ns sz0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem rd_pr2r : forall regs m rom sc cnt0 usage ns sz0, rd_pre regs m sc cnt0 usage ns sz0 ->
  scs_denot SEGS m (Ez regs (VALS_rd sc cnt0 usage ns sz0)) (snd (fst AXF_rd.RES_pr2r)) ->
  exists R, msteps SEGS (mkst regs (wa 0x528b0) m rom) (mkst R (wa 0x52924) (rd_mem_pr2r m regs sc cnt0 usage ns sz0) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 13 = wa ns /\ getr R 14 = wa sz0 /\ getr R 15 = wa (Z.land sc 3) /\ getr R 16 = wa 32768 /\ getr R 17 = wa 16384 /\ getr R 19 = wa cnt0 /\ getr R 25 = wa 3 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 12; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc cnt0 usage ns sz0 P Hsc. destruct (rd_setup regs m sc cnt0 usage ns sz0 P) as [HR HK].
  set (E := Ez regs (VALS_rd sc cnt0 usage ns sz0)) in *. destruct P as [rd_R8 rd_R10 rd_R11 rd_R13 rd_R14 rd_R19 rd_rng_sc rd_rng_cnt0 rd_rng_usage rd_rng_ns rd_rng_sz0].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = cnt0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sz0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52924] AXF_rd.scr_pr2r 0x528b0 AXF_rd.sr_rd AXF_rd.kn_rd 37 _ _ _ E m rom regs AXF_rd.RES_pr2r_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_rd.RES_pr2r fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (rd_mem_pr2r m regs sc cnt0 usage ns sz0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold rd_mem_pr2r. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition rd_mem_pr2k (m : word -> option byte) (regs : bvmap 5 word) (sc cnt0 usage ns sz0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem rd_pr2k : forall regs m rom sc cnt0 usage ns sz0, rd_pre regs m sc cnt0 usage ns sz0 ->
  scs_denot SEGS m (Ez regs (VALS_rd sc cnt0 usage ns sz0)) (snd (fst AXF_rd.RES_pr2k)) ->
  exists R, msteps SEGS (mkst regs (wa 0x528b0) m rom) (mkst R (wa 0x52924) (rd_mem_pr2k m regs sc cnt0 usage ns sz0) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 13 = wa ns /\ getr R 14 = wa sz0 /\ getr R 15 = wa (Z.land sc 3) /\ getr R 16 = wa 32768 /\ getr R 19 = wa cnt0 /\ getr R 25 = wa cnt0 /\ (forall k, In k [1; 2; 3; 4; 6; 7; 9; 12; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc cnt0 usage ns sz0 P Hsc. destruct (rd_setup regs m sc cnt0 usage ns sz0 P) as [HR HK].
  set (E := Ez regs (VALS_rd sc cnt0 usage ns sz0)) in *. destruct P as [rd_R8 rd_R10 rd_R11 rd_R13 rd_R14 rd_R19 rd_rng_sc rd_rng_cnt0 rd_rng_usage rd_rng_ns rd_rng_sz0].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = cnt0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sz0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52924] AXF_rd.scr_pr2k 0x528b0 AXF_rd.sr_rd AXF_rd.kn_rd 37 _ _ _ E m rom regs AXF_rd.RES_pr2k_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_rd.RES_pr2k fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (rd_mem_pr2k m regs sc cnt0 usage ns sz0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold rd_mem_pr2k. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition rd_mem_pr0b (m : word -> option byte) (regs : bvmap 5 word) (sc cnt0 usage ns sz0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem rd_pr0b : forall regs m rom sc cnt0 usage ns sz0, rd_pre regs m sc cnt0 usage ns sz0 ->
  scs_denot SEGS m (Ez regs (VALS_rd sc cnt0 usage ns sz0)) (snd (fst AXF_rd.RES_pr0b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x528b0) m rom) (mkst R (wa 0x52924) (rd_mem_pr0b m regs sc cnt0 usage ns sz0) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 13 = wa ns /\ getr R 14 = wa sz0 /\ getr R 15 = wa (Z.land sc 3) /\ getr R 16 = wa 32768 /\ getr R 19 = wa cnt0 /\ getr R 25 = wa 3 /\ (forall k, In k [1; 2; 3; 4; 6; 7; 9; 12; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc cnt0 usage ns sz0 P Hsc. destruct (rd_setup regs m sc cnt0 usage ns sz0 P) as [HR HK].
  set (E := Ez regs (VALS_rd sc cnt0 usage ns sz0)) in *. destruct P as [rd_R8 rd_R10 rd_R11 rd_R13 rd_R14 rd_R19 rd_rng_sc rd_rng_cnt0 rd_rng_usage rd_rng_ns rd_rng_sz0].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = cnt0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sz0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52924] AXF_rd.scr_pr0b 0x528b0 AXF_rd.sr_rd AXF_rd.kn_rd 37 _ _ _ E m rom regs AXF_rd.RES_pr0b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_rd.RES_pr0b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (rd_mem_pr0b m regs sc cnt0 usage ns sz0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold rd_mem_pr0b. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition rd_mem_pr0k (m : word -> option byte) (regs : bvmap 5 word) (sc cnt0 usage ns sz0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem rd_pr0k : forall regs m rom sc cnt0 usage ns sz0, rd_pre regs m sc cnt0 usage ns sz0 ->
  scs_denot SEGS m (Ez regs (VALS_rd sc cnt0 usage ns sz0)) (snd (fst AXF_rd.RES_pr0k)) ->
  exists R, msteps SEGS (mkst regs (wa 0x528b0) m rom) (mkst R (wa 0x52924) (rd_mem_pr0k m regs sc cnt0 usage ns sz0) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 13 = wa ns /\ getr R 14 = wa sz0 /\ getr R 15 = wa 8192 /\ getr R 16 = wa 32768 /\ getr R 19 = wa cnt0 /\ getr R 25 = wa cnt0 /\ (forall k, In k [1; 2; 3; 4; 6; 7; 9; 12; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc cnt0 usage ns sz0 P Hsc. destruct (rd_setup regs m sc cnt0 usage ns sz0 P) as [HR HK].
  set (E := Ez regs (VALS_rd sc cnt0 usage ns sz0)) in *. destruct P as [rd_R8 rd_R10 rd_R11 rd_R13 rd_R14 rd_R19 rd_rng_sc rd_rng_cnt0 rd_rng_usage rd_rng_ns rd_rng_sz0].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = cnt0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sz0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52924] AXF_rd.scr_pr0k 0x528b0 AXF_rd.sr_rd AXF_rd.kn_rd 37 _ _ _ E m rom regs AXF_rd.RES_pr0k_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_rd.RES_pr0k fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (rd_mem_pr0k m regs sc cnt0 usage ns sz0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold rd_mem_pr0k. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition rd_mem_pr05 (m : word -> option byte) (regs : bvmap 5 word) (sc cnt0 usage ns sz0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem rd_pr05 : forall regs m rom sc cnt0 usage ns sz0, rd_pre regs m sc cnt0 usage ns sz0 ->
  scs_denot SEGS m (Ez regs (VALS_rd sc cnt0 usage ns sz0)) (snd (fst AXF_rd.RES_pr05)) ->
  exists R, msteps SEGS (mkst regs (wa 0x528b0) m rom) (mkst R (wa 0x52924) (rd_mem_pr05 m regs sc cnt0 usage ns sz0) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 13 = wa ns /\ getr R 14 = wa sz0 /\ getr R 15 = wa 8192 /\ getr R 16 = wa 32768 /\ getr R 19 = wa 5 /\ getr R 25 = wa 5 /\ (forall k, In k [1; 2; 3; 4; 6; 7; 9; 12; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc cnt0 usage ns sz0 P Hsc. destruct (rd_setup regs m sc cnt0 usage ns sz0 P) as [HR HK].
  set (E := Ez regs (VALS_rd sc cnt0 usage ns sz0)) in *. destruct P as [rd_R8 rd_R10 rd_R11 rd_R13 rd_R14 rd_R19 rd_rng_sc rd_rng_cnt0 rd_rng_usage rd_rng_ns rd_rng_sz0].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = cnt0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sz0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52924] AXF_rd.scr_pr05 0x528b0 AXF_rd.sr_rd AXF_rd.kn_rd 37 _ _ _ E m rom regs AXF_rd.RES_pr05_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_rd.RES_pr05 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (rd_mem_pr05 m regs sc cnt0 usage ns sz0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold rd_mem_pr05. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition rd_mem_pr3 (m : word -> option byte) (regs : bvmap 5 word) (sc cnt0 usage ns sz0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem rd_pr3 : forall regs m rom sc cnt0 usage ns sz0, rd_pre regs m sc cnt0 usage ns sz0 ->
  scs_denot SEGS m (Ez regs (VALS_rd sc cnt0 usage ns sz0)) (snd (fst AXF_rd.RES_pr3)) ->
  exists R, msteps SEGS (mkst regs (wa 0x528b0) m rom) (mkst R (wa 0x52924) (rd_mem_pr3 m regs sc cnt0 usage ns sz0) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa usage /\ getr R 11 = wa 4096 /\ getr R 13 = wa ns /\ getr R 14 = wa sz0 /\ getr R 15 = wa (Z.land sc 3) /\ getr R 16 = wa 32768 /\ getr R 19 = wa cnt0 /\ getr R 25 = wa cnt0 /\ (forall k, In k [1; 2; 3; 4; 6; 7; 9; 12; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc cnt0 usage ns sz0 P Hsc. destruct (rd_setup regs m sc cnt0 usage ns sz0 P) as [HR HK].
  set (E := Ez regs (VALS_rd sc cnt0 usage ns sz0)) in *. destruct P as [rd_R8 rd_R10 rd_R11 rd_R13 rd_R14 rd_R19 rd_rng_sc rd_rng_cnt0 rd_rng_usage rd_rng_ns rd_rng_sz0].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = cnt0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sz0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52924] AXF_rd.scr_pr3 0x528b0 AXF_rd.sr_rd AXF_rd.kn_rd 37 _ _ _ E m rom regs AXF_rd.RES_pr3_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_rd.RES_pr3 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (rd_mem_pr3 m regs sc cnt0 usage ns sz0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold rd_mem_pr3. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End RD.
End AXF_rdz.


Module AXF_iv.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_cnt := EVar 32.
Definition e_size := EVar 33.
Definition e_ns := EVar 34.
Definition e_req := EVar 35.
Definition e_usage := EVar 36.
Definition sr_iv := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_usage)) 11 (ELit 4096)) 12 (EAlu ALU_ADD e_size (ELit 16))) 13 (e_ns)) 18 (e_req)) 24 (e_size)) 25 (e_cnt)).
Definition kn_iv : list kentry :=
  [ KRange e_cnt 1 32;
    KRange e_size 16 131056;
    KRange e_ns 0 1;
    KRange e_req 0 (2^26);
    KRange e_usage 0 (2^61) ].
Definition scr_iv : scripts := SCR [true] [] [].
Definition ss_iv := SS 0x52924 sr_iv [] kn_iv 37.
Definition RUN_iv := sym_exec SEGS 100 true [0x53328] scr_iv ss_iv [].

Definition scr_pivn : scripts := SCR [true] [] [].
Definition RES_pivn := Eval vm_compute in sym_exec SEGS 100 true [0x53328] scr_pivn ss_iv [].
Lemma RES_pivn_ok : sym_exec SEGS 100 true [0x53328] scr_pivn (SS 0x52924 sr_iv [] kn_iv 37) [] = RES_pivn.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pivc : scripts := SCR [false; true] [] [].
Definition RES_pivc := Eval vm_compute in sym_exec SEGS 100 true [0x53328] scr_pivc ss_iv [].
Lemma RES_pivc_ok : sym_exec SEGS 100 true [0x53328] scr_pivc (SS 0x52924 sr_iv [] kn_iv 37) [] = RES_pivc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pivs : scripts := SCR [false; false; false] [] [].
Definition RES_pivs := Eval vm_compute in sym_exec SEGS 100 true [0x53328] scr_pivs ss_iv [].
Lemma RES_pivs_ok : sym_exec SEGS 100 true [0x53328] scr_pivs (SS 0x52924 sr_iv [] kn_iv 37) [] = RES_pivs.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pivk : scripts := SCR [false; false; true; true] [] [].
Definition RES_pivk := Eval vm_compute in sym_exec SEGS 100 true [0x53328] scr_pivk ss_iv [].
Lemma RES_pivk_ok : sym_exec SEGS 100 true [0x53328] scr_pivk (SS 0x52924 sr_iv [] kn_iv 37) [] = RES_pivk.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pivu : scripts := SCR [false; false; true; false; true] [] [].
Definition RES_pivu := Eval vm_compute in sym_exec SEGS 100 true [0x53328] scr_pivu ss_iv [].
Lemma RES_pivu_ok : sym_exec SEGS 100 true [0x53328] scr_pivu (SS 0x52924 sr_iv [] kn_iv 37) [] = RES_pivu.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pivg : scripts := SCR [false; false; true; false; false] [] [].
Definition RES_pivg := Eval vm_compute in sym_exec SEGS 100 true [0x53328] scr_pivg ss_iv [].
Lemma RES_pivg_ok : sym_exec SEGS 100 true [0x53328] scr_pivg (SS 0x52924 sr_iv [] kn_iv 37) [] = RES_pivg.
Proof. vm_compute. reflexivity. Qed.
End AXF_iv.

Module AXF_ivz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section IV.
Context {fx : FPState}.

Definition VALS_iv (cnt size ns req usage : Z) : list Z := [cnt; size; ns; req; usage].

Record iv_pre (regs : bvmap 5 word) (m : word -> option byte) (cnt size ns req usage : Z) : Prop := {
  iv_R10 : getr regs 10 = wa usage ;
  iv_R11 : getr regs 11 = wa 4096 ;
  iv_R12 : getr regs 12 = wa (size + 16) ;
  iv_R13 : getr regs 13 = wa ns ;
  iv_R18 : getr regs 18 = wa req ;
  iv_R24 : getr regs 24 = wa size ;
  iv_R25 : getr regs 25 = wa cnt ;
  iv_rng_cnt : 1 <= cnt <= 32 ;
  iv_rng_size : 16 <= size <= 131056 ;
  iv_rng_ns : 0 <= ns <= 1 ;
  iv_rng_req : 0 <= req <= 2^26 ;
  iv_rng_usage : 0 <= usage <= 2^61
}.


#[using="Type"] Lemma iv_setup : forall regs m cnt size ns req usage, iv_pre regs m cnt size ns req usage ->
  regs_ok (Ez regs (VALS_iv cnt size ns req usage)) AXF_iv.sr_iv regs /\ know_ok SEGS (Ez regs (VALS_iv cnt size ns req usage)) m AXF_iv.kn_iv.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m cnt size ns req usage P. destruct P as [iv_R10 iv_R11 iv_R12 iv_R13 iv_R18 iv_R24 iv_R25 iv_rng_cnt iv_rng_size iv_rng_ns iv_rng_req iv_rng_usage].
  set (E := Ez regs (VALS_iv cnt size ns req usage)).
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = req) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_iv.sr_iv.
    apply (regs_ok_pin E _ regs 25); [apply (regs_ok_pin E _ regs 24); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|]|]|]|].
    - rewrite iv_R10. reflexivity.
    - rewrite iv_R11. reflexivity.
    - rewrite iv_R12, zeval_sound. cbn [zeval edenot AXF_iv.e_cnt AXF_iv.e_size AXF_iv.e_ns AXF_iv.e_req AXF_iv.e_usage]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite iv_R13. reflexivity.
    - rewrite iv_R18. reflexivity.
    - rewrite iv_R24. reflexivity.
    - rewrite iv_R25. reflexivity. }
  unfold know_ok, AXF_iv.kn_iv.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_iv.e_cnt AXF_iv.e_size AXF_iv.e_ns AXF_iv.e_req AXF_iv.e_usage a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range cnt _ _ iv_rng_cnt eq_refl eq_refl), ?(mod64_of_range size _ _ iv_rng_size eq_refl eq_refl), ?(mod64_of_range ns _ _ iv_rng_ns eq_refl eq_refl), ?(mod64_of_range req _ _ iv_rng_req eq_refl eq_refl), ?(mod64_of_range usage _ _ iv_rng_usage eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - iv_rng_cnt iv_rng_size iv_rng_ns iv_rng_req iv_rng_usage; lia).
  all: first [lia].
Qed.


Definition iv_mem_pivn (m : word -> option byte) (regs : bvmap 5 word) (cnt size ns req usage : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem iv_pivn : forall regs m rom cnt size ns req usage, iv_pre regs m cnt size ns req usage ->
  scs_denot SEGS m (Ez regs (VALS_iv cnt size ns req usage)) (snd (fst AXF_iv.RES_pivn)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52924) m rom) (mkst R (wa 0x53328) (iv_mem_pivn m regs cnt size ns req usage) rom) /\
    getr R 1 = wa 338336 /\ getr R 10 = wa 0 /\ getr R 11 = wa ((Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095 + (size * cnt)) + 16) /\ getr R 12 = wa 3 /\ getr R 13 = wa 34 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 16 = wa (Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095) /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa ((Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095 + (size * cnt)) + 16) /\ getr R 24 = wa size /\ getr R 25 = wa cnt /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 17; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt size ns req usage P Hsc. destruct (iv_setup regs m cnt size ns req usage P) as [HR HK].
  set (E := Ez regs (VALS_iv cnt size ns req usage)) in *. destruct P as [iv_R10 iv_R11 iv_R12 iv_R13 iv_R18 iv_R24 iv_R25 iv_rng_cnt iv_rng_size iv_rng_ns iv_rng_req iv_rng_usage].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = req) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53328] AXF_iv.scr_pivn 0x52924 AXF_iv.sr_iv AXF_iv.kn_iv 37 _ _ _ E m rom regs AXF_iv.RES_pivn_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_iv.RES_pivn fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (iv_mem_pivn m regs cnt size ns req usage) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold iv_mem_pivn. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition iv_mem_pivc (m : word -> option byte) (regs : bvmap 5 word) (cnt size ns req usage : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem iv_pivc : forall regs m rom cnt size ns req usage, iv_pre regs m cnt size ns req usage ->
  scs_denot SEGS m (Ez regs (VALS_iv cnt size ns req usage)) (snd (fst AXF_iv.RES_pivc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52924) m rom) (mkst R (wa 0x53328) (iv_mem_pivc m regs cnt size ns req usage) rom) /\
    getr R 1 = wa 338336 /\ getr R 10 = wa 0 /\ getr R 11 = wa ((Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095 + (size * cnt)) + 16) /\ getr R 12 = wa 3 /\ getr R 13 = wa 34 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 16 = wa (Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095) /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa ((Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095 + (size * cnt)) + 16) /\ getr R 24 = wa size /\ getr R 25 = wa cnt /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 17; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt size ns req usage P Hsc. destruct (iv_setup regs m cnt size ns req usage P) as [HR HK].
  set (E := Ez regs (VALS_iv cnt size ns req usage)) in *. destruct P as [iv_R10 iv_R11 iv_R12 iv_R13 iv_R18 iv_R24 iv_R25 iv_rng_cnt iv_rng_size iv_rng_ns iv_rng_req iv_rng_usage].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = req) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53328] AXF_iv.scr_pivc 0x52924 AXF_iv.sr_iv AXF_iv.kn_iv 37 _ _ _ E m rom regs AXF_iv.RES_pivc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_iv.RES_pivc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (iv_mem_pivc m regs cnt size ns req usage) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold iv_mem_pivc. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition iv_mem_pivs (m : word -> option byte) (regs : bvmap 5 word) (cnt size ns req usage : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem iv_pivs : forall regs m rom cnt size ns req usage, iv_pre regs m cnt size ns req usage ->
  scs_denot SEGS m (Ez regs (VALS_iv cnt size ns req usage)) (snd (fst AXF_iv.RES_pivs)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52924) m rom) (mkst R (wa 0x53328) (iv_mem_pivs m regs cnt size ns req usage) rom) /\
    getr R 1 = wa 338336 /\ getr R 10 = wa 0 /\ getr R 11 = wa ((req + Z.land ((((-1 * req) + -20)) mod 2^64) 4095) + 20) /\ getr R 12 = wa 3 /\ getr R 13 = wa 34 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 16 = wa (Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095) /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa ((req + Z.land ((((-1 * req) + -20)) mod 2^64) 4095) + 20) /\ getr R 24 = wa size /\ getr R 25 = wa 1 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 17; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt size ns req usage P Hsc. destruct (iv_setup regs m cnt size ns req usage P) as [HR HK].
  set (E := Ez regs (VALS_iv cnt size ns req usage)) in *. destruct P as [iv_R10 iv_R11 iv_R12 iv_R13 iv_R18 iv_R24 iv_R25 iv_rng_cnt iv_rng_size iv_rng_ns iv_rng_req iv_rng_usage].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = req) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53328] AXF_iv.scr_pivs 0x52924 AXF_iv.sr_iv AXF_iv.kn_iv 37 _ _ _ E m rom regs AXF_iv.RES_pivs_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_iv.RES_pivs fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (iv_mem_pivs m regs cnt size ns req usage) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold iv_mem_pivs. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition iv_mem_pivk (m : word -> option byte) (regs : bvmap 5 word) (cnt size ns req usage : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem iv_pivk : forall regs m rom cnt size ns req usage, iv_pre regs m cnt size ns req usage ->
  scs_denot SEGS m (Ez regs (VALS_iv cnt size ns req usage)) (snd (fst AXF_iv.RES_pivk)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52924) m rom) (mkst R (wa 0x53328) (iv_mem_pivk m regs cnt size ns req usage) rom) /\
    getr R 1 = wa 338336 /\ getr R 10 = wa 0 /\ getr R 11 = wa ((Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095 + (size * cnt)) + 16) /\ getr R 12 = wa 3 /\ getr R 13 = wa 34 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 16 = wa (Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095) /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa ((Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095 + (size * cnt)) + 16) /\ getr R 24 = wa size /\ getr R 25 = wa cnt /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 17; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt size ns req usage P Hsc. destruct (iv_setup regs m cnt size ns req usage P) as [HR HK].
  set (E := Ez regs (VALS_iv cnt size ns req usage)) in *. destruct P as [iv_R10 iv_R11 iv_R12 iv_R13 iv_R18 iv_R24 iv_R25 iv_rng_cnt iv_rng_size iv_rng_ns iv_rng_req iv_rng_usage].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = req) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53328] AXF_iv.scr_pivk 0x52924 AXF_iv.sr_iv AXF_iv.kn_iv 37 _ _ _ E m rom regs AXF_iv.RES_pivk_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_iv.RES_pivk fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (iv_mem_pivk m regs cnt size ns req usage) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold iv_mem_pivk. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition iv_mem_pivu (m : word -> option byte) (regs : bvmap 5 word) (cnt size ns req usage : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem iv_pivu : forall regs m rom cnt size ns req usage, iv_pre regs m cnt size ns req usage ->
  scs_denot SEGS m (Ez regs (VALS_iv cnt size ns req usage)) (snd (fst AXF_iv.RES_pivu)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52924) m rom) (mkst R (wa 0x53328) (iv_mem_pivu m regs cnt size ns req usage) rom) /\
    getr R 1 = wa 338336 /\ getr R 10 = wa 0 /\ getr R 11 = wa ((req + Z.land ((((-1 * req) + -20)) mod 2^64) 4095) + 20) /\ getr R 12 = wa 3 /\ getr R 13 = wa 34 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 16 = wa (Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095) /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa ((req + Z.land ((((-1 * req) + -20)) mod 2^64) 4095) + 20) /\ getr R 24 = wa size /\ getr R 25 = wa 1 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 17; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt size ns req usage P Hsc. destruct (iv_setup regs m cnt size ns req usage P) as [HR HK].
  set (E := Ez regs (VALS_iv cnt size ns req usage)) in *. destruct P as [iv_R10 iv_R11 iv_R12 iv_R13 iv_R18 iv_R24 iv_R25 iv_rng_cnt iv_rng_size iv_rng_ns iv_rng_req iv_rng_usage].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = req) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53328] AXF_iv.scr_pivu 0x52924 AXF_iv.sr_iv AXF_iv.kn_iv 37 _ _ _ E m rom regs AXF_iv.RES_pivu_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_iv.RES_pivu fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (iv_mem_pivu m regs cnt size ns req usage) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold iv_mem_pivu. repeat (apply (f_equal3 wbytes)); try reflexivity.
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


Definition iv_mem_pivg (m : word -> option byte) (regs : bvmap 5 word) (cnt size ns req usage : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem iv_pivg : forall regs m rom cnt size ns req usage, iv_pre regs m cnt size ns req usage ->
  scs_denot SEGS m (Ez regs (VALS_iv cnt size ns req usage)) (snd (fst AXF_iv.RES_pivg)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52924) m rom) (mkst R (wa 0x53328) (iv_mem_pivg m regs cnt size ns req usage) rom) /\
    getr R 1 = wa 338336 /\ getr R 10 = wa 0 /\ getr R 11 = wa ((Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095 + (size * cnt)) + 16) /\ getr R 12 = wa 3 /\ getr R 13 = wa 34 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 16 = wa (Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095) /\ getr R 18 = wa 18446744073709551615 /\ getr R 19 = wa ((Z.land ((((-1 * (size * cnt)) + -16)) mod 2^64) 4095 + (size * cnt)) + 16) /\ getr R 24 = wa size /\ getr R 25 = wa cnt /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 17; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt size ns req usage P Hsc. destruct (iv_setup regs m cnt size ns req usage P) as [HR HK].
  set (E := Ez regs (VALS_iv cnt size ns req usage)) in *. destruct P as [iv_R10 iv_R11 iv_R12 iv_R13 iv_R18 iv_R24 iv_R25 iv_rng_cnt iv_rng_size iv_rng_ns iv_rng_req iv_rng_usage].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ns) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = req) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = usage) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53328] AXF_iv.scr_pivg 0x52924 AXF_iv.sr_iv AXF_iv.kn_iv 37 _ _ _ E m rom regs AXF_iv.RES_pivg_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_iv.RES_pivg fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (iv_mem_pivg m regs cnt size ns req usage) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold iv_mem_pivg. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End IV.
End AXF_ivz.

From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_mmwz.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxTry OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.AxTry2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag2.AXF_bncoz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag2.AXF_bnciz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag2.AXF_sqz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag2.AXF_uaz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag2.AXF_uabz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag2.AXF_rdz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag2.AXF_ivz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_mmwz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ab_tr (sc : Z) : bool := (7 <=? sc) && (sc <? 39).
Definition ab_ns (sc b : Z) : Z := if ab_tr sc then (if b <? 100 then 0 else 1) else 0.
Definition ab_hit (sc useq seq : Z) : bool := ab_tr sc && negb (useq =? 0) && (seq - useq <? 10).
Definition ab_nb (b : Z) : Z := if b + 1 <? 100 then b + 1 else 150.
Definition ab_mem (m : word -> option byte) (sc b useq seq : Z) : word -> option byte :=
  if ab_hit sc useq seq then wbytes m (wa (sc + 614977)) (word_to_le_bytes 1 (wa (ab_nb b))) else m.

Section AG2.
Context {fx : FPState}.

#[using="Type"] Theorem seg_ab : forall R m rom sc b useq seq, getr R 8 = wa sc -> getr R 22 = wa 614096 -> 0 <= sc <= 47 -> 0 <= b <= 255 -> 0 <= useq <= 255 ->
  0 <= seq <= 255 -> rdn SEGS m (wa (0 + 615016)) 1 = Some (word_to_le_bytes 1 (wa seq)) ->
  (ab_tr sc = true -> rdn SEGS m (wa (sc + 614977)) 1 = Some (word_to_le_bytes 1 (wa b)) /\
     rdn SEGS m (wa (sc + 614945)) 1 = Some (word_to_le_bytes 1 (wa useq)) /\
     (forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (sc + 614977 + d)) k = true)) ->
  exists R', msteps SEGS (mkst R (wa 0x525bc) m rom) (mkst R' (wa 0x52870) (ab_mem m sc b useq seq) rom) /\
    getr R' 8 = wa sc /\ getr R' 13 = wa (ab_ns sc b) /\ getr R' 16 = wa seq /\ getr R' 22 = wa 614096 /\
    (forall k, In k [1; 2; 3; 4; 7; 9; 10; 11; 12; 14; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat ->
       getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sc b useq seq R8 R22 Hsc Hb Hu Hs Mseq Mtr. unfold ab_mem, ab_hit, ab_ns.
  destruct (ab_tr sc) eqn:Tr.
  - destruct (Mtr eq_refl) as (Mb & Mu & Wb). clear Mtr.
    assert (Hsc' : 7 <= sc <= 38) by (unfold ab_tr in Tr; apply andb_true_iff in Tr as [T1 T2]; apply Z.leb_le in T1; apply Z.ltb_lt in T2; lia).
    assert (P : bnci_pre R m sc b useq seq) by (constructor; assumption || lia).
    cbn [andb].
    destruct (Z.eq_dec useq 0) as [Ez|Ez].
    + subst useq. cbn [Z.eqb negb andb].
      destruct (bnci_pbz R m rom sc b 0 seq P) as (R' & Hms & Q5 & Q8 & Q13 & Q15 & Q16 & Q17 & Q22 & QK).
      { scs_go. zats. reflexivity. }
      exists R'. split; [exact Hms|]. split; [exact Q8|]. split; [exact Q13|]. split; [exact Q16|]. split; [exact Q22|].
      intros k Hk. apply QK. clear - Hk. klist Hk.
    + replace (useq =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ez). cbn [negb andb].
      destruct (seq - useq <? 10) eqn:Ed; [apply Z.ltb_lt in Ed | apply Z.ltb_ge in Ed].
      * unfold ab_nb. destruct (b + 1 <? 100) eqn:Eb; [apply Z.ltb_lt in Eb | apply Z.ltb_ge in Eb].
        -- destruct (bnci_pbi R m rom sc b useq seq P) as (R' & Hms & Q5 & Q6 & Q8 & Q13 & Q15 & Q16 & Q17 & Q22 & QK).
           { scs_go; zats.
             - rewrite !Z.mod_small by lia. apply Z.ltb_lt. lia.
             - rewrite br_lt_z by lia. apply Z.ltb_ge. lia.
             - rewrite !Z.mod_small by lia. apply Z.eqb_neq. exact Ez. }
           exists R'. split; [exact Hms|]. split; [exact Q8|]. split; [exact Q13|]. split; [exact Q16|]. split; [exact Q22|].
           intros k Hk. apply QK. clear - Hk. klist Hk.
        -- destruct (bnci_pbs R m rom sc b useq seq P) as (R' & Hms & Q5 & Q6 & Q8 & Q13 & Q15 & Q16 & Q17 & Q22 & QK).
           { scs_go; zats.
             - rewrite !Z.mod_small by lia. apply Z.ltb_ge. lia.
             - rewrite br_lt_z by lia. apply Z.ltb_ge. lia.
             - rewrite !Z.mod_small by lia. apply Z.eqb_neq. exact Ez. }
           exists R'. split; [exact Hms|]. split; [exact Q8|]. split; [exact Q13|]. split; [exact Q16|]. split; [exact Q22|].
           intros k Hk. apply QK. clear - Hk. klist Hk.
      * destruct (bnci_pbf R m rom sc b useq seq P) as (R' & Hms & Q5 & Q6 & Q8 & Q13 & Q15 & Q16 & Q17 & Q22 & QK).
        { scs_go; zats.
          - rewrite br_lt_z by lia. apply Z.ltb_lt. lia.
          - rewrite !Z.mod_small by lia. apply Z.eqb_neq. exact Ez. }
        exists R'. split; [exact Hms|]. split; [exact Q8|]. split; [exact Q13|]. split; [exact Q16|]. split; [exact Q22|].
        intros k Hk. apply QK. clear - Hk. klist Hk.
  - cbn [andb]. assert (P : bnco_pre R m sc seq) by (constructor; assumption).
    destruct (bnco_pbo R m rom sc seq P) as (R' & Hms & Q8 & Q13 & Q15 & Q16 & Q22 & QK).
    { scs_go; zats. apply Z.ltb_lt. unfold ab_tr in Tr. apply andb_false_iff in Tr.
      destruct Tr as [T|T]; [apply Z.leb_gt in T | apply Z.ltb_ge in T]; clear - Hsc T; lia. }
    exists R'. split; [exact Hms|]. split; [exact Q8|]. split; [exact Q13|]. split; [exact Q16|]. split; [exact Q22|].
    intros k Hk. apply QK. clear - Hk. klist Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sq_mem (m : word -> option byte) (seq : Z) : word -> option byte :=
  if seq =? 255 then
    wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 614952)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614960)) (word_to_le_bytes 8 (wa 0)))
      (wa (0 + 614968)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 614976)) (word_to_le_bytes 8 (wa 0))) (wa (0 + 615016)) (word_to_le_bytes 1 (wa 1))
  else wbytes (m) (wa (0 + 615016)) (word_to_le_bytes 1 (wa (seq + 1))).

#[using="Type"] Theorem seg_sq : forall R m rom seq, getr R 16 = wa seq -> getr R 22 = wa 614096 -> 0 <= seq <= 255 ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m (wa (0 + 614952 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (0 + 615016 + d)) k = true) ->
  exists R', msteps SEGS (mkst R (wa 0x52870) m rom) (mkst R' (wa 0x5289c) (sq_mem m seq) rom) /\
    getr R' 15 = wa 31 /\ getr R' 22 = wa 614096 /\
    (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat ->
       getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom seq R16 R22 Hs W1 W2. assert (P : sq_pre R m seq) by (constructor; assumption). unfold sq_mem.
  destruct (Z.eq_dec seq 255) as [->|Ne].
  - cbn [Z.eqb Pos.eqb]. destruct (sq_pres R m rom 255 P) as (R' & Hms & Q15 & Q16 & Q22 & QK).
    { scs_go; zats. reflexivity. }
    exists R'. split; [exact Hms|]. split; [exact Q15|]. split; [exact Q22|]. exact QK.
  - replace (seq =? 255) with false by (symmetry; apply Z.eqb_neq; exact Ne).
    destruct (sq_pinc R m rom seq P) as (R' & Hms & Q15 & Q16 & Q22 & QK).
    { scs_go; zats. rewrite !Z.mod_small by lia. cbn [negb]. apply negb_true_iff. apply Z.eqb_neq. exact Ne. }
    exists R'. split; [exact Hms|]. split; [exact Q15|]. split; [exact Q22|]. exact QK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma land1_even : forall x, 0 <= x < 2^64 -> (Z.land (x mod 2^64) (1 mod 2^64) mod 2^64 =? 0 mod 2^64) = Z.even x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x Hx. rewrite (Z.mod_small x) by lia. change (1 mod 2^64) with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2.
  rewrite (Z.mod_small (x mod 2)) by (pose proof (Z.mod_pos_bound x 2 ltac:(lia)); lia). change (0 mod 2^64) with 0.
  rewrite Zmod_even. destruct (Z.even x); reflexivity.
Qed.

Definition ua_u (sc u0 u1 : Z) : Z := if Z.even sc && (sc <? 32) then u0 + u1 else u0.

#[using="Type"] Theorem seg_ua : forall R m rom sc u0 u1, getr R 8 = wa sc -> getr R 10 = wa u0 -> getr R 15 = wa 31 -> getr R 23 = wa (8 * sc + 614096) ->
  0 <= sc <= 47 -> 0 <= u0 <= 2^60 -> 0 <= u1 <= 2^60 ->
  (sc <= 31 -> rdn SEGS m (wa (8 * sc + 614576)) 8 = Some (word_to_le_bytes 8 (wa u1))) ->
  exists R', msteps SEGS (mkst R (wa 0x5289c) m rom) (mkst R' (wa 0x528b0) m rom) /\
    getr R' 8 = wa sc /\ getr R' 10 = wa (ua_u sc u0 u1) /\ getr R' 23 = wa (8 * sc + 614096) /\
    (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 11; 12; 13; 14; 16; 17; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%nat ->
       getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sc u0 u1 R8 R10 R15 R23 Hsc Hu0 Hu1 Mu1. unfold ua_u.
  destruct (Z_le_gt_dec sc 31) as [S|S].
  - assert (P : ua_pre R m sc u0 u1) by (constructor; try assumption; first [lia | exact (Mu1 S)]).
    replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia). rewrite andb_true_r.
    destruct (Z.even sc) eqn:Ev.
    + destruct (ua_puae R m rom sc u0 u1 P) as (R' & Hms & Q8 & Q10 & Q15 & Q23 & QK).
      { scs_go; zats. rewrite land1_even by lia. rewrite Ev. reflexivity. }
      exists R'. split; [change (ua_mem_puae m R sc u0 u1) with m in Hms; exact Hms|]. split; [exact Q8|]. split; [exact Q10|]. split; [exact Q23|].
      intros k Hk. apply QK. clear - Hk. klist Hk.
    + destruct (ua_puao R m rom sc u0 u1 P) as (R' & Hms & Q8 & Q10 & Q15 & Q23 & QK).
      { scs_go; zats. rewrite land1_even by lia. rewrite Ev. reflexivity. }
      exists R'. split; [change (ua_mem_puao m R sc u0 u1) with m in Hms; exact Hms|]. split; [exact Q8|]. split; [exact Q10|]. split; [exact Q23|].
      intros k Hk. apply QK. clear - Hk. klist Hk.
  - assert (P : uab_pre R m sc) by (constructor; try assumption; lia).
    replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
    destruct (uab_puab R m rom sc P ltac:(constructor)) as (R' & Hms & Q8 & Q15 & QK).
    exists R'. split; [change (uab_mem_puab m R sc) with m in Hms; exact Hms|]. split; [exact Q8|]. split; [regk QK 10%nat; exact R10|]. split; [regk QK 23%nat; exact R23|].
    intros k Hk. apply QK. clear - Hk. klist Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac bdec := repeat match goal with
    | |- context [?x <? ?y] => first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia)
                                     | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]
    | |- context [?x =? ?y] => first [ replace (x =? y) with true by (symmetry; apply Z.eqb_eq; lia)
                                     | replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) ]
    end; reflexivity.
Ltac rdscs sc E3 := cbn [fst snd]; repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z;
    rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z; cbn [zeval]; rewrite ?sltu_z; cbn [zeval edenot]; zats; rewrite ?sllw2_small by lia;
    change (3 mod 2^64) with 3; change (1 mod 2^64) with 1; change (0 mod 2^64) with 0; rewrite ?(Z.mod_small sc) by lia; rewrite ?E3;
    rewrite ?Z.mod_small by lia; bdec.

Definition rd_cnt (sc cnt0 usage ns sz0 : Z) : Z :=
  if (usage <? 4 * cnt0) && (ns =? 0) then
    if (Z.land sc 3 =? 1) && (8 * 4096 <? sz0) then 2
    else if (Z.land sc 3 =? 2) && (4 * 4096 <? sz0) then 3
    else if (Z.land sc 3 =? 0) && (8 * 4096 <? sz0) then 3
    else if (Z.land sc 3 =? 0) && (2 * 4096 <? sz0) then 5
    else cnt0
  else cnt0.

#[using="Type"] Theorem seg_rd : forall R m rom sc cnt0 usage ns sz0, getr R 8 = wa sc -> getr R 10 = wa usage -> getr R 11 = wa 4096 ->
  getr R 13 = wa ns -> getr R 14 = wa sz0 -> getr R 19 = wa cnt0 ->
  0 <= sc <= 47 -> 1 <= cnt0 <= 32 -> 0 <= usage <= 2^61 -> 0 <= ns <= 1 -> 16 <= sz0 <= 2^23 ->
  exists R', msteps SEGS (mkst R (wa 0x528b0) m rom) (mkst R' (wa 0x52924) m rom) /\ getr R' 25 = wa (rd_cnt sc cnt0 usage ns sz0) /\
    getr R' 8 = wa sc /\ getr R' 10 = wa usage /\ getr R' 11 = wa 4096 /\ getr R' 13 = wa ns /\ getr R' 14 = wa sz0 /\
    (forall k, In k [1; 2; 3; 4; 6; 7; 9; 12; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat ->
       getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sc cnt0 usage ns sz0 R8 R10 R11 R13 R14 R19 Hsc Hc Hu Hns Hsz.
  assert (P : rd_pre R m sc cnt0 usage ns sz0) by (constructor; assumption).
  pose proof (land3_bound sc) as L3.
  assert (POST : forall R' v, msteps SEGS (mkst R (wa 0x528b0) m rom) (mkst R' (wa 0x52924) m rom) -> v = rd_cnt sc cnt0 usage ns sz0 ->
      getr R' 25 = wa v -> getr R' 8 = wa sc -> getr R' 10 = wa usage -> getr R' 11 = wa 4096 -> getr R' 13 = wa ns -> getr R' 14 = wa sz0 ->
      (forall k, In k [1; 2; 3; 4; 6; 7; 9; 12; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
      exists R', msteps SEGS (mkst R (wa 0x528b0) m rom) (mkst R' (wa 0x52924) m rom) /\ getr R' 25 = wa (rd_cnt sc cnt0 usage ns sz0) /\
      getr R' 8 = wa sc /\ getr R' 10 = wa usage /\ getr R' 11 = wa 4096 /\ getr R' 13 = wa ns /\ getr R' 14 = wa sz0 /\
      (forall k, In k [1; 2; 3; 4; 6; 7; 9; 12; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k)))).
  { intros R' v Hms -> Q25 Q8 Q10 Q11 Q13 Q14 QK. exists R'. repeat (split; [assumption|]). exact QK. }
  assert (E3 : Z.land sc 3 = 0 \/ Z.land sc 3 = 1 \/ Z.land sc 3 = 2 \/ Z.land sc 3 = 3) by lia.
  destruct (usage <? 4 * cnt0) eqn:Eu; [apply Z.ltb_lt in Eu | apply Z.ltb_ge in Eu].
  - destruct (Z.eq_dec ns 0) as [Ens|Ens].
    + subst ns.
      destruct E3 as [E3|[E3|[E3|E3]]].
      * destruct (8 * 4096 <? sz0) eqn:Ea; [apply Z.ltb_lt in Ea | apply Z.ltb_ge in Ea].
        -- destruct (rd_pr0b R m rom sc cnt0 usage 0 sz0 P) as (R' & Hms & Q8 & Q10 & Q11 & Q13 & Q14 & _ & _ & Q19 & Q25 & QK).
           { rdscs sc E3. }
           exact (POST R' 3 Hms ltac:(unfold rd_cnt; rewrite E3; bdec) Q25 Q8 Q10 Q11 Q13 Q14 ltac:(intros k Hk; apply QK; clear - Hk; klist Hk)).
        -- destruct (2 * 4096 <? sz0) eqn:Eb; [apply Z.ltb_lt in Eb | apply Z.ltb_ge in Eb].
           ++ destruct (rd_pr05 R m rom sc cnt0 usage 0 sz0 P) as (R' & Hms & Q8 & Q10 & Q11 & Q13 & Q14 & _ & _ & Q19 & Q25 & QK).
              { rdscs sc E3. }
              exact (POST R' 5 Hms ltac:(unfold rd_cnt; rewrite E3; bdec) Q25 Q8 Q10 Q11 Q13 Q14 ltac:(intros k Hk; apply QK; clear - Hk; klist Hk)).
           ++ destruct (rd_pr0k R m rom sc cnt0 usage 0 sz0 P) as (R' & Hms & Q8 & Q10 & Q11 & Q13 & Q14 & _ & _ & Q19 & Q25 & QK).
              { rdscs sc E3. }
              exact (POST R' cnt0 Hms ltac:(unfold rd_cnt; rewrite E3; bdec) Q25 Q8 Q10 Q11 Q13 Q14 ltac:(intros k Hk; apply QK; clear - Hk; klist Hk)).
      * destruct (8 * 4096 <? sz0) eqn:Ea; [apply Z.ltb_lt in Ea | apply Z.ltb_ge in Ea].
        -- destruct (rd_pr1r R m rom sc cnt0 usage 0 sz0 P) as (R' & Hms & Q8 & Q10 & Q11 & Q13 & Q14 & _ & _ & _ & Q19 & Q25 & QK).
           { rdscs sc E3. }
           exact (POST R' 2 Hms ltac:(unfold rd_cnt; rewrite E3; bdec) Q25 Q8 Q10 Q11 Q13 Q14 ltac:(intros k Hk; apply QK; clear - Hk; klist Hk)).
        -- destruct (rd_pr1k R m rom sc cnt0 usage 0 sz0 P) as (R' & Hms & Q8 & Q10 & Q11 & Q13 & Q14 & _ & _ & Q19 & Q25 & QK).
           { rdscs sc E3. }
           exact (POST R' cnt0 Hms ltac:(unfold rd_cnt; rewrite E3; bdec) Q25 Q8 Q10 Q11 Q13 Q14 ltac:(intros k Hk; apply QK; clear - Hk; klist Hk)).
      * destruct (4 * 4096 <? sz0) eqn:Ea; [apply Z.ltb_lt in Ea | apply Z.ltb_ge in Ea].
        -- destruct (rd_pr2r R m rom sc cnt0 usage 0 sz0 P) as (R' & Hms & Q8 & Q10 & Q11 & Q13 & Q14 & _ & _ & _ & Q19 & Q25 & QK).
           { rdscs sc E3. }
           exact (POST R' 3 Hms ltac:(unfold rd_cnt; rewrite E3; bdec) Q25 Q8 Q10 Q11 Q13 Q14 ltac:(intros k Hk; apply QK; clear - Hk; klist Hk)).
        -- destruct (rd_pr2k R m rom sc cnt0 usage 0 sz0 P) as (R' & Hms & Q8 & Q10 & Q11 & Q13 & Q14 & _ & _ & Q19 & Q25 & QK).
           { rdscs sc E3. }
           exact (POST R' cnt0 Hms ltac:(unfold rd_cnt; rewrite E3; bdec) Q25 Q8 Q10 Q11 Q13 Q14 ltac:(intros k Hk; apply QK; clear - Hk; klist Hk)).
      * destruct (rd_pr3 R m rom sc cnt0 usage 0 sz0 P) as (R' & Hms & Q8 & Q10 & Q11 & Q13 & Q14 & _ & _ & Q19 & Q25 & QK).
        { rdscs sc E3. }
        exact (POST R' cnt0 Hms ltac:(unfold rd_cnt; rewrite E3; bdec) Q25 Q8 Q10 Q11 Q13 Q14 ltac:(intros k Hk; apply QK; clear - Hk; klist Hk)).
    + 
      destruct (rd_prdn R m rom sc cnt0 usage ns sz0 P) as (R' & Hms & Q8 & Q10 & Q11 & Q13 & Q14 & Q19 & Q25 & QK).
      { rdscs sc E3. }
      exact (POST R' cnt0 Hms ltac:(unfold rd_cnt; bdec) Q25 Q8 Q10 Q11 Q13 Q14 ltac:(intros k Hk; apply QK; clear - Hk; klist Hk)).
  - destruct (rd_prdu R m rom sc cnt0 usage ns sz0 P) as (R' & Hms & Q8 & Q10 & Q11 & Q13 & Q14 & Q19 & Q25 & QK).
    { rdscs sc E3. }
    exact (POST R' cnt0 Hms ltac:(unfold rd_cnt; bdec) Q25 Q8 Q10 Q11 Q13 Q14 ltac:(intros k Hk; apply QK; clear - Hk; klist Hk)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition iv_plan (cnt size ns req usage : Z) : Z * Z :=
  if (ns =? 0) && (cnt <=? 7) then
    let rq := page_round (req + 20) in
    if (rq <? size + 16) || ((16384 <=? rq) && (usage <? 2 * cnt)) then (1, rq) else (cnt, page_round (size * cnt + 16))
  else (cnt, page_round (size * cnt + 16)).

#[using="Type"] Lemma page_round_range : forall x, 0 <= x < 2^40 -> 0 <= page_round x < 2^41.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x Hx. unfold page_round, PGSZ. split.
  - apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia].
  - pose proof (Z.mul_div_le (x + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

#[using="Type"] Theorem seg_iv : forall R m rom cnt size ns req usage, getr R 10 = wa usage -> getr R 11 = wa 4096 -> getr R 12 = wa (size + 16) ->
  getr R 13 = wa ns -> getr R 18 = wa req -> getr R 24 = wa size -> getr R 25 = wa cnt ->
  1 <= cnt <= 32 -> 16 <= size <= 131056 -> 0 <= ns <= 1 -> 0 <= req <= 2^26 -> 0 <= usage <= 2^61 ->
  exists R', msteps SEGS (mkst R (wa 0x52924) m rom) (mkst R' (wa 0x53328) m rom) /\
    getr R' 1 = wa 338336 /\ getr R' 10 = wa 0 /\ getr R' 11 = wa (snd (iv_plan cnt size ns req usage)) /\ getr R' 12 = wa 3 /\
    getr R' 13 = wa 34 /\ getr R' 14 = wa 18446744073709551615 /\ getr R' 15 = wa 0 /\ getr R' 18 = wa 18446744073709551615 /\
    getr R' 19 = wa (snd (iv_plan cnt size ns req usage)) /\ getr R' 24 = wa size /\ getr R' 25 = wa (fst (iv_plan cnt size ns req usage)) /\
    (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 17; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%nat ->
       getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom cnt size ns req usage R10 R11 R12 R13 R18 R24 R25 Hc Hs Hns Hr Hu.
  assert (P : iv_pre R m cnt size ns req usage) by (constructor; assumption).
  assert (Lrq : (req + Z.land ((-1 * req + -20) mod 2^64) 4095) + 20 = page_round (req + 20)) by (apply pr_rq; lia).
  assert (Lsz : (Z.land ((-1 * (size * cnt) + -16) mod 2^64) 4095 + (size * cnt)) + 16 = page_round (size * cnt + 16)) by (apply pr_sz; nia).
  pose proof (page_round_range (req + 20) ltac:(lia)) as Rrq. pose proof (page_round_range (size * cnt + 16) ltac:(nia)) as Rsz.
  assert (POST : forall R' c l, msteps SEGS (mkst R (wa 0x52924) m rom) (mkst R' (wa 0x53328) m rom) ->
      (c, l) = iv_plan cnt size ns req usage ->
      getr R' 1 = wa 338336 -> getr R' 10 = wa 0 -> getr R' 11 = wa l -> getr R' 12 = wa 3 -> getr R' 13 = wa 34 ->
      getr R' 14 = wa 18446744073709551615 -> getr R' 15 = wa 0 -> getr R' 18 = wa 18446744073709551615 -> getr R' 19 = wa l ->
      getr R' 24 = wa size -> getr R' 25 = wa c ->
      (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 17; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
      exists R', msteps SEGS (mkst R (wa 0x52924) m rom) (mkst R' (wa 0x53328) m rom) /\
      getr R' 1 = wa 338336 /\ getr R' 10 = wa 0 /\ getr R' 11 = wa (snd (iv_plan cnt size ns req usage)) /\ getr R' 12 = wa 3 /\
      getr R' 13 = wa 34 /\ getr R' 14 = wa 18446744073709551615 /\ getr R' 15 = wa 0 /\ getr R' 18 = wa 18446744073709551615 /\
      getr R' 19 = wa (snd (iv_plan cnt size ns req usage)) /\ getr R' 24 = wa size /\ getr R' 25 = wa (fst (iv_plan cnt size ns req usage)) /\
      (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 17; 20; 21; 22; 23; 26; 27; 28; 29; 30; 31]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k)))).
  { intros R' c l Hms Ep Q1 Q10 Q11 Q12 Q13 Q14 Q15 Q18 Q19 Q24 Q25 QK. rewrite <- Ep. cbn [fst snd]. exists R'. repeat (split; [assumption|]). exact QK. }
  Ltac ivscs := cbn [fst snd]; repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z;
    rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z; cbn [zeval edenot]; zats; rewrite ?sllw1_small by lia;
    change (4095 mod 2^64) with 4095; change (7 mod 2^64) with 7; change (0 mod 2^64) with 0; change (16384 mod 2^64) with 16384.
  unfold iv_plan.
  destruct (Z.eq_dec ns 0) as [Ens|Ens].
  - subst ns. cbn [Z.eqb andb].
    destruct (cnt <=? 7) eqn:E7; [apply Z.leb_le in E7 | apply Z.leb_gt in E7]; cbn [andb].
    + destruct (page_round (req + 20) <? size + 16) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; cbn [orb].
      * destruct (iv_pivs R m rom cnt size 0 req usage P) as (R' & Hms & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & _ & Q18 & Q19 & Q24 & Q25 & QK).
        { ivscs; rewrite ?Lrq; rewrite ?Z.mod_small by nia; bdec. }
        exists R'. rewrite Lrq in Q11, Q19. repeat (split; [assumption|]). exact QK.
      * destruct (16384 <=? page_round (req + 20)) eqn:E2; [apply Z.leb_le in E2 | apply Z.leb_gt in E2]; cbn [andb].
        -- destruct (usage <? 2 * cnt) eqn:E3; [apply Z.ltb_lt in E3 | apply Z.ltb_ge in E3].
           ++ destruct (iv_pivu R m rom cnt size 0 req usage P) as (R' & Hms & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & _ & Q18 & Q19 & Q24 & Q25 & QK).
              { ivscs; rewrite ?Lrq; rewrite ?Z.mod_small by nia; bdec. }
              exists R'. rewrite Lrq in Q11, Q19. repeat (split; [assumption|]). exact QK.
           ++ destruct (iv_pivg R m rom cnt size 0 req usage P) as (R' & Hms & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & _ & Q18 & Q19 & Q24 & Q25 & QK).
              { ivscs; rewrite ?Lrq; rewrite ?Z.mod_small by nia; bdec. }
              exists R'. rewrite Lsz in Q11, Q19. repeat (split; [assumption|]). exact QK.
        -- destruct (iv_pivk R m rom cnt size 0 req usage P) as (R' & Hms & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & _ & Q18 & Q19 & Q24 & Q25 & QK).
           { ivscs; rewrite ?Lrq; rewrite ?Z.mod_small by nia; bdec. }
           exists R'. rewrite Lsz in Q11, Q19. repeat (split; [assumption|]). exact QK.
    + destruct (iv_pivc R m rom cnt size 0 req usage P) as (R' & Hms & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & _ & Q18 & Q19 & Q24 & Q25 & QK).
      { ivscs; rewrite ?Z.mod_small by nia; bdec. }
      exists R'. rewrite Lsz in Q11, Q19. repeat (split; [assumption|]). exact QK.
  - replace (ns =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ens). cbn [andb].
    destruct (iv_pivn R m rom cnt size ns req usage P) as (R' & Hms & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & _ & Q18 & Q19 & Q24 & Q25 & QK).
    { ivscs; rewrite ?Z.mod_small by nia; bdec. }
    exists R'. rewrite Lsz in Q11, Q19. repeat (split; [assumption|]). exact QK.
Qed.
End AG2.
