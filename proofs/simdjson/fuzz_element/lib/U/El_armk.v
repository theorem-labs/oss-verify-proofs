(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_iface F_memcmp F_strncasecmp Atp_pid Atp_defs Atp_h_defs El_defs El_hdr El_h2 El_h3 El_act El_key.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition key_arm_row (a pc base centry : Z) : Prop :=
  (a = 25 /\ pc = 0x3c324 /\ base = EL_ATKEY /\ centry = bcmp_entry) \/
  (a = 29 /\ pc = 0x3c354 /\ base = EL_ATKEY2 /\ centry = bcmp_entry) \/
  (a = 30 /\ pc = 0x3c3b0 /\ base = EL_ATKEYCI /\ centry = EL_STRNCASECMP).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Ltac zlits := repeat match goal with |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v end.

#[local] Set Default Goal Selector "all".

Theorem key_arm : forall a pc base centry, key_arm_row a pc base centry -> cmp_stmt centry -> arm_stmt a pc.
Proof.
  intros a pc base centry KROW CMP.
  assert (ROW : key_row base centry) by (unfold key_row; destruct KROW as [(_ & _ & -> & ->)|[(_ & _ & -> & ->)|(_ & _ & -> & ->)]]; auto).
  unfold arm_stmt. intros until p50. intros EA AE HK.
  pose proof AE as AE'.
  destruct AE' as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & PRES & SJS & PL & FD
                   & VR & NTH0 & J0 & RES & OS & ROOT & PA0 & PIMPL & PA16 & DCAP & P48 & THIS & XSEL & XFD & SAVE).
  unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  assert (PTRF : (0 < zlength (ae_p1 E) -> 0 < ae_PTR E) /\ ae_PTR E + zlength (ae_p1 E) <= ae_lo E).
  { destruct (el_els_shape D d) as (P0 & P1 & rest & ELS & V0 & _). rewrite ELS in NTH0. cbn [nth] in NTH0. apply (f_equal fst) in NTH0. cbn [fst] in NTH0.
    rewrite EP1, ELO, <- NTH0. pose proof (el_rem_fd d FD) as [_ ZR]. unfold view_of in V0. unfold zlength in ZR |- *.
    destruct V0 as [[V1 V2]|(o & V1 & _ & OL)].
    - rewrite V1, V2. cbn [length]. lia.
    - rewrite V1. unfold payload_ok in PL. destruct PL as (_ & _ & D0 & _ & _ & [DN| (bk & Hb & B1 & B2)]).
      + rewrite DN in ZR. cbn [length] in ZR. lia.
      + pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (R1 & R2 & R3 & R4 & R5).
        unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in R4. unfold zlength in B2. lia. }

  destruct KROW as [(-> & -> & HB & HC)|[(-> & -> & HB & HC)|(-> & -> & HB & HC)]];
    unfold el_act, el_throwing; rewrite EA; cbn [Z.eqb Pos.eqb orb]; apply implM_ret_bind.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold implM. iprefix.

  step. step. step. step. step.
  rewrite <- EP1.
  eapply evt_cut;
    [ eapply evt_eq; [| eapply (key_spec E OK base centry ROW CMP) with (s := st) (lo := lo) (q := sp0)];
        [ unfold EL_ATKEY, EL_ATKEY2, EL_ATKEYCI in HB; atp_st_eq
        | exact AI| exact ROOT| exact HEAP| exact MI| exact FRM| exact RES| lia| rewrite EB; lia| lia| rewrite EB; lia| rewrite EDOC; lia
        | exact ST| rewrite ELO; lia| lia| exact (proj1 PTRF)| exact (proj2 PTRF) ] |].
  cbv beta. intros ms2 PO. unfold key_post in PO.
  destruct PO as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & b10 & b11 & b12 & b13 & b14 & F' & fc' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FRM2
                  & (w0 & w1 & ew & od & RES2 & _)).
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  destruct (rw_cells_forget _ _ _ _ RES2) as [jres' RES2']. cbn [cells_size csize Nat.add] in RES2'.
  assert (MU2' : munch [(lo, sp0); (sp0 + 8, sp0 + 296)]%Z m m2) by (eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros x Hx; lia).
  pose proof (agree_on_of_munch _ _ _ MU2 WM2) as AG2.
  apply (rw_cells_agree _ _ _ _ _ AG2) in OS; [| intros y Hy; cbn in Hy; cbn [outside]; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in ERR; [| intros y Hy; cbn in Hy; cbn [outside]; unfold LX_ERRNO, RATP in Hy; lia].
  assert (HEAP2 : RHEAP st (ae_LB E) m2)
    by (eapply LH_frame; [exact HEAP| exact MU2| exact WM2|]; constructor; [apply W_ok_stack; cbn; lia| constructor; [apply W_ok_stack; cbn; lia| constructor]]).
  destruct (act_env_call E m0 m m2 s00 st st LB D d sp0 lo B errv errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos jres' jos j313 j329 j361 j416 j441
              nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc fc' AE MU2' WM2 MI2 ST2 HEAP2 eq_refl eq_refl ERR RES2' OS FRM2) as (AE2 & _ & _).

  clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
  step.
  ihere. apply HK. unfold EL_EXIT in *.
  eapply act_post_here; [exact AE2| reflexivity| reflexivity].
Qed.

#[local] Set Default Goal Selector "1".

Theorem arm25_proof : arm_stmt 25 0x3c324.
Proof. apply (key_arm 25 0x3c324 EL_ATKEY bcmp_entry); [unfold key_arm_row; left; auto| apply bcmp_cmp]. Qed.
Theorem arm29_proof : arm_stmt 29 0x3c354.
Proof. apply (key_arm 29 0x3c354 EL_ATKEY2 bcmp_entry); [unfold key_arm_row; right; left; auto| apply bcmp_cmp]. Qed.

Lemma sncc_cmp : cmp_stmt EL_STRNCASECMP.
Proof.
  unfold cmp_stmt, EL_STRNCASECMP. intros until bq. intros LEN P0 Q0 PH QH DISJ BP BQ MI ST LOSP SPH _.
  eapply evt_cut; [eapply (sncc_spec_s ra gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sp lo p q bp bq); assumption|].
  cbv beta. intros ms' (r & a1' & a2' & m' & -> & MU & WM & MI' & ST').
  apply evt_done. exists r, a1', a2', a3, a4, m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'| exact ST'].
Qed.
Theorem arm30_proof : arm_stmt 30 0x3c3b0.
Proof. apply (key_arm 30 0x3c3b0 EL_ATKEYCI EL_STRNCASECMP); [unfold key_arm_row; do 2 right; auto| apply sncc_cmp]. Qed.
End WithCeiling0.
