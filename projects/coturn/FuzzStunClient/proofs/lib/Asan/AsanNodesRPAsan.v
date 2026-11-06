(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesRP AsanNodesRPSoundG AsanRegionPoisoned AsanReadCheck AsanPlanImages.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac img_cell_vm :=
  intros m Hm; unfold cell8; rewrite (AsanNodesRPSoundG.rdn_img _ 8%nat m) by (first [lia | intros i Hi; apply Hm; lia]);
  apply obytes_eq_of_unsigned; vm_compute; reflexivity.

Lemma asan_rp_img : rp_img ASEGS RPN.RP_ASAN.
Proof. constructor; cbn [RPN.rp_gsb RPN.rp_csb RPN.rp_gm1 RPN.rp_cm1 RPN.rp_gm2 RPN.rp_cm2 RPN.rp_ghi RPN.rp_chi RPN.RP_ASAN]; img_cell_vm. Qed.

Lemma rp_clob_sub : forall r : bv 5, rp_clob r = true -> In (ridx r) caller_saved.
Proof.
  intros r H. unfold rp_clob in H.
  repeat (apply orb_prop in H; destruct H as [H|H]);
    apply (f_equal negb) in H; cbn [negb] in H;
    match type of H with negb (bv_eqb r ?k) = false => destruct (bv_eq_dec 5 r k) as [->|NE]; [cbn; tauto | rewrite (bv_eqb_neq _ _ NE) in H; discriminate H] end.
Qed.

Lemma asan_rp_spec : rp_spec ASEGS RPN.RP_ASAN.
Proof.
  intros mem beg n usp regs ra Hn Hbeg Hrng Husp Hdisj Hz Hstk C1 C2 C3 C4 C5 C6 C7 C8 Hret H1 H2 H10 H11.
  assert (H : rpH mem beg n usp (Z_to_bv 8 0)).
  { constructor; try assumption.
    - intros g Hg. apply Hz. lia.
    - apply Hz. split; [apply Z.div_le_mono; lia | lia].
    - left. reflexivity.
    - unfold cells, cell. repeat split; assumption. }
  destruct (as_region_is_poisoned mem (seg_rom ASEGS) beg n usp (Z_to_bv 8 0) H regs ra Hret H1 H2 H10 H11)
    as (regs' & Hms & Ha0 & Hsp & Hra & Hkeep).
  exists regs', (rp_frame mem usp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)).
  split; [|split; [|split; [exact Ha0|split]]].
  - cbn [RPN.rp_entry RPN.RP_ASAN].
    match type of Hms with msteps _ (mkst _ ?p _ _) _ => replace (Z_to_bv 64 0x569ac) with p by (apply bv_eq; reflexivity) end.
    exact Hms.
  - intros r Hr0 Hcs. destruct (bv_eq_dec 5 r 2%bv) as [->|Hne2]; [rewrite Hsp, H2; reflexivity|].
    apply Hkeep. destruct (rp_clob r) eqn:E; [|reflexivity]. exfalso. exact (Hcs (rp_clob_sub r E)).
  - intros x Hx. unfold rp_frame.
    rewrite !wbytes_out; try reflexivity; rewrite ?length_N_to_le_bytes, ?zbv_u by lia; lia.
  - unfold rp_frame. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
Lemma asan_rc_spec : rc_spec ASEGS RPN.RP_ASAN.
Proof.
  intros mem rom buf res regs Hres Hbuf Hbuf64 C1 C2 Hz H9 H10.
  destruct (as_read_check mem rom buf res Hres Hbuf Hbuf64 C1 C2 Hz regs H9 H10) as (regs' & Hms & Hrest).
  exists regs'. split; [|exact Hrest].
  cbn [RPN.rc_entry RPN.rc_exit RPN.RP_ASAN].
  match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
    replace (Z_to_bv 64 0x45fb0) with p by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 0x46008) with q by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AsanNode.
Variable nx0 : N.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.

Theorem asan_rp_ext_sound : ext_stmt ASEGS ASAN nx0 LIMIT (RPN.xn ASEGS nx0 RPN.RP_ASAN) SINV argH FS0.
Proof.
  eapply (rp_xn_sound ASEGS ASAN nx0 LIMIT); try eassumption;
    first [ exact asan_wx | exact asan_in_hull | exact asan_hull_ok | exact asan_segs_wr | exact asan_rp_img | exact asan_rp_spec | exact asan_rc_spec | idtac ].
Qed.
End AsanNode.
