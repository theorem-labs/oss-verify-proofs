(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare AgentLib.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CxPlan CxPlanSound CxPlanSoundSums.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AsanNodesRP HBRegionPoisoned HBReadCheck HBPlanImage HBAtable CxNodesRPSound HBRPTab.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxAcctShape CxNodesLibE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2 AX2S CAP CXS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma rdn_img : forall SEGS n m (a : Z),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> m (Z_to_bv 64 i) = None) ->
  rdn SEGS m (Z_to_bv 64 a) n = rdn SEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros SEGS n. induction n as [|n IH]; intros m a Ha Hn Hm; [reflexivity|].
  cbn [rdn]. rewrite (Hm a) by lia.
  rewrite zbv_add1. rewrite (IH m (a + 1)); [reflexivity | lia | lia |].
  intros i Hi. apply Hm. lia.
Qed.

(* [comment removed for export] *)
Lemma map_unsigned_inj : forall (x y : list byte), map bv_unsigned x = map bv_unsigned y -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hab Hxy. f_equal; [apply bv_eq; exact Hab | apply IH; exact Hxy].
Qed.
Lemma obytes_eq_of_unsigned : forall (x y : option (list byte)),
  option_map (map bv_unsigned) x = option_map (map bv_unsigned) y -> x = y.
Proof.
  intros [x|] [y|] H; cbn in H; try discriminate; [|reflexivity].
  injection H as H. f_equal. apply map_unsigned_inj. exact H.
Qed.
Ltac img_cell_vm :=
  intros m Hm; unfold cell8; rewrite (rdn_img _ 8 m) by (first [lia | intros i Hi; apply Hm; lia]);
  apply obytes_eq_of_unsigned; vm_compute; reflexivity.

Lemma rp_clob_sub : forall r : bv 5, rp_clob r = true -> In (ridx r) caller_saved.
Proof.
  intros r H. unfold rp_clob in H.
  repeat (apply orb_prop in H; destruct H as [H|H]);
    apply (f_equal negb) in H; cbn [negb] in H;
    match type of H with negb (bv_eqb r ?k) = false => destruct (bv_eq_dec 5 r k) as [->|NE]; [cbn; tauto | rewrite (bv_eqb_neq _ _ NE) in H; discriminate H] end.
Qed.

Lemma ha_rp_img : rp_img HASEGS RP_HA.
Proof. constructor; cbn [RPN.rp_gsb RPN.rp_csb RPN.rp_gm1 RPN.rp_cm1 RPN.rp_gm2 RPN.rp_cm2 RPN.rp_ghi RPN.rp_chi RP_HA]; img_cell_vm. Qed.


Lemma ha_rp_spec : rp_spec HASEGS RP_HA.
Proof.
  intros mem beg n usp regs ra Hn Hbeg Hrng Husp Hdisj Hz Hstk C1 C2 C3 C4 C5 C6 C7 C8 Hret H1 H2 H10 H11.
  assert (H : rpH mem beg n usp (Z_to_bv 8 0)).
  { constructor; try assumption.
    - intros g Hg. apply Hz. lia.
    - apply Hz. split; [apply Z.div_le_mono; lia | lia].
    - left. reflexivity.
    - unfold cells, cell. repeat split; assumption. }
  destruct (as_region_is_poisoned mem (seg_rom HASEGS) beg n usp (Z_to_bv 8 0) H regs ra Hret H1 H2 H10 H11)
    as (regs' & Hms & Ha0 & Hsp & Hra & Hkeep).
  exists regs', (rp_frame mem usp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)).
  split; [|split; [|split; [exact Ha0|split]]].
  - cbn [RPN.rp_entry RP_HA].
    match type of Hms with msteps _ (mkst _ ?p _ _) _ => replace (Z_to_bv 64 0x1c04bc) with p by (apply bv_eq; reflexivity) end.
    exact Hms.
  - intros r Hr0 Hcs. destruct (bv_eq_dec 5 r 2%bv) as [->|Hne2]; [rewrite Hsp, H2; reflexivity|].
    apply Hkeep. destruct (rp_clob r) eqn:E; [|reflexivity]. exfalso. exact (Hcs (rp_clob_sub r E)).
  - intros x Hx. unfold rp_frame.
    rewrite !wbytes_out; try reflexivity; rewrite ?length_N_to_le_bytes, ?zbv_u by lia; lia.
  - unfold rp_frame. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.


Lemma ha_rc_spec : rc_spec HASEGS RP_HA.
Proof.
  intros mem rom buf res regs Hres Hbuf Hbuf64 C1 C2 Hz H9 H10.
  destruct (as_read_check mem rom buf res Hres Hbuf Hbuf64 C1 C2 Hz regs H9 H10) as (regs' & Hms & Hrest).
  exists regs'. split; [|exact Hrest].
  cbn [RPN.rc_entry RPN.rc_exit RP_HA].
  match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
    replace (Z_to_bv 64 0x1aab04) with p by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 0x1aab5c) with q by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.

(* [comment removed for export] *)
Section HANode.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Hypothesis NX0_spw : CAP.expr_vars_lt nx0 e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.

Theorem ha_rp_ext_sound : ext_stmt HASEGS HAT nx0 LIMIT (RPN.xn HASEGS nx0 RP_HA) SINV argH ISP FS0.
Proof.
  exact (rp_xn_sound HASEGS HAT nx0 LIMIT hat_segs_wx hat_in_hull hat_hull_ok SINV argH ISP argH_high NX0_spw argH_agree SINV_frame SINV_agree FS0
           RP_HA ha_rp_img ha_rp_spec ha_rc_spec).
Qed.
End HANode.
