(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanSizeLog
  AsanPlanImages AsanNodesRP AsanRegionPoisoned AsanReadCheck AsanQckCheck AsanNodesRPSound AsanMaxVA AsanInit AsanStartup AsanMainClosed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

Section FPW_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
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
  intros mem beg n usp regs ra Hn Hbeg Hrng Husp Hdisj Hz b1 Hb1 Hb1v Hstk C1 C2 C3 C4 C5 C6 C7 C8 Hret H1 H2 H10 H11.
  assert (H : rpH mem beg n usp b1).
  { constructor; try assumption.
    unfold cells, cell. repeat split; assumption. }
  destruct (as_region_is_poisoned mem (seg_rom ASEGS) beg n usp b1 H regs ra Hret H1 H2 H10 H11)
    as (regs' & Hms & Ha0 & Hsp & Hra & Hkeep).
  exists regs', (rp_frame mem usp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)).
  split; [|split; [|split; [exact Ha0|split]]].
  - cbn [RPN.rp_entry RPN.RP_ASAN].
    match type of Hms with msteps _ (mkst _ ?p _ _) _ => replace (Z_to_bv 64 0x77fe8) with p by (apply bv_eq; reflexivity) end.
    exact Hms.
  - intros r Hr0 Hcs. destruct (bv_eq_dec 5 r 2%bv) as [->|Hne2]; [rewrite Hsp, H2; reflexivity|].
    apply Hkeep. destruct (rp_clob r) eqn:E; [|reflexivity]. exfalso. exact (Hcs (rp_clob_sub r E)).
  - intros x Hx. unfold rp_frame.
    rewrite !wbytes_out; try reflexivity; rewrite ?length_N_to_le_bytes, ?zbv_u by lia; lia.
  - unfold rp_frame. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

Lemma asan_rc_spec : rc_spec ASEGS RPN.RP_ASAN.
Proof.
  intros mem rom buf res regs Hres Hbuf Hbuf64 C1 C2 Hz H9 H10.
  destruct (as_read_check mem rom buf res Hres Hbuf Hbuf64 C1 C2 Hz regs H9 H10) as (regs' & Hms & Hrest).
  exists regs'. split; [|exact Hrest].
  cbn [RPN.rc_entry RPN.rc_exit RPN.RP_ASAN].
  match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
    replace (Z_to_bv 64 0x62b84) with p by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 0x62bdc) with q by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.



Lemma asan_qc_src : qc_spec ASEGS RPN.RP_ASAN 0x75a2c 0x75a64 (Z_to_bv 5 11) (Z_to_bv 5 19).
Proof.
  intros mem rom beg n b1 regs Hn Hbeg Hbeg64 C1 C2 Hrdw Hz Hlast Hb1 H11 H12 H19.
  replace (Z_to_bv 5 11) with (11%bv : bv 5) in * by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 19) with (19%bv : bv 5) in * by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 12) with (12%bv : bv 5) in * by (apply bv_eq; reflexivity).
  destruct (qc_src_run mem rom beg n b1 Hn Hbeg Hbeg64 C1 C2 Hrdw Hz Hlast Hb1 regs H11 H12 H19) as (regs' & Hms & P & Pother).
  exists regs'. split; [|split; [exact P | exact Pother]].
  match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
    replace (Z_to_bv 64 0x75a2c) with p by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 0x75a64) with q by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.

Lemma asan_qc_dst : qc_spec ASEGS RPN.RP_ASAN 0x75a74 0x75aac (Z_to_bv 5 10) (Z_to_bv 5 20).
Proof.
  intros mem rom beg n b1 regs Hn Hbeg Hbeg64 C1 C2 Hrdw Hz Hlast Hb1 H10 H12 H20.
  replace (Z_to_bv 5 10) with (10%bv : bv 5) in * by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 20) with (20%bv : bv 5) in * by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 12) with (12%bv : bv 5) in * by (apply bv_eq; reflexivity).
  destruct (qc_dst_run mem rom beg n b1 Hn Hbeg Hbeg64 C1 C2 Hrdw Hz Hlast Hb1 regs H10 H12 H20) as (regs' & Hms & P & Pother).
  exists regs'. split; [|split; [exact P | exact Pother]].
  match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
    replace (Z_to_bv 64 0x75a74) with p by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 0x75aac) with q by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.

(* [comment removed for export] *)
Lemma asan_msb_spec : msb_spec ASEGS RPN.RP_ASAN.
Proof.
  intros mem rom s1 wz bs regs Hs0 Hs56 Hrd Hbs Hwz H9.
  assert (Hs1 : 0 <= s1 /\ s1 + 48 + 8 < 2 ^ 64) by lia.
  assert (H9' : PropExec.getr regs 9%bv = Z_to_bv 64 s1) by (replace (9%bv : bv 5) with (Z_to_bv 5 9) by (apply bv_eq; reflexivity); exact H9).
  destruct (as_msb_block mem rom s1 wz bs Hs1 Hrd Hbs Hwz regs H9') as (regs' & Hms & Hv & H14 & Hoth).
  exists regs'. split; [|split; [|split]].
  - match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
      replace (Z_to_bv 64 (RPN.msb_entry RPN.RP_ASAN)) with p by (apply bv_eq; reflexivity);
      replace (Z_to_bv 64 (RPN.msb_exit RPN.RP_ASAN)) with q by (apply bv_eq; reflexivity) end.
    exact Hms.
  - replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity).
    destruct (RPN.msb_regs (getr regs 18%bv) (Z_to_bv 64 wz)) as [[[[v11 v12] v15] v16] v19] eqn:Hm.
    destruct Hv as (_ & _ & _ & _ & H19). rewrite H19. reflexivity.
  - replace (Z_to_bv 5 14) with (14%bv : bv 5) by (apply bv_eq; reflexivity). exact H14.
  - intros r N11 N12 N14 N15 N16 N19. apply Hoth;
      [ replace (11%bv : bv 5) with (Z_to_bv 5 11) by (apply bv_eq; reflexivity)
      | replace (12%bv : bv 5) with (Z_to_bv 5 12) by (apply bv_eq; reflexivity)
      | replace (14%bv : bv 5) with (Z_to_bv 5 14) by (apply bv_eq; reflexivity)
      | replace (15%bv : bv 5) with (Z_to_bv 5 15) by (apply bv_eq; reflexivity)
      | replace (16%bv : bv 5) with (Z_to_bv 5 16) by (apply bv_eq; reflexivity)
      | replace (19%bv : bv 5) with (Z_to_bv 5 19) by (apply bv_eq; reflexivity) ]; assumption.
Qed.

(* [comment removed for export] *)
Lemma asan_segs_wr' : segs_wr_ok ASEGS.
Proof.
  intros seg Hin Hw. unfold ASEGS in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hw] |]). destruct Hin.
Qed.

Lemma asan_ls_spec : ls_spec ASEGS RPN.RP_ASAN.
Proof.
  intros mem rom s1 idx regs Hs0 Hs616 Hidx Hwr Hrd8 H9 H11.
  assert (H9' : PropExec.getr regs 9%bv = Z_to_bv 64 s1) by (replace (9%bv : bv 5) with (Z_to_bv 5 9) by (apply bv_eq; reflexivity); exact H9).
  assert (H11' : PropExec.getr regs 11%bv = Z_to_bv 64 idx) by (replace (11%bv : bv 5) with (Z_to_bv 5 11) by (apply bv_eq; reflexivity); exact H11).
  destruct (as_ls_block mem rom s1 idx (conj Hs0 Hs616) Hidx Hwr Hrd8 regs H9' H11') as (regs' & mem' & Hms & Hoth & Hmem).
  exists regs', mem'. split; [|split; [|exact Hmem]].
  - match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
      replace (Z_to_bv 64 (RPN.ls_entry RPN.RP_ASAN)) with p by (apply bv_eq; reflexivity);
      replace (Z_to_bv 64 (RPN.ls_exit RPN.RP_ASAN)) with q by (apply bv_eq; reflexivity) end.
    exact Hms.
  - intros r N11 N12 N13. apply Hoth;
      [ replace (11%bv : bv 5) with (Z_to_bv 5 11) by (apply bv_eq; reflexivity)
      | replace (12%bv : bv 5) with (Z_to_bv 5 12) by (apply bv_eq; reflexivity)
      | replace (13%bv : bv 5) with (Z_to_bv 5 13) by (apply bv_eq; reflexivity) ]; assumption.
Qed.

(* [comment removed for export] *)
Section AsanNode.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable LINV : (word -> option byte) -> Prop.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis nx0_ge : APS.nx0_ok nx0.   (* [comment removed for export] *)
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis LINV_frame : forall M M' : word -> option byte, (forall a : word, in_lfp ASAN (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M'.
Variable FS0 : Fs.Fs.
Hypothesis QS : qc_spec ASEGS RPN.RP_ASAN 0x75a2c 0x75a64 (Z_to_bv 5 11) (Z_to_bv 5 19).
Hypothesis QD : qc_spec ASEGS RPN.RP_ASAN 0x75a74 0x75aac (Z_to_bv 5 10) (Z_to_bv 5 20).
Hypothesis MS : msb_spec ASEGS RPN.RP_ASAN.
Hypothesis MV : mv_spec ASEGS RPN.RP_ASAN.   (* [comment removed for export] *)
Hypothesis LS : ls_spec ASEGS RPN.RP_ASAN.
Hypothesis WR : segs_wr_ok ASEGS.

Theorem asan_rp_ext_sound : ext_stmt ASEGS ASAN nx0 LIMIT (RPN.xn ASEGS ASAN nx0 RPN.RP_ASAN) SINV argH LINV FS0.
Proof.
  assert (HSB : img_hi ASAN <= RPN.SB) by (vm_compute; discriminate || (cbv; lia)).
  exact (rp_xn_sound ASEGS ASAN nx0 LIMIT asan_wx asan_in_hull asan_hull_ok SINV argH LINV argH_high argH_agree nx0_ge SINV_frame SINV_agree LINV_frame FS0
           RPN.RP_ASAN HSB asan_rp_img asan_rp_spec asan_rc_spec QS QD MS MV LS WR).
Qed.
End AsanNode.
End FPW_1.

(* [comment removed for export] *)
Theorem xrp_sound : forall LINV : (word -> option byte) -> Prop, LINV_STMT LINV -> XRP_STMT LINV.
Proof.
  intros LINV [_ HF] fx nx0 LIMIT SINV argH aH aA aT NG sF sA FS0.
  exact (asan_rp_ext_sound nx0 LIMIT SINV argH LINV aH aA NG sF sA HF FS0 asan_qc_src asan_qc_dst asan_msb_spec as_maxva_spec asan_ls_spec asan_segs_wr').   (* [comment removed for export] *)
Qed.
