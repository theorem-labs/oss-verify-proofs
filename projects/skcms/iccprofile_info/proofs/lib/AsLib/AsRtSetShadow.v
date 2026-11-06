(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
(* [comment removed for export] *)
#[local] Ltac AsSymDrive.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac AsSymDrive.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.

#[local] Abbreviation SEGS := Asan.M.loaded_segments.

Section SetShadow.
  Variables (entry fill : Z).
  Hypothesis Hef : entry = 0x53ef4%Z /\ fill = 0%Z \/ entry = 0x54014%Z /\ fill = 0xf8%Z.

  Lemma setsh_run : forall d FPI regs mem rom ret,
    getr regs 1 = ret -> ret_ok ret -> setsh_pre SEGS as_asan d FPI regs mem ->
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 entry) mem rom) (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ frame_mod mem mem' [(d, 122%Z)]
      /\ (fill = 0%Z -> forall i, (0 <= i < 122)%Z -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0)).
  Proof.
    intros d FPI regs mem rom ret Hra Hret (Hd & H11 & Hal & Hwr & Henv).
    destruct Hwr as (Hw0 & Hwn & Hw64 & Hst).
    destruct Henv as (Hc64 & _ & _ & _).
    pose proof (Hc64 0x9eb10%Z 0xa0950%Z ltac:(cbn; tauto)) as Hg.
    pose proof (Hc64 0xa0950%Z 0x98220%Z ltac:(cbn; tauto)) as Hp. unfold acell in Hg, Hp.
    pose proof (u64_range d) as Hdr.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' =>
         regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
         frame_mod mem mem' [(d, 122%Z)] /\
         (fill = 0%Z -> forall i, (0 <= i < 122)%Z -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0))).
    set (E := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [])).
    assert (HR0 : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [])).
    assert (HR : regs_ok E (sr_upd (sr_vars 0) 11 (ELit 122)) regs).
    { apply (regs_ok_pin E _ regs 11); [exact HR0|]. cbn [edenot]. exact H11. }
    pose proof (HR0 : id _) as HRid. clear HR0. pose proof (HF : id _) as HFid.
    assert (HK : know_ok SEGS E mem [KWord (SA (ELit 0) 0x9eb10) 8 (ELit 0xa0950); KWord (SA (ELit 0) 0xa0950) 8 (ELit 0x98220);
                                    KAlign (EVar 10) 8; KWr (SA (EVar 10) 0) 122]).
    { constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9eb10 8 (ELit 0xa0950) (Z_to_bv 64 0xa0950)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
      - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa0950 8 (ELit 0x98220) (Z_to_bv 64 0x98220)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
      - apply kalign_intro; [lia|]. cbn [edenot]. ev_simpl E. rewrite Hd. exact Hal.
      - apply (kwr_intro SEGS E mem (EVar 10) d 0 122); cbn [edenot]; try lia. ev_simpl E. exact Hd.
        rewrite Z.add_0_r. exact Hst. }
    assert (FIN : forall (FPI' : FPState) (R : bvmap 5 word) (log : list sentry) sr' sfr',
      regs_ok E sr' R -> fregs_ok E sfr' (fp_regs (FPState:=FPI')) ->
      log_flat E log ->
      forallb (fun r => expr_eqb (sr_get sr' r) (sr_get (sr_vars 0) r)) abi_kept = true ->
      forallb (fun r => expr_eqb (sfr_get sfr' r) (sfr_get (sfr_vars 32) r)) abi_fkept = true ->
      sr_get sr' 1 = EVar 1 ->
      log_in_regions log [(SA (EVar 10) 0, 122%Z)] = true ->
      (fill = 0%Z -> lz_cover log (EVar 10) 0 122%nat = true) ->
      runs_to SEGS (mkst (FP:=FPI') R (Z_to_bv 64 0x98314) (mem_denot E mem log) rom)
        (fun st' => exists (FPI'0 : FPState) regs' mem',
           st' = mkst (FP:=FPI'0) regs' ret mem' rom /\
           (regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'0)) /\
            frame_mod mem mem' [(d, 122%Z)] /\
            (fill = 0%Z -> forall i, (0 <= i < 122)%Z -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0))))).
    { intros FPI' R log sr' sfr' HR' HF' Hlf Hk Hfk H1 Hreg Hcov.
      fin_ret_with HR'.
      { rewrite (HR' 1%bv), H1. cbn [edenot]. ev_simpl E. rewrite Hra. exact Hret. }
      exists FPI', R, (mem_denot E mem log). split.
      + rewrite (HR' 1%bv), H1. cbn [edenot]. ev_simpl E. rewrite Hra. reflexivity.
      + split; [exact (regs_same_on E _ _ regs R abi_kept HRid HR' Hk)|].
        split; [exact (fregs_same_on E _ _ _ _ abi_fkept HFid HF' Hfk)|].
        split.
        * replace [(d, 122%Z)] with (regions_denot E [(SA (EVar 10) 0, 122%Z)]).
          -- apply frame_mod_mem_denot; [exact Hlf | | exact Hreg].
             constructor; [|constructor]. cbn [fst snd]. unfold flat, estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hd. lia.
          -- cbn [regions_denot map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hd, v_addi_0. reflexivity.
        * intros Hf0 i Hi. rewrite <- Hd.
          change (getr regs 10) with (edenot E (EVar 10)).
          apply (mem_denot_lz_cover E mem log (EVar 10) 0 122%nat Hlf (Hcov Hf0)); cbn [edenot]; ev_simpl E; rewrite ?Hd; lia. }
    destruct Hef as [[-> ->] | [-> ->]].
    - run_fp 400%nat [0x98314%Z] noscr true. subst M.
      eapply FIN; [exact HR | exact HF | exact HLF | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | intros _; vm_compute; reflexivity].
    - run_fp 400%nat [0x98314%Z] noscr true. subst M.
      eapply FIN; [exact HR | exact HF | exact HLF | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | intros HX; discriminate HX].
  Qed.
End SetShadow.

Theorem setsh00_asan : setsh00_contract SEGS as_asan.
Proof.
  intros d FPI regs mem rom ret Hra Hret PRE.
  destruct (setsh_run 0x53ef4 0 (or_introl (conj eq_refl eq_refl)) d FPI regs mem rom ret Hra Hret PRE) as (F' & R' & M' & A & B & C & D & G).
  exists F', R', M'. split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D | exact (G eq_refl)].
Qed.

Theorem setshf8_asan : setshf8_contract SEGS as_asan.
Proof.
  intros d FPI regs mem rom ret Hra Hret PRE.
  destruct (setsh_run 0x54014 0xf8 (or_intror (conj eq_refl eq_refl)) d FPI regs mem rom ret Hra Hret PRE) as (F' & R' & M' & A & B & C & D & G).
  exists F', R', M'. split; [exact A|]. split; [exact B|]. split; [exact C|]. exact D.
Qed.
