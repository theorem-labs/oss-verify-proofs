(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import Stdio_pure.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg F_memcpy.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require RMalloc_ifaceP RDriver_facts.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessM ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PM_model.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RunDraw PU_iface PM_kit PM_iface UM_guards.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Section CopyLoop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (S A' : Z).
  Hypothesis SRNG : 0 < S /\ S + 54 < 2^64 - 1.
  Hypothesis ARNG : 0 < A' /\ A' + 54 < 2^64 - 1.
  Hypothesis SEP : S + 54 <= A' \/ A' + 54 <= S.

  Definition CINV (m1 : mem) : Prop :=
    bytes_at usegs m1 S MSG /\ (exists bs, u8arr usegs m1 A' bs /\ length bs = 54%nat) /\ munch [(A', A' + 54)] m0 m1 /\ wmono usegs m0 m1 /\ mem_inv usegs m1.

  Definition copy_post : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) (Z_to_bv 64 (S + 54)) (Z_to_bv 64 (S + 54)) (Z_to_bv 64 (A' + 54)) (Z_to_bv 64 2)
                    (Z_to_bv 64 (A' + 54)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x3cd00) fc None m' (seg_rom usegs)
      /\ CINV m'.

  Lemma src_rd : forall m1 k, bytes_at usegs m1 S MSG -> 0 <= k < 54 ->
    exists b : byte, ov_read_bytes usegs m1 (Z_to_bv 64 (S + k)) 1 = Some [b].
  Proof.
    intros m1 k B1 Hk.
    destruct (nth_error MSG (Z.to_nat k)) as [b|] eqn:E; [| apply nth_error_None in E; rewrite MSG_length in E; lia].
    exists b. eapply (u8ro_read usegs m1 S MSG k); [exact B1| exact E| lia| reflexivity].
  Qed.
  Lemma cinv_store_ok : forall m1 k, CINV m1 -> 0 <= k < 54 -> store_ok usegs m1 (Z_to_bv 64 (A' + k)) 1 = true.
  Proof. intros m1 k (_ & (bs & DST & LEN) & _) Hk. eapply (u8arr_store_ok usegs m1 A' bs k); [exact DST| rewrite LEN; lia| reflexivity]. Qed.
  Lemma cinv_store : forall m1 k (v : word), CINV m1 -> 0 <= k < 54 -> CINV (write_to_mem m1 (Z_to_bv 64 (A' + k)) (le1 v)).
  Proof.
    intros m1 k v (SRC & (bs & DST & LEN) & MU & WM & MI) Hk.
    change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]. change (Z_to_bv 64 (A' + k)) with (wa (A' + k)). unfold CINV.
    split; [| split; [| split; [| split]]].
    - apply bytes_at_write_other; [exact SRC| lia| cbn; lia| rewrite MSG_length; cbn; lia].
    - exists (upd bs (Z.to_nat k) (Z_to_bv 8 (bv_unsigned v))). split; [| rewrite upd_length; exact LEN].
      apply (u8arr_write usegs m1 A' bs k); [exact DST| rewrite LEN; lia].
    - apply munch_write; [exact MU| lia| cbn; lia| cbn; left; lia].
    - apply wmono_write. exact WM.
    - apply mem_inv_store; [exact MI|]. cbn [length]. eapply (u8arr_store_ok usegs m1 A' bs k); [exact DST| rewrite LEN; lia| reflexivity].
  Qed.
  Ltac beta_ms := lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.

  Lemma copy_loop : forall fuel k m1 (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
    Z.of_nat fuel > 54 - k -> 0 <= k < 54 -> CINV m1 ->
    evt usegs copy_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) (Z_to_bv 64 (S + k)) (Z_to_bv 64 (S + 54)) (Z_to_bv 64 (A' + k)) (Z_to_bv 64 2)
               (Z_to_bv 64 (A' + k)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3ccd8) fc None m1 (seg_rom usegs)).
  Proof.
    induction fuel as [|fuel IH]; intros k m1 t0 t1 t2 a6 a7 t3 t4 t5 t6 FU Hk INV1; [lia|].
    pose proof INV1 as (SRC & (bs & DST & LEN) & MU & WM & MI).
    zstep. if_cases G0; zify_cond G0; [exfalso; lia|].         (* [comment removed for export] *)
    zstep. if_cases G1; zify_cond G1; [exfalso; lia|].         (* [comment removed for export] *)
    destruct (src_rd m1 k SRC Hk) as [b R0].
    zstep. clear R0. beta_ms.                                  (* [comment removed for export] *)
    pose proof (cinv_store_ok m1 k INV1 Hk) as ST1. zstep. clear ST1.   (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (INV2 : CINV mx) by (exact (cinv_store m1 k (Z_to_bv 64 (bv_unsigned b)) INV1 Hk));
      remember mx as m2 eqn:Em2; clear Em2 end.
    clear SRC DST MU WM MI INV1.
    zstep. if_cases G2; zify_cond G2; [exfalso; lia|].         (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep. if_cases G3; zify_cond G3; [exfalso; lia|].         (* [comment removed for export] *)
    zstep. zstep.                                              (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    - replace (S + k + 1) with (S + (k + 1)) by lia. replace (A' + k + 1) with (A' + (k + 1)) by lia.
      apply IH; [lia| lia| exact INV2].
    - apply evt_done. unfold copy_post. exists t0, t1, t2, (Z_to_bv 64 (bv_unsigned b)), a7, t3, t4, t5, t6, m2.
      replace (S + k + 1) with (S + 54) by lia. replace (A' + k + 1) with (A' + 54) by lia.
      split; [reflexivity| exact INV2].
  Qed.
End CopyLoop.

Section Proof.
  Hypothesis ON : opnew_stmt.
  Hypothesis OD : opdelete_stmt.

  (* [comment removed for export] *)
  Theorem assign_proof : assign_stmt.
  Proof.
    unfold assign_stmt. intros until sj. intros HP AUX SPB ST LOA LOS ERR MI TP VC VSP VB HB BUF HN TIN SC SEPS A0 A1 A2 A3.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ASSIGN_STACK, OPNEW_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR. unfold ERRSTR_BYTES, ERRMSG_LEN in *.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b0, In b0 LB -> blk_addr b0 + blk_size b0 <= ATOP) by (intros b0 Hb; destruct (LBR b0 HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    pose proof (LBR _ HP TIN) as SR. cbn [blk_addr blk_size fst snd] in SR. pose proof SR as (SR1 & SR2 & SR3 & SR4 & SR5).
    assert (OUTW : forall LB0 SP0 a, 0 <= a < 2^64 -> rclient_addr LB0 SP0 a -> ~ (V <= a < V + 24) -> bv_unsigned sp + -96 <= SP0 ->
              (forall b0, In b0 LB0 -> blk_addr b0 + blk_size b0 <= ATOP) -> outside [(lo, SP0); (V, V + 24)] a).
    { intros LB0 SP0 a Ha Hc Hx HS HB0. cbn. destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia|].
      specialize (HB0 b0 Hb). lia. }
    assert (LBBx : forall b0, In b0 (lbx b LB) -> blk_addr b0 + blk_size b0 <= ATOP).
    { intros b0 Hb0. apply LBB. destruct b; [eapply lb_remove_sub; exact Hb0| exact Hb0]. }
    assert (AR : 0 <= A /\ A + n < 2^64).
    { destruct b as [p|]; cbn [vbuf] in HB; [destruct HB as [PIN NP]; destruct (LBR _ HP PIN) as (R1 & R2 & R3 & R4 & R5); cbn [blk_addr blk_size fst snd] in *; lia| lia]. }
    unfold assign_model. unfold ERRMSG_LEN.
    assert (FWB : Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) [(lo, bv_unsigned sp); (V, V + 24)])
      by (unfold RAUXV_CELL; repeat constructor; cbn; lia).
    destruct (Z_lt_le_dec n 54) as [NLT|NGE].
    2:{ (* [comment removed for export] *)
      replace (54 <=? n) with true by (symmetry; apply Z.leb_le; lia).
      destruct b as [p|]; [| destruct HB; exfalso; lia]. destruct HB as [PIN NP]. specialize (BUF NP). cbn [lbx].
      pose proof (LBR _ HP PIN) as BR. cbn [blk_addr blk_size fst snd] in BR. pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
      apply implM_ret.
      pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      carve_frame 48%nat ST.
      subst a0 a1 a2 a3. unfold PASSIGN. unfold vec_cells in VC.
      do 7 zstep. do 3 zstep.                                 (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
      replace (A + n + - A) with n by lia.
      zstep. br_dead K0.                                      (* [comment removed for export] *)
      zstep. zstep. replace (A + n + - A) with n by lia.      (* [comment removed for export] *)
      zstep. br_dead K1.                                      (* [comment removed for export] *)
      zstep. zstep. zstep.                                    (* [comment removed for export] *)
      carve_frame 48%nat ST.
      do 6 zstep. do 4 zstep.                                 (* [comment removed for export] *)
      replace (S + 54 + - S) with 54 by lia.
      zstep. br_dead K2.                                      (* [comment removed for export] *)
      do 4 zstep.                                             (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. br_dead K3.
      do 4 zstep. zstep. if_cases K4; zify_cond K4.
      2:{ exfalso. rewrite !land_ones_mod in K4. change (Z.shiftl 54 1) with (54 + 54) in K4.
          eapply (memmove_test_apart A S 54); [lia| lia| lia| lia| lia| lia| exact K4]. }
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      pose proof (rw_cells_split_CB usegs m1 A [] (Z.to_nat n) old [] [54%nat; Z.to_nat (n - 54)] BUF ltac:(cbn; lia)) as BLK2.
      cbn [app mk_CB_cells] in BLK2. clear BUF.
      apply rw_cells_app_split with (cs1 := [CB 54 (firstn 54 old)]) in BLK2 as [BLKA BLKB]. cbn [cells_size csize Nat.add] in BLKB.
      change (Z.of_nat 54) with 54 in BLKB.
      destruct (rw_cells_app_split usegs m1 S [CB 54 MSG] _ SC) as [[[_ SRC] _] _].
      cbn [cells_bytes cbytes] in SRC. rewrite app_nil_r in SRC.
      hide MU. hide WM.
      eapply evt_cut.
      { eapply memcpy_spec; rewrite ?unsigned_lit by lia; [exact SRC| rewrite MSG_length; reflexivity| exact BLKA| lia| exact MI]. }
      intros ms3 PO. destruct PO as (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m4 & -> & MU4 & WM4 & MI4 & CPY4 & _).
      rewrite ?unsigned_lit in MU4 by lia. rewrite ?unsigned_lit in CPY4 by lia.
      ret_lit.
      trm MU4 WM4.
      assert (ST4 : stk usegs m4 lo (bv_unsigned sp + -96)) by (eapply stk_transport_disjoint; [exact ST| exact MU4| exact WM4| cbn; lia]).
      clear ST MI. hide MU4. hide WM4.
      pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m4) as MU5. pose proof (wmono_refl usegs m4) as WM5.
      (* [comment removed for export] *)
      zstep.                                                                        (* [comment removed for export] *)
      zstep. if_cases G0; zify_cond G0; [exfalso; lia|].                            (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases G1; zify_cond G1; [exfalso; ubguard G1; lia|].   (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases G2; zify_cond G2; [exfalso; ubguard G2; lia|].          (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. if_cases G3; zify_cond G3; [exfalso; ubguard G3; lia|].   (* [comment removed for export] *)
      zstep. if_cases G4; zify_cond G4; [exfalso; lia|].                            (* [comment removed for export] *)
      zstep.                                                                        (* [comment removed for export] *)
      do 7 zstep. ret_lit.                                                          (* [comment removed for export] *)
      release_frame FR0 ST4 (bv_unsigned sp + -48).
      (* [comment removed for export] *)
      zstep.                                                                        (* [comment removed for export] *)
      zstep. if_cases K5; zify_cond K5.
      + (* [comment removed for export] *)
        zstep.                                                                      (* [comment removed for export] *)
        do 8 zstep.                                                                 (* [comment removed for export] *)
        release_frame FR ST4 (bv_unsigned sp).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        unhide MU. unhide WM. unhide MU4. unhide WM4.
        apply evt_done. unfold helper_post. do 15 eexists. exists m5, errv. split; [reflexivity|].
        split; [exact MI4|]. split; [exact ST4|]. split; [rewrite errno_lit; lazymatch goal with H : rw_cells usegs m5 976052 _ |- _ => exact H end|].
        split.
        { eapply rauxv_ok_frame; [| exact MU5| exact WM5| exact FWB].
          eapply rauxv_ok_frame; [| exact MU4| exact WM4| constructor; [cbn; unfold RAUXV_CELL; split; [lia| destruct BR5; [left; lia| right; lia]]| constructor]].
          eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM| exact FWB]. }
        split.
        { eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| intros a Ha Hc Hx; exact (OUTW _ _ a Ha Hc Hx ltac:(lia) LBBx)]|].
          eapply rheap_pres_x_trans.
          { eapply rheap_pres_x_of_munch; [exact MU4| exact WM4|]. intros a Ha Hc Hx. cbn.
            destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [split; [lia| exact I]| unfold ralloc_static in Hc; split; [lia| exact I]|].
            pose proof (lb_remove_sub _ _ _ Hb) as Hb'. pose proof (lb_remove_ne _ _ _ Hb) as NE.
            pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ b0 (p, A, n) HP Hb' PIN NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ.
            split; [lia| exact I]. }
          eapply rheap_pres_x_of_munch; [exact MU5| exact WM5| intros a Ha Hc Hx; exact (OUTW _ _ a Ha Hc Hx ltac:(lia) LBBx)]. }
        split; [reflexivity|]. split; [reflexivity|].
        unfold assign_K. exists A, LB. replace (Z.max n 54) with n by lia. split; [exact BR|]. split.
        { eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU5| exact WM5| repeat constructor; cbn; lia].
          eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU4| exact WM4| constructor; [right; right; exists (p, A, n); split; [exact PIN| cbn; lia]| constructor]].
          eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia]. }
        replace (54 <=? n) with true by (symmetry; apply Z.leb_le; lia). split; [repeat split; reflexivity|].
        unfold vec_cells, ERRMSG_LEN. lazymatch goal with H : rw_cells usegs m5 V _ |- _ => replace (54 + A) with (A + 54) in H by lia; exact H end.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        zstep. if_cases G5; zify_cond G5; [exfalso; ubdec G5; lia|].
        zstep.                                                                      (* [comment removed for export] *)
        do 8 zstep.                                                                 (* [comment removed for export] *)
        release_frame FR ST4 (bv_unsigned sp).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        unhide MU. unhide WM. unhide MU4. unhide WM4.
        apply evt_done. unfold helper_post. do 15 eexists. exists m5, errv. split; [reflexivity|].
        split; [exact MI4|]. split; [exact ST4|]. split; [rewrite errno_lit; lazymatch goal with H : rw_cells usegs m5 976052 _ |- _ => exact H end|].
        split.
        { eapply rauxv_ok_frame; [| exact MU5| exact WM5| exact FWB].
          eapply rauxv_ok_frame; [| exact MU4| exact WM4| constructor; [cbn; unfold RAUXV_CELL; split; [lia| destruct BR5; [left; lia| right; lia]]| constructor]].
          eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM| exact FWB]. }
        split.
        { eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| intros a Ha Hc Hx; exact (OUTW _ _ a Ha Hc Hx ltac:(lia) LBBx)]|].
          eapply rheap_pres_x_trans.
          { eapply rheap_pres_x_of_munch; [exact MU4| exact WM4|]. intros a Ha Hc Hx. cbn.
            destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [split; [lia| exact I]| unfold ralloc_static in Hc; split; [lia| exact I]|].
            pose proof (lb_remove_sub _ _ _ Hb) as Hb'. pose proof (lb_remove_ne _ _ _ Hb) as NE.
            pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ b0 (p, A, n) HP Hb' PIN NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ.
            split; [lia| exact I]. }
          eapply rheap_pres_x_of_munch; [exact MU5| exact WM5| intros a Ha Hc Hx; exact (OUTW _ _ a Ha Hc Hx ltac:(lia) LBBx)]. }
        split; [reflexivity|]. split; [reflexivity|].
        unfold assign_K. exists A, LB. replace (Z.max n 54) with n by lia. split; [exact BR|]. split.
        { eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU5| exact WM5| repeat constructor; cbn; lia].
          eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU4| exact WM4| constructor; [right; right; exists (p, A, n); split; [exact PIN| cbn; lia]| constructor]].
          eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM| repeat constructor; cbn; lia]. }
        replace (54 <=? n) with true by (symmetry; apply Z.leb_le; lia). split; [repeat split; reflexivity|].
        unfold vec_cells, ERRMSG_LEN. lazymatch goal with H : rw_cells usegs m5 V _ |- _ => replace (54 + A) with (A + 54) in H by lia; exact H end. }
    (* [comment removed for export] *)
    replace (54 <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    (* [comment removed for export] *)
    destruct b as [p|].
    { (* [comment removed for export] *)
      destruct HB as [PIN NP]. specialize (BUF NP). cbn [lbx] in *.
      pose proof (LBR _ HP PIN) as BRo. cbn [blk_addr blk_size fst snd] in BRo. pose proof BRo as (Bo1 & Bo2 & Bo3 & Bo4 & Bo5).
      pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP) as ND.
      assert (TNE : t <> p).
      { intros E. apply (nodup_ids_ne LB (t, S, 56) (p, A, n) ND TIN PIN); [| cbn; exact E]. intros EQ. injection EQ. lia. }
      assert (TIN' : In (t, S, 56) (lb_remove p LB)) by (apply in_lb_remove; [exact TIN| cbn; exact TNE]).
      apply implM_from_evt.
      pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      carve_frame 48%nat ST.
      subst a0 a1 a2 a3. unfold PASSIGN. unfold vec_cells in VC.
      do 7 zstep. do 3 zstep.
      zstep. zstep. zstep. zstep.
      replace (A + n + - A) with n by lia.
      zstep. br_dead K0.                                       (* [comment removed for export] *)
      zstep. zstep.                                            (* [comment removed for export] *)
      carve_frame 16%nat ST.
      do 4 zstep. zstep.                                       (* [comment removed for export] *)
      zstep. br_dead K1.                                       (* [comment removed for export] *)
      zstep.                                                   (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2; [exfalso; lia|].       (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      zstep. if_cases G0; zify_cond G0; [exfalso; ubdec G0; lia|].   (* [comment removed for export] *)
      zstep. zstep. zstep. replace (A + n + - A) with n by lia.  (* [comment removed for export] *)
      zstep.                                                   (* [comment removed for export] *)
      apply evt_done.
      assert (FW : Forall (fun iv => ATOP <= fst iv) [(lo, bv_unsigned sp); (V, V + 24)]) by (repeat constructor; cbn; lia).
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| exact FW]);
        assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
      end.
      clear HP AUX. hide MU. hide WM. clear BUF.
      eapply implM_bind.
      { eapply (proj1 (proj2 OD)) with (lo := lo) (B := B); try reflexivity; rewrite ?unsigned_lit by lia;
          first [exact HP1 | exact PIN | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; exact ERR) | (unfold RFREE_STACK; lia) | lia ]. }
      cbv beta. intros [] sd msd PO.
      destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & md & -> & MId & STd & ERRd & AUXd & HPRd & FAEd & SOEd & HPd).
      rewrite ?unsigned_lit in STd by lia. rewrite ?unsigned_lit in HPRd by lia. rewrite errno_lit in ERRd. unfold RERRNO in ERRd.
      ret_lit.
      assert (LBBd : forall b0, In b0 (lb_remove p LB) -> blk_addr b0 + blk_size b0 <= ATOP) by (intros b0 Hb0; apply LBB; eapply lb_remove_sub; exact Hb0).
      trp HPRd. clear ST MI ERR AUX1 HP1.
      (* [comment removed for export] *)
      apply implM_from_evt.
      pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] md) as MU1. pose proof (wmono_refl usegs md) as WM1.
      zstep. zstep. zstep.                                     (* [comment removed for export] *)
      do 4 zstep. ret_lit.                                     (* [comment removed for export] *)
      release_frame FR0 STd (bv_unsigned sp + -48).
      zstep. br_dead K3.                                       (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.                              (* [comment removed for export] *)
      zstep. lit_if.                                           (* [comment removed for export] *)
      zstep.                                                   (* [comment removed for export] *)
      zstep. zstep. zstep. lit_if.                             (* [comment removed for export] *)
      zstep. zstep.                                            (* [comment removed for export] *)
      carve_frame 32%nat STd.
      do 4 zstep. zstep. br_dead K5. do 4 zstep.
      (* [comment removed for export] *)
      apply evt_done.
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (HP1 : RHEAP sd (lb_remove p LB) mx) by (eapply RHEAP_stack_frame; [exact HPd| exact MU1| exact WM1| exact FW]);
        assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUXd| exact MU1| exact WM1| repeat constructor; cbn; lia])
      end.
      clear HPd AUXd. hide MU1. hide WM1.
      eapply implM_bind.
      { eapply ON with (lo := lo) (B := B); try reflexivity; rewrite ?unsigned_lit by lia;
          first [exact HP1 | exact AUX1 | exact STd | exact MId | (rewrite errno_lit; exact ERRd) | (unfold OPNEW_STACK, RMALLOC_STACK; lia) | lia ]. }
      cbv beta. intros p' s1' ms1 PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mq & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
      destruct RR as (A' & jk & -> & BR & HP2 & BLK & _).
      rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
      ret_lit. pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
      trp HPR. clear STd MId ERRd AUX1 HP1.
      apply implM_ret.
      pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] mq) as MU2. pose proof (wmono_refl usegs mq) as WM2.
      zstep. zstep. zstep.
      zstep. if_cases G1; zify_cond G1; [exfalso; rewrite zb_lxor_ones in G1 by lia; lia|].   (* [comment removed for export] *)
      zstep. zstep.
      do 5 zstep. ret_lit.
      release_frame FR0 ST2 (bv_unsigned sp + -48).
      (* [comment removed for export] *)
      do 4 zstep. zstep.
      do 7 zstep.
      release_frame FR ST2 (bv_unsigned sp).
      zstep.                                                   (* [comment removed for export] *)
      carve_frame 32%nat ST2.
      do 4 zstep.                                              (* [comment removed for export] *)
      zstep. zstep.                                            (* [comment removed for export] *)
      zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
      zstep. zstep. zstep. zstep.
      zstep. if_cases G3; zify_cond G3; [exfalso; ubguard G3; lia|].
      zstep. zstep. zstep.                                     (* [comment removed for export] *)
      carve_frame 16%nat ST2.
      do 4 zstep. zstep.                                       (* [comment removed for export] *)
      zstep. br_dead K6.                                       (* [comment removed for export] *)
      zstep. zstep. zstep.                                     (* [comment removed for export] *)
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      pose proof (new_block_disj _ _ _ _ _ _ _ HP2 TIN') as DJS. cbn [blk_addr blk_size fst snd] in DJS.
      destruct (rw_cells_app_split usegs m3 S [CB 54 MSG] _ SC) as [[[_ SRC] _] _].
      cbn [cells_bytes cbytes] in SRC. rewrite app_nil_r in SRC.
      pose proof (u8arr_of_cells _ _ _ BLK) as DST. cbn [cells_bytes cbytes] in DST. rewrite app_nil_r in DST.
      pose proof (rw_cells_bound _ _ _ _ BLK) as BL. cbn [cells_size csize Nat.add] in BL.
      assert (JL : length jk = 54%nat) by (destruct BLK as [[WF _] _]; cbn in WF; destruct WF as [WF _]; exact WF).
      replace (Z_to_bv 64 A') with (Z_to_bv 64 (A' + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
      hide MU2. hide WM2.
      eapply evt_cut.
      { eapply (copy_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 S A' ltac:(lia) ltac:(lia) ltac:(lia) 55%nat 0); [lia| lia|].
        split; [exact SRC|]. split; [exists jk; split; [exact DST| exact JL]|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI2]. }
      intros ms6 PO. destruct PO as (y0 & y1 & y2 & ya6 & ya7 & y3 & y4 & y5 & y6 & m6 & -> & CI6).
      destruct CI6 as (SRC6 & (bs6 & DST6 & LEN6) & MU6 & WM6 & MI6).
      trm MU6 WM6.
      assert (ST6 : stk usegs m6 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST2| exact MU6| exact WM6| cbn; lia]).
      clear ST2 MI2. hide MU6. hide WM6.
      (* [comment removed for export] *)
      pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m6) as MU7. pose proof (wmono_refl usegs m6) as WM7.
      zstep. zstep. ret_lit.                                   (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases G4; zify_cond G4; [exfalso; ubguard G4; lia|].
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases G5; zify_cond G5; [exfalso; ubguard G5; lia|].
      zstep.                                                   (* [comment removed for export] *)
      do 4 zstep. ret_lit.                                     (* [comment removed for export] *)
      release_frame FR0 ST6 (bv_unsigned sp + -32).
      zstep.                                                   (* [comment removed for export] *)
      do 5 zstep.                                              (* [comment removed for export] *)
      release_frame FR ST6 (bv_unsigned sp).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
      unhide MU. unhide WM. unhide MU1. unhide WM1. unhide MU2. unhide WM2. unhide MU6. unhide WM6.
      apply evt_done. unfold helper_post. do 15 eexists. exists m7, errv2. split; [reflexivity|].
      split; [exact MI6|]. split; [exact ST6|]. split; [rewrite errno_lit; lazymatch goal with H : rw_cells usegs m7 976052 _ |- _ => exact H end|].
      assert (FWH : Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) [(A', A' + 54)]).
      { unfold RAUXV_CELL. constructor; [| constructor]. cbn. split; [lia|]. destruct BR5; [left; lia| right; lia]. }
      split.
      { eapply rauxv_ok_frame; [| exact MU7| exact WM7| exact FWB].
        eapply rauxv_ok_frame; [| exact MU6| exact WM6| exact FWH].
        eapply rauxv_ok_frame; [| exact MU2| exact WM2| exact FWB]. exact AUX2. }
      split.
      { eapply rheap_pres_x_trans.
        { eapply rheap_pres_x_of_munch; [exact MU| exact WM|]. intros a Ha Hc Hx. exact (OUTW _ _ a Ha Hc Hx ltac:(lia) LBBd). }
        eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_pres; [exact HPRd| lia| intros b0 Hb; exact Hb]|].
        eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU1| exact WM1| intros a Ha Hc Hx; exact (OUTW _ _ a Ha Hc Hx ltac:(lia) LBBd)]|].
        eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_pres; [exact HPR| lia| intros b0 Hb; exact Hb]|].
        eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU2| exact WM2| intros a Ha Hc Hx; exact (OUTW _ _ a Ha Hc Hx ltac:(lia) LBBd)]|].
        eapply rheap_pres_x_trans.
        { eapply rheap_pres_x_of_munch; [exact MU6| exact WM6|]. intros a Ha Hc Hx. cbn.
          destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [split; [lia| exact I]| unfold ralloc_static in Hc; split; [lia| exact I]|].
          pose proof (new_block_disj _ _ _ _ _ _ b0 HP2 Hb). split; [lia| exact I]. }
        eapply rheap_pres_x_of_munch; [exact MU7| exact WM7| intros a Ha Hc Hx; exact (OUTW _ _ a Ha Hc Hx ltac:(lia) LBBd)]. }
      split; [congruence|]. split; [congruence|].
      unfold assign_K. exists A', ((p', A', 54) :: lb_remove p LB). replace (Z.max n 54) with 54 by lia. split; [exact BR|]. split.
      { eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU7| exact WM7| repeat constructor; cbn; lia].
        eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU6| exact WM6| constructor; [right; right; exists (p', A', 54); split; [left; reflexivity| cbn; lia]| constructor]].
        eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP2| exact MU2| exact WM2| repeat constructor; cbn; lia]. }
      replace (54 <=? n) with false by (symmetry; apply Z.leb_gt; lia). split; [reflexivity|].
      unfold vec_cells, ERRMSG_LEN. lazymatch goal with H : rw_cells usegs m7 V _ |- _ => replace (A' + (A' + 54 + - A')) with (A' + 54) in H by lia; exact H end. }
    (* [comment removed for export] *)
    destruct HB as [Az Nz]. subst A. cbn [lbx] in *. clear BUF.
    apply implM_retb. apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 48%nat ST.
    subst a0 a1 a2 a3. unfold PASSIGN. unfold vec_cells in VC. rewrite Nz in VC |- *. cbn [Z.add] in VC.
    do 7 zstep. do 3 zstep.
    zstep. zstep. zstep. zstep.
    zstep. br_dead K0.                                         (* [comment removed for export] *)
    zstep. zstep.                                              (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 4 zstep. zstep.
    zstep. lit_if.                                             (* [comment removed for export] *)
    do 4 zstep. ret_lit.
    release_frame FR0 ST (bv_unsigned sp + -48).
    zstep. br_dead K3.                                         (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. lit_if.                                             (* [comment removed for export] *)
    zstep.
    zstep. zstep. zstep. lit_if.
    zstep. zstep.                                              (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 4 zstep. zstep. br_dead K5. do 4 zstep.
    (* [comment removed for export] *)
    apply evt_done.
    assert (FW : Forall (fun iv => ATOP <= fst iv) [(lo, bv_unsigned sp); (V, V + 24)]) by (repeat constructor; cbn; lia).
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| exact FW]);
      assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
    end.
    clear HP AUX. hide MU. hide WM.
    eapply implM_bind.
    { eapply ON with (lo := lo) (B := B); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; exact ERR) | (unfold OPNEW_STACK, RMALLOC_STACK; lia) | lia ]. }
    cbv beta. intros p' s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
    destruct RR as (A' & jk & -> & BR & HP2 & BLK & _).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    ret_lit. pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    trp HPR. clear ST MI ERR AUX1 HP1.
    apply implM_ret.
    pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    zstep. zstep. zstep.
    zstep. if_cases G1; zify_cond G1; [exfalso; rewrite zb_lxor_ones in G1 by lia; lia|].
    zstep. zstep.
    do 5 zstep. ret_lit.
    release_frame FR0 ST2 (bv_unsigned sp + -48).
    do 4 zstep. zstep.
    do 7 zstep.
    release_frame FR ST2 (bv_unsigned sp).
    zstep.
    carve_frame 32%nat ST2.
    do 4 zstep.
    zstep. zstep.
    zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
    zstep. zstep. zstep. zstep.
    zstep. if_cases G3; zify_cond G3; [exfalso; ubguard G3; lia|].
    zstep. zstep. zstep.
    carve_frame 16%nat ST2.
    do 4 zstep. zstep.
    zstep. br_dead K6.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    pose proof (new_block_disj _ _ _ _ _ _ _ HP2 TIN) as DJS. cbn [blk_addr blk_size fst snd] in DJS.
    destruct (rw_cells_app_split usegs m3 S [CB 54 MSG] _ SC) as [[[_ SRC] _] _].
    cbn [cells_bytes cbytes] in SRC. rewrite app_nil_r in SRC.
    pose proof (u8arr_of_cells _ _ _ BLK) as DST. cbn [cells_bytes cbytes] in DST. rewrite app_nil_r in DST.
    pose proof (rw_cells_bound _ _ _ _ BLK) as BL. cbn [cells_size csize Nat.add] in BL.
    assert (JL : length jk = 54%nat) by (destruct BLK as [[WF _] _]; cbn in WF; destruct WF as [WF _]; exact WF).
    replace (Z_to_bv 64 A') with (Z_to_bv 64 (A' + 0)) by (f_equal; lia).
    replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
    hide MU2. hide WM2.
    eapply evt_cut.
    { eapply (copy_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 S A' ltac:(lia) ltac:(lia) ltac:(lia) 55%nat 0); [lia| lia|].
      split; [exact SRC|]. split; [exists jk; split; [exact DST| exact JL]|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI2]. }
    intros ms6 PO. destruct PO as (y0 & y1 & y2 & ya6 & ya7 & y3 & y4 & y5 & y6 & m6 & -> & CI6).
    destruct CI6 as (SRC6 & (bs6 & DST6 & LEN6) & MU6 & WM6 & MI6).
    trm MU6 WM6.
    assert (ST6 : stk usegs m6 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST2| exact MU6| exact WM6| cbn; lia]).
    clear ST2 MI2. hide MU6. hide WM6.
    pose proof (munch_refl [(lo, bv_unsigned sp); (V, V + 24)] m6) as MU7. pose proof (wmono_refl usegs m6) as WM7.
    zstep. zstep. ret_lit.
    zstep. zstep. zstep. if_cases G4; zify_cond G4; [exfalso; ubguard G4; lia|].
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases G5; zify_cond G5; [exfalso; ubguard G5; lia|].
    zstep.
    do 4 zstep. ret_lit.
    release_frame FR0 ST6 (bv_unsigned sp + -32).
    zstep.
    do 5 zstep.
    release_frame FR ST6 (bv_unsigned sp).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    unhide MU. unhide WM. unhide MU2. unhide WM2. unhide MU6. unhide WM6.
    apply evt_done. unfold helper_post. do 15 eexists. exists m7, errv2. split; [reflexivity|].
    split; [exact MI6|]. split; [exact ST6|]. split; [rewrite errno_lit; lazymatch goal with H : rw_cells usegs m7 976052 _ |- _ => exact H end|].
    assert (FWH : Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) [(A', A' + 54)]).
    { unfold RAUXV_CELL. constructor; [| constructor]. cbn. split; [lia|]. destruct BR5; [left; lia| right; lia]. }
    split.
    { eapply rauxv_ok_frame; [| exact MU7| exact WM7| exact FWB].
      eapply rauxv_ok_frame; [| exact MU6| exact WM6| exact FWH].
      eapply rauxv_ok_frame; [| exact MU2| exact WM2| exact FWB]. exact AUX2. }
    split.
    { eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| intros a Ha Hc Hx; exact (OUTW _ _ a Ha Hc Hx ltac:(lia) LBB)]|].
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_pres; [exact HPR| lia| intros b0 Hb; exact Hb]|].
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU2| exact WM2| intros a Ha Hc Hx; exact (OUTW _ _ a Ha Hc Hx ltac:(lia) LBB)]|].
      eapply rheap_pres_x_trans.
      { eapply rheap_pres_x_of_munch; [exact MU6| exact WM6|]. intros a Ha Hc Hx. cbn.
        destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [split; [lia| exact I]| unfold ralloc_static in Hc; split; [lia| exact I]|].
        pose proof (new_block_disj _ _ _ _ _ _ b0 HP2 Hb). split; [lia| exact I]. }
      eapply rheap_pres_x_of_munch; [exact MU7| exact WM7| intros a Ha Hc Hx; exact (OUTW _ _ a Ha Hc Hx ltac:(lia) LBB)]. }
    split; [exact FAE|]. split; [exact SOE|].
    unfold assign_K. exists A', ((p', A', 54) :: LB). replace (Z.max n 54) with 54 by lia. split; [exact BR|]. split.
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU7| exact WM7| repeat constructor; cbn; lia].
      eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU6| exact WM6| constructor; [right; right; exists (p', A', 54); split; [left; reflexivity| cbn; lia]| constructor]].
      eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP2| exact MU2| exact WM2| repeat constructor; cbn; lia]. }
    replace (54 <=? n) with false by (symmetry; apply Z.leb_gt; lia). split; [reflexivity|].
    unfold vec_cells, ERRMSG_LEN. lazymatch goal with H : rw_cells usegs m7 V _ |- _ => replace (A' + (A' + 54 + - A')) with (A' + 54) in H by lia; exact H end.
  Qed.
End Proof.
End CANSEC1.
