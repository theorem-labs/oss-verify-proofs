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
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg F_memcpy.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessM ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RunDraw PU_iface PM_kit PM_model PM_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.

Section Proof.
  Hypothesis ON : opnew_stmt.
  Theorem strctor_proof : strctor_stmt.
  Proof.
    unfold strctor_stmt. intros until tj. intros HP AUX SPB ST LOA LOS ERR MI TP TC TSP TB A0 A1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold STRCTOR_STACK, OPNEW_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (T, T + 24)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    carve_frame 48%nat ST.
    subst a0 a1. unfold PSTRCTOR.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP) by (intros b Hb; destruct (LBR b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    clear LBR.
    assert (OUTW : forall LB0 SP0 a, 0 <= a < 2^64 -> rclient_addr LB0 SP0 a -> ~ (T <= a < T + 24) -> bv_unsigned sp + -48 <= SP0 ->
              (forall b, In b LB0 -> blk_addr b + blk_size b <= ATOP) -> outside [(lo, SP0); (T, T + 24)] a).
    { intros LB0 SP0 a Ha Hc Hx HS HB. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia|].
      specialize (HB b Hb). lia. }
    do 7 zstep.
    do 4 zstep.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply strlen_msg; exact MI|].
    intros ms1 PO. destruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & ->). ret_lit. unfold ERRMSG_LEN.
    zstep. zstep. br_dead K0.
    do 3 zstep. br_dead K1.
    do 2 zstep. lit_if.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply evt_done.
    assert (FW : Forall (fun iv => ATOP <= fst iv) [(lo, bv_unsigned sp); (T, T + 24)]) by (repeat constructor; cbn; lia).
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| exact FW]);
      assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
    end.
    clear HP AUX. hide MU. hide WM.
    eapply implM_post_evt'.
    { eapply ON with (lo := lo) (B := B); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; exact ERR) | (unfold OPNEW_STACK, RMALLOC_STACK; lia) | (unfold ERRSTR_BYTES; lia) ]. }
    cbv beta. intros t s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
    destruct RR as (A & jk & -> & BR & HP2 & BLK & _).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    ret_lit. unfold ERRSTR_BYTES in *.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    trp HPR. clear ST MI ERR AUX1 HP1.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp); (T, T + 24)] m2) as MU2. pose proof (wmono_refl psegs m2) as WM2.
    do 5 zstep.
    do 4 zstep.
    (* [comment removed for export] *)
    zstep. unfold PMSG. br_dead K2.
    do 4 zstep. zstep. if_cases K3; zify_cond K3.
    2:{ exfalso. rewrite !land_ones_mod in K3. change 108 with (54 + 54) in K3.
        eapply (memmove_test_apart A PMSG 54); [unfold PMSG; lia| lia| lia| unfold PMSG; lia| lia| unfold PMSG; lia| exact K3]. }
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (ROM : bytes_at psegs m3 PMSG MSG).
    { pose proof (ro_cells_image psegs m3 PMSG MSG MI2 MSG_ro ltac:(unfold PMSG; lia) ltac:(rewrite MSG_length; unfold PMSG; cbn; lia)) as [_ RB].
      cbn [cells_bytes cbytes] in RB. rewrite app_nil_r in RB. exact RB. }
    pose proof (rw_cells_split_CB psegs m3 A [] 56 jk [] [54%nat; 2%nat] BLK eq_refl) as BLK2. cbn [app mk_CB_cells] in BLK2. clear BLK.
    apply rw_cells_app_split with (cs1 := [CB 54 (firstn 54 jk)]) in BLK2 as [BLKA BLKB]. cbn [cells_size csize Nat.add] in BLKB.
    change (Z.of_nat 54) with 54 in BLKB.
    hide MU2. hide WM2.
    eapply evt_cut.
    { eapply memcpy_spec; rewrite ?unsigned_lit by lia; [unfold PMSG in ROM |- *; exact ROM| rewrite MSG_length; reflexivity| exact BLKA| unfold PMSG; lia| exact MI2]. }
    intros ms3 PO. destruct PO as (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m4 & -> & MU4 & WM4 & MI4 & CPY4 & _).
    rewrite ?unsigned_lit in MU4 by lia. rewrite ?unsigned_lit in CPY4 by lia.
    ret_lit.
    trm MU4 WM4.
    assert (ST4 : stk psegs m4 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST2| exact MU4| exact WM4| cbn; lia]).
    clear ST2 MI2. hide MU4. hide WM4.
    (* [comment removed for export] *)
    pose proof (munch_refl [(A + 54, A + 56)] m4) as MU5. pose proof (wmono_refl psegs m4) as WM5.
    lazymatch type of BLKB with rw_cells _ _ _ [CB 2 ?r] =>
      pose proof (rw_cells_split_CB psegs m4 (A + 54) [] 2 r [] [1%nat; 1%nat] BLKB eq_refl) as BLKC end. cbn [app mk_CB_cells] in BLKC. clear BLKB.
    zstep. zstep.
    do 8 zstep.
    release_frame FR ST4 (bv_unsigned sp).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    unhide MU2. unhide WM2. unhide MU4. unhide WM4. unhide MU. unhide WM.
    apply evt_done. unfold helper_post. do 15 eexists. exists m5, errv2. split; [reflexivity|].
    split; [| split; [exact ST4|]]. { lazymatch goal with H : mem_inv psegs m5 |- _ => exact H end. }
    split; [rewrite errno_lit; lazymatch goal with H : rw_cells psegs m5 932228 _ |- _ => exact H end|].
    assert (FWB : Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv))
                    [(lo, bv_unsigned sp); (T, T + 24)]) by (unfold RAUXV_CELL; repeat constructor; cbn; lia).
    assert (FWH : forall a e, A <= a -> e <= A + 56 -> Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) [(a, e)]).
    { intros a e H1 H2. unfold RAUXV_CELL. constructor; [| constructor]. cbn. split; [lia|]. destruct BR5; [left; lia| right; lia]. }
    split.
    { eapply rauxv_ok_frame; [| exact MU5| exact WM5| apply FWH; lia].
      eapply rauxv_ok_frame; [| exact MU4| exact WM4| apply FWH; lia].
      eapply rauxv_ok_frame; [| exact MU2| exact WM2| exact FWB].
      exact AUX2. }
    assert (OUTH : forall a x e, 0 <= a < 2^64 -> rclient_addr LB (bv_unsigned sp) a -> A <= x -> e <= A + 56 -> outside [(x, e)] a).
    { intros a x e Ha Hc H1 H2. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [split; [lia| exact I]| unfold ralloc_static in Hc; split; [lia| exact I]|].
      pose proof (new_block_disj _ _ _ _ _ _ b HP2 Hb). split; [lia| exact I]. }
    split.
    { eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]|].
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_pres; [exact HPR| lia| intros b Hb; exact Hb]|].
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU2| exact WM2| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]|].
      eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU4| exact WM4| intros a Ha Hc Hx; apply (OUTH a A (A + 54) Ha Hc); lia]|].
      eapply rheap_pres_x_of_munch; [exact MU5| exact WM5| intros a Ha Hc Hx; apply (OUTH a (A + 54) (A + 56) Ha Hc); lia]. }
    split; [exact FAE|]. split; [exact SOE|].
    unfold strctor_K. exists A.
    lazymatch goal with H : rw_cells psegs m5 (A + 54) [C1 _; CB 1 ?jb] |- _ => exists jb end.
    split; [exact BR|]. split.
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU5| exact WM5| constructor; [right; right; exists (t, A, 56); split; [left; reflexivity| cbn; lia]| constructor]].
      eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU4| exact WM4| constructor; [right; right; exists (t, A, 56); split; [left; reflexivity| cbn; lia]| constructor]].
      eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP2| exact MU2| exact WM2| repeat constructor; cbn; lia]. }
    split.
    { match goal with H1 : rw_cells psegs m5 A [CB _ MSG], H2 : rw_cells psegs m5 (A + 54) ?cs |- _ =>
        change (Z.to_nat 54) with 54%nat in H1;
        pose proof (rw_cells_app_join psegs m5 A [CB 54 MSG] cs H1 H2) as J; cbn [app] in J; exact J end. }
    unfold lstr_cells, ERRSTR_BYTES, ERRMSG_LEN. lazymatch goal with H : rw_cells psegs m5 T _ |- _ => exact H end.
  Qed.
End Proof.
End CANSEC1.
