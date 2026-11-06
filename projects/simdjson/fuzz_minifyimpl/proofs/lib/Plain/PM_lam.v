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
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require RMalloc_ifaceP RDriver_facts.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessM ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RunDraw PU_iface PM_kit PM_model PM_minify PM_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Section Proof.
  Hypothesis VCT : vctor_stmt.
  Hypothesis STR : strctor_stmt.
  Hypothesis ASG : assign_stmt.
  Hypothesis OD : opdelete_stmt.

  Theorem lam_proof : lam_stmt.
  Proof.
    unfold lam_stmt. intros until rj. intros HP AUX SPB ST LOA LOS ERR MI TP CI FB RC RSP0 RB CC CSP CB16 RCX DAT PLB DCR DRX D0 DTOP NLT A0 A1 A2.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold LAM_STACK, ASSIGN_STACK, OPNEW_STACK, RMALLOC_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    set (n := zlength pl) in *.
    assert (N0 : 0 <= n) by (unfold n, zlength; lia).
    destruct CI as (CI1 & CI2 & CI3 & CI4). unfold PFALLBACK, PFALLBACK_VT in FB.
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b0, In b0 LB -> blk_addr b0 + blk_size b0 <= ATOP) by (intros b0 Hb; destruct (LBR b0 HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    assert (LBPOS : forall b0, In b0 LB -> 0 < blk_addr b0) by (intros b0 Hb; destruct (LBR b0 HP Hb) as (R1 & _); exact R1).
    assert (OUTW : forall LB0 SP0 a, 0 <= a < 2^64 -> rclient_addr LB0 SP0 a -> ~ (R <= a < R + 24) -> bv_unsigned sp + -64 <= SP0 ->
              (forall b0, In b0 LB0 -> blk_addr b0 + blk_size b0 <= ATOP) -> outside [(lo, SP0); (R, R + 24)] a).
    { intros LB0 SP0 a Ha Hc Hx HS HB0. cbn. destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia|].
      specialize (HB0 b0 Hb). lia. }
    assert (FWB : Forall (fun iv : Z * Z => snd iv <= B /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) [(lo, bv_unsigned sp); (R, R + 24)])
      by (unfold RAUXV_CELL; repeat constructor; cbn; lia).
    assert (BSL : Z.of_nat (length (map (Z_to_bv 8) pl)) = n) by (rewrite length_map; reflexivity).
    assert (DJT : PJT + 768 <= D \/ D + n <= PJT).
    { unfold PJT. destruct DCR as [H|[H|(bq & Hb & Hr1 & Hr2)]]; [left; lia| left; lia|].
      destruct (LBR bq HP Hb) as (_ & _ & _ & _ & R5). lia. }
    assert (DIMG : 0xca000 <= D \/ D + n <= 0x10000).
    { destruct DCR as [H|[H|(bq & Hb & Hr1 & Hr2)]]; [left; lia| left; lia|]. destruct (LBR bq HP Hb) as (_ & _ & _ & _ & R5). lia. }
    assert (DLO : D + n <= bv_unsigned sp - 64 \/ bv_unsigned sp <= D).
    { destruct DCR as [H|[H|(b0 & Hb & Hr)]]; [right; exact H| left; lia| left; pose proof (LBB b0 Hb); lia]. }
    unfold lam_model.
    replace (Z.of_nat (length pl)) with n by (unfold n, zlength; reflexivity).
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (R, R + 24)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    carve_frame 64%nat ST.
    subst a0 a1 a2. unfold PLAM, PFALLBACK.
    do 5 zstep. do 4 zstep. zstep.
    (* [comment removed for export] *)
    apply evt_done.
    assert (FW : Forall (fun iv => ATOP <= fst iv) [(lo, bv_unsigned sp); (R, R + 24)]) by (repeat constructor; cbn; lia).
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| exact FW]);
      assert (AUX1 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| repeat constructor; cbn; lia])
    end.
    clear HP AUX. hide MU. hide WM.
    eapply implM_bind.
    { eapply VCT with (lo := lo) (B := B) (V := R) (n := n); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; exact ERR) | exact RC | (unfold VCTOR_STACK, OPNEW_STACK, RMALLOC_STACK; lia) | lia
              | match goal with |- ?G => idtac "LEFT:" G end ]. }
    cbv beta. intros b sv msv PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPX & FAE & SOE & KV).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPX by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    ret_lit.
    trx HPX. clear ST MI ERR AUX1 HP1 RC.
    (* [comment removed for export] *)
    assert (KV' : exists A LB1 bsA, RHEAP sv LB1 m2 /\ rw_cells psegs m2 R (vec_cells A (A + n) (A + n)) /\ u8arr psegs m2 A bsA
              /\ length bsA = Z.to_nat n /\ 0 <= A /\ A + n <= ATOP /\ (A + n <= 0x10000 \/ 0x105000 <= A)
              /\ (forall bq, In bq LB1 -> In bq LB \/ bq = (match b with Some p => p | None => ((0%N, 0), 0) end, A, n))
              /\ (forall bq, In bq LB -> In bq LB1)
              /\ LB1 = match b with Some p => (p, A, n) :: LB | None => LB end
              /\ match b with Some p => 0 < n /\ rblock_range A n | None => n = 0 /\ A = 0 end).
    { destruct b as [p|]; cbn [vctor_K] in KV.
      - destruct KV as (A & NP & BR & HPv & BLK & RCv). exists A, ((p, A, n) :: LB), (repeat (Z_to_bv 8 0) (Z.to_nat n)).
        pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
        split; [exact HPv|]. split; [exact RCv|]. split; [| split; [rewrite repeat_length; reflexivity|]].
        { pose proof (u8arr_of_cells _ _ _ BLK) as U. cbn [cells_bytes cbytes] in U. rewrite app_nil_r in U. exact U. }
        split; [lia|]. split; [lia|]. split; [lia|]. split; [intros bq [Hb|Hb]; [right; symmetry; exact Hb| left; exact Hb]|].
        split; [intros bq Hb; right; exact Hb|]. split; [reflexivity|]. split; [exact NP| exact BR].
      - destruct KV as (Nz & HPv & RCv). exists 0, LB, (@nil byte). unfold vec_cells in RCv |- *. cbn [Z.add] in RCv.
        split; [exact HPv|]. split; [rewrite Nz; cbn [Z.add]; exact RCv|]. split.
        { split; [apply bytes_at_nil; lia|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. }
        split; [rewrite Nz; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros bq Hb; left; exact Hb|].
        split; [intros bq Hb; exact Hb|]. split; [reflexivity|]. split; [exact Nz| reflexivity]. }
    clear KV. destruct KV' as (A & LB1 & bsA & HPv & RCv & BUFv & LENv & Alo & Ahi & Aimg & LB1sub & LB1sup & LB1eq & KB).
    (* [comment removed for export] *)
    assert (ADISJ : forall bq, In bq LB -> A + n <= blk_addr bq \/ blk_addr bq + blk_size bq <= A).
    { intros bq Hb. destruct b as [p|]; [| destruct KB as [Nz Az]; left; pose proof (LBPOS bq Hb); lia].
      subst LB1. exact (new_block_disj _ _ _ _ _ _ bq HPv Hb). }
    pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HPv) as ND1.
    assert (IDNE : forall bq p, In bq LB -> b = Some p -> blk_id bq <> p).
    { intros bq p Hb ->. subst LB1. cbn [map] in ND1. apply NoDup_cons_iff in ND1 as [NI _]. intros E. apply NI. cbn [blk_id fst]. rewrite <- E.
      apply (in_map blk_id LB bq). exact Hb. }
    assert (LBB1 : forall bq, In bq LB1 -> blk_addr bq + blk_size bq <= ATOP).
    { intros bq Hb. destruct (LB1sub bq Hb) as [H| ->]; [exact (LBB bq H)| cbn; lia]. }
    unfold vec_cells in RCv.
    (* [comment removed for export] *)
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (R, R + 24)] m2) as MU2. pose proof (wmono_refl psegs m2) as WM2.
    assert (SEPDA : D + n <= A \/ A + n <= D).
    { destruct b as [p|].
      - destruct KB as [NP BR]. subst LB1.
        destruct DCR as [H|[H|(bq & Hb & Hr1 & Hr2)]]; [right; lia| destruct Aimg; [right; lia| left; unfold ralloc_static in H; lia]|].
        pose proof (new_block_disj _ _ _ _ _ _ bq HPv Hb). lia.
      - destruct KB as [Nz Az]. right. lia. }
    destruct BUFv as [BUFb BUFw].
    do 5 zstep.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    destruct (rw_cells_cut psegs m3 _ _ 1 FR) as [FRS FR1]. cbn [firstn skipn cells_size csize Nat.add] in FRS, FR1. change (Z.of_nat 24) with 24 in FR1.
    destruct (rw_cells_cut psegs m3 _ _ 1 FR1) as [FRZ FR2]. clear FR FR1. cbn [firstn skipn cells_size csize Nat.add] in FRZ, FR2. change (Z.of_nat 8) with 8 in FR2.
    replace (bv_unsigned sp + -64 + 24 + 8) with (bv_unsigned sp + -32) in FR2 by lia.
    replace (bv_unsigned sp + -64 + 24) with (bv_unsigned sp + -40) in FRZ by lia.
    hide MU2. hide WM2.
    eapply evt_cut.
    { eapply (minify_proof) with (D := D) (B := A) (R := bv_unsigned sp + -40) (pl := pl) (bs0 := bsA) (rv := Z_to_bv 64 0);
        try (apply eq_refl); rewrite ?unsigned_lit by lia;
        first [ exact DAT | exact PLB | split; [exact BUFb| exact BUFw] | exact LENv | exact FRZ | exact MI2 | unfold PJT in *; lia | (f_equal; lia)
              | match goal with |- ?G => idtac "LEFT:" G end ]. all: fail. }
    intros ms4 PO. destruct PO as (y0 & y1 & y2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m4 & pos & bs4 & -> & MU4 & WM4 & MI4 & POS & RCZ & DST4 & LEN4 & DAT4).
    rewrite ?unsigned_lit in MU4 by lia.
    ret_lit.
    trm MU4 WM4.
    assert (ST4 : stk psegs m4 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST2| exact MU4| exact WM4| cbn; lia]).
    clear ST2 MI2 BUFb BUFw FRZ. hide MU4. hide WM4.
    (* [comment removed for export] *)
    unhide MU2. unhide WM2.
    assert (HP4 : RHEAP sv LB1 m4).
    { unhide MU4. destruct b as [p|].
      - destruct KB as [NP BR].
        eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU4| exact WM4|].
        2:{ constructor; [| constructor; [unfold rclient_write_ok; left; unfold fst; lia| constructor]].
            right; right; exists (p, A, n); split; [subst LB1; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]. }
        eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HPv| exact MU2| exact WM2| repeat constructor; cbn; lia].
      - destruct KB as [Nz Az].
        assert (MU4' : munch [(bv_unsigned sp + -40, bv_unsigned sp + -40 + 8)] m3 m4).
        { eapply munch_weaken; [| exact MU4]. intros x Hx. cbn in Hx |- *. lia. }
        eapply RMalloc_ifaceP.RHEAP_frame_proof; [| exact MU4'| exact WM4| constructor; [unfold rclient_write_ok; left; unfold fst; lia| constructor]].
        eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HPv| exact MU2| exact WM2| repeat constructor; cbn; lia]. }
    hide MU4.
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [| unhide MU4; exact MU4| exact WM4|].
      2:{ unfold RAUXV_CELL. constructor; [cbn; split; [lia| destruct Aimg; [left; lia| right; destruct b; [destruct KB as [NP _]; lia| destruct KB as [Nz _]; lia]]]|].
          constructor; [cbn; lia| constructor]. }
      eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2| exact FWB]. }
    hide MU2. hide WM2. clear HPv AUX2.
    destruct (unclosed pl) eqn:U.
    - (* [comment removed for export] *)
      change (if true then 15 else 0) with 15.
      pose proof (munch_refl [(lo, bv_unsigned sp); (R, R + 24)] m4) as MU5. pose proof (wmono_refl psegs m4) as WM5.
      zstep. lit_if.
      do 7 zstep.
      apply evt_done.
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      eapply implM_bind.
      { eapply STR with (lo := lo) (B := B) (T := bv_unsigned sp + -64); try (apply eq_refl); rewrite ?unsigned_lit by lia;
          first [exact HP4 | exact AUX4 | exact ST4 | exact MI4 | (rewrite errno_lit; exact ERR2) | exact FRS | (unfold STRCTOR_STACK, OPNEW_STACK, RMALLOC_STACK; lia)
                | (unfold PMSG; apply eq_refl) | lia | match goal with |- ?G => idtac "LEFT:" G end ]. }
      cbv beta. intros t st mst PO.
      destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m6 & errv6 & -> & MI6 & ST6 & ERR6 & AUX6 & HPX6 & FAE6 & SOE6 & KS).
      destruct KS as (S & jr & SR & HP6 & SC6 & TC6). pose proof SR as (SR1 & SR2 & SR3 & SR4 & SR5).
      rewrite ?unsigned_lit in ST6 by lia. rewrite ?unsigned_lit in HPX6 by lia. rewrite errno_lit in ERR6. unfold RERRNO in ERR6. unfold ERRSTR_BYTES, ERRMSG_LEN in *.
      ret_lit.
      trx HPX6. clear ST4 MI4 ERR2 AUX4 HP4 FRS.
      unfold lstr_cells in TC6. change (56 + 1) with 57 in TC6.
      (* [comment removed for export] *)
      pose proof (InitMem.rw_cells_recast psegs m6 _ _ [C1 (Z_to_bv 8 57); CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 54); C8 (Z_to_bv 64 S)] TC6
        ltac:(cbn; repeat split; exact I)
        ltac:(cbn [cells_bytes cbytes app]; change (le8 (Z_to_bv 64 57)) with ([Z_to_bv 8 57] ++ repeat (Z_to_bv 8 0) 7); reflexivity)
        eq_refl) as TC6b.
      pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP6) as ND6.
      (* [comment removed for export] *)
      assert (PIN6 : forall p, b = Some p -> In (p, A, n) ((t, S, 56) :: LB1)) by (intros p ->; right; subst LB1; left; reflexivity).
      assert (SEPS : S + 56 <= A \/ A + n <= S).
      { destruct b as [p|]; [| destruct KB as [Nz Az]; right; lia].
        assert (PIN1 : In (p, A, n) LB1) by (subst LB1; left; reflexivity).
        pose proof (new_block_disj _ _ _ _ _ _ (p, A, n) HP6 PIN1) as DJ. cbn [blk_addr blk_size fst snd] in DJ. lia. }
      assert (BUF6 : 0 < n -> rw_cells psegs m6 A [CB (Z.to_nat n) bs4]).
      { intros NP. destruct b as [p|]; [| destruct KB as [Nz Az]; exfalso; lia].
        pose proof (cells_of_u8arr _ _ _ DST4) as CB4. rewrite LEN4 in CB4. change (zlength pl) with n in CB4.
        eapply rheap_pres_x_rw_cells; [exact HPX6| exact CB4| | cbn [cells_size csize Nat.add]; lia].
        right; right. exists (p, A, n). split; [subst LB1; left; reflexivity| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia]. }
      clear DST4.
      hide MU5. hide WM5.
      apply implM_from_evt.
      pose proof (munch_refl [(lo, bv_unsigned sp); (R, R + 24)] m6) as MU7. pose proof (wmono_refl psegs m6) as WM7.
      zstep. zstep. zstep. lit_if. zstep. zstep. lit_if.
      do 4 zstep.
      (* [comment removed for export] *)
      apply evt_done.
      eapply implM_bind.
      { eapply ASG with (lo := lo) (B := B) (V := R) (A := A) (S := S) (t := t) (n := n) (old := bs4);
          try (apply eq_refl); rewrite ?unsigned_lit by lia;
          first [exact HP6 | exact AUX6 | exact ST6 | exact MI6 | (rewrite errno_lit; exact ERR6) | exact BUF6 | exact SC6 | exact SEPS
                | (unfold vec_cells; lazymatch goal with H : rw_cells psegs m6 R _ |- _ => exact H end)
                | (left; reflexivity)
                | (destruct b as [p|]; cbn [vbuf]; [split; [exact (PIN6 p eq_refl)| destruct KB as [NP _]; exact NP]| destruct KB as [Nz Az]; split; [exact Az| exact Nz]])
                | (unfold ASSIGN_STACK, OPNEW_STACK, RMALLOC_STACK; lia) | (unfold ERRSTR_BYTES, ERRMSG_LEN; apply eq_refl) | (unfold ERRMSG_LEN; f_equal; lia) | lia
                | match goal with |- ?G => idtac "LEFT:" G end ]. }
      cbv beta. intros b' sa msa PO.
      destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m8 & errv8 & -> & MI8 & ST8 & ERR8 & AUX8 & HPX8 & FAE8 & SOE8 & KA).
      rewrite ?unsigned_lit in ST8 by lia. rewrite ?unsigned_lit in HPX8 by lia. rewrite errno_lit in ERR8. unfold RERRNO in ERR8. unfold ERRSTR_BYTES, ERRMSG_LEN in KA.
      ret_lit.
      destruct b' as [p'|]; [| destruct KA].
      destruct KA as (A' & LB' & BR' & HP8 & CASE & RC8). unfold vec_cells in RC8.
      assert (TIN8 : In (t, S, 56) LB').
      { destruct (Z_lt_le_dec n 54) as [LT'|GE].
        2:{ rewrite (proj2 (Z.leb_le _ _) GE) in CASE. destruct CASE as (_ & _ & ->). left. reflexivity. }
        rewrite (proj2 (Z.leb_gt _ _) LT') in CASE. rewrite CASE. right. destruct b as [p|]; cbn [lbx]; [| left; reflexivity].
          apply in_lb_remove; [left; reflexivity|]. cbn. intros E.
          apply NoDup_cons_iff in ND6 as [NI _]. apply NI. cbn. rewrite E. subst LB1. left. reflexivity. }
      assert (LBB8 : forall bq, In bq (lbx b ((t, S, 56) :: LB1)) -> blk_addr bq + blk_size bq <= ATOP).
      { intros bq Hb. assert (Hb' : In bq ((t, S, 56) :: LB1)) by (destruct b; cbn [lbx] in Hb; [eapply lb_remove_sub; exact Hb| exact Hb]).
        destruct Hb' as [<-|Hb']; [cbn; lia| exact (LBB1 bq Hb')]. }
      trx HPX8. clear ST6 MI6 ERR6 AUX6 HP6 BUF6 RCv SC6.
      pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ HP8) as ND8.
      (* [comment removed for export] *)
      apply implM_from_evt.
      pose proof (munch_refl [(lo, bv_unsigned sp); (R, R + 24)] m8) as MU9. pose proof (wmono_refl psegs m8) as WM9.
      zstep. zstep. zstep. lit_if. zstep. zstep. zstep. zstep.
      apply evt_done.
      eapply implM_bind.
      { eapply (proj1 (proj2 OD)) with (lo := lo) (B := B) (A := S) (n := 56) (p := t); try (apply eq_refl); rewrite ?unsigned_lit by lia;
          first [exact HP8 | exact TIN8 | exact AUX8 | exact ST8 | exact MI8 | (rewrite errno_lit; exact ERR8) | (unfold RFREE_STACK; lia) | lia
                | match goal with |- ?G => idtac "LEFT:" G end ]. }
      cbv beta. intros [] sd msd PO.
      destruct PO as (v0' & v1' & v2' & c0' & c1' & c2' & c3' & c4' & c5' & c6' & c7' & v3' & v4' & v5' & v6' & m9 & -> & MI9 & ST9 & ERR9 & AUX9 & HPR9 & FAE9 & SOE9 & HP9).
      rewrite ?unsigned_lit in ST9 by lia. rewrite ?unsigned_lit in HPR9 by lia. rewrite errno_lit in ERR9. unfold RERRNO in ERR9.
      ret_lit.
      assert (SUB9 : forall bq, In bq LB -> In bq (lb_remove t LB')).
      { intros bq Hb. apply in_lb_remove.
        - destruct (Z_lt_le_dec n 54) as [LT'|GE].
          + rewrite (proj2 (Z.leb_gt _ _) LT') in CASE. rewrite CASE. right. destruct b as [p|]; cbn [lbx].
            * apply in_lb_remove; [right; apply LB1sup; exact Hb| exact (IDNE bq p Hb eq_refl)].
            * right. apply LB1sup. exact Hb.
          + rewrite (proj2 (Z.leb_le _ _) GE) in CASE. destruct CASE as (_ & _ & ->). right. apply LB1sup. exact Hb.
        - cbn [map] in ND6. apply NoDup_cons_iff in ND6 as [NI _]. intros E. apply NI. cbn. rewrite <- E. apply in_map. apply LB1sup. exact Hb. }
      trp HPR9. clear ST8 MI8 ERR8 AUX8 HP8.
      (* [comment removed for export] *)
      apply implM_ret.
      do 6 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m10 end.
      assert (STF : stk psegs m10 lo (bv_unsigned sp)).
      { eapply stk_merge; [exact ST9| | lia].
        eapply stk_merge; [lazymatch goal with H : rw_cells psegs m10 (bv_unsigned sp + -64) [C8 _; C8 _; C8 _] |- _ => pose proof (stk_of_cells _ _ _ H) as K1; cbn [cells_size csize Nat.add] in K1; exact K1 end| |cbn; lia].
        eapply stk_merge; [pose proof (stk_of_cells _ _ _ RCZ) as K2; cbn [cells_size csize Nat.add] in K2; replace (bv_unsigned sp + -64 + Z.of_nat 24) with (bv_unsigned sp + -40) by lia; exact K2| | cbn; lia].
        pose proof (stk_of_cells _ _ _ FR2) as K3. cbn [cells_size csize Nat.add] in K3.
        replace (bv_unsigned sp + -40 + Z.of_nat 8) with (bv_unsigned sp + -32) by lia. replace (bv_unsigned sp) with (bv_unsigned sp + -32 + Z.of_nat 32) at 2 by lia. exact K3. }
      unhide MU. unhide WM. unhide MU2. unhide WM2. unhide MU4. unhide WM4. unhide MU5. unhide WM5.
      apply evt_done. unfold helper_post. do 15 eexists. exists m10, errv8. split; [reflexivity|].
      split; [exact MI9|]. split; [exact STF|]. split; [rewrite errno_lit; exact ERR9|]. split; [exact AUX9|].
      split.
      { (* [comment removed for export] *)
        assert (OUTW' : forall a W', 0 <= a < 2^64 -> rclient_addr LB (bv_unsigned sp) a -> ~ (R <= a < R + 24) ->
                  (forall x, outside [(lo, bv_unsigned sp); (R, R + 24)] x -> outside W' x) -> outside W' a).
        { intros a W' Ha Hc Hx HW. apply HW. exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB). }
        eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]|].
        eapply rheap_pres_x_trans; [eapply (rheap_pres_x_weaken LB LB); [exact HPX| lia| intros bq Hb; exact Hb| intros a _ Hx; exact Hx]|].
        eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU2| exact WM2| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]|].
        eapply rheap_pres_x_trans.
        { eapply rheap_pres_x_of_munch; [exact MU4| exact WM4|]. intros a Ha Hc Hx.
          clear - Ha Hc Hx Alo Ahi Aimg LOA LOS ATOPR ADISJ LBB N0. cbn [outside].
          destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [split; [lia| split; [lia| exact I]]| unfold ralloc_static in Hc; split; [lia| split; [lia| exact I]]|].
          pose proof (ADISJ bq Hb). pose proof (LBB bq Hb). split; [lia| split; [lia| exact I]]. }
        eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU5| exact WM5| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]|].
        eapply rheap_pres_x_trans.
        { eapply (rheap_pres_x_weaken LB LB1); [exact HPX6| lia| exact LB1sup|].
          intros a Hc Hx. clear - Hc Hx LOA LOS ATOPR LBB.       (* [comment removed for export] *)
          destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia| pose proof (LBB bq Hb); lia]. }
        eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU7| exact WM7| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]|].
        eapply rheap_pres_x_trans.
        { eapply (rheap_pres_x_weaken LB); [exact HPX8| lia| | intros a _ Hx; exact Hx].
          intros bq Hb. destruct b as [p|]; cbn [lbx]; [| right; apply LB1sup; exact Hb].
          apply in_lb_remove; [right; apply LB1sup; exact Hb| exact (IDNE bq p Hb eq_refl)]. }
        eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU9| exact WM9| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]|].
        eapply rheap_pres_x_of_pres; [exact HPR9| lia| exact SUB9]. }
      split; [congruence|]. split; [congruence|].
      unfold lam_K. exists A', (Z.max n 54), 54.
      split.
      { (* [comment removed for export] *)
        assert (EQ : lb_remove t LB' = (p', A', Z.max n 54) :: LB).
        { destruct (Z_lt_le_dec n 54) as [LT'|GE].
          - rewrite (proj2 (Z.leb_gt _ _) LT') in CASE. replace (Z.max n 54) with 54 by lia.
            assert (E1 : lbx b ((t, S, 56) :: LB1) = (t, S, 56) :: LB).
            { destruct b as [p|]; cbn [lbx]; [| subst LB1; reflexivity]. subst LB1. apply RDriver_facts.lb_remove_second; [reflexivity| exact ND6]. }
            rewrite E1 in CASE. subst LB'. apply RDriver_facts.lb_remove_second; [reflexivity| exact ND8].
          - rewrite (proj2 (Z.leb_le _ _) GE) in CASE. destruct CASE as (E0 & -> & ->). replace (Z.max n 54) with n by lia.
            destruct b as [p|]; [| destruct KB as [Nz _]; exfalso; lia]. injection E0 as <-. subst LB1.
            apply RDriver_facts.lb_remove_hd; [reflexivity| exact ND6]. }
        rewrite <- EQ. eapply RHEAP_stack_frame; [exact HP9| apply munch_refl| apply wmono_refl| constructor]. }
      split; [lia|]. split; [exact BR'|]. split; [lia|].
      unfold vec_cells. unfold ERRMSG_LEN in RC8. lazymatch goal with H : rw_cells psegs m10 R _ |- _ => exact H end.
    - (* [comment removed for export] *)
      change (if false then 15 else 0) with 0.
      pose proof (munch_refl [(lo, bv_unsigned sp); (R, R + 24)] m4) as MU5. pose proof (wmono_refl psegs m4) as WM5.
      zstep. lit_if.                                            (* [comment removed for export] *)
      zstep.                                                    (* [comment removed for export] *)
      zstep.                                                    (* [comment removed for export] *)
      zstep. br_dead K1.                                        (* [comment removed for export] *)
      zstep. zstep.                                             (* [comment removed for export] *)
      zstep. zstep. zstep.                                      (* [comment removed for export] *)
      zstep. br_dead K2.                                        (* [comment removed for export] *)
      (* [comment removed for export] *)
      Ltac lam_tail lo sp LB MU WM MU2 WM2 MU4 WM4 MU5 WM5 HPX OUTW LBB ADISJ RCZ FR2 FRS ST4 MI4 ERR2 AUX4 FWB FAE SOE Alo Ahi Aimg LOA LOS ATOPR N0 :=
        zstep;
        do 6 zstep;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (STF : stk psegs mx lo (bv_unsigned sp));
        [ eapply stk_merge; [exact ST4| | lia];
          eapply stk_merge; [pose proof (stk_of_cells _ _ _ FRS) as SK1; cbn [cells_size csize Nat.add] in SK1; exact SK1| |cbn; lia];
          eapply stk_merge; [pose proof (stk_of_cells _ _ _ RCZ) as SK2; cbn [cells_size csize Nat.add] in SK2; replace (bv_unsigned sp + -64 + Z.of_nat 24) with (bv_unsigned sp + -40) by lia; exact SK2| | cbn; lia];
          pose proof (stk_of_cells _ _ _ FR2) as SK3; cbn [cells_size csize Nat.add] in SK3;
          replace (bv_unsigned sp + -40 + Z.of_nat 8) with (bv_unsigned sp + -32) by lia; replace (bv_unsigned sp) with (bv_unsigned sp + -32 + Z.of_nat 32) at 2 by lia; exact SK3
        | unhide MU; unhide WM; unhide MU2; unhide WM2; unhide MU4; unhide WM4;
          apply evt_done; apply implM_ret; apply evt_done; unfold helper_post; do 15 eexists; exists mx; eexists; split; [reflexivity|];
          split; [exact MI4|]; split; [exact STF|]; split; [rewrite errno_lit; exact ERR2|];
          split; [eapply rauxv_ok_frame; [exact AUX4| exact MU5| exact WM5| exact FWB]|];
          split;
          [ eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU| exact WM| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]|];
            eapply rheap_pres_x_trans; [eapply (rheap_pres_x_weaken LB LB); [exact HPX| lia| intros bq Hb; exact Hb| intros a _ Hx; exact Hx]|];
            eapply rheap_pres_x_trans; [eapply rheap_pres_x_of_munch; [exact MU2| exact WM2| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)]|];
            eapply rheap_pres_x_trans;
            [ eapply rheap_pres_x_of_munch; [exact MU4| exact WM4|]; intros a Ha Hc Hx;
              clear - Ha Hc Hx Alo Ahi Aimg LOA LOS ATOPR ADISJ LBB N0; cbn [outside];
              destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [split; [lia| split; [lia| exact I]]| unfold ralloc_static in Hc; split; [lia| split; [lia| exact I]]|];
              pose proof (ADISJ bq Hb); pose proof (LBB bq Hb); split; [lia| split; [lia| exact I]]
            | eapply rheap_pres_x_of_munch; [exact MU5| exact WM5| intros a Ha Hc Hx; exact (OUTW LB _ a Ha Hc Hx ltac:(lia) LBB)] ]
          |];
          split; [exact FAE|]; split; [exact SOE|] ]
        end.
      zstep. if_cases K3; zify_cond K3.
      + (* [comment removed for export] *)
        zstep. ret_lit.
        lam_tail lo sp LB MU WM MU2 WM2 MU4 WM4 MU5 WM5 HPX OUTW LBB ADISJ RCZ FR2 FRS ST4 MI4 ERR2 AUX4 FWB FAE SOE Alo Ahi Aimg LOA LOS ATOPR N0.
        destruct b as [p|]; unfold lam_K; change (zlength pl) with n; cbv beta iota zeta.
        * destruct KB as [NP BR]. exists A, n, n. subst LB1.
          split; [eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP4| exact MU5| exact WM5| repeat constructor; cbn; lia]|].
          split; [exact NP|]. split; [exact BR|]. split; [lia|].
          unfold vec_cells. lazymatch goal with H : rw_cells psegs _ R _ |- _ => exact H end.
        * destruct KB as [Nz Az]. subst LB1.
          split; [exact Nz|]. split; [first [exact U | reflexivity]|].
          split; [eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP4| exact MU5| exact WM5| repeat constructor; cbn; lia]|].
          unfold vec_cells. lazymatch goal with H : rw_cells psegs _ R _ |- _ => rewrite Az, Nz in H; cbn [Z.add] in H; exact H end.
      + (* [comment removed for export] *)
        assert (NP : 0 < n) by lia.
        destruct b as [p|]; [| destruct KB as [Nz Az]; exfalso; lia]. destruct KB as [_ BR]. subst LB1.
        zstep. zstep.                                           (* [comment removed for export] *)
        zstep. ret_lit.
        lam_tail lo sp LB MU WM MU2 WM2 MU4 WM4 MU5 WM5 HPX OUTW LBB ADISJ RCZ FR2 FRS ST4 MI4 ERR2 AUX4 FWB FAE SOE Alo Ahi Aimg LOA LOS ATOPR N0.
        unfold lam_K. change (zlength pl) with n. cbv beta iota zeta.
        exists A, n, pos.
        split; [eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP4| exact MU5| exact WM5| repeat constructor; cbn; lia]|].
        split; [exact NP|]. split; [exact BR|]. split; [lia|].
        unfold vec_cells. lazymatch goal with H : rw_cells psegs _ R _ |- _ => exact H end.
  Qed.
End Proof.
End CANSEC1.
