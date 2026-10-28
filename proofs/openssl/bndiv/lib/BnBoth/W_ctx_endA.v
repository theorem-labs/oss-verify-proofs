(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_ctxA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2409064 => 1
  | 2409068 => 2
  | 2409116 => 2
  | 2409204 => 2
  | 2409208 => 1
  | 2409212 => 1
  | 2409216 => 1
  | 2409220 => 2
  | 2409224 => 2
  | 2409228 => 1
  | 2409232 => 2
  | 2409368 => 2
  | 2409372 => 1
  | 2409376 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma BN_CTX_end_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo : Z),
  bn_preA Σ ls m OW LB AD EA sp lo BN_CTX_END_STACK 0 -> tp = wz TP_A -> a0 = wz (ad_ctx AD) ->
  implA (BN_CTX_end (tree_ops bptr) ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA 0 (fun _ _ OW' _ => OW' = OW))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_CTX_END) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED) -> ->.
  unfold BN_CTX_END_STACK, BN_CTX_END, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof SOK as (_ & _ & _ & _ & _ & POK & (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & CK7)).
  destruct (lib_state_cx_open [] ls m OW AD EA LS) as (H & Cu & IX & CX & STK & PM & HH & LSC).
  pose proof ADB as (_ & _ & _ & _ & _ & BC). pose proof (AH_range _ _ _ _ _ _ _ HEAP BC) as (CA0 & CA16 & _ & CAC & CAI).
  set (c := ls_ctx ls) in *.
  unfold ctx_cells in CX. rewrite CK7 in CX. change (Z.of_nat 0) with 0 in CX.
  assert (INC : In (ad_pc AD, ad_ctx AD, 72) (OW ++ LB)) by (apply in_or_app; left; exact BC).
  pose proof (AH_acc_in _ _ _ _ (ad_pc AD, ad_ctx AD, 72) (ad_ctx AD) 72 HEAP INC ltac:(cbn; lia) ltac:(cbn; lia)) as ACC.
  assert (AL : ad_ctx AD mod 8 = 0) by (clear - CA16; Z.div_mod_to_equations; lia).
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  unfold BN_CTX_end, bbind, bgetctx, bret, bunr, bsetctx.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold c.
  rewrite CK7. cbn [Nat.eqb negb].
  destruct (rev (cx_frames c)) as [|fp rest] eqn:EREV.
  { apply implA_unr. }
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]).
  { pose proof (AH_offsh _ _ _ _ (ad_pc AD, ad_ctx AD, 72) HEAP INC) as O. cbn [blk_addr blk_size fst snd] in O.
    cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. lia. }
  assert (EFR : cx_frames c = rev rest ++ [fp]).
  { rewrite <- (rev_involutive (cx_frames c)), EREV. reflexivity. }
  assert (DEPp : length (cx_frames c) = S (length rest)) by (rewrite EFR, length_app, length_rev; cbn; lia).
  assert (SSZ : cx_ssize c = 0%nat \/ cx_ssize c = 32%nat).
  { unfold stack_rep in STK. destruct (cx_indexes c); [right; exact (proj1 (proj2 STK))| left; exact (proj1 (proj2 STK))]. }
  assert (FPU : (fp <= cx_used c)%nat).
  { rewrite EFR in CK4. rewrite <- app_assoc in CK4. cbn [app] in CK4. eapply nondecr_last_le; exact CK4. }
  apply implA_from_evt.
  carve_frame 16%nat ST. do 4 (ub; step).
  ub; step. if_cases KN; zify_cond KN; [exfalso; rewrite ?unsigned_lit in KN by (unfold BnHeapA.ACEIL in *; lia); lia|]. clear KN.
  do 3 (ub; step). do 3 (ub; step). ub; shl. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
  ub; step. if_true.
  do 3 (ub; step). ub; shl. ub; chk0.
  do 3 (ub; step). ub; shl. ub; step. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (length (cx_frames c)))) by lia.
  ub; step. replace (Z.of_nat (length (cx_frames c)) + -1) with (Z.of_nat (length rest)) by lia.
  ub; step. do 2 (ub; step).
  rewrite (unsigned_lit (Z.of_nat (length rest))) by lia. rewrite shl32_shr30 by lia.
  ub; step.
  (* [comment removed for export] *)
  unfold stack_rep in STK. destruct (cx_indexes c) as [q|] eqn:EI; [|exfalso; destruct STK as (_ & _ & E2); rewrite E2 in DEPp; cbn in DEPp; lia].
  destruct STK as (HinI & SZ32 & stale & LEN & ARR).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP HinI) as (IA0 & IA16 & _ & IAC & IAI).
  assert (NEI : ad_pc AD <> q) by (eapply ids_ad_m; [exact IDS| unfold ad_ids; cbn; tauto| apply idx_in_m; exact EI]).
  pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HinI NEI) as CXI.
  assert (INI : In (q, IX, 128) (OW ++ LB)) by (apply in_or_app; left; exact HinI).
  pose proof (AH_acc_in _ _ _ _ (q, IX, 128) IX 128 HEAP INI ltac:(cbn; lia) ltac:(cbn; lia)) as ACCI.
  assert (ALI : IX mod 8 = 0) by (clear - IA16; Z.div_mod_to_equations; lia).
  remember (map (fun k : nat => wz (Z.of_nat k)) (cx_frames c) ++ stale) as ws eqn:Ews.
  assert (LWS : length ws = 32%nat) by (subst ws; rewrite length_app, length_map; exact LEN).
  assert (NTH : nth_error ws (Z.to_nat (Z.of_nat (length rest))) = Some (wz (Z.of_nat fp))).
  { rewrite Nat2Z.id, Ews, EFR, map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
    rewrite nth_error_app2 by (rewrite length_map, length_rev; lia). rewrite length_map, length_rev, Nat.sub_diag. reflexivity. }
  pose proof ARR as ARR0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of MU with munch ?W0 _ _ =>
      apply (u32arr_transport bsegs W0 m mx IX ws) in ARR; [| exact MU| exact WM| cbn [disjoint_from]; rewrite LWS; lia] end end.
  do 2 (ub; step). ub; shl. ub; chk0.
  do 3 (ub; step). ub; shl.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let a := cur_mem_addr in
    pose proof (u32arr_read bsegs mx IX ws (Z.of_nat (length rest)) (wz (Z.of_nat fp)) a ARR NTH ltac:(lia) ltac:(addr_tac)) as RD end.
  ub; step. clear RD. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat fp)) by lia. ub; chk0.
  ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (cx_used c))) by lia.
  set (pu' := if (fp <? cx_used c)%nat then (cx_pused c - (cx_used c - fp))%nat else cx_pused c).
  set (cur' := if (fp <? cx_used c)%nat && (pu' =? 0)%nat then None else cx_current c).
  lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mx _) => rename mx into m1;
    assert (FIN : forall (x5 x6 x11 x12 x13 x17 : word) (mX : mem) (CuX : Z),
      rw_cells bsegs mX (ad_ctx AD)
        [C8 (wz H); C8 (wz CuX); C8 (wz H); C4 (wz (Z.of_nat pu')); C4 (wz (Z.of_nat (cx_psize c))); C8 (wz IX);
         C4 (wz (Z.of_nat (length rest))); C4 (wz (Z.of_nat (cx_ssize c))); C4 (wz (Z.of_nat (cx_used c)));
         C4 (wz 0); C4 (wz (Z.b2z (cx_too_many c))); C4 (wz 0); C8 (wz 0)] ->
      rw_cells bsegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
      stk bsegs mX lo (bv_unsigned sp + -16) ->
      munch [(bv_unsigned sp + -16, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]%Z m mX -> wmono bsegs m mX -> mem_inv bsegs mX ->
      ((cur' = None /\ CuX = 0) \/ (cur' = cx_head c /\ cur' <> None /\ CuX = H)) ->
      evt bsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 TP_A) x5 x6 t2 sp s1 (Z_to_bv 64 (ad_ctx AD))
                           x11 x12 x13 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat fp)) (Z_to_bv 64 ((ad_ctx AD + 48) ≫ 3 + SHB)) x17
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 2409428) fc None mX (seg_rom bsegs))) end.
  { intros x5 x6 x11 x12 x13 x17 mX CuX CXX FRX STX MUX WMX MIX HCUR.
    clear MU WM MI ST FR CX ARR.
    unfold MallocRep.wz in *.
    ub; shl. ub; chk0. ub; step. do 3 (ub; step). ub; shl. ub; chk0. ub; step.
    do 2 (ub; step). release_frame FRX STX (bv_unsigned sp). ub; step. ub; step.
    apply evt_done. apply implA_ret.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mF end.
    lazymatch goal with |- context [set_ctx ?cc ls] => set (c' := cc) end.
    assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp + -16, bv_unsigned sp); (ad_ctx AD, ad_ctx AD + 72)]).
    { constructor; [left; cbn; lia|]. constructor; [right; exists (ad_pc AD, ad_ctx AD, 72); cbn; auto with zarith| constructor]. }
    assert (EPU : pu' = fp).
    { subst pu'. destruct (fp <? cx_used c)%nat eqn:EL; [lia|]. apply Nat.ltb_ge in EL. lia. }
    assert (LSF : lib_state (set_ctx c' ls) mF OW AD EA).
    { unfold lib_state. eapply (lib_state_cx_close [] ls mF OW AD EA c' H CuX IX); [| exact ND| reflexivity| reflexivity| exact HH| | | | |].
      - eapply (lib_state_frame Σ LB); [exact HEAP| exact LSC| exact MUX| exact WMX|].
        constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|].
        constructor; [apply w_cx; [reflexivity| intros x Hx; left; cbn in Hx; lia]| constructor].
      - unfold ctx_cells, c'. cbn [cx_pused cx_psize cx_frames cx_ssize cx_used cx_err_stack cx_too_many Z.b2z].
        rewrite length_rev. fold pu'. rewrite EPU in *. exact CXX.
      - unfold stack_rep, c'. cbn [cx_indexes cx_ssize cx_frames]. split; [exact HinI|]. split; [exact SZ32|].
        exists (wz (Z.of_nat fp) :: stale). split; [rewrite length_rev; cbn [length]; rewrite DEPp in LEN; lia|].
        lazymatch type of MUX with munch ?W0 _ _ =>
          apply (u32arr_transport bsegs W0 m mF IX ws) in ARR0; [| exact MUX| exact WMX| cbn [disjoint_from]; rewrite LWS; lia] end.
        rewrite Ews, EFR, map_app in ARR0. cbn [map] in ARR0. rewrite <- app_assoc in ARR0. cbn [app] in ARR0. exact ARR0.
      - assert (PMF : pool_mem mF H Cu c).
        { eapply (pool_mem_keep Σ OW LB m mF ls AD EA H Cu); [exact HEAP| exact IDS| exact ADB| exact HH| exact PM| exact MUX| exact WMX|].
          constructor; [left; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [right; left; cbn; lia| constructor]. }
        unfold pool_mem in *. subst c'. cbn [cx_head cx_current]. fold pu'. fold cur'.
        destruct (cx_head c) as [ph|] eqn:Eh.
        + split; [exact (proj1 PMF)|]. destruct HCUR as [[E1 E2]|(E1 & E2 & E3)]; [left; auto| right; auto].
        + destruct HCUR as [[E1 E2]|(E1 & E2 & E3)]; [auto| congruence].
      - unfold ctx_okm, c'. cbn [cx_pused cx_used cx_psize cx_vals cx_frames cx_ssize cx_current cx_head cx_err_stack]. fold pu'. fold cur'.
        split; [exact EPU|]. split; [lia|]. split; [exact CK3|].
        split. { rewrite EFR in CK4. rewrite <- app_assoc in CK4. cbn [app] in CK4. eapply nondecr_drop_last; exact CK4. }
        split; [rewrite length_rev; lia|]. split; [|reflexivity].
        intros HP. subst cur'. replace (pu' =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact HP). rewrite andb_false_r.
        apply CK6. lia.
      - apply ids_ok_set_ctx_same; [exact IDS| reflexivity| symmetry; exact EI| reflexivity]. }
    unfold bn_postA. do 17 eexists. exists mF, OW. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MUX WMX HWL CEIL ltac:(unfold USTACK_TOP; lia))|]. split; [exact LSF|].
    split; [exact STX|]. split; [assumption|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MUX HWL CEIL ltac:(lia))|].
    split; [lia|].
    split. { unfold cnt_eq, cnt_bal. rewrite (blocks_of_set_ctx c' ls); [reflexivity | reflexivity | reflexivity | symmetry; exact EI]. }
    split; [intros r' a' HA'; exact HA'| reflexivity]. }
  assert (HCUR0 : (cx_current c = None /\ Cu = 0) \/ (cx_current c = cx_head c /\ cx_current c <> None /\ Cu = H)).
  { unfold pool_mem in PM. destruct (cx_head c) as [ph|] eqn:Eh.
    - destruct PM as [_ [[E1 E2]|[E1 E2]]]; [left; auto| right; rewrite E1; repeat split; [discriminate| exact E2]].
    - destruct PM as [E1 E2]. left. auto. }
  ub; step. if_cases KR; zify_cond KR; rewrite ?unsigned_lit in KR by lia.
  - (* [comment removed for export] *)
    assert (ELT : (fp <? cx_used c)%nat = false) by (apply Nat.ltb_ge; lia).
    eapply FIN; [| exact FR| exact ST| exact MU| exact WM| exact MI|].
    + subst pu'. rewrite ELT. exact CX.
    + subst cur'. rewrite ELT. cbn [andb]. exact HCUR0.
  - (* [comment removed for export] *)
    assert (ELT : (fp <? cx_used c)%nat = true) by (apply Nat.ltb_lt; lia).
    do 3 (ub; step). ub; shl. ub; chk0.
    ub; step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (cx_pused c))) by lia.
    do 4 (ub; step).
    rewrite !(unsigned_lit (Z.of_nat fp)), !(unsigned_lit (Z.of_nat (cx_used c))), !(unsigned_lit (Z.of_nat (cx_pused c))) by lia.
    rewrite !(bk_swrap32_small (Z.of_nat (cx_used c) - Z.of_nat fp)) by lia.
    rewrite !(unsigned_lit (Z.of_nat (cx_used c) - Z.of_nat fp)) by lia.
    rewrite !(bk_swrap32_small (Z.of_nat fp - Z.of_nat (cx_used c))) by lia.
    rewrite !(bk_swrap32_small (Z.of_nat (cx_pused c) - (Z.of_nat (cx_used c) - Z.of_nat fp))) by lia.
    replace (Z.of_nat (cx_pused c) - (Z.of_nat (cx_used c) - Z.of_nat fp)) with (Z.of_nat pu') by (subst pu'; rewrite ELT; lia).
    ub; step. ub; step. rewrite ?(unsigned_lit (ad_ctx AD + 8)) by (unfold BnHeapA.ACEIL in *; lia).
    ub; step. ub; step.
    rewrite ?(unsigned_lit (Z.of_nat (cx_pused c) + -1)) by lia.
    replace (Z.land (Z.of_nat (cx_pused c) + -1) 15) with (Z.of_nat (cx_pused c) + -1)
      by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    ub; step.
    replace (Z.of_nat fp - Z.of_nat (cx_used c)) with (- (Z.of_nat (cx_used c) - Z.of_nat fp)) by lia.
    eapply evt_eq; [| eapply (end_loopA (cx_used c - fp - 1)) with (off := Z.of_nat (cx_pused c) + -1) (j := Z.of_nat (cx_used c) - Z.of_nat fp);
                      [lia| lia| lia| lia|] ]; [reflexivity|].
    replace (Z.of_nat (cx_used c) - Z.of_nat fp - Z.of_nat (cx_used c - fp - 1)) with 1 by lia.
    replace (Z.of_nat (cx_pused c) + -1 - Z.of_nat (cx_used c - fp - 1)) with (Z.of_nat pu') by (subst pu'; rewrite ELT; lia).
    assert (PUR : (pu' <= 16)%nat) by (subst pu'; rewrite ELT; lia).
    ub; step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
    + (* [comment removed for export] *)
      assert (EP0 : pu' = 0%nat) by lia.
      assert (PNZ : cx_pused c <> 0%nat) by lia.
      pose proof (CK6 PNZ) as ECUR.
      destruct HCUR0 as [[E1 E2]|(E1 & E2 & E3)].
      { (* [comment removed for export] *)
        exfalso. rewrite ECUR in E1. destruct POK as [EV|[EV _]]; [rewrite EV in CK3; cbn in CK3; lia|].
        clear - LSC E1 EV. destruct LSC as (_ & _ & _ & (_ & _ & (_ & _ & _ & _ & _ & _ & _ & (H' & Cu' & I' & _ & HPool & _)))).
        fold c in HPool. rewrite E1 in HPool. destruct HPool as [_ EV0]. rewrite EV0 in EV. discriminate. }
      subst Cu.
      destruct (cx_head c) as [ph|] eqn:Eh; [|congruence].
      unfold pool_mem in PM. rewrite Eh in PM. destruct PM as [PN _].
      pose proof (AH_range _ _ _ _ _ _ _ HEAP HH) as (HA0 & HA16 & _ & HAC & HAI).
      assert (NEH : ad_pc AD <> ph) by (eapply ids_ad_m; [exact IDS| unfold ad_ids; cbn; tauto| apply head_in_m; exact Eh]).
      pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HH NEH) as CXH.
      assert (INH : In (ph, H, 400) (OW ++ LB)) by (apply in_or_app; left; exact HH).
      pose proof (AH_acc_in _ _ _ _ (ph, H, 400) H 400 HEAP INH ltac:(cbn; lia) ltac:(cbn; lia)) as ACCH.
      assert (ALH : H mod 8 = 0) by (clear - HA16; Z.div_mod_to_equations; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch type of MU with munch ?W0 _ _ =>
          apply (rw_cells_transport bsegs W0 m mx (H + 384)) in PN; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end end.
      unfold MallocRep.wz in CX, PN.
      ub; shl. ub; chk0. ub; step. ub; step. do 2 (ub; step). ub; shl. ub; chk0. ub; shl. ub; chk0. ub; step. ub; step. ub; step. ub; step.
      rewrite (swrap32_wrap64 (- (1)) 1) by lia. change (- (1) + 1) with 0.
      ub; step. if_false.
      eapply FIN; [| exact FR| exact ST| exact MU| exact WM| exact MI|].
      * exact CX.
      * left. subst cur'. rewrite ELT. replace (pu' =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; exact EP0). cbn. auto.
    + (* [comment removed for export] *)
      ub; step. ub; step. ub; step.
      rewrite (swrap32_wrap64 (- (1)) 1) by lia. change (- (1) + 1) with 0.
      ub; step. if_false.
      eapply FIN; [| exact FR| exact ST| exact MU| exact WM| exact MI|].
      * exact CX.
      * subst cur'. replace (pu' =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). rewrite andb_false_r. exact HCUR0.
Qed.

End WithRT.
