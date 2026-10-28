(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac W_prefix_create W_bio_push W_locks W_ex_data W_bio_new.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac al8chk A := step; let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso; rewrite ?unsigned_lit in K by lia; try (change 7 with (Z.ones 3) in K; rewrite Z.land_ones in K by lia); clear - K A; Z.div_mod_to_equations; lia | clear K].
Local Ltac al4chk A := step; let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso; rewrite ?unsigned_lit in K by lia; try (change 3 with (Z.ones 2) in K; rewrite Z.land_ones in K by lia); clear - K A; Z.div_mod_to_equations; lia | clear K].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition bio_dead_cells (meth init ptr next prev nw : Z) : list cell :=
  [C8 (wz 0); C8 (wz meth); C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz init); C4 (wz 1); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz ptr); C8 (wz next); C8 (wz prev);
   C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz nw); C8 (wz 0); C8 (wz 0)].

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma prefix_destroy_walk0 : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (pb ppre pctx : bptr) (bio meth init nxt prev nw ctxA preA npre indent linestart : Z)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - PREFIX_DESTROY_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    In (pb, bio, BIO_SIZE) L -> In (ppre, preA, npre) L -> In (pctx, ctxA, PREFIX_CTX_SIZE) L -> pb <> pctx -> pb <> ppre -> ppre <> pctx ->
    rw_cells ctusegs m bio (bio_dead_cells meth init ctxA nxt prev nw) ->
    rw_cells ctusegs m ctxA (prefix_ctx_cells preA indent linestart) ->
    a0 = wz bio ->
    (forall s' ms', free2_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pctx (lb_remove ppre L)) lo B errv m 1
                      (fun m' => rw_cells ctusegs m' bio (bio_dead_cells meth init ctxA nxt prev nw)) s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (LFree ppre (LFree pctx k))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz PREFIX_DESTROY) fc None m (seg_rom ctusegs)).
  Proof using HF.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS HBIN HPIN HCIN NBC NBP NPC HB HC -> K.
    unfold PREFIX_DESTROY_STACK, CRYPTO_FREE_STACK, RFREE_STACK, PREFIX_DESTROY, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP HBIN) as (BB0 & BB1 & BB2 & BB3 & BB4).
    pose proof (LH_block_range _ _ _ _ HEAP HCIN) as (BC0 & BC1 & BC2 & BC3 & BC4).
    unfold BIO_SIZE, PREFIX_CTX_SIZE in *. cbn [blk_addr blk_size fst snd] in *.
    assert (SEPB : bio + 128 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bio) by lia.
    assert (SEPC : ctxA + 16 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= ctxA) by lia.
    unfold bio_dead_cells, MallocRep.wz in HB. unfold prefix_ctx_cells, MallocRep.wz in HC.
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 6 step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 5 step. step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ. step. al8chk BB1. do 4 step. release_frame FR0 ST (bv_unsigned sp + -32).
    step. step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|]. clear KZ. step. step. al8chk BC1. do 6 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply BnRep.crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m1) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := preA) (n := npre);
      [exact HEAP1 | exact HPIN | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | ].
    intros st1 ms1 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & HEAP3).
    replace (ret_pc (Z_to_bv 64 1307808)) with (Z_to_bv 64 1307808) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in HB;
      [| intros a Ha; right; right; exists (pb, bio, 128); split; [apply lb_remove_In; split; [exact HBIN| cbn; congruence]| cbn; cbn in Ha; lia]].
    assert (CS3 : crypto_statics m3).
    { eapply BnRep.crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP)| | exact CS1].
      intros a Ha. right. left. split; [revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia|].
      revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (HCIN3 : In (pctx, ctxA, 16) (lb_remove ppre L)) by (apply lb_remove_In; split; [exact HCIN| cbn; congruence]).
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    unfold implM. iprefix. do 4 step.
    assert (ND : List.NoDup (map blk_id L)) by (eapply LH_nodup; exact HEAP).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := ctxA) (n := 16);
      [exact HEAP3 | exact HCIN3 | exact AUX3 | rewrite ESP; lia | rewrite ESP; exact ST3 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR3 | exact MI3 | reflexivity
      | exact CS3 | reflexivity | ].
    intros st2 ms2 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    replace (ret_pc (Z_to_bv 64 1307824)) with (Z_to_bv 64 1307824) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP4)) in HB;
      [| intros a Ha; right; right; exists (pb, bio, 128); split; [apply lb_remove_In; split; [apply lb_remove_In; split; [exact HBIN| cbn; congruence]| cbn; congruence]| cbn; cbn in Ha; lia]].
    eapply implM_evt with (P := free2_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pctx (lb_remove ppre L)) lo B errv m 1
                   (fun m' => rw_cells ctusegs m' bio (bio_dead_cells meth init ctxA nxt prev nw)) st2); [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m4) as MU4. pose proof (wmono_refl ctusegs m4) as WM4.
    unfold LX_ERRNO, RATP in ERR4. change (3355176 - 164) with 3355012 in ERR4.
    assert (CLI4 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pctx (lb_remove ppre L)) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      apply lb_remove_incl in Hb'. apply lb_remove_incl in Hb'. pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    unfold MallocRep.wz. step. do 5 step. release_frame FR ST4 (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    apply evt_done. unfold free2_post, MallocRep.wz.
    do 14 eexists. exists m9. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|]. split; [unfold LX_ERRNO, RATP; exact ERR4|].
    split. { eapply rauxv_ok_frame; [exact AUX4| exact MU4| exact WM4|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply lb_remove_incl; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP4| lia| auto]|].
             eapply heap_pres_of_munch; [exact MU4| exact WM4| apply CLI4]. }
    split; [congruence|]. split; [congruence|].
    split. { eapply LH_frame; [exact HEAP4| exact MU4| exact WM4|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    unfold bio_dead_cells, MallocRep.wz. exact HB.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition BIO_FREE : Z := 0x10c238.
  Definition BIO_FREE_INT : Z := 0x10c260.
  (* [comment removed for export] *)
  Definition BIO_FREE_STACK : Z := 64 + PREFIX_DESTROY_STACK.

  Lemma BIO_free_prefix_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word) (E : ap_env)
      (pb ppre pctx : bptr) (A preA npre ctxA nxt prev nw indent linestart : Z)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - BIO_FREE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    ap_statics_fixed m E -> exlock_free m E -> In (p_xl E, e_xl E, MUTEX_SIZE) L ->
    ro_cells ctusegs m (AP_PREFIX_METH + 80) [C8 (wz PREFIX_DESTROY)] ->
    In (pb, A, BIO_SIZE) L -> In (ppre, preA, npre) L -> In (pctx, ctxA, PREFIX_CTX_SIZE) L ->
    pb <> pctx -> pb <> ppre -> ppre <> pctx -> p_xl E <> pb -> p_xl E <> ppre -> p_xl E <> pctx ->
    rw_cells ctusegs m A (bio_cells AP_PREFIX_METH 1 ctxA nxt prev nw) ->
    rw_cells ctusegs m ctxA (prefix_ctx_cells preA indent linestart) ->
    a0 = wz A -> bv_unsigned sp mod 16 = 0 ->
    (forall s' ms', free2_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pb (lb_remove pctx (lb_remove ppre L))) lo B errv m 1
                      (fun _ => True) s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (LFree ppre (LFree pctx (LFree pb k)))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BIO_FREE) fc None m (seg_rom ctusegs)).
  Proof using HF.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> SF HXL HXLIN HMD HBIN HPIN HCIN NBC NBP NPC NXB NXP NXC HB HC -> SP16 K.
    unfold BIO_FREE_STACK, PREFIX_DESTROY_STACK, CRYPTO_FREE_STACK, RFREE_STACK, BIO_FREE, GLOBALS_TOP, MUTEX_SIZE, BIO_SIZE, PREFIX_CTX_SIZE, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof SF as SF0. destruct SF0 as (CS & _).
    pose proof (LH_block_range _ _ _ _ HEAP HXLIN) as (BX0 & BX1 & BX2 & BX3 & BX4).
    pose proof (LH_block_range _ _ _ _ HEAP HBIN) as (BB0 & BB1 & BB2 & BB3 & BB4).
    pose proof (LH_block_range _ _ _ _ HEAP HCIN) as (BC0 & BC1 & BC2 & BC3 & BC4).
    cbn [blk_addr blk_size fst snd] in *.
    assert (ND : List.NoDup (map blk_id L)) by (eapply LH_nodup; exact HEAP).
    pose proof (LH_disjoint _ _ _ (pb, A, 128) (p_xl E, e_xl E, 40) HEAP HBIN HXLIN ltac:(cbn; congruence)) as DJX.
    pose proof (LH_disjoint _ _ _ (pb, A, 128) (pctx, ctxA, 16) HEAP HBIN HCIN ltac:(cbn; congruence)) as DJC.
    pose proof (LH_disjoint _ _ _ (pctx, ctxA, 16) (p_xl E, e_xl E, 40) HEAP HCIN HXLIN ltac:(cbn; congruence)) as DJCX.
    cbn [blk_addr blk_size blk_id fst snd] in DJX, DJC, DJCX.
    assert (SEPX : e_xl E + 40 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= e_xl E) by lia.
    assert (SEPB : A + 128 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= A) by lia.
    assert (SEPC : ctxA + 16 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= ctxA) by lia.
    unfold AP_PREFIX_METH in HMD. change (2963608 + 80) with 2963688 in HMD.
    assert (SEPMD : 2963688 + 8 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= 2963688) by lia.
    unfold exlock_free in HXL. unfold mutex_free_cells, zeros4, MallocRep.wz in HXL. cbn [repeat] in HXL.
    unfold bio_cells, MallocRep.wz in HB. unfold prefix_ctx_cells, MallocRep.wz in HC.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    assert (AMO : amo_aligned AW (Z_to_bv 64 (A + 88)) = true) by (apply amo_aligned_w_intro; lia).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + 128)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 4 step. step. step.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 6 step.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. al8chk BB1. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of HB with context [C4 (Z_to_bv 64 (bv_unsigned ?XX))] => change (bv_unsigned XX) with 0%Z in HB end.
    rewrite (sx32_small 1) by lia.
    step. step. if_false. step. al4chk SP16. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. if_false. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. rewrite (sx32_small 0) by lia. (* [comment removed for export] *)
    step. if_false. (* [comment removed for export] *)
    step. step. if_false. (* [comment removed for export] *)
    step. step. if_true. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. if_false. unfold AP_PREFIX_METH. step. assert (MA8 : 2963608 mod 8 = 0) by reflexivity. al8chk MA8. clear MA8. step. (* [comment removed for export] *)
    step. if_false. step. step. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 PREFIX_DESTROY)) with (Z_to_bv 64 PREFIX_DESTROY) by (symmetry; apply ret_pc_even; [unfold PREFIX_DESTROY; lia| reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HEAP2 : RHEAP s L m2).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [eapply (W_ok_block _ (pb, A, 128)); [exact HBIN| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX2 : rauxv_ok m2 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (AG2 : agree_on (lib_addr []) m m2).
    { eapply lib_agree_of_munch; [exact MU| exact WM|]. intros a Ha. cbn. lia. }
    assert (CS2 : crypto_statics m2) by (eapply (ApRep.crypto_statics_agree []); [exact CS| exact AG2]).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pb L) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + 128)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]];
        [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      apply lb_remove_In in Hb0. destruct Hb0 as [Hb' Hnp].
      pose proof (LH_disjoint _ _ _ (pb, A, 128) b' HEAP HBIN Hb' ltac:(cbn; congruence)) as DJ. cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). split; [lia| split; [lia| exact I]]. }
    assert (HP0 : rheap_pres (lb_remove pb L) (bv_unsigned sp) m m2) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (prefix_destroy_walk0) with (B := B) (lo := lo) (errv := errv) (pb := pb) (bio := A) (meth := AP_PREFIX_METH) (init := 1)
           (ctxA := ctxA) (nxt := nxt) (prev := prev) (nw := nw) (preA := preA) (npre := npre) (indent := indent) (linestart := linestart);
      [exact HEAP2 | exact AUX2 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold PREFIX_DESTROY_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia
      | unfold LX_ERRNO, RATP; eassumption | eassumption | reflexivity | exact CS2
      | exact HBIN | exact HPIN | exact HCIN | exact NBC | exact NBP | exact NPC
      | unfold bio_dead_cells, AP_PREFIX_METH, MallocRep.wz; exact HB | unfold prefix_ctx_cells, MallocRep.wz; exact HC | reflexivity | ].
    intros st3 ms3 PO. unfold free2_post in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP3 & FA3 & SO3 & HEAP3 & HB3).
    replace (ret_pc (Z_to_bv 64 1098520)) with (Z_to_bv 64 1098520) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP3)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP3)) in FR0; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP3)) in HXL;
      [| intros a Ha; right; right; exists (p_xl E, e_xl E, 40); split;
         [apply lb_remove_In; split; [apply lb_remove_In; split; [exact HXLIN| cbn; congruence]| cbn; congruence]| cbn; cbn in Ha; lia]].
    assert (AG3 : agree_on (lib_addr []) m m3) by (eapply agree_on_trans; [exact AG2| eapply lib_agree_of_heap_pres; exact HP3]).
    assert (SF3 : ap_statics_fixed m3 E) by (eapply (ap_statics_fixed_agree []); [exact SF| exact AG3]).
    assert (HBIN3 : In (pb, A, 128) (lb_remove pctx (lb_remove ppre L))).
    { apply lb_remove_In. split; [apply lb_remove_In; split; [exact HBIN| cbn; congruence]| cbn; congruence]. }
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    unfold bio_dead_cells, MallocRep.wz in HB3.
    (* [comment removed for export] *)
    lazymatch type of HB3 with rw_cells _ _ _ ?cs =>
      lazymatch eval cbv in (firstn 18%nat cs) with ?cs1 =>
      lazymatch eval cbv in (skipn 18%nat cs) with ?cs2 =>
        change cs with (cs1 ++ cs2) in HB3 end end end.
    apply rw_cells_app in HB3. destruct HB3 as [HB1 HAD]. cbn [cells_size csize Nat.add] in HAD. replace (Z.of_nat 112) with 112 in HAD by reflexivity.
    pose proof (munch_refl [(bv_unsigned sp - 448, bv_unsigned sp); (A + 112, A + 128)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    unfold MallocRep.wz. unfold implM. iprefix.
    do 3 step. step. (* [comment removed for export] *)
    eapply evt_cut.
    { eapply CRYPTO_free_ex_data_spec with (lo := lo) (E := E) (ad := A + 112);
        [rewrite ESP; exact ST3| exact MI3| unfold GLOBALS_TOP; lia| rewrite ESP; unfold FREE_EX_DATA_STACK; lia| reflexivity| exact SF3| exact HXL
        | unfold obj_range, MUTEX_SIZE, GLOBALS_TOP; lia| lia| exact HAD| unfold obj_range, GLOBALS_TOP; lia| clear - BB1; Z.div_mod_to_equations; lia| unfold MUTEX_SIZE; lia
        | reflexivity| reflexivity]. }
    clear HAD HXL SF3. post_call_esp ESP m3. rewrite ?ESP in *.
    match goal with H : stk ctusegs _ lo (bv_unsigned sp + -64) |- _ => rename H into ST4 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (AG4 : agree_on (lib_addr []) m m4).
    { eapply agree_on_trans; [exact AG3| eapply lib_agree_of_munch; [exact MU3| exact WM3|]]. intros a Ha. cbn. lia. }
    assert (HEAP4 : RHEAP st3 (lb_remove pctx (lb_remove ppre L)) m4).
    { eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|].
      constructor; [apply W_ok_stack; cbn; lia|]. constructor; [eapply (W_ok_block _ (pb, A, 128)); [exact HBIN3| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (CS4 : crypto_statics m4) by (eapply (ApRep.crypto_statics_agree []); [exact CS| exact AG4]).
    do 4 step. step. (* [comment removed for export] *)
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := A) (n := 128);
      [exact HEAP4 | exact HBIN3 | exact AUX4 | rewrite ESP; lia | rewrite ESP; exact ST4 | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; eassumption | eassumption | reflexivity
      | exact CS4 | reflexivity | ].
    intros st5 ms5 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m5
                    & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & HEAP5).
    replace (ret_pc (Z_to_bv 64 1098556)) with (Z_to_bv 64 1098556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP5)) in FR0; [| intros a Ha; left; cbn in Ha; lia].
    eapply implM_evt with (P := free2_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pb (lb_remove pctx (lb_remove ppre L))) lo B errv m 1
                   (fun _ => True) st5); [| intros ms' PO'; apply K; exact PO'].
    unfold LX_ERRNO, RATP in ERR5. change (3355176 - 164) with 3355012 in ERR5.
    unfold MallocRep.wz.
    step. step. (* [comment removed for export] *)
    do 4 step. step. release_frame FR0 ST5 (bv_unsigned sp + -32). step.
    (* [comment removed for export] *)
    do 2 step. step. release_frame FR ST5 (bv_unsigned sp). step.
    apply evt_done. unfold free2_post, MallocRep.wz.
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pb (lb_remove pctx (lb_remove ppre L))) (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 448, bv_unsigned sp); (A + 112, A + 128)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]];
        [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      apply lb_remove_In in Hb0. destruct Hb0 as [Hb1 Hnp]. apply lb_remove_incl in Hb1. apply lb_remove_incl in Hb1.
      pose proof (LH_disjoint _ _ _ (pb, A, 128) b' HEAP HBIN Hb1 ltac:(cbn; congruence)) as DJ. cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb1) as (_ & _ & _ & B3' & _). split; [lia| split; [lia| exact I]]. }
    do 14 eexists. exists m5. split; [reflexivity|].
    split; [exact MI5|]. split; [exact ST5|]. split; [unfold LX_ERRNO, RATP; exact ERR5|]. split; [exact AUX5|].
    split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; apply lb_remove_In; apply lb_remove_In in Hb;
                                          destruct Hb as [Hb Hn]; split; [eapply lb_remove_incl; eapply lb_remove_incl; exact Hb| exact Hn]]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP3| lia| intros b Hb; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU3| exact WM3| apply CLI3]|].
             eapply rheap_pres_weaken; [exact HP5| lia| auto]. }
    split; [congruence|]. split; [congruence|]. split; [exact HEAP5| exact I].
  Qed.
End Proofs.
End WithCeiling0.
