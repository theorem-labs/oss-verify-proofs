(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApWalkTac W_prefix_create.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
Ltac bytes_lit_eq := cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]].

(* [comment removed for export] *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))      (* [comment removed for export] *)
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.


Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition ASN1_OBJECT_FREE : Z := 0xfd754.
  Definition ASN1_OBJECT_FREE_STACK : Z := 32 + CRYPTO_FREE_STACK.
  Definition AOBJ_DYN_FLAGS : Z := 9.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition vfree_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (L' : list block) (lo B : Z) (errv : word) (m : mem) (fin : mem -> Prop)
      (s' : PState) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' LX_ERRNO [C4 errv] /\ rauxv_ok m' B
      /\ rheap_pres L' (bv_unsigned sp) m m'
      /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
      /\ RHEAP s' L' m' /\ fin m'.

  (* [comment removed for export] *)
  Lemma ASN1_OBJECT_free_dyn_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (pblk pdata : bptr) (A D alloc nid len : Z)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ASN1_OBJECT_FREE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    In (pblk, A, ASN1_OBJECT_SIZE) L -> In (pdata, D, alloc) L -> pblk <> pdata ->
    rw_cells ctusegs m A (asn1_object_cells 0 0 nid len D AOBJ_DYN_FLAGS) ->
    a0 = wz A ->
    (forall s' ms', vfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pblk (lb_remove pdata L)) lo B errv m
                      (fun m' => True) s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (LFree pdata (LFree pblk k))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ASN1_OBJECT_FREE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS HBIN HDIN NBD HB -> K.
    unfold ASN1_OBJECT_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK, ASN1_OBJECT_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP HBIN) as (BB0 & BB1 & BB2 & BB3 & BB4).
    pose proof (LH_block_range _ _ _ _ HEAP HDIN) as (BD0 & BD1 & BD2 & BD3 & BD4).
    unfold ASN1_OBJECT_SIZE in *. cbn [blk_addr blk_size fst snd] in *.
    assert (SEPB : A + 40 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= A) by lia.
    unfold asn1_object_cells, AOBJ_DYN_FLAGS, MallocRep.wz in HB.
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 6 step.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. step. if_cases KC; zify_cond KC; [exfalso; rewrite ?unsigned_lit in KC by lia; change 7 with (Z.ones 3) in KC; rewrite Z.land_ones in KC by lia; clear - KC BB1; Z.div_mod_to_equations; lia|]. clear KC.
    step. replace (zx32 (Z_to_bv 64 9)) with (Z_to_bv 64 9) by reflexivity.
    step. step. if_cases K1; zify_cond K1; [|exfalso; revert K1; vm_compute; congruence]. clear K1.
    step. step. if_cases K2; zify_cond K2; [exfalso; revert K2; vm_compute; congruence|]. clear K2.
    step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m1) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := D) (n := alloc);
      [exact HEAP1 | exact HDIN | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | ].
    intros st1 ms1 PO. unfold cfree_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & HEAP3).
    replace (ret_pc (Z_to_bv 64 1038296)) with (Z_to_bv 64 1038296) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in HB;
      [| intros a Ha; right; right; exists (pblk, A, 40); split; [apply lb_remove_In; split; [exact HBIN| cbn; congruence]| cbn; cbn in Ha; lia]].
    assert (CS3 : crypto_statics m3).
    { eapply crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP)| | exact CS1].
      intros a Ha. right. left. split; [revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia|].
      revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (HBIN3 : In (pblk, A, 40) (lb_remove pdata L)) by (apply lb_remove_In; split; [exact HBIN| cbn; congruence]).
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 40)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    unfold implM. iprefix.
    step. replace (sx32 (Z_to_bv 64 9)) with (Z_to_bv 64 9) by reflexivity. step. step.
    step. step. if_cases K3; zify_cond K3; [| exfalso; lia]. clear K3.
    do 9 step. release_frame FR ST3 (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HEAP2 : RHEAP st1 (lb_remove pdata L) m2).
    { eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|].
      constructor; [apply W_ok_stack; cbn; lia|].
      constructor; [eapply (W_ok_block _ (pblk, A, 40)); [exact HBIN3| cbn; lia| cbn; lia]| constructor]. }
    assert (AUX2 : rauxv_ok m2 B).
    { eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (CS2 : crypto_statics m2).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU3 WM3)| | exact CS3].
      intros a Ha. cbn. split; [|split; [|exact I]]; revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia. }
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pblk (lb_remove pdata L)) (bv_unsigned sp) a ->
                             outside [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 40)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [split; [lia|split; [lia|exact I]] | split; [lia|split; [lia|exact I]] |].
      pose proof Hb' as Hb''. apply lb_remove_In in Hb''. destruct Hb'' as [Hb3 NE3]. apply lb_remove_incl in Hb3.
      pose proof (LH_block_range _ _ _ _ HEAP Hb3) as (_ & _ & _ & B3' & _).
      pose proof (LH_disjoint _ _ _ _ _ HEAP Hb3 HBIN ltac:(cbn; cbn in NE3; congruence)) as DJ. cbn in DJ.
      split; [lia|]. split; [|exact I]. destruct b' as [[bp ba] bn]. cbn in *. unfold in_block in Hr. cbn in Hr. lia. }
    assert (HP3 : rheap_pres (lb_remove pblk (lb_remove pdata L)) (bv_unsigned sp) m3 m2) by (eapply heap_pres_of_munch; [exact MU3| exact WM3| apply CLI3]).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := A) (n := 40);
      [exact HEAP2 | exact HBIN3 | exact AUX2 | lia | exact ST3 | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR3 | match goal with H : mem_inv _ m2 |- _ => exact H end | reflexivity
      | exact CS2 | reflexivity | ].
    intros st2 ms2 PO. apply K. unfold cfree_post in PO. unfold vfree_post.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    do 15 eexists. exists m4. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|].
    split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply lb_remove_incl; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [exact HP3|].
             replace (lb_remove pblk (lb_remove pdata L)) with (lb_remove pblk (lb_remove pdata L)) by reflexivity. exact HP4. }
    split; [congruence|]. split; [congruence|]. split; [exact HEAP4| exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma ASN1_OBJECT_free_static_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo X : Z),
    stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 32)%Z ->
    ro_cells ctusegs m (X + 32) [C4 (wz 0)] -> 0 < X -> X + 40 <= lo -> X mod 8 = 0 -> a0 = wz X ->
    evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom ctusegs)
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
        /\ stk ctusegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASN1_OBJECT_FREE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until X. intros ST MI GLO LO FL XP XL XAL ->.
    unfold ASN1_OBJECT_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ FL) as XB. cbn in XB.
    carve_frame 32%nat ST. do 6 zstep.
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; rewrite ?unsigned_lit in KC by lia; change 7 with (Z.ones 3) in KC; rewrite Z.land_ones in KC by lia; clear - KC XAL; Z.div_mod_to_equations; lia|]. clear KC.
    zstep. zstep.
    zstep. if_cases K1; zify_cond K1; [|exfalso; revert K1; vm_compute; congruence]. clear K1.
    zstep. zstep. if_cases K2; zify_cond K2; [|exfalso; revert K2; vm_compute; congruence]. clear K2.
    zstep. zstep. if_cases K3; zify_cond K3; [exfalso; revert K3; vm_compute; congruence|]. clear K3.
    do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    replace (Z.land (bv_unsigned (zx32 (Z_to_bv 64 0))) 1) with 0 by reflexivity.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ASN1_OBJECT_free_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
    stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 32)%Z ->
    a0 = Z_to_bv 64 0 ->
    evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom ctusegs)
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
        /\ stk ctusegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASN1_OBJECT_FREE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until lo. intros ST MI GLO LO ->.
    unfold ASN1_OBJECT_FREE, GLOBALS_TOP in *.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    carve_frame 32%nat ST. do 6 zstep.
    zstep. if_cases K0; zify_cond K0; [|exfalso; apply K0; reflexivity]. clear K0.
    do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    finish.
  Qed.

End Proofs.
End WithCeiling0.
