(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac ApCells ApRepDefs ApWalkTac W_prefix_create.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac bytes_lit_eq := cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]].
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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Definition SCT_NEW_STACK : Z := 16 + CRYPTO_ZALLOC_STACK.

  (* [comment removed for export] *)
  Definition sct_zero_cells : list cell :=
    [C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0)].
  (* [comment removed for export] *)
  Definition sct_new_cells (m1 : word) : list cell :=
    [C4 m1; C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 m1; C4 (wz 0); C4 (wz 0); C4 (wz 0)].

  Lemma zero104_sct_cells : forall m A,
    rw_cells ctusegs m A [CB 104%nat (repeat (Z_to_bv 8 0) 104%nat)] -> rw_cells ctusegs m A sct_zero_cells.
  Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; repeat split; auto| unfold sct_zero_cells, MallocRep.wz; bytes_lit_eq| reflexivity]. Qed.

  Lemma SCT_new_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SCT_NEW_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    k None = LUnr ->
    (forall p s' ms',
       calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L SCT_SIZE lo B m
                   (fun A m' => rw_cells ctusegs m' A (sct_new_cells (Z_to_bv 64 (-1)))) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc SCT_SIZE k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz SCT_NEW) fc None m (seg_rom ctusegs)).
  Proof using HM.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS KN K.
    unfold SCT_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, SCT_NEW, SCT_SIZE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    unfold implM. iprefix.
    carve_frame 16%nat ST. do 9 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_zalloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := 104);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
    replace (ret_pc (Z_to_bv 64 1692896)) with (Z_to_bv 64 1692896) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    apply zero104_sct_cells in BLK. unfold sct_zero_cells, MallocRep.wz in BLK.
    assert (SEPA : A + 104 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) by lia.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 16, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    eapply implM_evt with (P := calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L 104 lo B m
                   (fun A m' => rw_cells ctusegs m' A (sct_new_cells (Z_to_bv 64 (-1)))) p st1);
      [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 104)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    assert (ND : List.NoDup (map blk_id ((p, A, 104) :: L))) by (eapply LH_nodup; exact HEAP3).
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 104)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]];
        [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      pose proof (LH_disjoint _ _ _ (p, A, 104) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      assert (p <> blk_id b') as NE.
      { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map. exact Hb'. }
      specialize (DJ NE). split; [lia| split; [lia| exact I]]. }
    unfold MallocRep.wz.
    (* [comment removed for export] *)
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. uchk. step. step. step.
    do 3 step. release_frame FR ST3 (bv_unsigned sp). step.
    apply evt_done. unfold calloc_post, MallocRep.wz.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m2 end.
    do 14 eexists. exists m2, A, errv2. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [unfold LX_ERRNO, RATP; exact ERR3|].
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|].
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [exact HP0|]. eapply heap_pres_of_munch; [exact MU3| exact WM3| apply CLI3]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|].
             constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (p, A, 104)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    unfold sct_new_cells, MallocRep.wz. exact BLK.
  Qed.
End Proofs.
End WithCeiling0.
