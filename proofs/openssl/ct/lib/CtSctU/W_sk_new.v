(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac ApCells ApRepDefs ApWalkTac ApErrKit3.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sk_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
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

Definition OPENSSL_SK_NEW_NULL : Z := 0xe6a1c.
Definition OPENSSL_SK_SET_THUNKS : Z := 0xe6d44.
Definition OPENSSL_SK_SET_CMP_THUNKS : Z := 0xe6d78.
Definition OPENSSL_SK_SET_COPY_THUNKS : Z := 0xe6dac.

(* [comment removed for export] *)
Definition sk_cells0 (cmp fr cp : Z) : list cell :=
  [C4 (wz 0); C4 (wz 0); C8 (wz 0); C4 (wz 1); C4 (wz 0); C8 (wz 0); C8 (wz cmp); C8 (wz fr); C8 (wz cp)].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Definition SK_NEW_NULL_STACK : Z := 16 + CRYPTO_ZALLOC_STACK.

  Definition sk_zero_cells : list cell :=
    [C4 (wz 0); C4 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
  Lemma zero56_sk_cells : forall m A,
    rw_cells ctusegs m A [CB 56%nat (repeat (Z_to_bv 8 0) 56%nat)] -> rw_cells ctusegs m A sk_zero_cells.
  Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; repeat split; auto| unfold sk_zero_cells, MallocRep.wz; bytes_lit_eq| reflexivity]. Qed.

  (* [comment removed for export] *)
  Lemma OPENSSL_sk_new_null_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SK_NEW_NULL_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    k None = LUnr ->
    (forall p s' ms',
       calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L STACK_SIZE lo B m
                   (fun A m' => rw_cells ctusegs m' A (sk_cells0 0 0 0)) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc STACK_SIZE k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz OPENSSL_SK_NEW_NULL) fc None m (seg_rom ctusegs)).
  Proof using HM.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS KN K.
    unfold SK_NEW_NULL_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, OPENSSL_SK_NEW_NULL, STACK_SIZE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 4 step. do 5 step.
    name_mem m1.
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
    eapply (CRYPTO_zalloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := 56);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
    replace (ret_pc (Z_to_bv 64 944704)) with (Z_to_bv 64 944704) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    apply zero56_sk_cells in BLK. unfold sk_zero_cells, MallocRep.wz in BLK.
    assert (SEPA : A + 56 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) by lia.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 16, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    eapply implM_evt with (P := calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L 56 lo B m
                   (fun A m' => rw_cells ctusegs m' A (sk_cells0 0 0 0)) p st1);
      [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 56)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    assert (ND : List.NoDup (map blk_id ((p, A, 56) :: L))) by (eapply LH_nodup; exact HEAP3).
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 56)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]];
        [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      pose proof (LH_disjoint _ _ _ (p, A, 56) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
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
    name_mem m2. apply evt_done. unfold calloc_post, MallocRep.wz.
    do 14 eexists. exists m2, A, errv2. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [unfold LX_ERRNO, RATP; exact ERR3|].
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|].
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [exact HP0|]. eapply heap_pres_of_munch; [exact MU3| exact WM3| apply CLI3]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|].
             constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (p, A, 56)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    unfold sk_cells0, MallocRep.wz. exact BLK.
  Qed.
End Proofs.

(* [comment removed for export] *)
Definition setter_site (entry : Z) (cmp fr cp f cmp' fr' cp' : Z) : Prop :=
  (entry = OPENSSL_SK_SET_CMP_THUNKS /\ cmp' = f /\ fr' = fr /\ cp' = cp)
  \/ (entry = OPENSSL_SK_SET_THUNKS /\ cmp' = cmp /\ fr' = f /\ cp' = cp)
  \/ (entry = OPENSSL_SK_SET_COPY_THUNKS /\ cmp' = cmp /\ fr' = fr /\ cp' = f).

Lemma OPENSSL_sk_set_thunk_spec : forall (entry cmp fr cp f cmp' fr' cp' : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SA : Z),
  setter_site entry cmp fr cp f cmp' fr' cp' ->
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
  rblock_range SA STACK_SIZE -> rw_cells ctusegs m SA (sk_cells0 cmp fr cp) -> 0 <= f < 2^64 ->
  a0 = wz SA -> a1 = wz f ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz SA) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctusegs)
               /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (SA, SA + STACK_SIZE)] m m' /\ wmono ctusegs m m'
               /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
               /\ rw_cells ctusegs m' SA (sk_cells0 cmp' fr' cp'))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz entry) fc None m (seg_rom ctusegs)).
Proof.
  intros until SA. intros SITE ST MI CEIL GLO LO BR HC Hf -> ->.
  unfold OPENSSL_SK_SET_CMP_THUNKS, OPENSSL_SK_SET_THUNKS, OPENSSL_SK_SET_COPY_THUNKS, STACK_SIZE, GLOBALS_TOP, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
  destruct BR as (B0 & B16 & _ & BC & BI).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (SA, SA + 56)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  assert (SEPA : SA + 56 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= SA) by lia.
  unfold sk_cells0, MallocRep.wz in HC.
  destruct SITE as [(-> & -> & -> & ->)|[(-> & -> & -> & ->)|(-> & -> & -> & ->)]];
    (carve_frame 16%nat ST; do 4 step;
     step; if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]; clear K; step; uchk;
     step; do 3 step; release_frame FR ST (bv_unsigned sp); step;
     name_mem m2; apply evt_done; do 15 eexists; split; [reflexivity|];
     split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST|]; unfold sk_cells0, MallocRep.wz; exact HC).
Qed.
End WithCeiling0.
