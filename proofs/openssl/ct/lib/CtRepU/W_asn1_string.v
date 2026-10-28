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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push W_prefix_create W_obj_free.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac step := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.

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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ASN1_STRING_TYPE_NEW : Z := 0xfe300.
  Definition ASN1_STRING_TYPE_NEW_STACK : Z := 32 + CRYPTO_ZALLOC_STACK.

  (* [comment removed for export] *)
  Lemma zero24_string_cells : forall m A,
    rw_cells ctusegs m A [CB 24%nat (repeat (Z_to_bv 8 0) 24%nat)] -> rw_cells ctusegs m A [C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0)].
  Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; auto| unfold MallocRep.wz; bytes_lit_eq| reflexivity]. Qed.

  Lemma ASN1_STRING_type_new_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (ty : Z)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ASN1_STRING_TYPE_NEW_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    a0 = wz ty -> 0 <= ty < 2^31 ->
    k None = LUnr ->
    (forall p s' ms',
       calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L 24 lo B m
                   (fun A m' => rw_cells ctusegs m' A (asn1_string_cells 0 ty 0 0)) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc 24 k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ASN1_STRING_TYPE_NEW) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS -> TY KN K.
    unfold ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, ASN1_STRING_TYPE_NEW, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    unfold implM. iprefix.
    carve_frame 32%nat ST. do 11 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_zalloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := 24);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & A & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
    replace (ret_pc (Z_to_bv 64 1041196)) with (Z_to_bv 64 1041196) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    apply zero24_string_cells in BLK.
    assert (SEPA : A + 24 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= A) by lia.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    eapply implM_evt with (P := calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L 24 lo B m
                   (fun A m' => rw_cells ctusegs m' A (asn1_string_cells 0 ty 0 0)) p st1);
      [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 24)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    assert (ND : List.NoDup (map blk_id ((p, A, 24) :: L))) by (eapply LH_nodup; exact HEAP3).
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 24)] a).
    { intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]];
        [split; [lia| split; [lia| exact I]] | split; [lia| split; [lia| exact I]] |].
      pose proof (LH_disjoint _ _ _ (p, A, 24) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      assert (p <> blk_id b') as NE.
      { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map. exact Hb'. }
      specialize (DJ NE). split; [lia| split; [lia| exact I]]. }
    unfold MallocRep.wz.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step.
    do 4 step. release_frame FR ST3 (bv_unsigned sp). step.
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
             constructor; [eapply (W_ok_block _ (p, A, 24)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    unfold asn1_string_cells, MallocRep.wz. exact BLK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ASN1_STRING_FREE : Z := 0xfe120.
  Definition OSSL_ASN1_STRING_FREE_INT : Z := 0xfe354.
  Definition ASN1_STRING_FREE_STACK : Z := 48 + CRYPTO_FREE_STACK.

  Lemma str_cells_w : forall m A pre,
    rw_cells ctusegs m A (pre ++ [C8 (wz 0)]) -> rw_cells ctusegs m A (pre ++ [C4 (wz 0); C4 (wz 0)]).
  Proof.
    intros m A pre H. eapply rw_cells_recast; [exact H| | |].
    - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn. tauto.
    - rewrite !cells_bytes_app. f_equal.
    - rewrite !cells_size_app. reflexivity.
  Qed.
  Lemma str_cells_d : forall m A pre,
    rw_cells ctusegs m A (pre ++ [C4 (wz 0); C4 (wz 0)]) -> rw_cells ctusegs m A (pre ++ [C8 (wz 0)]).
  Proof.
    intros m A pre H. eapply rw_cells_recast; [exact H| | |].
    - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn. tauto.
    - rewrite !cells_bytes_app. f_equal.
    - rewrite !cells_size_app. reflexivity.
  Qed.
  Lemma str_cells_b : forall m A pre,
    rw_cells ctusegs m A (pre ++ [C8 (wz 0)]) ->
    rw_cells ctusegs m A (pre ++ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (wz 0)]).
  Proof.
    intros m A pre H. eapply rw_cells_recast; [exact H| | |].
    - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn. tauto.
    - rewrite !cells_bytes_app. f_equal.
    - rewrite !cells_size_app. reflexivity.
  Qed.
  Lemma str_cells_db : forall m A pre,
    rw_cells ctusegs m A (pre ++ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (wz 0)]) ->
    rw_cells ctusegs m A (pre ++ [C8 (wz 0)]).
  Proof.
    intros m A pre H. eapply rw_cells_recast; [exact H| | |].
    - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn. tauto.
    - rewrite !cells_bytes_app. f_equal.
    - rewrite !cells_size_app. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ASN1_STRING_free_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (pblk pdata : bptr) (A D alloc len ty : Z)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ASN1_STRING_FREE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    In (pblk, A, ASN1_STRING_SIZE) L -> In (pdata, D, alloc) L -> pblk <> pdata ->
    rw_cells ctusegs m A (asn1_string_cells len ty D 0) ->
    a0 = wz A ->
    (forall s' ms', vfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pblk (lb_remove pdata L)) lo B errv m
                      (fun m' => True) s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (LFree pdata (LFree pblk k))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ASN1_STRING_FREE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS HBIN HDIN NBD HB -> K.
    unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK, ASN1_STRING_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP HBIN) as (BB0 & BB1 & BB2 & BB3 & BB4).
    pose proof (LH_block_range _ _ _ _ HEAP HDIN) as (BD0 & BD1 & BD2 & BD3 & BD4).
    unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in *.
    assert (SEPB : A + 24 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= A) by lia.
    unfold asn1_string_cells, MallocRep.wz in HB.
    change ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 0)])
      with ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 D)] ++ [C8 (wz 0)]) in HB.
    apply str_cells_w in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 4 step.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 7 step.
    step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    do 3 step.
    change ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
      with ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 D)] ++ [C4 (wz 0); C4 (wz 0)]) in HB.
    apply str_cells_d in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
    step.
    step. step. if_cases K2; zify_cond K2; [|exfalso; revert K2; vm_compute; congruence]. clear K2.
    step. step. if_cases K3; zify_cond K3; [exfalso; revert K3; vm_compute; congruence|]. clear K3.
    step. step. if_cases K4; zify_cond K4; [|exfalso; apply K4; reflexivity]. clear K4.
    do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)] a).
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
    replace (ret_pc (Z_to_bv 64 1041436)) with (Z_to_bv 64 1041436) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in HB;
      [| intros a Ha; right; right; exists (pblk, A, 24); split; [apply lb_remove_In; split; [exact HBIN| cbn; congruence]| cbn; cbn in Ha; lia]].
    assert (CS3 : crypto_statics m3).
    { eapply crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP)| | exact CS1].
      intros a Ha. right. left. split; [revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia|].
      revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    assert (HBIN3 : In (pblk, A, 24) (lb_remove pdata L)) by (apply lb_remove_In; split; [exact HBIN| cbn; congruence]).
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    change ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 0)])
      with ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 D)] ++ [C8 (wz 0)]) in HB.
    apply str_cells_b in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
    unfold implM. iprefix.
    step. if_cases K5; zify_cond K5; [|exfalso; apply K5; reflexivity]. clear K5.
    step. step. step. if_cases K6; zify_cond K6; [exfalso; revert K6; vm_compute; congruence|]. clear K6.
    step. if_cases K7; zify_cond K7; [|exfalso; apply K7; reflexivity]. clear K7.
    do 4 step. do 6 step. release_frame FR ST3 (bv_unsigned sp). step.
    (* [comment removed for export] *)
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    change ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 D); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)])
      with ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 D)] ++ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (wz 0)]) in HB.
    apply str_cells_db in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := A) (n := 24);
      [exact HEAP3 | exact HBIN3 | exact AUX3 | lia | exact ST3 | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR3 | exact MI3 | reflexivity
      | exact CS3 | reflexivity | ].
    intros st2 ms2 PO. apply K. unfold cfree_post in PO. unfold vfree_post.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    do 15 eexists. exists m4. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|].
    split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply lb_remove_incl; eapply lb_remove_incl; exact Hb]|].
             eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; eapply lb_remove_incl; exact Hb]|].
             exact HP4. }
    split; [congruence|]. split; [congruence|]. split; [exact HEAP4| exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma ASN1_STRING_free_nodata_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (pblk : bptr) (A len ty : Z)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ASN1_STRING_FREE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    In (pblk, A, ASN1_STRING_SIZE) L ->
    rw_cells ctusegs m A (asn1_string_cells len ty 0 0) ->
    a0 = wz A ->
    (forall s' ms', vfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pblk L) lo B errv m
                      (fun m' => True) s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (LFree pblk k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ASN1_STRING_FREE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS HBIN HB -> K.
    unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK, ASN1_STRING_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP HBIN) as (BB0 & BB1 & BB2 & BB3 & BB4).
    unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in *.
    assert (SEPB : A + 24 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= A) by lia.
    unfold asn1_string_cells, MallocRep.wz in HB.
    change ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
      with ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 0)] ++ [C8 (wz 0)]) in HB.
    apply str_cells_w in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 4 step.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
    step. step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 7 step.
    step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    do 3 step.
    change ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
      with ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 0)] ++ [C4 (wz 0); C4 (wz 0)]) in HB.
    apply str_cells_d in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
    step.
    step. step. if_cases K2; zify_cond K2; [|exfalso; revert K2; vm_compute; congruence]. clear K2.
    step. step. if_cases K3; zify_cond K3; [exfalso; revert K3; vm_compute; congruence|]. clear K3.
    step. step. if_cases K4; zify_cond K4; [|exfalso; apply K4; reflexivity]. clear K4.
    do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (CRYPTO_free_null_spec) with (lo := lo);
        [rewrite ESP; exact ST| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact MI| exact CS1| reflexivity]. }
    clear CS1. post_call_esp ESP m1. rewrite ?ESP in *.
    match goal with H : stk ctusegs _ lo (bv_unsigned sp + -48) |- _ => rename H into ST3 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HEAP3 : RHEAP s L m3).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX3 : rauxv_ok m3 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS3 : crypto_statics m3).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 64, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3) by (eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]).
    change ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
      with ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 0)] ++ [C8 (wz 0)]) in HB.
    apply str_cells_b in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
    step. if_cases K5; zify_cond K5; [|exfalso; apply K5; reflexivity]. clear K5.
    step. step. step. if_cases K6; zify_cond K6; [exfalso; revert K6; vm_compute; congruence|]. clear K6.
    step. if_cases K7; zify_cond K7; [|exfalso; apply K7; reflexivity]. clear K7.
    do 4 step. do 6 step. release_frame FR ST3 (bv_unsigned sp). step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    change ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)])
      with ([C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 0)] ++ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (wz 0)]) in HB.
    apply str_cells_db in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
    eapply (CRYPTO_free_walk HF) with (B := B) (lo := lo) (errv := errv) (A := A) (n := 24);
      [exact HEAP3 | exact HBIN | exact AUX3 | lia | exact ST3 | exact CEIL | unfold GLOBALS_TOP; lia
      | unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | match goal with H : mem_inv _ m3 |- _ => exact H end | reflexivity
      | exact CS3 | reflexivity | ].
    intros st2 ms2 PO. apply K. unfold cfree_post in PO. unfold vfree_post.
    destruct PO as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    do 15 eexists. exists m4. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|].
    split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply lb_remove_incl; exact Hb]|]. exact HP4. }
    split; [congruence|]. split; [congruence|]. split; [exact HEAP4| exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma ASN1_STRING_free_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
    stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
    a0 = Z_to_bv 64 0 ->
    evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom ctusegs)
        /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
        /\ stk ctusegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASN1_STRING_FREE) fc None m (seg_rom ctusegs)).
  Proof.
    intros until lo. intros ST MI GLO LO ->.
    unfold ASN1_STRING_FREE, GLOBALS_TOP in *.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    carve_frame 16%nat ST. do 4 zstep.
    zstep. if_cases K0; zify_cond K0; [|exfalso; apply K0; reflexivity]. clear K0.
    do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ASN1_OCTET_STRING_FREE : Z := 0x1150fc.
  Definition ASN1_INTEGER_FREE : Z := 0x1151b8.
  Definition ASN1_ENUMERATED_FREE : Z := 0x115200.
  Definition asn1_pfree_entry (e : Z) : Prop :=
    e = ASN1_STRING_FREE \/ e = ASN1_OCTET_STRING_FREE \/ e = ASN1_INTEGER_FREE \/ e = ASN1_ENUMERATED_FREE.

  Lemma asn1_pfree_fwd : forall (P : machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) fc (m : mem) (lo e : Z),
    asn1_pfree_entry e ->
    stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
    (forall m1, munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 ->
                stk ctusegs m1 lo (bv_unsigned sp) ->
                evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (wz ASN1_STRING_FREE) fc None m1 (seg_rom ctusegs))) ->
    evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (wz e) fc None m (seg_rom ctusegs)).
  Proof.
    intros until e. intros He ST MI GLO LO H.
    unfold asn1_pfree_entry, ASN1_STRING_FREE, ASN1_OCTET_STRING_FREE, ASN1_INTEGER_FREE, ASN1_ENUMERATED_FREE, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct He as [-> | [-> | [-> | ->]]].
    - apply (H m MU WM MI ST).
    - carve_frame 16%nat ST. do 7 zstep. release_frame FR ST (bv_unsigned sp). zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply (H mx MU WM ltac:(assumption) ST) end.
    - carve_frame 16%nat ST. do 7 zstep. release_frame FR ST (bv_unsigned sp). zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply (H mx MU WM ltac:(assumption) ST) end.
    - carve_frame 16%nat ST. do 7 zstep. release_frame FR ST (bv_unsigned sp). zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply (H mx MU WM ltac:(assumption) ST) end.
  Qed.

  (* [comment removed for export] *)
  Lemma ASN1_pfree_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (e : Z) (pblk pdata : bptr) (A D alloc len ty : Z)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    asn1_pfree_entry e ->
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ASN1_STRING_FREE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    In (pblk, A, ASN1_STRING_SIZE) L -> In (pdata, D, alloc) L -> pblk <> pdata ->
    rw_cells ctusegs m A (asn1_string_cells len ty D 0) ->
    a0 = wz A ->
    (forall s' ms', vfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pblk (lb_remove pdata L)) lo B errv m
                      (fun m' => True) s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (LFree pdata (LFree pblk k))) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz e) fc None m (seg_rom ctusegs)).
  Proof using HF.
    intros until Q. intros He HEAP AUX SPB ST CEIL GLO LO ERR MI TP CS HBIN HDIN NBD HB HA0 K.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (LH_block_range _ _ _ _ HEAP HBIN) as (BB0 & BB1 & BB2 & BB3 & BB4). unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in *.
    unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK, GLOBALS_TOP in *.
    unfold implM. iprefix. eapply asn1_pfree_fwd with (lo := lo); [exact He| exact ST| exact MI| exact GLO| lia|].
    intros m1 MU1 WM1 MI1 ST1. ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 16, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]];
        [lia| unfold GLOBALS_TOP, ASN1_STRING_FREE_STACK in *; lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). unfold ASN1_STRING_FREE_STACK in LO. lia. }
    eapply (ASN1_STRING_free_walk) with (B := B) (lo := lo) (errv := errv) (A := A) (D := D) (alloc := alloc) (len := len) (ty := ty);
      [ eapply LH_frame; [exact HEAP| exact MU1| exact WM1|]; constructor; [apply W_ok_stack; cbn; lia| constructor]
      | eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]
      | exact SPB | exact ST1 | exact CEIL | exact GLO | exact LO
      | eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| cbn; unfold LX_ERRNO, RATP; lia]
      | exact MI1 | exact TP
      | eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU1 WM1)| | exact CS];
        intros a Ha; cbn; split; [|exact I]; revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia
      | exact HBIN | exact HDIN | exact NBD
      | eapply rw_cells_transport; [exact HB| exact MU1| exact WM1| cbn; lia]
      | exact HA0 | ].
    intros s' ms' PO. apply K. unfold vfree_post in *.
    destruct PO as (q5 & q6 & q7 & qa0 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4 & _).
    do 16 eexists. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|].
    split. { eapply rheap_pres_trans; [| exact HP4].
             eapply rheap_pres_weaken; [eapply heap_pres_of_munch; [exact MU1| exact WM1| exact CLI]| lia| intros b Hb; eapply lb_remove_incl; eapply lb_remove_incl; exact Hb]. }
    split; [exact FA4|]. split; [exact SO4|]. split; [exact HEAP4| exact I].
  Qed.

  Lemma ASN1_pfree_nodata_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (e : Z) (pblk : bptr) (A len ty : Z)
      (k : lprog X) (Q : X -> PState -> machine_state -> Prop),
    asn1_pfree_entry e ->
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ASN1_STRING_FREE_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m ->
    In (pblk, A, ASN1_STRING_SIZE) L ->
    rw_cells ctusegs m A (asn1_string_cells len ty 0 0) ->
    a0 = wz A ->
    (forall s' ms', vfree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (lb_remove pblk L) lo B errv m
                      (fun m' => True) s' ms' ->
                    implM ctusegs (interp k) s' Q ms') ->
    implM ctusegs (interp (LFree pblk k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz e) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros He HEAP AUX SPB ST CEIL GLO LO ERR MI TP CS HBIN HB HA0 K.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (LH_block_range _ _ _ _ HEAP HBIN) as (BB0 & BB1 & BB2 & BB3 & BB4). unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in *.
    unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK, GLOBALS_TOP in *.
    unfold implM. iprefix. eapply asn1_pfree_fwd with (lo := lo); [exact He| exact ST| exact MI| exact GLO| lia|].
    intros m1 MU1 WM1 MI1 ST1. ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 16, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    eapply (ASN1_STRING_free_nodata_walk) with (B := B) (lo := lo) (errv := errv) (A := A) (len := len) (ty := ty);
      [ eapply LH_frame; [exact HEAP| exact MU1| exact WM1|]; constructor; [apply W_ok_stack; cbn; lia| constructor]
      | eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]
      | exact SPB | exact ST1 | exact CEIL | exact GLO | exact LO
      | eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| cbn; unfold LX_ERRNO, RATP; lia]
      | exact MI1 | exact TP
      | eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU1 WM1)| | exact CS];
        intros a Ha; cbn; split; [|exact I]; revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia
      | exact HBIN
      | eapply rw_cells_transport; [exact HB| exact MU1| exact WM1| cbn; lia]
      | exact HA0 | ].
    intros s' ms' PO. apply K. unfold vfree_post in *.
    destruct PO as (q5 & q6 & q7 & qa0 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4 & _).
    do 16 eexists. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|].
    split. { eapply rheap_pres_trans; [| exact HP4].
             eapply rheap_pres_weaken; [eapply heap_pres_of_munch; [exact MU1| exact WM1| exact CLI]| lia| intros b Hb; eapply lb_remove_incl; exact Hb]. }
    split; [exact FA4|]. split; [exact SO4|]. split; [exact HEAP4| exact I].
  Qed.

  Lemma ASN1_pfree_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo e : Z),
    asn1_pfree_entry e ->
    stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
    a0 = Z_to_bv 64 0 ->
    evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom ctusegs)
        /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
        /\ stk ctusegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 e) fc None m (seg_rom ctusegs)).
  Proof.
    intros until e. intros He ST MI GLO LO HA0.
    apply (asn1_pfree_fwd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo e He ST MI GLO LO).
    intros m1 MU1 WM1 MI1 ST1.
    eapply evt_mono; [eapply ASN1_STRING_free_null_spec with (lo := lo); [exact ST1| exact MI1| exact GLO| exact LO| exact HA0]|].
    intros ms' PO. cbn beta in PO.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & -> & MU2 & WM2 & MI2 & ST2).
    do 15 eexists. split; [reflexivity|]. split; [eapply munch_trans; [exact MU1| exact MU2]|].
    split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2| exact ST2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition CRYPTO_REALLOC_STACK : Z := CRYPTO_MALLOC_STACK.   (* [comment removed for export] *)

  Lemma CRYPTO_realloc_null_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (n lo B : Z) (errv : word)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CRYPTO_REALLOC_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m -> realloc_statics m -> a0 = wz 0 -> a1 = wz n -> 0 < n < 2^32 ->
    k None = LUnr ->
    (forall p s' ms',
       calloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L n lo B m
                   (fun A m' => exists junk, rw_cells ctusegs m' A [CB (Z.to_nat n) junk]) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc n k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz CRYPTO_REALLOC) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI TP CS RS -> -> Hn KN K.
    unfold CRYPTO_REALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, CRYPTO_REALLOC, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    destruct RS as [RS1 RS2]. unfold CR_GOT_MALLOC, CR_REALLOC_IMPL, CRYPTO_REALLOC, MallocRep.wz in RS1, RS2.
    change (3270968 + 8) with 3270976 in RS1.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    unfold implM. iprefix.
    carve_frame 48%nat ST. do 7 step. do 3 step. do 3 step. step. step.
    step. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
    step. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. clear K1.
    do 3 step. do 6 step. release_frame FR ST (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_malloc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := n);
      [ eapply LH_frame; [exact HEAP| exact MU| exact WM|]; constructor; [apply W_ok_stack; cbn; lia| constructor]
      | eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]
      | exact SPB | exact ST | exact CEIL | unfold GLOBALS_TOP; lia | unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
      | unfold LX_ERRNO, RATP; exact ERR | match goal with H : mem_inv _ m1 |- _ => exact H end | exact TP
      | eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS];
        intros a Ha; cbn; split; [|exact I]; revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia
      | reflexivity | exact Hn | exact KN | ].
    intros p s' ms' PO. apply K. unfold calloc_post in *.
    destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4 & A & errv4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & BR4 & HEAP4 & BLK4).
    do 14 eexists. exists m4, A, errv4. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|].
    split. { eapply rheap_pres_trans; [| exact HP4]. eapply heap_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    split; [exact FA4|]. split; [exact SO4|]. split; [exact BR4|]. split; [exact HEAP4| exact BLK4].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ASN1_STRING_SET1_DATA : Z := 0xfe204.
  Definition ASN1_STRING_SET_STACK : Z := 48 + CRYPTO_MALLOC_STACK.

  (* [comment removed for export] *)
  Lemma ASN1_STRING_set1_data_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (pblk pp : bptr) (A ty P PA psz n : Z) (src : list byte)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ASN1_STRING_SET_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m -> realloc_statics m ->
    In (pblk, A, ASN1_STRING_SIZE) L -> rw_cells ctusegs m A (asn1_string_cells 0 ty 0 0) -> 0 <= ty < 2^31 -> ty <> 3 ->
    In (pp, PA, psz) L -> pp <> pblk -> PA <= P -> P + n <= PA + psz -> bytes_at ctusegs m P src -> length src = Z.to_nat n ->
    a0 = wz A -> a1 = wz P -> a2 = wz n -> 0 < n < 2^31 ->
    k None = LUnr ->
    (forall p s' ms',
       oalloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L pblk n lo B m 1
                   (fun C m' => rw_cells ctusegs m' C [CB (Z.to_nat n) src] /\ rw_cells ctusegs m' A (asn1_string_cells n ty C 0)
                                /\ bytes_at ctusegs m' P src) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc n k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ASN1_STRING_SET1_DATA) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS RS HBIN HB TY TY3 HPIN NPP PA1 PA2 SRC SLEN -> -> -> Hn KN K.
    unfold ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, ASN1_STRING_SET1_DATA, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP HBIN) as (BB0 & BB1 & BB2 & BB3 & BB4).
    pose proof (LH_block_range _ _ _ _ HEAP HPIN) as (BP0 & BP1 & BP2 & BP3 & BP4).
    unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in *.
    assert (SEPB : A + 24 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= A) by lia.
    assert (SEPP : P + n <= bv_unsigned sp - 48 \/ bv_unsigned sp <= P) by lia.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite SLEN, Z2Nat.id in SB by lia.
    pose proof (LH_disjoint _ _ _ (pp, PA, psz) (pblk, A, 24) HEAP HPIN HBIN NPP) as DJAP. cbn [blk_addr blk_size blk_id fst snd] in DJAP.
    unfold asn1_string_cells, MallocRep.wz in HB.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 4 step.
    step. rewrite (sx32_small ty) by lia. step.
    step. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
    step. step. if_cases K1; zify_cond K1; [| exfalso; apply K1; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia]. clear K1.
    do 3 step. release_frame FR ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 7 step. step. step.
    step. if_cases K2; zify_cond K2; [| exfalso; rewrite signed_small in K2 by lia; lia]. clear K2.
    do 3 step. step. if_cases K3; zify_cond K3; [exfalso; revert K3; rewrite ?unsigned_lit by lia; lia|]. clear K3.
    step. step. step. if_cases K4; zify_cond K4; [| exfalso; revert K4; vm_compute; congruence]. clear K4.
    step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. clear K5.
    step. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. clear K6.
    step. if_cases K7; zify_cond K7; [| exfalso; apply K7; reflexivity]. clear K7.
    do 4 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (RS1 : realloc_statics m1).
    { destruct RS as [RSa RSb]. unfold realloc_statics, CR_GOT_MALLOC, CR_REALLOC_IMPL in *.
      split; (eapply ro_cells_agree; [apply (agree_on_of_munch _ _ _ MU WM)| eassumption| intros a Ha; cbn; cbn in Ha; split; [lia| exact I]]). }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_realloc_null_walk) with (B := B) (lo := lo) (errv := errv) (n := n);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_REALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | exact RS1 | reflexivity | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & C & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & (junkC & BLK)).
    replace (ret_pc (Z_to_bv 64 1040288)) with (Z_to_bv 64 1040288) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in HB;
      [| intros a Ha; right; right; exists (pblk, A, 24); split; [exact HBIN| cbn; cbn in Ha; lia]].
    apply (bytes_at_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in SRC;
      [| intros a Ha; right; right; exists (pp, PA, psz); split; [exact HPIN| cbn; rewrite SLEN, Z2Nat.id in Ha by lia; lia]].
    pose proof BR as (BC0 & BC16 & _ & BCC & BCI).
    assert (ND : List.NoDup (map blk_id ((p, C, n) :: L))) by (eapply LH_nodup; exact HEAP3).
    assert (NEB : p <> pblk).
    { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map_iff. exists (pblk, A, 24). split; [reflexivity| exact HBIN]. }
    assert (NEP : p <> pp).
    { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map_iff. exists (pp, PA, psz). split; [reflexivity| exact HPIN]. }
    pose proof (LH_disjoint _ _ _ (p, C, n) (pblk, A, 24) HEAP3 ltac:(left; reflexivity) ltac:(right; exact HBIN) NEB) as DJB.
    pose proof (LH_disjoint _ _ _ (p, C, n) (pp, PA, psz) HEAP3 ltac:(left; reflexivity) ltac:(right; exact HPIN) NEP) as DJP.
    cbn [blk_addr blk_size blk_id fst snd] in DJB, DJP.
    assert (SEPC : C + n <= bv_unsigned sp - 48 \/ bv_unsigned sp <= C) by lia.
    assert (CS3 : crypto_statics m3).
    { eapply crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP)| | exact CS1].
      intros a Ha. right. left. split; [revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia|].
      revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    eapply implM_evt with (P := oalloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L pblk n lo B m 1
                   (fun C m' => rw_cells ctusegs m' C [CB (Z.to_nat n) src] /\ rw_cells ctusegs m' A (asn1_string_cells n ty C 0)
                                /\ bytes_at ctusegs m' P src) p st1);
      [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 24); (C, C + n)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pblk L) (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 24); (C, C + n)] a).
    { (* [comment removed for export] *)
      intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]];
        [ clear - Ha Hc CEIL GLO LO SPR BB3 BB4 BCC BCI; split; [lia| split; [lia| split; [lia| exact I]]]
        | clear - Ha Hc CEIL GLO LO SPR BB3 BB4 BCC BCI; split; [lia| split; [lia| split; [lia|exact I]]] |].
      apply lb_remove_In in Hb0. destruct Hb0 as [Hb' Hnp].
      pose proof (LH_disjoint _ _ _ (p, C, n) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
      pose proof (LH_disjoint _ _ _ (pblk, A, 24) b' HEAP ltac:(exact HBIN) ltac:(exact Hb')) as DJB2.
      cbn [blk_addr blk_size blk_id fst snd] in DJ, DJB2.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      assert (p <> blk_id b') as NE.
      { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map. exact Hb'. }
      specialize (DJ NE). specialize (DJB2 ltac:(intros E; apply Hnp; symmetry; exact E)). clear - Ha Hr DJ DJB2 B3' CEIL LO SPR. split; [lia| split; [lia| split; [lia| exact I]]]. }
    unfold MallocRep.wz.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. step.
    step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]. clear KB.
    step. step. if_cases KC; zify_cond KC; [exfalso; rewrite ?unsigned_lit in KC by lia; lia|]. clear KC.
    do 3 step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    eapply evt_cut.
    { eapply memcpy_spec with (src := src) (junk := junkC);
        [ rewrite unsigned_lit by lia; exact SRC | rewrite unsigned_lit by lia; exact SLEN
        | rewrite !unsigned_lit by lia; exact BLK | rewrite !unsigned_lit by lia; lia | assumption ]. }
    unfold memcpy_post. intros ms' PO. rewrite ?unsigned_lit in PO by lia. rewrite ?ESP in PO. revert ms' PO. post_call ctusegs m5.
    step. step. setreg 10%Z (Z_to_bv 64 0) ltac:(apply bv_eq; vm_compute; reflexivity). step.
    step. step. do 6 step.
    match goal with H : stk ctusegs _ lo (bv_unsigned sp + -48) |- _ => release_frame FR H (bv_unsigned sp) end. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    apply evt_done. unfold oalloc_post, MallocRep.wz.
    do 14 eexists. exists m2, C, errv2. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [unfold LX_ERRNO, RATP; assumption|].
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|].
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply lb_remove_incl; exact Hb]|].
             eapply heap_pres_of_munch; [exact MU3| exact WM3| apply CLI3]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|].
             constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (pblk, A, 24)); [right; exact HBIN| cbn; lia| cbn; lia]|].
             constructor; [eapply (W_ok_block _ (p, C, n)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    split; [assumption|]. split; [| assumption].
    unfold asn1_string_cells, MallocRep.wz. assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ASN1_STRING_set1_data_nosrc_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
      (pblk : bptr) (A ty n : Z)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ASN1_STRING_SET_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    crypto_statics m -> realloc_statics m ->
    In (pblk, A, ASN1_STRING_SIZE) L -> rw_cells ctusegs m A (asn1_string_cells 0 ty 0 0) -> 0 <= ty < 2^31 -> ty <> 3 ->
    a0 = wz A -> a1 = wz 0 -> a2 = wz n -> 0 < n < 2^31 ->
    k None = LUnr ->
    (forall p s' ms',
       oalloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L pblk n lo B m 1
                   (fun C m' => (exists junk, rw_cells ctusegs m' C [CB (Z.to_nat n) junk]) /\ rw_cells ctusegs m' A (asn1_string_cells n ty C 0)) p s' ms' ->
       implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc n k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ASN1_STRING_SET1_DATA) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB ST CEIL GLO LO ERR MI -> CS RS HBIN HB TY TY3 -> -> -> Hn KN K.
    unfold ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, ASN1_STRING_SET1_DATA, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP HBIN) as (BB0 & BB1 & BB2 & BB3 & BB4).
    unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in *.
    assert (SEPB : A + 24 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= A) by lia.
    unfold asn1_string_cells, MallocRep.wz in HB.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 4 step.
    step. rewrite (sx32_small ty) by lia. step.
    step. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
    step. step. if_cases K1; zify_cond K1; [| exfalso; apply K1; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia]. clear K1.
    do 3 step. release_frame FR ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 7 step. step. step.
    step. if_cases K2; zify_cond K2; [| exfalso; rewrite signed_small in K2 by lia; lia]. clear K2.
    do 3 step. step. if_cases K3; zify_cond K3; [exfalso; revert K3; rewrite ?unsigned_lit by lia; lia|]. clear K3.
    step. step. step. if_cases K4; zify_cond K4; [| exfalso; revert K4; vm_compute; congruence]. clear K4.
    step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. clear K5.
    step. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. clear K6.
    step. if_cases K7; zify_cond K7; [| exfalso; apply K7; reflexivity]. clear K7.
    do 4 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. lia. }
    assert (RS1 : realloc_statics m1).
    { destruct RS as [RSa RSb]. unfold realloc_statics, CR_GOT_MALLOC, CR_REALLOC_IMPL in *.
      split; (eapply ro_cells_agree; [apply (agree_on_of_munch _ _ _ MU WM)| eassumption| intros a Ha; cbn; cbn in Ha; split; [lia| exact I]]). }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (CRYPTO_realloc_null_walk) with (B := B) (lo := lo) (errv := errv) (n := n);
      [exact HEAP1 | exact AUX1 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_REALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity
      | exact CS1 | exact RS1 | reflexivity | reflexivity | lia | exact KN | ].
    intros p st1 ms1 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & C & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & (junkC & BLK)).
    replace (ret_pc (Z_to_bv 64 1040288)) with (Z_to_bv 64 1040288) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in HB;
      [| intros a Ha; right; right; exists (pblk, A, 24); split; [exact HBIN| cbn; cbn in Ha; lia]].
    pose proof BR as (BC0 & BC16 & _ & BCC & BCI).
    assert (ND : List.NoDup (map blk_id ((p, C, n) :: L))) by (eapply LH_nodup; exact HEAP3).
    assert (NEB : p <> pblk).
    { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map_iff. exists (pblk, A, 24). split; [reflexivity| exact HBIN]. }
    pose proof (LH_disjoint _ _ _ (p, C, n) (pblk, A, 24) HEAP3 ltac:(left; reflexivity) ltac:(right; exact HBIN) NEB) as DJB.
    cbn [blk_addr blk_size blk_id fst snd] in DJB.
    assert (SEPC : C + n <= bv_unsigned sp - 48 \/ bv_unsigned sp <= C) by lia.
    assert (CS3 : crypto_statics m3).
    { eapply crypto_statics_agree; [apply (agree_of_heap_pres _ _ _ _ HP)| | exact CS1].
      intros a Ha. right. left. split; [revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia|].
      revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    assert (HP0 : rheap_pres L (bv_unsigned sp) m m3).
    { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU| exact WM| apply CLI]|].
      eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    eapply implM_evt with (P := oalloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L pblk n lo B m 1
                   (fun C m' => (exists junk, rw_cells ctusegs m' C [CB (Z.to_nat n) junk]) /\ rw_cells ctusegs m' A (asn1_string_cells n ty C 0)) p st1);
      [| intros ms' PO'; apply K; exact PO'].
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 24); (C, C + n)]%Z m3) as MU3. pose proof (wmono_refl ctusegs m3) as WM3.
    assert (CLI3 : forall a, 0 <= a < 2^64 -> rclient_addr (lb_remove pblk L) (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 24); (C, C + n)] a).
    { (* [comment removed for export] *)
      intros a Ha Hc. cbn. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]];
        [ clear - Ha Hc CEIL GLO LO SPR BB3 BB4 BCC BCI; split; [lia| split; [lia| split; [lia| exact I]]]
        | clear - Ha Hc CEIL GLO LO SPR BB3 BB4 BCC BCI; split; [lia| split; [lia| split; [lia|exact I]]] |].
      apply lb_remove_In in Hb0. destruct Hb0 as [Hb' Hnp].
      pose proof (LH_disjoint _ _ _ (p, C, n) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb')) as DJ.
      pose proof (LH_disjoint _ _ _ (pblk, A, 24) b' HEAP ltac:(exact HBIN) ltac:(exact Hb')) as DJB2.
      cbn [blk_addr blk_size blk_id fst snd] in DJ, DJB2.
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      assert (p <> blk_id b') as NE.
      { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map. exact Hb'. }
      specialize (DJ NE). specialize (DJB2 ltac:(intros E; apply Hnp; symmetry; exact E)). clear - Ha Hr DJ DJB2 B3' CEIL LO SPR. split; [lia| split; [lia| split; [lia| exact I]]]. }
    unfold MallocRep.wz.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.
    step. step.
    step. if_cases KB; zify_cond KB; [| exfalso; apply KB; reflexivity]. clear KB.
    step. step. setreg 10%Z (Z_to_bv 64 0) ltac:(apply bv_eq; vm_compute; reflexivity). step.
    step. step. do 6 step.
    match goal with H : stk ctusegs _ lo (bv_unsigned sp + -48) |- _ => release_frame FR H (bv_unsigned sp) end. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    apply evt_done. unfold oalloc_post, MallocRep.wz.
    do 14 eexists. exists m2, C, errv2. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [unfold LX_ERRNO, RATP; assumption|].
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU3| exact WM3|].
             constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split. { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros b Hb; eapply lb_remove_incl; exact Hb]|].
             eapply heap_pres_of_munch; [exact MU3| exact WM3| apply CLI3]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|].
    split. { eapply LH_frame; [exact HEAP3| exact MU3| exact WM3|].
             constructor; [apply W_ok_stack; cbn; lia|].
             constructor; [eapply (W_ok_block _ (pblk, A, 24)); [right; exact HBIN| cbn; lia| cbn; lia]|].
             constructor; [eapply (W_ok_block _ (p, C, n)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
    split; [exists junkC; assumption|].
    unfold asn1_string_cells, MallocRep.wz. assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ASN1_STRING_set1_data_zero_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo A ty : Z),
    stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 64)%Z ->
    crypto_statics m ->
    rw_cells ctusegs m A (asn1_string_cells 0 ty 0 0) -> 0 <= ty < 2^31 -> ty <> 3 -> obj_range A 24 lo -> A mod 8 = 0 ->
    a0 = wz A -> a2 = wz 0 ->
    evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom ctusegs)
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + 16)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
        /\ stk ctusegs m' lo (bv_unsigned sp)
        /\ rw_cells ctusegs m' A (asn1_string_cells 0 ty 0 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASN1_STRING_SET1_DATA) fc None m (seg_rom ctusegs)).
  Proof.
    intros until ty. intros ST MI GLO LO CS HB TY TY3 (A0 & AL & AI) A8 -> ->.
    unfold ASN1_STRING_SET1_DATA, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + 16)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold asn1_string_cells, MallocRep.wz in HB.
    carve_frame 16%nat ST. do 4 step.
    step. rewrite (sx32_small ty) by lia. step.
    step. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
    step. step. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. clear K1.
    do 3 step. release_frame FR ST (bv_unsigned sp). step.
    carve_frame 48%nat ST. do 7 step. step. step.
    step. if_cases K2; zify_cond K2; [| exfalso; revert K2; vm_compute; congruence]. clear K2.
    do 3 step. step. if_cases K3; zify_cond K3; [exfalso; revert K3; vm_compute; congruence|]. clear K3.
    step. step. step. if_cases K4; zify_cond K4; [| exfalso; revert K4; vm_compute; congruence]. clear K4.
    step. if_cases K5; zify_cond K5; [| exfalso; apply K5; reflexivity]. clear K5.
    do 4 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact CS].
      intros a Ha. cbn. split; [|split; [|exact I]]; revert Ha; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; lia. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (CRYPTO_free_null_spec) with (lo := lo);
        [rewrite ESP; exact ST| unfold GLOBALS_TOP; lia| rewrite ESP; lia| assumption| exact CS1| reflexivity]. }
    clear CS1. post_call_esp ESP m1. rewrite ?ESP in *.
    match goal with H : stk ctusegs _ lo (bv_unsigned sp + -48) |- _ => rename H into ST3 end.
    step. step. step. do 6 step. release_frame FR ST3 (bv_unsigned sp). step.
    finish.
  Qed.

End Proofs.
End WithCeiling0.
