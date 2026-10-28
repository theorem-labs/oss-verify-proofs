(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog BnBase BnModel BnTree ApBase ApLogic ApPrim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface W_akit W_bio_push W_prefix_create W_obj_free W_strdup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
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

Definition ASN1_STRING_TYPE_NEW_A : Z := 0x224b04.
Definition ASN1_INTEGER_NEW_A : Z := 0x246f18.
Definition ASN1_STRING_TYPE_NEW_STACK : Z := 32 + CRYPTO_ZALLOC_STACK.
Definition ASN1_STRING_FREE_A : Z := 0x224820.
Definition OSSL_ASN1_STRING_FREE_INT_A : Z := 0x224b88.
(* [comment removed for export] *)
Definition ASN1_STRING_FREE_STACK : Z := 64 + CRYPTO_FREE_STACK.
Definition ASN1_OCTET_STRING_FREE_A : Z := 0x246e80.
Definition ASN1_INTEGER_FREE_A : Z := 0x246f3c.
Definition ASN1_ENUMERATED_FREE_A : Z := 0x246f84.
(* [comment removed for export] *)
Definition asn1_pfree_entryA (e : Z) : Prop := e = ASN1_OCTET_STRING_FREE_A.

(* [comment removed for export] *)
Lemma zero24_string_cells : forall m A,
  rw_cells ctasegs m A [CB 24%nat (repeat (Z_to_bv 8 0) 24%nat)] -> rw_cells ctasegs m A [C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; auto| unfold MallocRep.wz; bytes_lit_eq| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma str_cells_w : forall m A pre,
  rw_cells ctasegs m A (pre ++ [C8 (wz 0)]) -> rw_cells ctasegs m A (pre ++ [C4 (wz 0); C4 (wz 0)]).
Proof.
  intros m A pre H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn. tauto.
  - rewrite !cells_bytes_app. f_equal.
  - rewrite !cells_size_app. reflexivity.
Qed.
Lemma str_cells_d : forall m A pre,
  rw_cells ctasegs m A (pre ++ [C4 (wz 0); C4 (wz 0)]) -> rw_cells ctasegs m A (pre ++ [C8 (wz 0)]).
Proof.
  intros m A pre H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn. tauto.
  - rewrite !cells_bytes_app. f_equal.
  - rewrite !cells_size_app. reflexivity.
Qed.
Lemma str_cells_b : forall m A pre,
  rw_cells ctasegs m A (pre ++ [C8 (wz 0)]) ->
  rw_cells ctasegs m A (pre ++ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (wz 0)]).
Proof.
  intros m A pre H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn. tauto.
  - rewrite !cells_bytes_app. f_equal.
  - rewrite !cells_size_app. reflexivity.
Qed.
Lemma str_cells_db : forall m A pre,
  rw_cells ctasegs m A (pre ++ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (wz 0)]) ->
  rw_cells ctasegs m A (pre ++ [C8 (wz 0)]).
Proof.
  intros m A pre H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn. tauto.
  - rewrite !cells_bytes_app. f_equal.
  - rewrite !cells_size_app. reflexivity.
Qed.
(* [comment removed for export] *)
Local Notation E_tnew_zalloc := (E_ASN1_STRING_type_new_222e68 : uk_call 0x224b04 0x224b40 0x1fcef0).          (* [comment removed for export] *)
Local Notation E_sfree_tail := (E_ASN1_STRING_free_222b74 : uk_tail 0x224820 0x224b88).                        (* [comment removed for export] *)
Local Notation E_ifree_call := (E_ossl_asn1_string_free_internal_223018 : uk_call 0x224b88 0x224cdc 0x1fd334).  (* [comment removed for export] *)
Local Notation E_ifree_tail := (E_ossl_asn1_string_free_internal_223074 : uk_tail 0x224b88 0x1fd334).           (* [comment removed for export] *)
Local Notation E_ofree_tail := (E_ASN1_OCTET_STRING_free_249fd0 : uk_tail 0x246e80 0x224820).                  (* [comment removed for export] *)
Local Notation E_realloc_tail := (E_CRYPTO_realloc_1fc68c : uk_tail 0x1fd224 0x1fce24).                          (* [comment removed for export] *)
Local Notation E_set1_tail := (E_ASN1_STRING_set1_data_222dc8 : uk_tail 0x2249e8 0x2243f8).                     (* [comment removed for export] *)
Local Notation E_sint_realloc := (E_ossl_asn1_string_set_internal_222850 : uk_call 0x2243f8 0x224524 0x1fd224). (* [comment removed for export] *)
Local Notation E_sint_free := (E_ossl_asn1_string_set_internal_222924 : uk_call 0x2243f8 0x2245f8 0x1fd334).    (* [comment removed for export] *)


Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ASN1_STRING_type_new_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (ty : Z) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - ASN1_STRING_TYPE_NEW_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  a0 = wz ty -> 0 <= ty < 2^31 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ASN1_STRING_TYPE_NEW_A (bv_unsigned ra :: ras) ->      (* [comment removed for export] *)
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB 24 lo m
                  (fun A m' => rw_cells ctasegs m' A (asn1_string_cells 0 ty 0 0)) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc 24 k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_STRING_TYPE_NEW_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> CS -> TY UW CTX K.
  unfold ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK, ASN1_STRING_TYPE_NEW_A, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply implAp_from_evt.
  carve_frame 32%nat ST. do 6 step.
  (* [comment removed for export] *)
  do 6 step.
  name_mem m1.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [left; cbn; alia | constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | | exact CS].
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  apply evt_done.
  eapply (CRYPTO_zalloc_walkAp) with (n := 24) (lo := lo) (OW := OW) (LB := LB); try reflexivity.
  - exact HEAP1.
  - rewrite ESP. exact ST.
  - exact CEIL.
  - rewrite ESP. unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK. lia.
  - rewrite ESP. alia.
  - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
  - exact MI.
  - exact CS1.
  - lia.
  - unfold mcost. cbn. exact (af_credit_nonneg RT AF Σ m1 (AH_art _ _ _ _ HEAP1)).
  - rewrite ESP. uw_call_mu_tac m 32 UW MU FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia].
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_tnew_zalloc CTX).
  - intros p Σ' ms' Hp PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & A & -> & MI2 & ST2 & AG2 & CR2 & BR2 & HEAP2 & ACC2 & BLK).
    unfold MallocRep.wz in *. rewrite ESP in ST2, AG2.
    rewrite (ret_pc_even 0x224b40) by (lia || reflexivity).
    pose proof BR2 as (A0 & A16 & _ & ACE & AIMG).
    assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; alia).
    pose proof (AH_offsh _ _ _ _ (p, A, 24) HEAP2 (or_introl eq_refl)) as OSHA. cbn [blk_addr blk_size fst snd] in OSHA.
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn in Ha; alia].
    apply zero24_string_cells in BLK. unfold MallocRep.wz in BLK.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 24)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
    assert (OFF2 : offshW [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 24)]%Z) by (cbn [offshW]; alia).
    rename MU into MU0. clear WM HEAP1 CS1 SHB1 SHB2.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EA in KA; lia|]. clear KA.
    step.
    do 4 step. release_frame FR ST2 (bv_unsigned sp). step. step.
    name_mem m9.
    apply evt_done. apply (K p Σ' _ Hp).
    unfold calloc_postA, MallocRep.wz.
    do 16 eexists. exists m9, A. split; [reflexivity|].
    assert (MU9 : munch [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 24)]%Z m2 m9) by assumption.
    split; [assumption|]. split; [assumption|].
    split.
    { eapply agree_on_trans; [| eapply agree_on_trans; [eapply agree_on_mono; [exact AG2| intros a [Ha|[Ha|Ha]]; [left; lia| right; left; exact Ha| right; right; exact Ha]]|]].
      - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU0)|].
        intros a [Ha|[Ha|Ha]]; cbn [outside]; (split; [|exact I]).
        + lia.
        + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
        + destruct Ha as (b & Hb & Hr). pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). lia.
      - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU9)|]. intros a Ha. cbn [outside].
        split; [| split; [| exact I]].
        + destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia| |].
          * destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
          * pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). lia.
        + intros HAr. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
          * unfold BnHeapA.ACEIL in *. lia.
          * eapply (blk_not_static _ ((p, A, 24) :: OW) LB m2 (p, A, 24) a HEAP2 (or_introl eq_refl)); [cbn; lia | exact Ha].
          * assert (NE : blk_id b <> p) by (intros E; apply Hp; rewrite <- E; apply in_map; exact Hb).
            pose proof (AH_disjoint_gen _ _ _ _ b (p, A, 24) HEAP2 (or_intror Hb) (or_introl eq_refl) NE) as DJ. cbn in DJ. lia. }
    split; [exact CR2|]. split; [exact BR2|].
    assert (HEAP9 : AHEAP Σ' ((p, A, 24) :: OW) LB m9).
    { eapply AH_frame; [exact HEAP2| exact MU9| apply wmono_refl || assumption|].
      constructor; [left; cbn; alia|]. constructor; [right; right; exists (p, A, 24); split; [left; reflexivity| cbn; lia]| constructor]. }
    split; [exact HEAP9|].
    split; [exact (proj2 (AH_acc _ _ _ _ (p, A, 24) HEAP9 (or_introl eq_refl)))|].
    unfold asn1_string_cells, MallocRep.wz. exact BLK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ASN1_STRING_free_dyn_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (pblk pdata : bptr) (A D alloc len ty : Z) (ras : list Z)
    (k : aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - ASN1_STRING_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  In (pblk, A, ASN1_STRING_SIZE) OW -> In (pdata, D, alloc) OW -> pblk <> pdata ->
  rw_cells ctasegs m A (asn1_string_cells len ty D 0) ->
  a0 = wz A ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ASN1_STRING_FREE_A (bv_unsigned ra :: ras) ->      (* [comment removed for export] *)
  (forall Σ' ms', vfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ (lb_remove pblk (lb_remove pdata OW)) LB lo m
                    (fun m' => True) Σ' ms' ->
                  implAp k Σ' Q ms') ->
  implAp (AFree pdata (AFree pblk k)) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_STRING_FREE_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> CS HBIN HDIN NBD HB -> UW CTX K.
  unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RT_STACK, ASN1_STRING_FREE_A, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (pblk, A, ASN1_STRING_SIZE) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  assert (HDIN' : In (pdata, D, alloc) (OW ++ LB)) by (apply in_or_app; left; exact HDIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HDIN') as (BD0 & _ & _ & BD3 & BD4).
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB.
  unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4, BD0, BD3, BD4.
  assert (SEPB : A + 24 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= A) by (unfold BnHeapA.ACEIL in *; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  ablock HEAP HBIN' ACCB OFFB.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  unfold asn1_string_cells, MallocRep.wz in HB.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 64, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 step.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?EA in K0; lia|]. clear K0.
  apply (str_cells_w _ _ [C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 D)]) in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
  step. step. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  (* [comment removed for export] *)
  carve_frame 64%nat ST. do 9 step.
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?EA in K1; lia|]. clear K1.
  apply (str_cells_d _ _ [C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 D)]) in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
  step. step.
  (* [comment removed for export] *)
  step. zstep. step. step. if_true.
  (* [comment removed for export] *)
  apply (str_cells_b _ _ [C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 D)]) in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
  step. zstep. step. if_false.
  (* [comment removed for export] *)
  step. step. if_true. do 4 step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU1) | | exact CS].
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  apply evt_done.
  eapply CRYPTO_free_walkAp with (p := pdata) (A := D) (n := alloc) (lo := lo) (OW := OW) (LB := LB); try reflexivity.
  - exact HEAP1.
  - exact HDIN.
  - rewrite ESP. exact ST.
  - exact CEIL.
  - rewrite ESP. unfold CRYPTO_FREE_STACK, RT_STACK. lia.
  - rewrite ESP. unfold USTACK_TOP. lia.
  - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
  - exact MI.
  - exact CS1.
  - rewrite ESP. uw_call_mu_tac m 64 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia].
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_ifree_call (uk_ctx_tail _ _ _ E_sfree_tail CTX)).
  - intros Σ3 ms3 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & m3 & -> & MI3 & ST3 & AG3 & CR3 & HEAP3).
    unfold MallocRep.wz in *. rewrite ESP in ST3, AG3. rewrite (ret_pc_even 0x224cdc) by (clear; lia).
    assert (HBIN3 : In (pblk, A, 24) (lb_remove pdata OW)) by (apply lb_remove_In; split; [exact HBIN| cbn; congruence]).
    assert (HBIN3' : In (pblk, A, 24) (lb_remove pdata OW ++ LB)) by (apply in_or_app; left; exact HBIN3).
    pose proof (AH_nodup _ _ _ _ HEAP) as ND.
    assert (LBD : forall b', In b' LB -> blk_id b' <> pdata) by (exact (ids_disj OW LB pdata D alloc ND HDIN)).
    apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; cbn in Ha; left; unfold USTACK_TOP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in HB;
      [| intros a Ha; cbn in Ha; right; right; exists (pblk, A, 24); split; [apply lb_remove_app_l; [exact LBD| exact HBIN3']| cbn; lia]].
    assert (CS3 : crypto_statics m3).
    { eapply crypto_statics_agree; [exact AG3| | exact CS1].
      intros a Ha. right; left; apply client_static_intro. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. lia. }
    ablock HEAP3 HBIN3' ACCB3 OFFB3.
    destruct (AH_shb _ _ _ _ HEAP3) as [SHB1' SHB2'].
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
    clear HEAP1 CS1 ACCB SHB1 SHB2.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. if_true.
    step. zstep. step. if_false.
    step. if_true.
    (* [comment removed for export] *)
    do 4 step. do 7 step. release_frame FR ST3 (bv_unsigned sp). step. step.
    apply evt_done.
    eapply CRYPTO_free_walkAp with (p := pblk) (A := A) (n := 24) (lo := lo) (OW := lb_remove pdata OW) (LB := LB); try reflexivity.
    + exact HEAP3.
    + exact HBIN3.
    + exact ST3.
    + exact CEIL.
    + unfold CRYPTO_FREE_STACK, RT_STACK. lia.
    + unfold USTACK_TOP. lia.
    + exact SP16.
    + exact MI3.
    + exact CS3.
    + eapply uw_chain_munchP; [exact MU3 | | intros a H1 Ha; cbn [outside fst snd]; lia].
      eapply uw_chain_agreeP; [exact AG3 | | intros a H1 Ha; left; unfold USTACK_TOP in *; lia].
      eapply uw_chain_munchP; [exact MU1 | exact UW | intros a H1 Ha; cbn [outside fst snd]; lia].
    + exact (uk_ctx_tail _ _ _ E_ifree_tail (uk_ctx_tail _ _ _ E_sfree_tail CTX)).
    + intros Σ4 ms4 PO. apply K. unfold vfree_postA, MallocRep.wz.
      destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & CR4 & HEAP4).
      do 17 eexists. exists m4. split; [reflexivity|].
      split; [exact MI4|]. split; [exact ST4|].
      split.
      { unfold apres.
        assert (LBB : forall b', In b' LB -> blk_id b' <> pblk) by (exact (ids_disj OW LB pblk A 24 ND HBIN)).
        assert (FRM : forall a, aclient_addr (lb_remove pblk (lb_remove pdata OW) ++ LB) (bv_unsigned sp) a ->
                      outside [(bv_unsigned sp - 64, bv_unsigned sp)]%Z a).
        { intros a Ha. cbn [outside]. split; [| exact I].
          destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
          - lia.
          - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
          - pose proof (lb_remove2_app_incl _ _ _ _ _ Hb) as Hb'. pose proof (AH_range_gen _ _ _ _ b HEAP Hb') as (_ & _ & _ & B3' & _). unfold BnHeapA.ACEIL in *. lia. }
        eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact FRM]|].
        eapply agree_on_trans; [eapply agree_on_mono; [exact AG3| intros a Ha; eapply aclient_addr_sub; [| | exact Ha];
          [intros b Hb; apply (lb_remove_app_l pdata OW LB b LBD); eapply lb_remove_app_incl1; exact Hb| lia]]|].
        eapply agree_on_mono; [exact AG4|]. intros a Ha. eapply aclient_addr_sub; [| | exact Ha]; [| lia].
        intros b Hb. exact (lb_remove_app_l pblk (lb_remove pdata OW) LB b LBB Hb). }
      split; [rewrite CR4, CR3; apply Z.le_refl|]. split; [exact HEAP4| exact I].
Qed.

(* [comment removed for export] *)
Lemma ASN1_STRING_free_nodata_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (pblk : bptr) (A len ty : Z) (ras : list Z)
    (k : aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - ASN1_STRING_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  In (pblk, A, ASN1_STRING_SIZE) OW ->
  rw_cells ctasegs m A (asn1_string_cells len ty 0 0) ->
  a0 = wz A ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ASN1_STRING_FREE_A (bv_unsigned ra :: ras) ->      (* [comment removed for export] *)
  (forall Σ' ms', vfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ (lb_remove pblk OW) LB lo m (fun m' => True) Σ' ms' ->
                  implAp k Σ' Q ms') ->
  implAp (AFree pblk k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_STRING_FREE_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> CS HBIN HB -> UW CTX K.
  unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RT_STACK, ASN1_STRING_FREE_A, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (pblk, A, ASN1_STRING_SIZE) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4).
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB.
  unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  assert (SEPB : A + 24 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= A) by (unfold BnHeapA.ACEIL in *; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  ablock HEAP HBIN' ACCB OFFB.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  unfold asn1_string_cells, MallocRep.wz in HB.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 64, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  apply implAp_from_evt.
  carve_frame 16%nat ST. do 4 step.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?EA in K0; lia|]. clear K0.
  apply (str_cells_w _ _ [C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 0)]) in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
  step. step. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  carve_frame 64%nat ST. do 9 step.
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?EA in K1; lia|]. clear K1.
  apply (str_cells_d _ _ [C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 0)]) in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
  step. step.
  step. zstep. step. step. if_true.
  apply (str_cells_b _ _ [C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 ty); C8 (Z_to_bv 64 0)]) in HB. cbn [app] in HB. unfold MallocRep.wz in HB.
  step. zstep. step. if_false.
  step. step. if_true. do 4 step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU1) | | exact CS].
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  apply evt_done.
  eapply implAp_step_same.
  { eapply CRYPTO_free_null_cpsA with (lo := lo) (OW := OW) (LB := LB); try reflexivity;
      [exact HEAP1| rewrite ESP; exact ST| exact CEIL| rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; lia| rewrite ESP; unfold USTACK_TOP; lia
      | rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI| exact CS1
      | rewrite ESP; uw_call_mu_tac m 64 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ifree_call (uk_ctx_tail _ _ _ E_sfree_tail CTX))]. }
  intros ms3 PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & m3 & -> & MI3 & ST3 & HEAP3 & AG3).
  unfold MallocRep.wz in *. rewrite ESP in ST3, AG3. rewrite (ret_pc_even 0x224cdc) by (clear; lia).
  apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; cbn in Ha; left; unfold USTACK_TOP; lia].
  apply (rw_cells_agree _ _ _ _ _ AG3) in HB; [| intros a Ha; cbn in Ha; right; right; exists (pblk, A, 24); split; [exact HBIN'| cbn; lia]].
  assert (CS3 : crypto_statics m3).
  { eapply crypto_statics_agree; [exact AG3| | exact CS1].
    intros a Ha. right; left; apply client_static_intro. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. lia. }
  ablock HEAP3 HBIN' ACCB3 OFFB3.
  destruct (AH_shb _ _ _ _ HEAP3) as [SHB1' SHB2'].
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  clear HEAP1 CS1 ACCB SHB1 SHB2.
  apply implAp_from_evt.
  step. if_true.
  step. zstep. step. if_false.
  step. if_true.
  do 4 step. do 7 step. release_frame FR ST3 (bv_unsigned sp). step. step.
  apply evt_done.
  eapply CRYPTO_free_walkAp with (p := pblk) (A := A) (n := 24) (lo := lo) (OW := OW) (LB := LB); try reflexivity.
  + exact HEAP3.
  + exact HBIN.
  + exact ST3.
  + exact CEIL.
  + unfold CRYPTO_FREE_STACK, RT_STACK. lia.
  + unfold USTACK_TOP. lia.
  + exact SP16.
  + exact MI3.
  + exact CS3.
  + eapply uw_chain_munchP; [exact MU3 | | intros a H1 Ha; cbn [outside fst snd]; lia].
    eapply uw_chain_agreeP; [exact AG3 | | intros a H1 Ha; left; unfold USTACK_TOP in *; lia].
    eapply uw_chain_munchP; [exact MU1 | exact UW | intros a H1 Ha; cbn [outside fst snd]; lia].
  + exact (uk_ctx_tail _ _ _ E_ifree_tail (uk_ctx_tail _ _ _ E_sfree_tail CTX)).
  + intros Σ4 ms4 PO. apply K. unfold vfree_postA, MallocRep.wz.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & CR4 & HEAP4).
    do 17 eexists. exists m4. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|].
    split.
    { unfold apres. pose proof (AH_nodup _ _ _ _ HEAP) as ND.
      assert (LBB : forall b', In b' LB -> blk_id b' <> pblk) by (exact (ids_disj OW LB pblk A 24 ND HBIN)).
      assert (FRM : forall a, aclient_addr (lb_remove pblk OW ++ LB) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 64, bv_unsigned sp)]%Z a).
      { intros a Ha. cbn [outside]. split; [| exact I].
        destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
        - lia.
        - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
        - pose proof (lb_remove_app_incl1 _ _ _ _ Hb) as Hb'. pose proof (AH_range_gen _ _ _ _ b HEAP Hb') as (_ & _ & _ & B3' & _). unfold BnHeapA.ACEIL in *. lia. }
      eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact FRM]|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact AG3| intros a Ha; eapply aclient_addr_sub; [| | exact Ha]; [intros b Hb; eapply lb_remove_app_incl1; exact Hb| lia]]|].
      eapply agree_on_mono; [exact AG4|]. intros a Ha. eapply aclient_addr_sub; [| | exact Ha]; [| lia].
      intros b Hb. exact (lb_remove_app_l pblk OW LB b LBB Hb). }
    split; [rewrite CR4; apply Z.le_refl|]. split; [exact HEAP4| exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asn1_pfree_fwdA : forall {X : Type} (t : aprog bptr X) (Σ : rts RT) (Q : X -> rts RT -> machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo e : Z),
  asn1_pfree_entryA e ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> lo <= bv_unsigned sp - 16 ->
  (forall m1, munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m1 -> wmono ctasegs m m1 -> mem_inv ctasegs m1 ->
              stk ctasegs m1 lo (bv_unsigned sp) ->
              implAp t Σ Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (wz ASN1_STRING_FREE_A) fc None m1 (seg_rom ctasegs))) ->
  implAp t Σ Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz e) fc None m (seg_rom ctasegs)).
Proof.
  intros until e. intros He ST MI CEIL LO H.
  unfold asn1_pfree_entryA, ASN1_STRING_FREE_A, ASN1_OCTET_STRING_FREE_A, ASN1_INTEGER_FREE_A, ASN1_ENUMERATED_FREE_A, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold BnHeapA.ACEIL in CEIL.
  unfold asn1_pfree_entryA in He. subst e. apply implAp_from_evt.
  carve_frame 16%nat ST. do 6 step. release_frame FR ST (bv_unsigned sp). step. step. apply evt_done.
  lazymatch goal with |- implAp _ _ _ (MS _ _ _ _ _ ?mx _) => apply (H mx MU WM ltac:(assumption) ST) end.
Qed.

(* [comment removed for export] *)
Lemma apres_wrapA : forall Σ OW OW' LB m m1 sp lo,
  AHEAP Σ OW LB m -> (forall b, In b OW' -> In b OW) -> ACEIL <= lo -> lo <= sp - 16 ->
  munch [(sp - 16, sp)]%Z m m1 -> apres LB OW' sp m m1.
Proof.
  intros Σ OW OW' LB m m1 sp lo HEAP INC CEIL LO MU. eapply apres_of_munch; [exact MU|].
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP, BnHeapA.ACEIL in *.
  intros a Ha. cbn [outside]. split; [| exact I].
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
  - lia.
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - assert (Hb' : In b (OW ++ LB)) by (apply in_app_iff in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; exact (INC b Hb)| right; exact Hb]).
    pose proof (AH_range_gen _ _ _ _ b HEAP Hb') as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in B3. lia.
Qed.

Lemma ASN1_pfree_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (e : Z) (pblk pdata : bptr) (A D alloc len ty : Z) (ras : list Z)
    (k : aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  asn1_pfree_entryA e ->
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - ASN1_STRING_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  In (pblk, A, ASN1_STRING_SIZE) OW -> In (pdata, D, alloc) OW -> pblk <> pdata ->
  rw_cells ctasegs m A (asn1_string_cells len ty D 0) ->
  a0 = wz A ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx e (bv_unsigned ra :: ras) ->      (* [comment removed for export] *)
  (forall Σ' ms', vfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ (lb_remove pblk (lb_remove pdata OW)) LB lo m
                    (fun m' => True) Σ' ms' ->
                  implAp k Σ' Q ms') ->
  implAp (AFree pdata (AFree pblk k)) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz e) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros He HEAP ST CEIL LO SPT SP16 MI TP CS HBIN HDIN NBD HB HA0 UW CTX K.
  pose proof LO as LO'. unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RT_STACK in LO'.
  eapply asn1_pfree_fwdA; [exact He| exact ST| exact MI| exact CEIL| clear - LO'; lia|].
  intros m1 MU WM MI1 ST1.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU| exact WM|]. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). constructor; [left; cbn; alia| constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | | exact CS]. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. alia. }
  pose proof (AH_range_gen _ _ _ _ _ HEAP (in_or_app _ _ _ (or_introl HBIN))) as (_ & _ & _ & BB3 & _). cbn [blk_addr blk_size fst snd] in BB3.
  apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in HB;
    [| intros a Ha; cbn [outside]; split; [| exact I]; unfold asn1_string_cells in Ha; cbn in Ha; clear - Ha BB3 CEIL LO'; unfold ASN1_STRING_SIZE in *; alia].
  eapply ASN1_STRING_free_dyn_walkA; [exact HEAP1| exact ST1| exact CEIL| exact LO| exact SPT| exact SP16| exact MI1| exact TP| exact CS1| exact HBIN| exact HDIN| exact NBD| exact HB| exact HA0
    | eapply uw_chain_munchP; [exact MU | exact UW | intros a H1 Ha; cbn [outside fst snd]; lia]| unfold asn1_pfree_entryA in He; rewrite He in CTX; exact (uk_ctx_tail _ _ _ E_ofree_tail CTX)|].
  intros Σ' ms' PO. apply K. unfold vfree_postA in PO |- *.
  destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & CR4 & HEAP4 & _).
  do 17 eexists. exists m4. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|].
  split; [| split; [exact CR4| split; [exact HEAP4| exact I]]].
  eapply apres_trans; [| exact AG4]. eapply (apres_wrapA Σ OW); [exact HEAP| | exact CEIL| clear - LO'; lia| exact MU].
  intros b Hb. apply lb_remove_In in Hb. destruct Hb as [Hb _]. apply lb_remove_In in Hb. exact (proj1 Hb).
Qed.

Lemma ASN1_pfree_nodata_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (e : Z) (pblk : bptr) (A len ty : Z) (ras : list Z)
    (k : aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  asn1_pfree_entryA e ->
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - ASN1_STRING_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  In (pblk, A, ASN1_STRING_SIZE) OW ->
  rw_cells ctasegs m A (asn1_string_cells len ty 0 0) ->
  a0 = wz A ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx e (bv_unsigned ra :: ras) ->      (* [comment removed for export] *)
  (forall Σ' ms', vfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ (lb_remove pblk OW) LB lo m (fun m' => True) Σ' ms' ->
                  implAp k Σ' Q ms') ->
  implAp (AFree pblk k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz e) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros He HEAP ST CEIL LO SPT SP16 MI TP CS HBIN HB HA0 UW CTX K.
  pose proof LO as LO'. unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RT_STACK in LO'.
  eapply asn1_pfree_fwdA; [exact He| exact ST| exact MI| exact CEIL| clear - LO'; lia|].
  intros m1 MU WM MI1 ST1.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU| exact WM|]. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). constructor; [left; cbn; alia| constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | | exact CS]. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. alia. }
  pose proof (AH_range_gen _ _ _ _ _ HEAP (in_or_app _ _ _ (or_introl HBIN))) as (_ & _ & _ & BB3 & _). cbn [blk_addr blk_size fst snd] in BB3.
  apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in HB;
    [| intros a Ha; cbn [outside]; split; [| exact I]; unfold asn1_string_cells in Ha; cbn in Ha; clear - Ha BB3 CEIL LO'; unfold ASN1_STRING_SIZE in *; alia].
  eapply ASN1_STRING_free_nodata_walkA; [exact HEAP1| exact ST1| exact CEIL| exact LO| exact SPT| exact SP16| exact MI1| exact TP| exact CS1| exact HBIN| exact HB| exact HA0
    | eapply uw_chain_munchP; [exact MU | exact UW | intros a H1 Ha; cbn [outside fst snd]; lia]| unfold asn1_pfree_entryA in He; rewrite He in CTX; exact (uk_ctx_tail _ _ _ E_ofree_tail CTX)|].
  intros Σ' ms' PO. apply K. unfold vfree_postA in PO |- *.
  destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & CR4 & HEAP4 & _).
  do 17 eexists. exists m4. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|].
  split; [| split; [exact CR4| split; [exact HEAP4| exact I]]].
  eapply apres_trans; [| exact AG4]. eapply (apres_wrapA Σ OW); [exact HEAP| | exact CEIL| clear - LO'; lia| exact MU].
  intros b Hb. apply lb_remove_In in Hb. exact (proj1 Hb).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CRYPTO_REALLOC_STACK : Z := CRYPTO_MALLOC_STACK.   (* [comment removed for export] *)

Lemma CRYPTO_realloc_null_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (n lo : Z) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_REALLOC_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  crypto_statics m -> realloc_statics m -> a0 = wz 0 -> a1 = wz n -> 0 < n < 2^32 ->
  mcost n <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_REALLOC (bv_unsigned ra :: ras) ->      (* [comment removed for export] *)
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB n lo m
                  (fun A m' => exists junk, rw_cells ctasegs m' A [CB (Z.to_nat n) junk]) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc n k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_REALLOC) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI TP CS RS -> -> Hn CRED UW CTX K.
  pose proof LO as LO'. unfold CRYPTO_REALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK, CRYPTO_REALLOC, MallocRep.wz in LO' |- *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof RS as RS'. unfold realloc_statics, CR_REALLOC_IMPL, CRYPTO_REALLOC, MallocRep.wz in RS'.
  destruct (af_client_consts RT AF Σ m (AH_art _ _ _ _ HEAP)) as (_ & _ & _ & _ & RRO).
  assert (GR : ro_cells ctasegs m 0x5aa898 [C8 (Z_to_bv 64 0x1fd224)]).
  { apply (relro_ro_cells m _ _ RRO); try (vm_compute; reflexivity); try (cbn; repeat split); unfold RELRO_LO, RELRO_HI; cbn; lia. }
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply implAp_from_evt.
  carve_frame 48%nat ST. do 7 step. do 3 step.
  (* [comment removed for export] *)
  do 4 step. step. if_true. step. if_true.
  do 3 step. do 5 step. release_frame FR ST (bv_unsigned sp). step. step.
  name_mem m1.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [left; cbn; alia | constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | | exact CS].
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  apply evt_done.
  eapply CRYPTO_malloc_walkAp with (lo := lo); [exact HEAP1| exact ST| exact CEIL| exact LO| exact SPT| exact SP16| assumption| exact TP| exact CS1| reflexivity| exact Hn| exact CRED
    | eapply uw_chain_munchP; [exact MU | exact UW | intros a H1 Ha; cbn [outside fst snd]; lia] | exact (uk_ctx_tail _ _ _ E_realloc_tail CTX) |].
  intros p Σ' ms' Hp PO. apply (K p Σ' ms' Hp).
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & A & -> & MI2 & ST2 & AG2 & REST).
  unfold calloc_postA. do 16 eexists. exists m2, A. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [| exact REST].
  eapply agree_on_trans; [| exact AG2]. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|].
  intros a [Ha|[Ha|Ha]]; cbn [outside]; (split; [|exact I]).
  - lia.
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
  - destruct Ha as (b & Hb & Hr). pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). unfold BnHeapA.ACEIL in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASN1_STRING_SET1_DATA_A : Z := 0x2249e8.
(* [comment removed for export] *)
Definition ASN1_STRING_SET_STACK : Z := 80 + CRYPTO_MALLOC_STACK.

Lemma ASN1_STRING_set1_data_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (pblk : bptr) (bsrc : block) (A ty P n : Z) (src : list byte)
    (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - ASN1_STRING_SET_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m -> realloc_statics m ->
  In (pblk, A, ASN1_STRING_SIZE) OW -> rw_cells ctasegs m A (asn1_string_cells 0 ty 0 0) -> 0 <= ty < 2^31 -> ty <> 3 ->
  In bsrc (OW ++ LB) -> blk_id bsrc <> pblk -> blk_addr bsrc <= P -> P + n <= blk_addr bsrc + blk_size bsrc ->
  bytes_at ctasegs m P src -> Z.of_nat (length src) = n ->
  a0 = wz A -> a1 = wz P -> a2 = wz n -> 0 < n < 2^31 ->
  mcost n <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ASN1_STRING_SET1_DATA_A (bv_unsigned ra :: ras) ->      (* [comment removed for export] *)
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     oalloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB A ASN1_STRING_SIZE n lo m 1
                  (fun C m' => rw_cells ctasegs m' C [CB (Z.to_nat n) src] /\ rw_cells ctasegs m' A (asn1_string_cells n ty C 0)
                               /\ bytes_at ctasegs m' P src) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc n k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_STRING_SET1_DATA_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI TP CS RS HBIN HB TY TY3 INS NPB S1 S2 SRC SLEN -> -> -> Hn CRED UW CTX K.
  pose proof LO as LO'. unfold ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RT_STACK, ASN1_STRING_SET1_DATA_A, MallocRep.wz in LO' |- *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (pblk, A, ASN1_STRING_SIZE) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4).
  pose proof (AH_range_gen _ _ _ _ bsrc HEAP INS) as (BS0 & _ & _ & BS3 & BS4).
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB.
  unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  ablock HEAP HBIN' ACCB OFFB.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  unfold asn1_string_cells, MallocRep.wz in HB.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 96, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 step.
  step. step. step. if_cases K0; zify_cond K0; [clear K0| exfalso; rewrite (sx32_small ty) in K0 by lia; rewrite unsigned_lit in K0 by lia; exact (TY3 K0)].
  zstep. step. if_cases K1; zify_cond K1; [clear K1| exfalso; apply K1; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia].
  do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  (* [comment removed for export] *)
  carve_frame 80%nat ST. do 12 step.
  step. step. if_cases K2; zify_cond K2; [clear K2| exfalso; rewrite ab_signed_small in K2 by lia; lia].
  step. step. step.
  step. if_cases K3; zify_cond K3; [exfalso; clear - K3 Hn; lia| clear K3].
  (* [comment removed for export] *)
  step. zstep. step. step. if_true.
  step. if_cases K4; zify_cond K4; [exfalso; clear - K4 Hn; lia| clear K4].
  (* [comment removed for export] *)
  Step.zstep. ab_shload 4. Step.zstep. rewrite ?zxb_z8, ?sxb_z8. if_false. Step.zstep. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  step. if_cases K5; zify_cond K5; [exfalso; clear - K5 Hn; lia| clear K5].
  step. if_true.
  do 5 step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  assert (AGL1 : agree_on (lib_addr OW) m m1).
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn. split; [| exact I].
    destruct Ha as [Ha|(b & Hb & Hr)]; [revert Ha; unfold LIBW_S; cbn [rin_ivs fst snd]; unfold BnHeapA.ACEIL in *; lia|].
    pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & BC & _). unfold BnHeapA.ACEIL in *. lia. }
  assert (CS1 : crypto_statics m1) by (exact (crypto_statics_agree' OW m m1 CS AGL1)).
  assert (RS1 : realloc_statics m1) by (exact (realloc_statics_agree OW m m1 RS AGL1)).
  apply evt_done.
  eapply CRYPTO_realloc_null_walkA with (lo := lo) (n := n); [exact HEAP1| rewrite ESP; exact ST| exact CEIL| rewrite ESP; unfold CRYPTO_REALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia
    | rewrite ESP; unfold USTACK_TOP; lia| rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| assumption| exact TP| exact CS1| exact RS1| reflexivity| reflexivity| lia| exact CRED
    | rewrite ESP; uw_call_mu_tac m 80 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia]
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_sint_realloc (uk_ctx_tail _ _ _ E_set1_tail CTX))|].
  intros p Σ' ms' Hp PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & C & -> & MI2 & ST2 & AG2 & CR2 & BR2 & HEAP2 & ACC2 & (jk & BLK)).
  unfold MallocRep.wz in *. rewrite ESP in ST2, AG2.
  rewrite (ret_pc_even 0x224524) by (lia || reflexivity).
  pose proof BR2 as (C0 & C16 & _ & CCE & CIMG).
  assert (EC : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; alia).
  assert (HBIN2 : In (pblk, A, 24) (((p, C, n) :: OW) ++ LB)) by (right; exact HBIN').
  assert (INS2 : In bsrc (((p, C, n) :: OW) ++ LB)) by (right; exact INS).
  pose proof (AH_offsh _ _ _ _ (p, C, n) HEAP2 (or_introl eq_refl)) as OSHC. cbn [blk_addr blk_size fst snd] in OSHC.
  pose proof (AH_disjoint_gen _ _ _ _ (p, C, n) (pblk, A, 24) HEAP2 (or_introl eq_refl) HBIN2
                ltac:(cbn; intros E; apply Hp; rewrite E; apply in_map_iff; exists (pblk, A, 24); split; [reflexivity| exact HBIN'])) as DJB.
  cbn [blk_addr blk_size blk_id fst snd] in DJB.
  pose proof (AH_disjoint_gen _ _ _ _ (p, C, n) bsrc HEAP2 (or_introl eq_refl) INS2
                ltac:(cbn; intros E; apply Hp; rewrite E; apply in_map; exact INS)) as DJS.
  cbn [blk_addr blk_size blk_id fst snd] in DJS.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn in Ha; alia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in HB; [| intros a Ha; right; right; exists (pblk, A, 24); split; [exact HBIN'| cbn; cbn in Ha; alia]].
  apply (bytes_at_agree _ _ _ _ _ AG2) in SRC; [| intros a Ha; right; right; exists bsrc; split; [exact INS| lia]].
  ablock HEAP2 HBIN2 ACCB2 OFFB2.
  destruct (AH_shb _ _ _ _ HEAP2) as [SHB1' SHB2'].
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
  assert (OFF2 : offshW [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z) by (cbn [offshW]; alia).
  rename MU1 into MU0. clear HEAP1 CS1 RS1 ACCB SHB1 SHB2 OFF.
  pose proof (AH_disjoint_gen _ _ _ _ bsrc (pblk, A, 24) HEAP INS HBIN' NPB) as DJP. cbn [blk_addr blk_size blk_id fst snd] in DJP.
  lazymatch type of SRC with ?T => change (frozen T) in SRC end.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC; [exfalso; rewrite ?EC in KC; lia|]. clear KC.
  step. ab_shload 4. Step.zstep. rewrite ?zxb_z8, ?sxb_z8. if_false. step.
  step. if_cases KS; zify_cond KS; [exfalso; rewrite ?unsigned_lit in KS by lia; lia|]. clear KS.
  (* [comment removed for export] *)
  step. step. if_cases KD; zify_cond KD; [exfalso; rewrite ?EC in KD; lia|]. clear KD.
  step. step. step.
  name_mem m3.
  match goal with H : munch _ m2 m3 |- _ => rename H into MU3 end. match goal with H : wmono ctasegs m2 m3 |- _ => rename H into WM3 end.
  match goal with H : stk ctasegs m3 _ _ |- _ => rename H into ST3 end. match goal with H : mem_inv ctasegs m3 |- _ => rename H into MI3 end.
  assert (HEAP3 : AHEAP Σ' ((p, C, n) :: OW) LB m3).
  { eapply AH_frame; [exact HEAP2| exact MU3| exact WM3|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (pblk, A, 24); split; [exact HBIN2| cbn; lia]| constructor]. }
  unfold frozen in SRC. apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU3)) in SRC; [| intros a Ha; cbn [outside]; clear - Ha S1 S2 SLEN DJP BS3 CEIL LO'; alia].
  rewrite ?ESP in ST3.
  apply evt_done. eapply implAp_step_same.
  { eapply asan_memcpy_cpsA with (d := C) (s := P) (bs := src) (bd := (p, C, n)) (bsrc := bsrc) (lo := lo) (OW := (p, C, n) :: OW) (LB := LB); try reflexivity;
      rewrite ?ESP, ?SLEN; cbn [blk_addr blk_size fst snd];
      [exact HEAP3| exact ST3| exact CEIL| unfold RT_STACK; lia| unfold USTACK_TOP; lia| uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI3
      | left; reflexivity| lia| exact INS2| exact S1| exact S2| exact SRC| clear - DJS S1 S2; lia| lia| reflexivity]. }
  intros msM PO.
  destruct PO as (v0 & v1 & v2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & F3 & fc3 & mM & -> & MIM & STM & HEAPM & WMM & AGM & BYM & WRM).
  unfold MallocRep.wz in *. rewrite ?ESP in STM, AGM. rewrite (ret_pc_even 0x224578) by (clear; lia).
  apply (rw_cells_agree _ _ _ _ _ AGM) in FR; [| intros a Ha; cbn in Ha; split; [left; alia| clear - Ha CCE CEIL LO' SLEN; alia]].
  apply (rw_cells_agree _ _ _ _ _ AGM) in HB; [| intros a Ha; cbn in Ha; split; [right; right; exists (pblk, A, 24); split; [exact HBIN2| cbn; lia]| clear - Ha DJB Hn SLEN; lia]].
  ablock HEAPM HBIN2 ACCBM OFFBM.
  destruct (AH_shb _ _ _ _ HEAPM) as [SHB1M SHB2M].
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z mM) as MUM. pose proof (wmono_refl ctasegs mM) as WMM'.
  clear ACCB2 SHB1' SHB2'. try clear MU2. try clear WM2.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. zstep. step. step. step.
  do 9 step. release_frame FR STM (bv_unsigned sp). step. step.
  name_mem m9.
  apply evt_done. apply (K p Σ' _ Hp).
  unfold oalloc_postA, MallocRep.wz.
  do 16 eexists. exists m9, C. split; [reflexivity|].
  assert (MU9 : munch [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z mM m9) by assumption.
  split; [assumption|]. split; [assumption|].
  assert (HEAP9 : AHEAP Σ' ((p, C, n) :: OW) LB m9).
  { eapply AH_frame; [exact HEAPM| exact MU9| apply wmono_refl || assumption|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (pblk, A, 24); split; [exact HBIN2| cbn; lia]| constructor]. }
  split.
  { (* [comment removed for export] *)
    unfold apres_but.
    assert (FRM : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (A <= a < A + 24) -> outside [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z a).
    { intros a [Ha Hnb]. cbn [outside]. split; [| split; [clear - Hnb; lia| exact I]].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). clear - Hr BC CEIL LO'. alia. }
    assert (NEWB : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> ~ (C <= a < C + n)).
    { intros a Ha HAr. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
      - clear - Ha HAr CCE CEIL LO'. alia.
      - eapply (blk_not_static _ ((p, C, n) :: OW) LB m2 (p, C, n) a HEAP2 (or_introl eq_refl)); [cbn; clear - HAr; lia | exact Ha].
      - assert (NE : blk_id b <> p) by (intros E; apply Hp; rewrite <- E; apply in_map; exact Hb).
        pose proof (AH_disjoint_gen _ _ _ _ b (p, C, n) HEAP2 (or_intror Hb) (or_introl eq_refl) NE) as DJ. cbn in DJ. clear - DJ Hr HAr. lia. }
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU0)| intros a Ha; pose proof (FRM a Ha) as O; cbn [outside] in O |- *; clear - O; tauto]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG2| intros a [[Ha|[Ha|Ha]] _]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Ha]]|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU3)| exact FRM]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGM| intros a [Ha Hnb]; split; [| rewrite SLEN; exact (NEWB a Ha)];
      destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; apply in_block_mono with (L1 := OW ++ LB); [intros b Hb; right; exact Hb| exact Ha]]]|].
    eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU9)| exact FRM]. }
  split; [exact CR2|]. split; [exact BR2|]. split; [exact HEAP9|].
  split; [exact (proj2 (AH_acc _ _ _ _ (p, C, n) HEAP9 (or_introl eq_refl)))|].
  split.
  { pose proof (rw_cells_of_bytes _ C src BYM WRM) as HC. rewrite <- SLEN, Nat2Z.id. exact HC. }
  split.
  { unfold asn1_string_cells, MallocRep.wz. match goal with H : rw_cells ctasegs m9 A _ |- _ => exact H end. }
  eapply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU9)).
  - eapply (bytes_at_agree _ _ _ _ _ AGM); [exact SRC|]. intros a Ha. split; [right; right; exists bsrc; split; [exact INS2| clear - Ha S1 S2 SLEN; lia]| clear - Ha DJS S1 S2 SLEN; lia].
  - intros a Ha. cbn [outside]. clear - Ha S1 S2 SLEN DJP BS3 CEIL LO'. alia.
Qed.

(* [comment removed for export] *)
Lemma ASN1_STRING_set1_data_nosrc_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (pblk : bptr) (A ty n : Z)
    (ras : list Z) (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - ASN1_STRING_SET_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m -> realloc_statics m ->
  In (pblk, A, ASN1_STRING_SIZE) OW -> rw_cells ctasegs m A (asn1_string_cells 0 ty 0 0) -> 0 <= ty < 2^31 -> ty <> 3 ->
  a0 = wz A -> a1 = wz 0 -> a2 = wz n -> 0 < n < 2^31 ->
  mcost n <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ASN1_STRING_SET1_DATA_A (bv_unsigned ra :: ras) ->      (* [comment removed for export] *)
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     oalloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB A ASN1_STRING_SIZE n lo m 1
                  (fun C m' => (exists junk, rw_cells ctasegs m' C [CB (Z.to_nat n) junk]) /\ rw_cells ctasegs m' A (asn1_string_cells n ty C 0)) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc n k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_STRING_SET1_DATA_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI TP CS RS HBIN HB TY TY3 -> -> -> Hn CRED UW CTX K.
  pose proof LO as LO'. unfold ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RT_STACK, ASN1_STRING_SET1_DATA_A, MallocRep.wz in LO' |- *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (pblk, A, ASN1_STRING_SIZE) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4).
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB.
  unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  ablock HEAP HBIN' ACCB OFFB.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  unfold asn1_string_cells, MallocRep.wz in HB.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 96, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 step.
  step. step. step. if_cases K0; zify_cond K0; [clear K0| exfalso; rewrite (sx32_small ty) in K0 by lia; rewrite unsigned_lit in K0 by lia; exact (TY3 K0)].
  zstep. step. if_cases K1; zify_cond K1; [clear K1| exfalso; apply K1; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia].
  do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  (* [comment removed for export] *)
  carve_frame 80%nat ST. do 12 step.
  step. step. if_cases K2; zify_cond K2; [clear K2| exfalso; rewrite ab_signed_small in K2 by lia; lia].
  step. step. step.
  step. if_cases K3; zify_cond K3; [exfalso; clear - K3 Hn; lia| clear K3].
  (* [comment removed for export] *)
  step. zstep. step. step. if_true.
  step. if_cases K4; zify_cond K4; [exfalso; clear - K4 Hn; lia| clear K4].
  (* [comment removed for export] *)
  Step.zstep. ab_shload 4. Step.zstep. rewrite ?zxb_z8, ?sxb_z8. if_false. Step.zstep. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  step. if_cases K5; zify_cond K5; [exfalso; clear - K5 Hn; lia| clear K5].
  step. if_true.
  do 5 step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  assert (AGL1 : agree_on (lib_addr OW) m m1).
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn. split; [| exact I].
    destruct Ha as [Ha|(b & Hb & Hr)]; [revert Ha; unfold LIBW_S; cbn [rin_ivs fst snd]; unfold BnHeapA.ACEIL in *; lia|].
    pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & BC & _). unfold BnHeapA.ACEIL in *. lia. }
  assert (CS1 : crypto_statics m1) by (exact (crypto_statics_agree' OW m m1 CS AGL1)).
  assert (RS1 : realloc_statics m1) by (exact (realloc_statics_agree OW m m1 RS AGL1)).
  apply evt_done.
  eapply CRYPTO_realloc_null_walkA with (lo := lo) (n := n); [exact HEAP1| rewrite ESP; exact ST| exact CEIL| rewrite ESP; unfold CRYPTO_REALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia
    | rewrite ESP; unfold USTACK_TOP; lia| rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| assumption| exact TP| exact CS1| exact RS1| reflexivity| reflexivity| lia| exact CRED
    | rewrite ESP; uw_call_mu_tac m 80 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia]
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_sint_realloc (uk_ctx_tail _ _ _ E_set1_tail CTX))|].
  intros p Σ' ms' Hp PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & C & -> & MI2 & ST2 & AG2 & CR2 & BR2 & HEAP2 & ACC2 & (jk & BLK)).
  unfold MallocRep.wz in *. rewrite ESP in ST2, AG2.
  rewrite (ret_pc_even 0x224524) by (lia || reflexivity).
  pose proof BR2 as (C0 & C16 & _ & CCE & CIMG).
  assert (EC : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; alia).
  assert (HBIN2 : In (pblk, A, 24) (((p, C, n) :: OW) ++ LB)) by (right; exact HBIN').
  pose proof (AH_offsh _ _ _ _ (p, C, n) HEAP2 (or_introl eq_refl)) as OSHC. cbn [blk_addr blk_size fst snd] in OSHC.
  pose proof (AH_disjoint_gen _ _ _ _ (p, C, n) (pblk, A, 24) HEAP2 (or_introl eq_refl) HBIN2
                ltac:(cbn; intros E; apply Hp; rewrite E; apply in_map_iff; exists (pblk, A, 24); split; [reflexivity| exact HBIN'])) as DJB.
  cbn [blk_addr blk_size blk_id fst snd] in DJB.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn in Ha; alia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in HB; [| intros a Ha; right; right; exists (pblk, A, 24); split; [exact HBIN'| cbn; cbn in Ha; alia]].
  ablock HEAP2 HBIN2 ACCB2 OFFB2.
  destruct (AH_shb _ _ _ _ HEAP2) as [SHB1' SHB2'].
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
  assert (OFF2 : offshW [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z) by (cbn [offshW]; alia).
  rename MU1 into MU0. clear HEAP1 CS1 RS1 ACCB SHB1 SHB2 OFF.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC; [exfalso; rewrite ?EC in KC; lia|]. clear KC.
  step. ab_shload 4. Step.zstep. rewrite ?zxb_z8, ?sxb_z8. if_false. step.
  step. if_true.
  name_mem mM.
  match goal with H : munch _ m2 mM |- _ => rename H into MUM0 end. match goal with H : wmono ctasegs m2 mM |- _ => rename H into WMM0 end.
  match goal with H : stk ctasegs mM _ _ |- _ => rename H into STM end.
  assert (HEAPM : AHEAP Σ' ((p, C, n) :: OW) LB mM).
  { eapply AH_frame; [exact HEAP2| exact MUM0| exact WMM0|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (pblk, A, 24); split; [exact HBIN2| cbn; lia]| constructor]. }
  pose proof (agree_on_of_munch_nw _ _ _ MUM0) as AGM.
  ablock HEAPM HBIN2 ACCBM OFFBM.
  destruct (AH_shb _ _ _ _ HEAPM) as [SHB1M SHB2M].
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z mM) as MUM. pose proof (wmono_refl ctasegs mM) as WMM'.
  clear ACCB2 SHB1' SHB2'. try clear MUM0. try clear WMM0.
  apply evt_done.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step. zstep. step. step. step.
  do 9 step. release_frame FR STM (bv_unsigned sp). step. step.
  name_mem m9.
  apply evt_done. apply (K p Σ' _ Hp).
  unfold oalloc_postA, MallocRep.wz.
  do 16 eexists. exists m9, C. split; [reflexivity|].
  assert (MU9 : munch [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z mM m9) by assumption.
  split; [assumption|]. split; [assumption|].
  assert (HEAP9 : AHEAP Σ' ((p, C, n) :: OW) LB m9).
  { eapply AH_frame; [exact HEAPM| exact MU9| apply wmono_refl || assumption|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (pblk, A, 24); split; [exact HBIN2| cbn; lia]| constructor]. }
  split.
  { (* [comment removed for export] *)
    unfold apres_but.
    assert (FRM : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (A <= a < A + 24) -> outside [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z a).
    { intros a [Ha Hnb]. cbn [outside]. split; [| split; [clear - Hnb; lia| exact I]].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). clear - Hr BC CEIL LO'. alia. }
    assert (NEWB : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> ~ (C <= a < C + n)).
    { intros a Ha HAr. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
      - clear - Ha HAr CCE CEIL LO'. alia.
      - eapply (blk_not_static _ ((p, C, n) :: OW) LB m2 (p, C, n) a HEAP2 (or_introl eq_refl)); [cbn; clear - HAr; lia | exact Ha].
      - assert (NE : blk_id b <> p) by (intros E; apply Hp; rewrite <- E; apply in_map; exact Hb).
        pose proof (AH_disjoint_gen _ _ _ _ b (p, C, n) HEAP2 (or_intror Hb) (or_introl eq_refl) NE) as DJ. cbn in DJ. clear - DJ Hr HAr. lia. }
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU0)| intros a Ha; pose proof (FRM a Ha) as O; cbn [outside] in O |- *; clear - O; tauto]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG2| intros a [[Ha|[Ha|Ha]] _]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Ha]]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGM| exact FRM]|].
    eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU9)| exact FRM]. }
  split; [exact CR2|]. split; [exact BR2|]. split; [exact HEAP9|].
  split; [exact (proj2 (AH_acc _ _ _ _ (p, C, n) HEAP9 (or_introl eq_refl)))|].
  split.
  { exists jk. exact BLK. }
  unfold asn1_string_cells, MallocRep.wz. match goal with H : rw_cells ctasegs m9 A _ |- _ => exact H end.
Qed.

(* [comment removed for export] *)
Definition set1_zero_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (A ty lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres_ex LB OW (bv_unsigned sp) [(A, A + ASN1_STRING_SIZE)]%Z m m'
    /\ AHEAP Σ OW LB m'
    /\ rw_cells ctasegs m' A (asn1_string_cells 0 ty 0 0).

Lemma ASN1_STRING_set1_data_zero_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (pblk : bptr) (A ty : Z) (ras : list Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - ASN1_STRING_SET_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  In (pblk, A, ASN1_STRING_SIZE) OW -> rw_cells ctasegs m A (asn1_string_cells 0 ty 0 0) -> 0 <= ty < 2^31 -> ty <> 3 ->
  a0 = wz A -> a2 = wz 0 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ASN1_STRING_SET1_DATA_A (bv_unsigned ra :: ras) ->      (* [comment removed for export] *)
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz ASN1_STRING_SET1_DATA_A) fc None m (seg_rom ctasegs))))
      (ASTA RT Σ PMc (set1_zero_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB A ty lo m)).
Proof.
  intros until ras. intros HEAP ST CEIL LO SPT SP16 MI TP CS HBIN HB TY TY3 -> -> UW CTX.
  pose proof LO as LO'. unfold ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RT_STACK, ASN1_STRING_SET1_DATA_A, MallocRep.wz in LO' |- *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (pblk, A, ASN1_STRING_SIZE) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4).
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB.
  unfold ASN1_STRING_SIZE in *. cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  ablock HEAP HBIN' ACCB OFFB.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  unfold asn1_string_cells, MallocRep.wz in HB.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 96, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  apply cps_from_evt'.
  carve_frame 16%nat ST. do 4 step.
  step. step. step. if_cases K0; zify_cond K0; [clear K0| exfalso; rewrite (sx32_small ty) in K0 by lia; rewrite unsigned_lit in K0 by lia; exact (TY3 K0)].
  zstep. step. if_true.
  do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  carve_frame 80%nat ST. do 12 step.
  step. step. if_true.
  step. step. step.
  step. if_false.
  step. zstep. step. step. if_true.
  step. if_true.
  (* [comment removed for export] *)
  step. do 4 step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU1) | | exact CS].
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  apply evt_done. eapply cps_step_same.
  { eapply CRYPTO_free_null_cpsA with (lo := lo) (OW := OW) (LB := LB); try reflexivity;
      [exact HEAP1| rewrite ESP; exact ST| exact CEIL| rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; lia| rewrite ESP; unfold USTACK_TOP; lia
      | rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI| exact TP| exact CS1
      | rewrite ESP; uw_call_mu_tac m 80 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_sint_free (uk_ctx_tail _ _ _ E_set1_tail CTX))]. }
  intros ms3 PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & m3 & -> & MI3 & ST3 & HEAP3 & AG3).
  unfold MallocRep.wz in *. rewrite ESP in ST3, AG3. rewrite (ret_pc_even 0x2245f8) by (clear; lia).
  apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; cbn in Ha; left; unfold USTACK_TOP; lia].
  apply (rw_cells_agree _ _ _ _ _ AG3) in HB; [| intros a Ha; cbn in Ha; right; right; exists (pblk, A, 24); split; [exact HBIN'| cbn; lia]].
  ablock HEAP3 HBIN' ACCB3 OFFB3.
  destruct (AH_shb _ _ _ _ HEAP3) as [SHB1' SHB2'].
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  assert (OFF3 : offshW [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z) by (cbn [offshW]; alia).
  clear HEAP1 CS1 ACCB SHB1 SHB2 OFF.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. step. step.
  do 9 step. release_frame FR ST3 (bv_unsigned sp). step. step.
  name_mem m9.
  apply evt_done. apply cps_post. intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-.
  unfold set1_zero_postA, MallocRep.wz.
  do 16 eexists. exists m9. split; [reflexivity|].
  assert (MU9 : munch [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z m3 m9) by assumption.
  split; [assumption|]. split; [assumption|].
  assert (FRM : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(A, A + 24)]%Z a -> outside [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z a).
  { intros a [Ha [Hnb _]]. cbn [outside]. split; [| split; [exact Hnb| exact I]].
    destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
    - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). clear - Hr BC CEIL LO'. alia. }
  split.
  { unfold apres_ex.
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| intros a Ha; pose proof (FRM a Ha) as O; cbn [outside] in O |- *; clear - O; tauto]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG3| intros a [[Ha|[Ha|Ha]] _]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Ha]]|].
    eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU9)| exact FRM]. }
  split.
  { eapply AH_frame; [exact HEAP3| exact MU9| apply wmono_refl || assumption|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (pblk, A, 24); split; [exact HBIN'| cbn; lia]| constructor]. }
  unfold asn1_string_cells, MallocRep.wz. match goal with H : rw_cells ctasegs _ A _ |- _ => exact H end.
Qed.
End WithRT.
