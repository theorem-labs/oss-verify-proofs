(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG BnTree.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface W_akit W_obj_free ApErrKitA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import CtSizes CtWire CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sk_new W_sk_push.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import RtGenStmtA SctRepA W_crypto_reallocA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
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

Definition OPENSSL_SK_PUSH_A : Z := 0x1fc6f8.
Definition OPENSSL_SK_INSERT_A : Z := 0x1fb960.
Definition SK_RESERVE_A : Z := 0x1fb4e4.
(* [comment removed for export] *)
Definition SK_PUSH_STACK_A : Z := 208 + CRYPTO_CALLOC_STACK.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sk_rawA (num D sorted na : Z) : list cell :=
  [C4 (wz num); C4 (wz 0); C8 (wz D); C4 (wz sorted); C4 (wz na); C8 (wz 0); C8 (wz SK_SCT_CMP_THUNK_A); C8 (wz SK_SCT_FREEFUNC_THUNK_A); C8 (wz SK_SCT_COPY_THUNK_A)].
Lemma sk_cells_rawA : forall adr k sorted, sk_cells adr k sorted = sk_rawA (sk_num k) (optr adr (sk_data k)) sorted (olen (sk_data k)).
Proof. intros. reflexivity. Qed.

Notation magic_div5 := CtSctP.W_sk_push.magic_div5.
Notation lxor_ones31 := CtSctP.W_sk_push.lxor_ones31.
Notation sorted_after := CtSctP.W_sk_push.sorted_after.

(* [comment removed for export] *)
Definition sk_push_mcost (k : skr bptr) : Z :=
  match sk_data k with
  | None => 0
  | Some (_, na) => if Z.max (sk_num k + 1) SK_MIN_NODES <=? na then 0 else mcost (8 * (na * 8 / 5))
  end.

(* [comment removed for export] *)
Definition sk_na_after (k : skr bptr) : Z :=
  match sk_data k with
  | None => SK_MIN_NODES
  | Some (_, na) => if Z.max (sk_num k + 1) SK_MIN_NODES <=? na then na else na * 8 / 5
  end.

(* [comment removed for export] *)
Lemma lxor_63_small : forall num, 0 <= num < 2^63 -> Z.lxor num (2^63) = num + 2^63.
Proof.
  intros num H. rewrite <- Z.add_nocarry_lxor; [reflexivity|]. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec i 63) as [->|NE].
  - destruct (Z.eq_dec num 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
    rewrite (Z.bits_above_log2 num 63); [reflexivity| lia|]. apply Z.log2_lt_pow2; lia.
  - rewrite (Z.pow2_bits_eqb 63 i) by lia. replace (63 =? i) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
Qed.
Lemma loc_append_flag : forall num, 0 <= num < 2^31 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (v_slti (Z_to_bv 64 num) 0)) (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (v_slt (Z_to_bv 64 num) (Z_to_bv 64 num))) 1)))) = Z_to_bv 64 1.
Proof.
  intros num H. rewrite v_slt_b2z, v_slti_b2z, (unsigned_lit num) by lia. rewrite Z.ltb_irrefl.
  rewrite lxor_63_small by lia. replace (num + 2^63 <? 0 + 2^63) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma rw_cells_CB_ofA : forall (m : word -> option (bv 8)) A cs, rw_cells ctasegs m A cs -> rw_cells ctasegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs [[W B] R]. split; [split|].
  - cbn. split; [apply cells_bytes_length; exact W|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact R.
Qed.
Lemma rw_cells_old_junk : forall (m : word -> option (bv 8)) A n n0 (junk old : list (bv 8)),
  rw_cells ctasegs m A [CB (Z.to_nat n) junk] -> bytes_at ctasegs m A old -> Z.of_nat (length old) = n0 -> 0 <= n0 <= n ->
  rw_cells ctasegs m A [CB (Z.to_nat n0) old; CB (Z.to_nat (n - n0)) (skipn (Z.to_nat n0) junk)].
Proof.
  intros m A n n0 junk old [[W B] R] HO HL Hn. cbn in W. destruct W as [LJ _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  assert (EO : old = firstn (Z.to_nat n0) junk).
  { apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i (length old)) as [Hi|Hi].
    - destruct HO as (_ & _ & HO). destruct B as (_ & _ & HB). rewrite <- (HO i Hi).
      rewrite nth_error_firstn. replace (i <? Z.to_nat n0)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite <- (HB i) by lia. reflexivity.
    - rewrite (proj2 (nth_error_None old i) Hi). symmetry. apply nth_error_None. rewrite firstn_length. lia. }
  split; [split|].
  - cbn. rewrite length_skipn. repeat split; auto; lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, EO, firstn_skipn. exact B.
  - cbn [cells_size csize]. cbn [cells_size csize] in R. rewrite Nat.add_0_r in R |- *. replace (Z.to_nat n0 + Z.to_nat (n - n0))%nat with (Z.to_nat n) by lia. exact R.
Qed.

Local Notation E_push_tail := (E_OPENSSL_sk_push_1f8024 : uk_tail 0x1fc6f8 0x1fb960).                 (* [comment removed for export] *)
Local Notation E_ins_reserve := (E_OPENSSL_sk_insert_1f7034 : uk_call 0x1fb960 0x1fba48 0x1fb4e4).    (* [comment removed for export] *)
Local Notation E_res_calloc := (E_sk_reserve_1f6c5c : uk_call 0x1fb4e4 0x1fb5e4 0x202484).            (* [comment removed for export] *)
Local Notation E_res_rarray := (E_sk_reserve_1f6cdc : uk_call 0x1fb4e4 0x1fb70c 0x2025f4).            (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Hypothesis REA : realloc_contract_gen RT.

(* [comment removed for export] *)
Lemma CRYPTO_calloc_walkAp : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (num size lo : Z) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_CALLOC_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  crypto_statics m -> a0 = wz num -> a1 = wz size -> 0 < num -> 0 < size -> num * size < 2^32 ->
  mcost (num * size) <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_CALLOC (bv_unsigned ra :: ras) ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB (num * size) lo m
                  (fun A m' => rw_cells ctasegs m' A [CB (Z.to_nat (num * size)) (repeat (Z_to_bv 8 0) (Z.to_nat (num * size)))]) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc (num * size) k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_CALLOC) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI TP CS A0 A1 Hnum Hsize Hn CRED UW CTX K.
  change (AMalloc (num * size) k) with (apbind (bt_embed (TMalloc (num * size) (fun r => TRet r))) k).
  eapply implAp_bind.
  - apply implAp_bt. eapply (CRYPTO_calloc_walkA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB num size lo ras
             (fun r => TRet r) (fun r Σ' ms' => exists p, r = Some p /\ ~ In p (map blk_id (OW ++ LB)) /\
                calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB (num * size) lo m
                             (fun A m' => rw_cells ctasegs m' A [CB (Z.to_nat (num * size)) (repeat (Z_to_bv 8 0) (Z.to_nat (num * size)))]) p Σ' ms'));
      try eassumption.
    intros p Σ' ms' Hp PO. apply implA_ret. exists p. split; [reflexivity|]. split; [exact Hp | exact PO].
  - intros r Σ' ms' (p & -> & Hp & PO). exact (K p Σ' ms' Hp PO).
Qed.

(* [comment removed for export] *)
Lemma push_prefixA : forall (P : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (pst : bptr) (SA X num D sorted na : Z) (ras : list Z),
  AHEAP Σ OW LB m -> In (pst, SA, STACK_SIZE) OW ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> mem_inv ctasegs m ->
  rw_cells ctasegs m SA (sk_rawA num D sorted na) -> 0 <= num < 2^22 ->
  a0 = wz SA -> a1 = wz X ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx OPENSSL_SK_PUSH_A (bv_unsigned ra :: ras) ->
  (forall m1 (j8 j9 : list (bv 8)) (a3' a4' : word),
     munch [(bv_unsigned sp - 192, bv_unsigned sp)] m m1 -> wmono ctasegs m m1 -> mem_inv ctasegs m1 -> stk ctasegs m1 lo (bv_unsigned sp + -192) ->
     AHEAP Σ OW LB m1 ->
     rw_cells ctasegs m1 (bv_unsigned sp + -112) [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     rw_cells ctasegs m1 (bv_unsigned sp + -192) [CB 8 j9; C8 (Z_to_bv 64 (Z.shiftr SA 3 + SHB)); C8 s6; C8 s5; C8 (wz X); C8 s3; C8 (wz num); C8 (wz SA); C8 sp; C8 (wz 0x1fba48)] ->      (* [comment removed for export] *)
     rw_cells ctasegs m1 SA (sk_rawA num D sorted na) ->
     uw_chain USTACK_TOP m1 (bv_unsigned sp + -192) (bv_unsigned sp + -112) (0x1fba48 :: bv_unsigned ra :: ras) ->
     uk_ctx SK_RESERVE_A (0x1fba48 :: bv_unsigned ra :: ras) ->
     evt ctasegs P
       (* [comment removed for export] *)
       (MS (mkR (wz 0x1fba48) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -112)) (wz SA)
                (wz 0) (wz 1) (wz 0) a3' a4' a5 a6 a7
                (wz (SA + 8)) (wz (Z.max (num + 1) 4)) (wz X) (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (SA + 8))) 3 + SHB)) (wz SHB)
                (Z_to_bv 64 (Z.shiftr SA 3 + SHB)) (wz SHB) s9 s10 s11 t3 t4 t5 t6)
           F (wz 0x1fb59c) fc None m1 (seg_rom ctasegs))) ->
  evt ctasegs P
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz OPENSSL_SK_PUSH_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until ras. intros HEAP HIN ST CEIL LO SPT SP16 MI HC Hnum -> -> UW CTX K.
  unfold OPENSSL_SK_PUSH_A, SK_RESERVE_A, STACK_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HIN' : In (pst, SA, 56) (OW ++ LB)) by (apply in_or_app; left; exact HIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN') as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HIN)) as ALS.
  assert (EA : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  ablock HEAP HIN' ACCS OFFS.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 192, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  unfold sk_rawA, MallocRep.wz in HC.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 step.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?EA in K0; lia|]. clear K0.
  (* [comment removed for export] *)
  step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  setreg 12%Z (Z_to_bv 64 num) ltac:(symmetry; apply usx32_small; lia).
  (* [comment removed for export] *)
  carve_frame 112%nat ST. do 15 step.
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?EA in K1; lia|]. clear K1.
  step. step. step. step. setreg 10%Z (Z_to_bv 64 num) ltac:(symmetry; apply usx32_small; lia).
  step. step.
  step. if_cases K2; zify_cond K2; [| exfalso; revert K2; rewrite ?unsigned_lit by lia; lia]. clear K2.
  do 4 step.
  (* [comment removed for export] *)
  carve_frame 80%nat ST. do 11 step.
  step. step. setreg 10%Z (Z_to_bv 64 num) ltac:(symmetry; apply usx32_small; lia).
  step. step. step. setreg 13%Z (Z_to_bv 64 (2147483647 - num)) ltac:(rewrite (unsigned_lit num) by lia; rewrite lxor_ones31 by lia; reflexivity).
  step. if_cases K3; zify_cond K3; [| exfalso; revert K3; rewrite ?ab_signed_small, ?signed_small, ?unsigned_lit by lia; lia]. clear K3.
  step. setreg 19%Z (Z_to_bv 64 (num + 1)) ltac:(rewrite ?(unsigned_lit num), ?(unsigned_lit 1), ?swrap32_small by lia; f_equal; lia).
  step.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [left; cbn; alia| constructor]. }
  assert (UWI : uw_chain USTACK_TOP m1 (bv_unsigned sp + -112) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { uw_call_mu_tac m 112 UW MU FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia]. }
  assert (UWR : uw_chain USTACK_TOP m1 (bv_unsigned sp + -192) (bv_unsigned sp + -112) (0x1fba48 :: bv_unsigned ra :: ras)).
  { lazymatch goal with FR0 : rw_cells _ m1 (bv_unsigned sp + -192) (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: _) |- _ =>
      apply (uw_push_frame m1 _ (bv_unsigned sp + -112) 80 [c0; c1; c2; c3; c4; c5; c6; c7] 0x1fba48 (bv_unsigned sp) (bv_unsigned ra :: ras));
      [reflexivity | lia | clear - SP16; uchk_open; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | exact SPR | | exact UWI] end.
    rewrite !Z_to_bv_bv_unsigned. replace (bv_unsigned sp + -112 + -80) with (bv_unsigned sp + -192) by lia.
    match goal with FR0 : rw_cells _ m1 (bv_unsigned sp + -192) _ |- _ => exact FR0 end. }
  pose proof (uk_ctx_call _ _ _ _ E_ins_reserve (uk_ctx_tail _ _ _ E_push_tail CTX)) as CTXR.
  step. if_cases K4; zify_cond K4.
  - (* [comment removed for export] *)
    rewrite ?ab_signed_small, ?signed_small in K4 by lia.
    apre. setreg 19%Z (Z_to_bv 64 (Z.max (num + 1) 4)) ltac:(rewrite Z.max_l by lia; reflexivity). rewrite ?EA in *.
    eapply K; [exact MU| exact WM| exact MI| exact ST| exact HEAP1| exact FR| | unfold sk_rawA, MallocRep.wz; exact HC| exact UWR| exact CTXR].
    match goal with FR0 : rw_cells _ m1 (bv_unsigned sp + -192) _ |- _ => exact FR0 end.
  - (* [comment removed for export] *)
    rewrite ?ab_signed_small, ?signed_small in K4 by lia.
    step. apre. setreg 19%Z (Z_to_bv 64 (Z.max (num + 1) 4)) ltac:(rewrite Z.max_r by lia; reflexivity). rewrite ?EA in *.
    eapply K; [exact MU| exact WM| exact MI| exact ST| exact HEAP1| exact FR| | unfold sk_rawA, MallocRep.wz; exact HC| exact UWR| exact CTXR].
    match goal with FR0 : rw_cells _ m1 (bv_unsigned sp + -192) _ |- _ => exact FR0 end.
Qed.
(* [comment removed for export] *)
Lemma insert_tailA : forall (P : machine_state -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (x1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 x19 x21 x22 x25 x26 x27 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (pst pd : bptr) (SA X num D sorted na : Z)
    (wl : list word) (jb j8 : list (bv 8)),
  AHEAP Σ OW LB m -> In (pst, SA, STACK_SIZE) OW -> In (pd, D, 8 * na) OW -> pd <> pst ->
  stk ctasegs m lo (bv_unsigned sp + -112) -> ACEIL <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m ->
  rw_cells ctasegs m SA (sk_rawA num D sorted na) -> 0 <= num -> num + 1 <= na -> na < 2^23 -> 0 <= sorted <= 1 -> 0 <= X < 2^64 ->
  rw_cells ctasegs m D (map C8 wl ++ [CB (length jb) jb]) -> zlength wl = num -> Z.of_nat (length jb) = 8 * (na - num) ->
  rw_cells ctasegs m (bv_unsigned sp + -112) [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  (forall m2 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     munch [(bv_unsigned sp - 112, bv_unsigned sp); (SA, SA + STACK_SIZE); (D + 8 * num, D + 8 * num + 8)] m m2 -> wmono ctasegs m m2 -> mem_inv ctasegs m2 ->
     stk ctasegs m2 lo (bv_unsigned sp) ->
     rw_cells ctasegs m2 SA (sk_rawA (num + 1) D (sorted_after sorted num) na) ->
     rw_cells ctasegs m2 D (map C8 (wl ++ [wz X]) ++ [CB (length jb - 8) (skipn 8 jb)]) ->
     evt ctasegs P
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (num + 1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F (ret_pc ra) fc None m2 (seg_rom ctasegs))) ->
  evt ctasegs P
    (* [comment removed for export] *)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 sp (wz SA) (wz 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
             (wz num) x19 (wz X) x21 x22 (Z_to_bv 64 (Z.shiftr SA 3 + SHB)) (wz SHB) x25 x26 x27 xt3 xt4 xt5 xt6)
        F (wz 0x1fba48) fc None m (seg_rom ctasegs)).
Proof.
  intros until j8. intros HEAP HSIN HDIN NPD ST CEIL LO SPT SP16 MI HC Hn0 Hna Hna2 Hs HX HD WL JB FR K.
  unfold STACK_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HSIN' : In (pst, SA, 56) (OW ++ LB)) by (apply in_or_app; left; exact HSIN).
  assert (HDIN' : In (pd, D, 8 * na) (OW ++ LB)) by (apply in_or_app; left; exact HDIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HSIN') as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HDIN') as (D0 & _ & _ & DC & DI). cbn [blk_addr blk_size fst snd] in D0, DC, DI.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HSIN)) as ALS. pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HDIN)) as ALD.
  pose proof (AH_disjoint_gen _ _ _ _ (pd, D, 8 * na) (pst, SA, 56) HEAP HDIN' HSIN' NPD) as DJ. cbn [blk_addr blk_size blk_id fst snd] in DJ.
  assert (EA : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  ablock HEAP HSIN' ACCS OFFS. ablock HEAP HDIN' ACCD OFFD.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (SA, SA + 56); (D + 8 * num, D + 8 * num + 8)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 112, bv_unsigned sp); (SA, SA + 56); (D + 8 * num, D + 8 * num + 8)]%Z) by (cbn [offshW]; alia).
  unfold sk_rawA, MallocRep.wz in HC.
  (* [comment removed for export] *)
  apply rw_cells_app in HD. destruct HD as [HDL HDR].
  assert (EL : Z.of_nat (cells_size (map C8 wl)) = 8 * num).
  { unfold zlength in WL. rewrite <- WL. clear. induction wl as [|w t IH]; [reflexivity|]. cbn [map cells_size csize length]. cbn [map cells_size] in IH. lia. }
  rewrite EL in HDR. remember (D + 8 * num) as Dn eqn:EDn.
  assert (DNR : D <= Dn /\ Dn + 8 <= D + 8 * na) by lia.
  assert (HDR2 : rw_cells ctasegs m Dn ([CB 8%nat (firstn 8 jb)] ++ [CB (length jb - 8)%nat (skipn 8 jb)])).
  { eapply rw_cells_recast; [exact HDR| | |].
    - cbn. rewrite firstn_length_le, length_skipn by lia. auto.
    - cbn. rewrite !app_nil_r. apply firstn_skipn.
    - cbn. lia. }
  clear HDR. apply rw_cells_app in HDR2. destruct HDR2 as [HDR HDT].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HDT. change (frozen (rw_cells ctasegs m (Dn + 8) [CB (length jb - 8)%nat (skipn 8 jb)])) in HDT.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; lia|]. clear K0.
  step. setreg 11%Z (Z_to_bv 64 num) ltac:(symmetry; apply usx32_small; lia).
  step.
  step. step. step. step. setreg 12%Z (Z_to_bv 64 1) ltac:(symmetry; apply loc_append_flag; lia).
  step. if_cases KL; [exfalso; revert KL; vm_compute; congruence|]. clear KL.
  (* [comment removed for export] *)
  step. setreg 12%Z (Z_to_bv 64 (8 * num)) ltac:(apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
  OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. setreg 10%Z (Z_to_bv 64 Dn) ltac:(subst Dn; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve).
  step.
  step. step.
  (* [comment removed for export] *)
  step. setreg 10%Z (Z_to_bv 64 num) ltac:(symmetry; apply usx32_small; lia).
  step. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
  setreg 11%Z (Z_to_bv 64 (num + 1)) ltac:(rewrite ?(unsigned_lit num), ?swrap32_small by lia; f_equal; lia).
  step. step.
  name_mem m1.
  assert (JOIN : forall (x10 x11 x12 x13 x14 x21 x22 x27 : word) mj,
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (SA, SA + 56); (Dn, Dn + 8)] m mj -> wmono ctasegs m mj -> mem_inv ctasegs mj ->
    stk ctasegs mj lo (bv_unsigned sp + -112) ->
    rw_cells ctasegs mj SA [C4 (Z_to_bv 64 (num + 1)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 (sorted_after sorted num)); C4 (Z_to_bv 64 na); C8 (Z_to_bv 64 0);
                          C8 (Z_to_bv 64 SK_SCT_CMP_THUNK_A); C8 (Z_to_bv 64 SK_SCT_FREEFUNC_THUNK_A); C8 (Z_to_bv 64 SK_SCT_COPY_THUNK_A)] ->
    rw_cells ctasegs mj D (map C8 wl) -> rw_cells ctasegs mj Dn [C8 (Z_to_bv 64 X)] ->
    rw_cells ctasegs mj (bv_unsigned sp + -112) [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt ctasegs P
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 xa5 xa6 xa7
               (Z_to_bv 64 num) (Z_to_bv 64 (SA + 8)) (Z_to_bv 64 (SA + 16)) x21 x22 (Z_to_bv 64 (Z.shiftr SA 3 + SHB)) (Z_to_bv 64 SHB)
               (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (SA + 8))) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (SA + 16))) 3 + SHB)) x27 xt3 xt4 xt5 xt6)
         F (Z_to_bv 64 0x1fbc14) fc None mj (seg_rom ctasegs))).
  { intros x10 x11 x12 x13 x14 x21' x22' x27' mj MUj WMj MIj STj HCj HDLj HDRj FRj.
    step. setreg 10%Z (Z_to_bv 64 (num + 1)) ltac:(symmetry; apply usx32_small; lia).
    do 13 step. release_frame FRj STj (bv_unsigned sp). step. step.
    eapply K; [exact MUj| exact WMj| exact MIj| exact STj| unfold sk_rawA, MallocRep.wz; exact HCj|].
    rewrite map_app, <- app_assoc. apply rw_cells_app. split; [exact HDLj|]. rewrite EL. cbn [map app]. unfold MallocRep.wz.
    change (C8 (Z_to_bv 64 X) :: [CB (length jb - 8)%nat (skipn 8 jb)]) with ([C8 (Z_to_bv 64 X)] ++ [CB (length jb - 8)%nat (skipn 8 jb)]).
    apply rw_cells_app. rewrite <- EDn. split; [exact HDRj|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unfold frozen in HDT.
    eapply rw_cells_transport; [exact HDT| exact MUj| exact WMj|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  step. if_cases KS; zify_cond KS.
  - (* [comment removed for export] *)
    eapply JOIN; [eassumption| eassumption| eassumption| eassumption| | eassumption| eassumption| eassumption].
    assert (S0 : sorted = 0) by (revert KS; rewrite ?usx32_small, ?unsigned_lit by lia; lia). subst sorted. unfold CtSctP.W_sk_push.sorted_after. cbn. assumption.
  - (* [comment removed for export] *)
    step. if_cases KN; [zify_cond KN|].
    + (* [comment removed for export] *)
      eapply JOIN; [eassumption| eassumption| eassumption| eassumption| | eassumption| eassumption| eassumption].
      unfold CtSctP.W_sk_push.sorted_after. replace (0 <? num) with false by (symmetry; apply Z.ltb_ge; revert KN; rewrite ?usx32_small, ?ab_signed_small, ?signed_small, ?unsigned_lit, ?swrap32_small by lia; lia).
      rewrite Bool.andb_false_r. assumption.
    + (* [comment removed for export] *)
      apply Bool.negb_false_iff in KN. zify_cond KN.
      step. step. if_cases KC; [| exfalso; revert KC; vm_compute; congruence]. clear KC.
      step.
      eapply JOIN; [eassumption| eassumption| eassumption| eassumption| | eassumption| eassumption| eassumption].
      unfold CtSctP.W_sk_push.sorted_after. replace (negb (sorted =? 0) && (0 <? num)) with true; [assumption|].
      symmetry. apply andb_true_iff. split; [apply Bool.negb_true_iff; apply Z.eqb_neq| apply Z.ltb_lt];
        revert KS KN0; rewrite ?usx32_small, ?ab_signed_small, ?signed_small, ?unsigned_lit, ?swrap32_small by lia; lia.
Qed.
Lemma AH_permOW : forall Σ OW OW' LB m, AHEAP Σ OW LB m -> Permutation OW OW' -> AHEAP Σ OW' LB m.
Proof.
  intros Σ OW OW' LB m (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & F & AP) & ND & HF1 & HF2) P.
  split; [exact HA|]. split; [exact HS|]. split; [exact HFr|].
  split. { split; [exact FW|]. exists PB, LBr. split; [exact P1|]. split; [| split; [exact F| exact AP]].
           eapply Permutation_trans; [exact P2|]. apply Permutation_map. apply Permutation_app_tail. exact P. }
  split. { eapply nodup_ids_perm; [| exact ND]. apply Permutation_app_tail. exact P. }
  split; [| exact HF2]. apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) HF1). eapply Permutation_in; [symmetry; exact P| exact Hb].
Qed.

Lemma perm_readdA : forall (b : block) L, List.NoDup (map blk_id L) -> In b L -> Permutation L (b :: lb_remove (blk_id b) L).
Proof.
  intros b L. induction L as [|c L IH]; intros ND IN; [destruct IN|]. cbn in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
  rewrite BnHeapA.lb_remove_cons. destruct IN as [->|IN].
  - rewrite bptr_eqb_refl. rewrite BnHeapA.lb_remove_notin by exact NI. apply Permutation_refl.
  - rewrite (bptr_eqb_neq (blk_id c) (blk_id b)) by (intros E; apply NI; rewrite E; apply in_map; exact IN).
    apply Permutation_trans with (c :: b :: lb_remove (blk_id b) L); [apply perm_skip; apply IH; assumption| apply perm_swap].
Qed.

(* [comment removed for export] *)
Definition push_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (lo : Z) (m : mem) (k : skr bptr) (x : sctr bptr) (SA X sorted : Z) (ws : list word) (st : ap_st bptr)
    (r : skr bptr * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' (q' : bptr) (D' na' : Z) (jb' : list (bv 8)),
    let num := sk_num k in
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz (num + 1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ r = (mkSK (sk_blk k) (Some (q', na')) (sk_items k ++ [x]), st)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (lb_remove (sk_blk k) (lremove (sk_data k) OW) ++ LB) (bv_unsigned sp)) m m'
    /\ rt_credit RT Σ - sk_push_mcost k <= rt_credit RT Σ'
    /\ ablock_range D' (8 * na') /\ AHEAP Σ' ((q', D', 8 * na') :: lremove (sk_data k) OW) LB m'
    /\ rw_cells ctasegs m' SA (sk_rawA (num + 1) D' (sorted_after sorted num) na')
    /\ rw_cells ctasegs m' D' (map C8 (ws ++ [wz X]) ++ [CB (length jb') jb']) /\ Z.of_nat (length jb') = 8 * (na' - num - 1)
    /\ num + 1 <= na' /\ SK_MIN_NODES <= na' < 2^23
    /\ na' = sk_na_after k.
  (* [comment removed for export] *)

Theorem OPENSSL_sk_push_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (k : skr bptr) (x : sctr bptr) (st : ap_st bptr) (SA X D sorted : Z) (ws : list word) (jb : list (bv 8)) (ras : list Z),
  let num := sk_num k in
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - SK_PUSH_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> bv_unsigned ra mod 2 = 0 ->
  crypto_statics m -> realloc_statics m ->
  In (sk_blk k, SA, STACK_SIZE) OW -> rw_cells ctasegs m SA (sk_rawA num D sorted (olen (sk_data k))) -> 0 <= sorted <= 1 -> num < 2^22 ->
  match sk_data k with
  | Some (q, na) => In (q, D, 8 * na) OW /\ q <> sk_blk k /\ num <= na /\ SK_MIN_NODES <= na < 2^23
                    /\ rw_cells ctasegs m D (map C8 ws ++ [CB (length jb) jb]) /\ Z.of_nat (length jb) = 8 * (na - num)
  | None => sk_items k = [] /\ D = 0 /\ jb = []
  end -> zlength ws = num ->
  0 <= X < 2^64 -> a0 = wz SA -> a1 = wz X ->
  sk_push_mcost k <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx OPENSSL_SK_PUSH_A (bv_unsigned ra :: ras) ->
  implAp (sk_push k x st) Σ
        (push_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m k x SA X sorted ws st)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz OPENSSL_SK_PUSH_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until ras. cbn zeta. intros HEAP ST CEIL LO SPT SP16 MI TP RAEV CS RS HSIN HC Hs Hnum HD WS HX HA0 HA1 CRED UW CTX.
  pose proof (Zle_0_nat (length (sk_items k))) as NUM0. change (Z.of_nat (length (sk_items k))) with (sk_num k) in NUM0.
  unfold sk_push. unfold sk_push_mcost in CRED |- *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  assert (LO' : lo <= bv_unsigned sp - 192) by (unfold SK_PUSH_STACK_A, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO; lia).
  assert (HSIN' : In (sk_blk k, SA, STACK_SIZE) (OW ++ LB)) by (apply in_or_app; left; exact HSIN).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP HSIN) as BRS. pose proof BRS as (B0 & B16 & _ & BC & BI).
  pose proof (AH_nodup _ _ _ _ HEAP) as ND. pose proof (AH_nodup_l _ _ _ _ HEAP) as NDL.
  destruct (sk_data k) as [[q na]|] eqn:EDATA.
  - destruct HD as (HDIN & NQS & Hna & Hna4 & HD & JB). cbn [olen] in HC.
    assert (HDIN' : In (q, D, 8 * na) (OW ++ LB)) by (apply in_or_app; left; exact HDIN).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP HDIN) as BRD. pose proof BRD as (D0 & D16 & _ & DC & DI).
    pose proof (AH_disjoint_gen _ _ _ _ (q, D, 8 * na) (sk_blk k, SA, STACK_SIZE) HEAP HDIN' HSIN' NQS) as DJ. cbn [blk_addr blk_size blk_id fst snd] in DJ.
    unfold STACK_SIZE in *.
    destruct (Z.max (sk_num k + 1) SK_MIN_NODES <=? na) eqn:ROOM.
    + (* [comment removed for export] *)
      unfold aret. apply implAp_ret_evt. apply Z.leb_le in ROOM. unfold SK_MIN_NODES in ROOM.
      eapply (push_prefixA _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB lo (sk_blk k) SA X (sk_num k) D sorted na ras);
        [exact HEAP| exact HSIN| exact ST| exact CEIL| exact LO'| exact SPT| exact SP16| exact MI| exact HC| lia| exact HA0| exact HA1| exact UW| exact CTX|].
      intros m1 j8 j9 xa3 xa4 MU WM MI1 ST1 HEAP1 FR FR0 HC1 UWR CTXR. unfold sk_rawA, MallocRep.wz in HC1. unfold MallocRep.wz in FR0 |- *.
      assert (EW : Z.of_nat (cells_size (map C8 ws ++ [CB (length jb) jb])) = 8 * na).
      { rewrite cells_size_app. cbn [cells_size csize]. unfold zlength in WS.
        replace (cells_size (map C8 ws)) with (8 * length ws)%nat; [lia|].
        clear. induction ws as [|w t IH]; [reflexivity|]. cbn [map cells_size csize length]. cbn [map cells_size] in IH. lia. }
      assert (HD1 : rw_cells ctasegs m1 D (map C8 ws ++ [CB (length jb) jb])) by (eapply rw_cells_transport; [exact HD| exact MU| exact WM| cbn [disjoint_from]; rewrite EW; unfold BnHeapA.ACEIL in *; lia]).
      change (frozen (rw_cells ctasegs m1 D (map C8 ws ++ [CB (length jb) jb]))) in HD1. clear HD.
      ablock HEAP1 HSIN' ACCS OFFS.
      pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m1) as MU1. pose proof (wmono_refl ctasegs m1) as WM1'.
      assert (OFF1 : offshW [(bv_unsigned sp - 192, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
      (* [comment removed for export] *)
      step. step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (unfold BnHeapA.ACEIL in *; lia); lia|]. clear K0.
      step. step. if_cases K1; [| exfalso; revert K1; vm_compute; congruence]. clear K1.
      step. if_cases K2; zify_cond K2; [| exfalso; revert K2; rewrite ?usx32_small, ?ab_signed_small, ?signed_small, ?unsigned_lit by lia; lia]. clear K2.
      step. do 9 step. release_frame FR0 ST1 (bv_unsigned sp + -112). step. step.
      unfold frozen in HD1.
      eapply insert_tailA with (lo := lo) (D := D) (sorted := sorted) (na := na) (wl := ws) (jb := jb) (pst := sk_blk k) (pd := q) (OW := OW) (LB := LB) (Σ := Σ);
        [exact HEAP1| exact HSIN| exact HDIN| exact NQS| exact ST1| exact CEIL| exact LO'| exact SPT| exact SP16| exact MI1
        | exact HC1| lia| lia| lia| lia| lia| exact HD1| exact WS| exact JB| exact FR|].
      intros m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MU2 WM2 MI2 ST2 HC2 HD2. unfold STACK_SIZE in MU2.
      apply evt_done. unfold push_postA. cbn zeta. unfold MallocRep.wz. rewrite EDATA. cbn [CtRepP.ApErrKit.lremove].
      exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, F, fc, m2, q, D, na, (skipn 8 jb).
      split; [subst tp; reflexivity|]. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|].
      assert (CLI : forall a, aclient_addr (lb_remove (sk_blk k) (lb_remove q OW) ++ LB) (bv_unsigned sp) a ->
                    outside [(bv_unsigned sp - 112, bv_unsigned sp); (SA, SA + 56); (D + 8 * sk_num k, D + 8 * sk_num k + 8)] a
                    /\ outside [(bv_unsigned sp - 192, bv_unsigned sp)] a).
      { intros a Hc. cbn [outside]. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]].
        - repeat split; try exact I; lia.
        - destruct Hc as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
          destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold BnHeapA.ACEIL in *; repeat split; try exact I; lia.
        - apply in_app_iff in Hb0.
          assert (Hb' : In b' (OW ++ LB) /\ blk_id b' <> sk_blk k /\ blk_id b' <> q).
          { destruct Hb0 as [Hb0|Hb0].
            - apply BnHeapA.lb_remove_In in Hb0. destruct Hb0 as [Hb1 Hns]. apply BnHeapA.lb_remove_In in Hb1. destruct Hb1 as [Hb1 Hnq].
              split; [apply in_or_app; left; exact Hb1| split; [exact Hns| exact Hnq]].
            - split; [apply in_or_app; right; exact Hb0|]. rewrite map_app in ND. destruct (CtSctP.W_sct_list_free.NoDup_app_split _ _ ND) as (_ & NX & _).
              split; intros E; [apply (NX (sk_blk k)); [apply (in_map blk_id _ _ HSIN)| rewrite <- E; apply in_map; exact Hb0]
                               | apply (NX q); [apply (in_map blk_id _ _ HDIN)| rewrite <- E; apply in_map; exact Hb0]]. }
          destruct Hb' as (Hb' & Hns & Hnq).
          pose proof (AH_disjoint_gen _ _ _ _ (sk_blk k, SA, 56) b' HEAP HSIN' Hb' ltac:(cbn; intros E; apply Hns; symmetry; exact E)) as DJ1.
          pose proof (AH_disjoint_gen _ _ _ _ (q, D, 8 * na) b' HEAP HDIN' Hb' ltac:(cbn; intros E; apply Hnq; symmetry; exact E)) as DJ2.
          cbn [blk_addr blk_size blk_id fst snd] in DJ1, DJ2.
          pose proof (AH_range_gen _ _ _ _ b' HEAP Hb') as (_ & _ & _ & B3' & _). unfold BnHeapA.ACEIL in *. repeat split; try exact I; lia. }
      split. { eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)| intros a Ha; exact (proj2 (CLI a Ha))]|].
               eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU2)| intros a Ha; exact (proj1 (CLI a Ha))]. }
      split. { unfold sk_push_mcost. rewrite EDATA. replace (Z.max (sk_num k + 1) SK_MIN_NODES <=? na) with true by (symmetry; apply Z.leb_le; unfold SK_MIN_NODES; lia).
               pose proof (af_credit_nonneg RT AF Σ m (AH_art _ _ _ _ HEAP)). lia. }
      split; [exact BRD|].
      split. { eapply AH_permOW; [| apply (perm_readdA (q, D, 8 * na)); [exact NDL| exact HDIN]].
               eapply AH_frame; [exact HEAP1| exact MU2| exact WM2|].
               constructor; [left; cbn; alia|]. constructor; [right; right; exists (sk_blk k, SA, 56); split; [exact HSIN'| cbn; lia]|].
               constructor; [right; right; exists (q, D, 8 * na); split; [exact HDIN'| cbn; lia]| constructor]. }
      split; [exact HC2|]. split; [rewrite length_skipn; exact HD2|].
      split; [rewrite length_skipn; lia|].
      split; [lia|]. split; [unfold SK_MIN_NODES; lia|]. unfold sk_na_after. rewrite EDATA. replace (Z.max (sk_num k + 1) SK_MIN_NODES <=? na) with true by (symmetry; apply Z.leb_le; unfold SK_MIN_NODES in *; lia). reflexivity.
    + (* [comment removed for export] *)
      unfold abind, arealloc, aret. cbn [apbind].
      apply Z.leb_gt in ROOM. unfold SK_MIN_NODES in *.
      assert (EN : na = sk_num k) by lia.
      replace (Z.max (sk_num k + 1) 4) with (na + 1) by lia. rewrite (sk_grow_once na) by lia.
      apply implAp_from_evt.
      eapply (push_prefixA _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB lo (sk_blk k) SA X (sk_num k) D sorted na ras);
        [exact HEAP| exact HSIN| exact ST| exact CEIL| exact LO'| exact SPT| exact SP16| exact MI| exact HC| lia| exact HA0| exact HA1| exact UW| exact CTX|].
      intros m1 j8 j9 xa3 xa4 MU WM MI1 ST1 HEAP1 FR FR0 HC1 UWR CTXR. unfold sk_rawA, MallocRep.wz in HC1. unfold MallocRep.wz in FR0 |- *.
      assert (EW : Z.of_nat (cells_size (map C8 ws ++ [CB (length jb) jb])) = 8 * na).
      { rewrite cells_size_app. cbn [cells_size csize]. unfold zlength in WS.
        replace (cells_size (map C8 ws)) with (8 * length ws)%nat; [lia|].
        clear. induction ws as [|w t IH]; [reflexivity|]. cbn [map cells_size csize length]. cbn [map cells_size] in IH. lia. }
      assert (HD1 : rw_cells ctasegs m1 D (map C8 ws ++ [CB (length jb) jb])) by (eapply rw_cells_transport; [exact HD| exact MU| exact WM| cbn [disjoint_from]; rewrite EW; unfold BnHeapA.ACEIL in *; lia]).
      clear HD.
      ablock HEAP1 HSIN' ACCS OFFS.
      pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m1) as MU1. pose proof (wmono_refl ctasegs m1) as WM1'.
      assert (OFF1 : offshW [(bv_unsigned sp - 192, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
      replace (Z.max (sk_num k + 1) 4) with (na + 1) by lia.
      (* [comment removed for export] *)
      step. step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (unfold BnHeapA.ACEIL in *; lia); lia|]. clear K0.
      step. setreg 15%Z (Z_to_bv 64 na) ltac:(symmetry; apply usx32_small; lia).
      step. if_cases K1; [| exfalso; revert K1; vm_compute; congruence]. clear K1.
      step. if_cases K2; zify_cond K2; [exfalso; revert K2; rewrite ?usx32_small, ?ab_signed_small, ?unsigned_lit by lia; lia|]. clear K2.
      do 7 step.
      (* [comment removed for export] *)
      step. step.
      setreg 15%Z (Z_to_bv 64 7)
        ltac:(f_equal; symmetry; rewrite Z.shiftr_div_pow2 by lia; rewrite Z_to_bv_unsigned; unfold bv_wrap;
              change (bv_modulus 64) with (4294967296 * 4294967296); change (bv_modulus 32) with 4294967296;
              rewrite Z.mod_mod_divide by (exists 4294967296; lia);
              replace ((na + -268435456) mod 4294967296) with (na + 4026531840) by (rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small by lia; lia);
              replace ((na + 4026531840) / 2 ^ 29) with 7 by (apply Z.div_unique with (r := na + 4026531840 - 7 * 2^29); lia);
              apply swrap32_small; lia).
      (* [comment removed for export] *)
      step. if_true. step. step. step. step. step.
      setreg 23%Z (Z_to_bv 64 (na * 8 / 5))
        ltac:(f_equal; symmetry; rewrite (unsigned_lit na) by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8;
              rewrite swrap32_small by lia; rewrite (unsigned_lit (na * 8)) by lia; rewrite ab_signed_small by nia;
              rewrite (unsigned_lit (na * 8 * 1717986919)) by nia; rewrite !Z.shiftr_div_pow2 by lia; rewrite magic_div5 by lia;
              rewrite (Z.div_small _ (2 ^ 63)) by nia; rewrite Z.add_0_r; reflexivity).
      assert (GR : na + 1 <= na * 8 / 5) by (apply Z.div_le_lower_bound; lia).
      assert (GR2 : na * 8 / 5 < 2 ^ 23) by (apply Z.div_lt_upper_bound; lia).
      (* [comment removed for export] *)
      step. setreg 15%Z (Z_to_bv 64 (na * 8 / 5)) ltac:(first [ symmetry; apply usx32_small; lia | rewrite ?(unsigned_lit (na * 8 / 5)) by lia; rewrite ?Z.add_0_r; rewrite ?swrap32_small by lia; f_equal; lia ]).
      step. if_cases K4; zify_cond K4; [exfalso; revert K4; rewrite ?ab_signed_small, ?unsigned_lit by lia; lia|]. clear K4.
      step. setreg 11%Z (Z_to_bv 64 (na * 8 / 5)) ltac:(first [ symmetry; apply usx32_small; lia | rewrite ?(unsigned_lit (na * 8 / 5)) by lia; rewrite ?Z.add_0_r; rewrite ?swrap32_small by lia; f_equal; lia ]).
      step. step. step. step. step.
      (* [comment removed for export] *)
      pose proof (rw_cells_CB_ofA _ _ _ HD1) as HDB.
      replace (cells_size (map C8 ws ++ [CB (length jb) jb])) with (Z.to_nat (8 * na)) in HDB by lia.
      set (old := cells_bytes (map C8 ws ++ [CB (length jb) jb])) in HDB.
      assert (OLDL : Z.of_nat (length old) = 8 * na).
      { subst old. pose proof (proj1 (proj1 HDB)) as WF. cbn in WF. lia. }
      pose proof (proj2 (proj1 HDB)) as OLDB. cbn [cells_bytes cbytes] in OLDB. rewrite app_nil_r in OLDB.
      replace (8 * (na * 8 / 5)) with (na * 8 / 5 * 8) by lia.
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -192)) = bv_unsigned sp + -192) by (apply unsigned_lit; lia).
      assert (ESP2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
      assert (RS1 : realloc_statics m1).
      { unfold realloc_statics in *. eapply ro_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU)| exact RS|].
        intros a Ha. cbn [outside]. unfold CR_REALLOC_IMPL in Ha. cbn in Ha. unfold BnHeapA.ACEIL in *. lia. }
      apply evt_done.
      eapply (CRYPTO_realloc_array_walkAp REA) with (A := D) (n0 := 8 * na) (lo := lo) (OW := OW) (LB := LB) (ras := 0x1fba48 :: bv_unsigned ra :: ras);
        [exact HEAP1| exact HDIN| rewrite ESP; exact ST1| exact CEIL| rewrite ESP; unfold CRYPTO_REALLOC_ARRAY_STACK_A, CRYPTO_REALLOC2_STACK, RT_STACK; unfold SK_PUSH_STACK_A, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO; lia
        | rewrite ESP; unfold USTACK_TOP in *; lia| rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI1| exact TP
        | rewrite unsigned_lit by (clear; lia); reflexivity| exact RS1| reflexivity| reflexivity| reflexivity| lia| lia| lia
        | replace (na * 8 / 5 * 8) with (8 * (na * 8 / 5)) by lia; exact CRED
        | rewrite ESP, ESP2; exact UWR| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_res_rarray CTXR)|].
      intros q' Σ3 ms3 Hq' PO. unfold realloc_postA in PO. rewrite ?ESP, ?ESP2 in PO.
      destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & F3 & fc3 & m3 & A' & -> & MI3 & ST3 & AG3 & CR3 & BR' & HEAP3 & ACC3 & [junk HJ3] & OLD3).
      rewrite (ret_pc_even 0x1fb70c) by (clear; lia).
      set (na' := na * 8 / 5) in *.
      pose proof BR' as (A0 & A16 & _ & AC & AI).
      assert (EA' : bv_unsigned (Z_to_bv 64 A') = A') by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
      pose proof (AH_nodup _ _ _ _ HEAP3) as ND3. cbn [map blk_id fst snd app] in ND3. rewrite map_app in ND3. apply NoDup_cons_iff in ND3. destruct ND3 as [NQ' ND3'].
      assert (HSIN3 : In (sk_blk k, SA, 56) (lb_remove q OW)) by (apply BnHeapA.lb_remove_In; split; [exact HSIN| cbn; intros E; apply NQS; symmetry; exact E]).
      assert (HSIN3' : In (sk_blk k, SA, 56) (((q', A', na' * 8) :: lb_remove q OW) ++ LB)) by (right; apply in_or_app; left; exact HSIN3).
      assert (NQS' : q' <> sk_blk k) by (intros E; apply Hq'; rewrite E; apply (in_map blk_id _ (sk_blk k, SA, 56)); exact HSIN').
      pose proof (AH_disjoint_gen _ _ _ _ (q', A', na' * 8) (sk_blk k, SA, 56) HEAP3 ltac:(left; reflexivity) HSIN3' NQS') as DJ'.
      cbn [blk_addr blk_size blk_id fst snd] in DJ'.
      (* [comment removed for export] *)
      assert (AGS : forall a, bv_unsigned sp - 192 <= a < bv_unsigned sp \/ SA <= a < SA + 56 -> aclient_addr (lb_remove q OW ++ LB) (bv_unsigned sp + -192) a).
      { intros a [Ha|Ha]; [left; unfold USTACK_TOP in *; lia| right; right; exists (sk_blk k, SA, 56); split; [apply in_or_app; left; exact HSIN3| cbn; lia]]. }
      apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; apply AGS; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG3) in FR0; [| intros a Ha; apply AGS; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AG3) in HC1; [| intros a Ha; apply AGS; right; cbn in Ha; lia].
      (* [comment removed for export] *)
      assert (JB0 : jb = []) by (destruct jb; [reflexivity| exfalso; cbn [length] in JB; lia]). subst jb.
      pose proof (OLD3 old OLDB ltac:(rewrite OLDL; lia)) as OLD3'.
      pose proof (rw_cells_old_junk m3 A' (na' * 8) (8 * na) junk old HJ3 OLD3' OLDL ltac:(lia)) as HDN0.
      assert (HDN : rw_cells ctasegs m3 A' (map C8 ws ++ [CB (Z.to_nat (na' * 8 - 8 * na)) (skipn (Z.to_nat (8 * na)) junk)])).
      { eapply rw_cells_recast; [exact HDN0| | |].
        - apply cells_wf_app'. split; [clear; induction ws as [|w t IH]; cbn; [exact I| split; [exact I| exact IH]]|]. cbn. rewrite length_skipn.
          pose proof (proj1 (proj1 HJ3)) as WJ. cbn in WJ. split; [lia| exact I].
        - subst old. rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
        - rewrite cells_size_app. cbn [cells_size csize]. rewrite cells_size_app in EW. cbn [cells_size csize length] in EW. lia. }
      assert (LJ : length junk = Z.to_nat (na' * 8)) by (pose proof (proj1 (proj1 HJ3)) as WJ; cbn in WJ; lia).
      clear HDN0 HJ3.
      ablock HEAP3 HSIN3' ACCS3 OFFS3.
      destruct (AH_shb _ _ _ _ HEAP3) as [SHB1' SHB2'].
      pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp); (SA, SA + 56)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
      assert (OFF3 : offshW [(bv_unsigned sp - 192, bv_unsigned sp); (SA, SA + 56)]%Z) by (cbn [offshW]; alia).
      assert (SEPA' : A' + na' * 8 <= bv_unsigned sp - 192) by (unfold BnHeapA.ACEIL in *; lia).
      change (frozen (rw_cells ctasegs m3 A' (map C8 ws ++ [CB (Z.to_nat (na' * 8 - 8 * na)) (skipn (Z.to_nat (8 * na)) junk)]))) in HDN.
      clear ACCS MU1 WM1' OFF1.
      (* [comment removed for export] *)
      apply implAp_ret_evt. unfold MallocRep.wz.
      step. if_cases K5; zify_cond K5; [exfalso; rewrite ?EA' in K5; lia|]. clear K5.
      step. step. step.
      do 9 step. release_frame FR0 ST3 (bv_unsigned sp + -112). step. step.
      name_mem m4. unfold frozen in HDN.
      replace (na' * 8) with (8 * na') in BR', HEAP3 by lia.
      assert (HDIN4 : In (q', A', 8 * na') ((q', A', 8 * na') :: lb_remove q OW)) by (left; reflexivity).
      assert (HSIN4 : In (sk_blk k, SA, 56) ((q', A', 8 * na') :: lb_remove q OW)) by (right; exact HSIN3).
      assert (HEAP4 : AHEAP Σ3 ((q', A', 8 * na') :: lb_remove q OW) LB m4).
      { match goal with MU4 : munch _ m3 m4 |- _ => eapply AH_frame; [exact HEAP3| exact MU4| assumption|] end.
        constructor; [left; cbn; alia|]. constructor; [right; right; exists (sk_blk k, SA, 56); split; [replace (na' * 8) with (8 * na') in HSIN3' by lia; exact HSIN3'| cbn; lia]| constructor]. }
      eapply insert_tailA with (lo := lo) (D := A') (sorted := sorted) (na := na') (wl := ws) (jb := skipn (Z.to_nat (8 * na)) junk) (pst := sk_blk k) (pd := q')
                               (OW := (q', A', 8 * na') :: lb_remove q OW) (LB := LB) (Σ := Σ3);
        [exact HEAP4| exact HSIN4| exact HDIN4| exact NQS'| assumption| exact CEIL| exact LO'| exact SPT| exact SP16| assumption
        | match goal with H : rw_cells ctasegs m4 SA _ |- _ => exact H end| lia| lia| lia| lia| lia| | exact WS| | exact FR|].
      { replace (length (skipn (Z.to_nat (8 * na)) junk)) with (Z.to_nat (na' * 8 - 8 * na)).
        - match goal with MU4 : munch _ m3 m4 |- _ => eapply rw_cells_transport; [exact HDN| exact MU4| assumption|] end.
          rewrite cells_size_app. cbn [disjoint_from cells_size csize]. rewrite cells_size_app in EW. cbn [cells_size csize length] in EW. lia.
        - rewrite length_skipn, LJ. lia. }
      { rewrite length_skipn, LJ. lia. }
      intros m5 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MU5 WM5 MI5 ST5 HC5 HD5. unfold STACK_SIZE in MU5.
      apply evt_done. unfold push_postA. cbn zeta. unfold MallocRep.wz. rewrite EDATA. cbn [CtRepP.ApErrKit.lremove].
      exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, F3, fc3, m5, q', A', na', (skipn 8 (skipn (Z.to_nat (8 * na)) junk)).
      split; [reflexivity|]. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|].
      assert (CLI5 : forall a, aclient_addr (lb_remove (sk_blk k) (lb_remove q OW) ++ LB) (bv_unsigned sp) a ->
                     outside [(bv_unsigned sp - 112, bv_unsigned sp); (SA, SA + 56); (A' + 8 * sk_num k, A' + 8 * sk_num k + 8)] a
                     /\ outside [(bv_unsigned sp - 192, bv_unsigned sp); (SA, SA + 56)] a /\ outside [(bv_unsigned sp - 192, bv_unsigned sp)] a
                     /\ aclient_addr (lb_remove q OW ++ LB) (bv_unsigned sp + -192) a).
      { intros a Hc. cbn [outside]. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]].
        - repeat split; try exact I; try lia. left. lia.
        - pose proof Hc as Hc'. destruct Hc as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
          destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold BnHeapA.ACEIL in *; (repeat split; try exact I; try lia; right; left; exact Hc').
        - apply in_app_iff in Hb0.
          assert (Hb' : In b' (OW ++ LB) /\ blk_id b' <> sk_blk k /\ blk_id b' <> q /\ In b' (lb_remove q OW ++ LB)).
          { destruct Hb0 as [Hb0|Hb0].
            - apply BnHeapA.lb_remove_In in Hb0. destruct Hb0 as [Hb1 Hns]. pose proof Hb1 as Hb1'. apply BnHeapA.lb_remove_In in Hb1. destruct Hb1 as [Hb1 Hnq].
              split; [apply in_or_app; left; exact Hb1| split; [exact Hns| split; [exact Hnq| apply in_or_app; left; exact Hb1']]].
            - split; [apply in_or_app; right; exact Hb0|]. rewrite map_app in ND. destruct (CtSctP.W_sct_list_free.NoDup_app_split _ _ ND) as (_ & NX & _).
              split; [| split; [| apply in_or_app; right; exact Hb0]]; intros E;
                [apply (NX (sk_blk k)); [apply (in_map blk_id _ _ HSIN)| rewrite <- E; apply in_map; exact Hb0]
                | apply (NX q); [apply (in_map blk_id _ _ HDIN)| rewrite <- E; apply in_map; exact Hb0]]. }
          destruct Hb' as (Hb' & Hns & Hnq & HbR).
          pose proof (AH_disjoint_gen _ _ _ _ (sk_blk k, SA, 56) b' HEAP HSIN' Hb' ltac:(cbn; intros E; apply Hns; symmetry; exact E)) as DJ1.
          assert (NB : q' <> blk_id b') by (intros E; apply Hq'; rewrite E; apply in_map; exact Hb').
          pose proof (AH_disjoint_gen _ _ _ _ (q', A', 8 * na') b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact HbR) NB) as DJ2.
          cbn [blk_addr blk_size blk_id fst snd] in DJ1, DJ2.
          pose proof (AH_range_gen _ _ _ _ b' HEAP Hb') as (_ & _ & _ & B3' & _). unfold BnHeapA.ACEIL in *.
          repeat split; try exact I; try lia. right; right. exists b'. split; [exact HbR| exact Hr]. }
      split. { eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)| intros a Ha; exact (proj1 (proj2 (proj2 (CLI5 a Ha))))]|].
               eapply agree_on_trans; [eapply agree_on_mono; [exact AG3| intros a Ha; exact (proj2 (proj2 (proj2 (CLI5 a Ha))))]|].
               eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU3)| intros a Ha; exact (proj1 (proj2 (CLI5 a Ha)))]|].
               eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU5)| intros a Ha; exact (proj1 (CLI5 a Ha))]. }
      split. { unfold sk_push_mcost. rewrite EDATA. replace (Z.max (sk_num k + 1) SK_MIN_NODES <=? na) with false by (symmetry; apply Z.leb_gt; unfold SK_MIN_NODES; lia).
               subst na'. replace (8 * (na * 8 / 5)) with (na * 8 / 5 * 8) by lia. exact CR3. }
      split; [exact BR'|].
      split. { eapply AH_frame; [exact HEAP4| exact MU5| exact WM5|].
               constructor; [left; cbn; alia|]. constructor; [right; right; exists (sk_blk k, SA, 56); split; [right; apply in_or_app; left; exact HSIN3| cbn; lia]|].
               constructor; [right; right; exists (q', A', 8 * na'); split; [left; reflexivity| cbn; lia]| constructor]. }
      split; [exact HC5|]. split; [rewrite length_skipn; exact HD5|].
      split; [rewrite !length_skipn, LJ; lia|].
      split; [lia|]. split; [unfold SK_MIN_NODES; lia|]. unfold sk_na_after. rewrite EDATA. replace (Z.max (sk_num k + 1) SK_MIN_NODES <=? na) with false by (symmetry; apply Z.leb_gt; unfold SK_MIN_NODES in *; lia). reflexivity.
  - (* [comment removed for export] *)
    destruct HD as (ITEMS0 & D0 & JB0). subst D jb. cbn [olen] in HC.
    assert (N0 : sk_num k = 0) by (unfold sk_num, zlength; rewrite ITEMS0; reflexivity).
    assert (WS0 : ws = []) by (destruct ws; [reflexivity| exfalso; unfold zlength in WS; cbn [length] in WS; lia]). subst ws.
    rewrite N0 in *. change (Z.max (0 + 1) SK_MIN_NODES) with 4. change (8 * 4) with (4 * 8).
    unfold abind, amalloc, aret. cbn [apbind].
    apply implAp_from_evt.
    eapply (push_prefixA _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB lo (sk_blk k) SA X 0 0 sorted 0 ras);
      [exact HEAP| exact HSIN| exact ST| exact CEIL| exact LO'| exact SPT| exact SP16| exact MI| exact HC| lia| exact HA0| exact HA1| exact UW| exact CTX|].
    intros m1 j8 j9 xa3 xa4 MU WM MI1 ST1 HEAP1 FR FR0 HC1 UWR CTXR. unfold sk_rawA, MallocRep.wz in HC1. unfold MallocRep.wz in FR0 |- *. unfold STACK_SIZE in *.
    ablock HEAP1 HSIN' ACCS OFFS.
    pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m1) as MU1. pose proof (wmono_refl ctasegs m1) as WM1'.
    assert (OFF1 : offshW [(bv_unsigned sp - 192, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -192)) = bv_unsigned sp + -192) by (apply unsigned_lit; lia).
    assert (ESP2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
    change (Z.max (0 + 1) 4) with 4.
    (* [comment removed for export] *)
    step. step. if_cases K0; [| exfalso; revert K0; vm_compute; congruence]. clear K0.
    do 6 step.
    apply evt_done.
    eapply CRYPTO_calloc_walkAp with (num := 4) (size := 8) (lo := lo) (OW := OW) (LB := LB) (ras := 0x1fba48 :: bv_unsigned ra :: ras); try reflexivity;
      [exact HEAP1| rewrite ESP; exact ST1| exact CEIL| rewrite ESP; unfold SK_PUSH_STACK_A in LO; lia| rewrite ESP; unfold USTACK_TOP in *; lia
      | rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI1| exact TP| exact CS1
      | unfold mcost; cbn; exact (af_credit_nonneg RT AF Σ m1 (AH_art _ _ _ _ HEAP1))
      | rewrite ESP, ESP2; exact UWR| rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_res_calloc CTXR)|].
    intros p Σ3 ms3 Hp PO. unfold calloc_postA in PO. rewrite ?ESP, ?ESP2 in PO.
    destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & F3 & fc3 & m3 & A' & -> & MI3 & ST3 & AG3 & CR3 & BR' & HEAP3 & ACC3 & BLK).
    rewrite (ret_pc_even 0x1fb5e4) by (clear; lia).
    change (Z.to_nat (4 * 8)) with 32%nat in BLK. change (4 * 8) with 32 in BR', HEAP3, ACC3.
    pose proof BR' as (A0 & A16 & _ & AC & AI).
    assert (EA' : bv_unsigned (Z_to_bv 64 A') = A') by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
    assert (HSIN3' : In (sk_blk k, SA, 56) (((p, A', 32) :: OW) ++ LB)) by (right; exact HSIN').
    assert (NQS' : p <> sk_blk k) by (intros E; apply Hp; rewrite E; apply (in_map blk_id _ (sk_blk k, SA, 56)); exact HSIN').
    pose proof (AH_disjoint_gen _ _ _ _ (p, A', 32) (sk_blk k, SA, 56) HEAP3 ltac:(left; reflexivity) HSIN3' NQS') as DJ'.
    cbn [blk_addr blk_size blk_id fst snd] in DJ'.
    (* [comment removed for export] *)
    assert (AGS : forall a, bv_unsigned sp - 192 <= a < bv_unsigned sp \/ SA <= a < SA + 56 -> aclient_addr (OW ++ LB) (bv_unsigned sp + -192) a).
    { intros a [Ha|Ha]; [left; unfold USTACK_TOP in *; lia| right; right; exists (sk_blk k, SA, 56); split; [exact HSIN'| cbn; lia]]. }
    apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; apply AGS; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in FR0; [| intros a Ha; apply AGS; left; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in HC1; [| intros a Ha; apply AGS; right; cbn in Ha; lia].
    ablock HEAP3 HSIN3' ACCS3 OFFS3.
    destruct (AH_shb _ _ _ _ HEAP3) as [SHB1' SHB2'].
    pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp); (SA, SA + 56)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
    assert (OFF3 : offshW [(bv_unsigned sp - 192, bv_unsigned sp); (SA, SA + 56)]%Z) by (cbn [offshW]; alia).
    assert (SEPA' : A' + 32 <= bv_unsigned sp - 192) by (unfold BnHeapA.ACEIL in *; lia).
    change (frozen (rw_cells ctasegs m3 A' [CB 32%nat (repeat (Z_to_bv 8 0) 32%nat)])) in BLK.
    clear ACCS MU1 WM1' OFF1.
    (* [comment removed for export] *)
    apply implAp_ret_evt. unfold MallocRep.wz.
    step.
    step. if_cases K5; zify_cond K5; [exfalso; rewrite ?EA' in K5; lia|]. clear K5.
    step. step. step.
    do 9 step. release_frame FR0 ST3 (bv_unsigned sp + -112). step. step.
    name_mem m4. unfold frozen in BLK.
    assert (HDIN4 : In (p, A', 8 * 4) ((p, A', 8 * 4) :: OW)) by (left; reflexivity).
    assert (HSIN4 : In (sk_blk k, SA, 56) ((p, A', 8 * 4) :: OW)) by (right; exact HSIN).
    assert (HEAP4 : AHEAP Σ3 ((p, A', 8 * 4) :: OW) LB m4).
    { change (8 * 4) with 32. match goal with MU4 : munch _ m3 m4 |- _ => eapply AH_frame; [exact HEAP3| exact MU4| assumption|] end.
      constructor; [left; cbn; alia|]. constructor; [right; right; exists (sk_blk k, SA, 56); split; [exact HSIN3'| cbn; lia]| constructor]. }
    replace 32 with (8 * 4) in BR' by reflexivity.
    eapply insert_tailA with (lo := lo) (D := A') (sorted := sorted) (na := 4) (wl := []) (jb := repeat (Z_to_bv 8 0) 32%nat) (pst := sk_blk k) (pd := p)
                             (OW := (p, A', 8 * 4) :: OW) (LB := LB) (Σ := Σ3);
      [exact HEAP4| exact HSIN4| exact HDIN4| exact NQS'| assumption| exact CEIL| exact LO'| exact SPT| exact SP16| assumption
      | match goal with H : rw_cells ctasegs m4 SA _ |- _ => exact H end| lia| lia| lia| lia| lia| | reflexivity| reflexivity| exact FR|].
    { cbn [map app length repeat]. match goal with MU4 : munch _ m3 m4 |- _ => eapply rw_cells_transport; [exact BLK| exact MU4| assumption|] end.
      cbn [disjoint_from cells_size csize Nat.add]. lia. }
    intros m5 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MU5 WM5 MI5 ST5 HC5 HD5. unfold STACK_SIZE in MU5.
    apply evt_done. unfold push_postA. cbn zeta. unfold MallocRep.wz. rewrite EDATA, N0. cbn [CtRepP.ApErrKit.lremove].
    exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, F3, fc3, m5, p, A', 4, (skipn 8 (repeat (Z_to_bv 8 0) 32%nat)).
    split; [reflexivity|]. split; [rewrite ITEMS0; reflexivity|]. split; [exact MI5|]. split; [exact ST5|].
    assert (CLI5 : forall a, aclient_addr (lb_remove (sk_blk k) OW ++ LB) (bv_unsigned sp) a ->
                   outside [(bv_unsigned sp - 112, bv_unsigned sp); (SA, SA + 56); (A' + 8 * 0, A' + 8 * 0 + 8)] a
                   /\ outside [(bv_unsigned sp - 192, bv_unsigned sp); (SA, SA + 56)] a /\ outside [(bv_unsigned sp - 192, bv_unsigned sp)] a
                   /\ aclient_addr (OW ++ LB) (bv_unsigned sp + -192) a).
    { intros a Hc. cbn [outside]. destruct Hc as [Hc|[Hc|(b' & Hb0 & Hr)]].
      - repeat split; try exact I; try lia. left. lia.
      - pose proof Hc as Hc'. destruct Hc as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
        destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold BnHeapA.ACEIL in *; (repeat split; try exact I; try lia; right; left; exact Hc').
      - apply in_app_iff in Hb0.
        assert (Hb' : In b' (OW ++ LB) /\ blk_id b' <> sk_blk k).
        { destruct Hb0 as [Hb0|Hb0].
          - apply BnHeapA.lb_remove_In in Hb0. destruct Hb0 as [Hb1 Hns]. split; [apply in_or_app; left; exact Hb1| exact Hns].
          - split; [apply in_or_app; right; exact Hb0|]. rewrite map_app in ND. destruct (CtSctP.W_sct_list_free.NoDup_app_split _ _ ND) as (_ & NX & _).
            intros E. apply (NX (sk_blk k)); [apply (in_map blk_id _ _ HSIN)| rewrite <- E; apply in_map; exact Hb0]. }
        destruct Hb' as (Hb' & Hns).
        pose proof (AH_disjoint_gen _ _ _ _ (sk_blk k, SA, 56) b' HEAP HSIN' Hb' ltac:(cbn; intros E; apply Hns; symmetry; exact E)) as DJ1.
        assert (NB : p <> blk_id b') by (intros E; apply Hp; rewrite E; apply in_map; exact Hb').
        pose proof (AH_disjoint_gen _ _ _ _ (p, A', 32) b' HEAP3 ltac:(left; reflexivity) ltac:(right; exact Hb') NB) as DJ2.
        cbn [blk_addr blk_size blk_id fst snd] in DJ1, DJ2.
        pose proof (AH_range_gen _ _ _ _ b' HEAP Hb') as (_ & _ & _ & B3' & _). unfold BnHeapA.ACEIL in *.
        repeat split; try exact I; try lia. right; right. exists b'. split; [exact Hb'| exact Hr]. }
    split. { eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)| intros a Ha; exact (proj1 (proj2 (proj2 (CLI5 a Ha))))]|].
             eapply agree_on_trans; [eapply agree_on_mono; [exact AG3| intros a Ha; exact (proj2 (proj2 (proj2 (CLI5 a Ha))))]|].
             eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU3)| intros a Ha; exact (proj1 (proj2 (CLI5 a Ha)))]|].
             eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU5)| intros a Ha; exact (proj1 (CLI5 a Ha))]. }
    split. { assert (MC0 : forall z, z = 4 * 8 -> mcost z = 0) by (intros z ->; reflexivity).
             first [rewrite (MC0 (4 * 8) eq_refl) in CR3 | rewrite (MC0 32 eq_refl) in CR3]. unfold sk_push_mcost. rewrite ?EDATA. lia. }
    split; [exact BR'|].
    split. { change (8 * 4) with 32. eapply AH_frame; [change 32 with (8 * 4); exact HEAP4| exact MU5| exact WM5|].
             constructor; [left; cbn; alia|]. constructor; [right; right; exists (sk_blk k, SA, 56); split; [exact HSIN3'| cbn; lia]|].
             constructor; [right; right; exists (p, A', 32); split; [left; reflexivity| cbn; lia]| constructor]. }
    split; [exact HC5|]. split; [rewrite length_skipn; exact HD5|].
    split; [rewrite length_skipn; cbn; lia|].
    split; [lia|]. split; [unfold SK_MIN_NODES; lia|]. unfold sk_na_after. rewrite EDATA. reflexivity.
Qed.

End WithRT.
