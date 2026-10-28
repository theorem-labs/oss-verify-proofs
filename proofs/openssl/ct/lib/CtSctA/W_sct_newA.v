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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG.
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_new.
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

Definition SCT_NEW_A : Z := 0x3374cc.
Definition SCT_NEW_STACK_A : Z := 32 + CRYPTO_ZALLOC_STACK.
Definition CRYPTO_MEMDUP_A : Z := 0x203fd8.
Definition CRYPTO_MEMDUP_STACK_A : Z := 48 + CRYPTO_MALLOC_STACK.

(* [comment removed for export] *)
Notation sct_zero_cells := CtSctP.W_sct_new.sct_zero_cells.
Notation sct_new_cells := CtSctP.W_sct_new.sct_new_cells.

Lemma zero104_sct_cellsA : forall m A,
  rw_cells ctasegs m A [CB 104%nat (repeat (Z_to_bv 8 0) 104%nat)] -> rw_cells ctasegs m A sct_zero_cells.
Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; repeat split; auto| unfold CtSctP.W_sct_new.sct_zero_cells, MallocRep.wz; bytes_lit_eq| reflexivity]. Qed.

Lemma rw_cells_of_bytesA : forall m A bs, bytes_at ctasegs m A bs -> wr_at ctasegs m A (Z.of_nat (length bs)) -> rw_cells ctasegs m A [CB (length bs) bs].
Proof.
  intros m A bs HB HW. split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]|].
  cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact HW.
Qed.

Local Notation E_new_zalloc := (E_SCT_new_34b970 : uk_call 0x3374cc 0x337504 0x1fcef0).          (* [comment removed for export] *)
Local Notation E_dup_malloc := (E_CRYPTO_memdup_1fe6ac : uk_call 0x203fd8 0x204020 0x1fce24).    (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma SCT_new_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - SCT_NEW_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_NEW_A (bv_unsigned ra :: ras) ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB SCT_SIZE lo m
                  (fun A m' => rw_cells ctasegs m' A (sct_new_cells (Z_to_bv 64 (-1)))) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc SCT_SIZE k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SCT_NEW_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> CS UW CTX K.
  unfold SCT_NEW_STACK_A, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK, SCT_NEW_A, SCT_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply implAp_from_evt.
  carve_frame 32%nat ST. do 5 step.
  (* [comment removed for export] *)
  do 5 step.
  name_mem m1.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia | constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU1) | | exact CS].
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  apply evt_done.
  eapply (CRYPTO_zalloc_walkAp) with (n := 104) (lo := lo) (OW := OW) (LB := LB) (ras := bv_unsigned ra :: ras); try reflexivity.
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
  - rewrite ESP. uw_call_mu_tac m 32 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia].
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_new_zalloc CTX).
  - intros p Σ' ms' Hp PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & A & -> & MI2 & ST2 & AG2 & CR2 & BR2 & HEAP2 & ACC2 & BLK).
    unfold MallocRep.wz in *. rewrite ESP in ST2, AG2.
    rewrite (ret_pc_even 0x337504) by (lia || reflexivity).
    pose proof BR2 as (A0 & A16 & _ & ACE & AIMG).
    assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; alia).
    pose proof (AH_offsh _ _ _ _ (p, A, 104) HEAP2 (or_introl eq_refl)) as OSHA. cbn [blk_addr blk_size fst snd] in OSHA.
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn in Ha; alia].
    apply zero104_sct_cellsA in BLK. unfold CtSctP.W_sct_new.sct_zero_cells, MallocRep.wz in BLK.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 104)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
    assert (OFF2 : offshW [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 104)]%Z) by (cbn [offshW]; alia).
    rename MU1 into MU0. clear WM1 HEAP1 CS1 SHB1 SHB2.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EA in KA; lia|]. clear KA.
    step. step. step. step.
    do 3 step. release_frame FR ST2 (bv_unsigned sp). step. step.
    name_mem m9.
    apply evt_done. apply (K p Σ' _ Hp).
    unfold calloc_postA, MallocRep.wz.
    do 16 eexists. exists m9, A. split; [reflexivity|].
    assert (MU9 : munch [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 104)]%Z m2 m9) by assumption.
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
          * eapply (blk_not_static _ ((p, A, 104) :: OW) LB m2 (p, A, 104) a HEAP2 (or_introl eq_refl)); [cbn; lia | exact Ha].
          * assert (NE : blk_id b <> p) by (intros E; apply Hp; rewrite <- E; apply in_map; exact Hb).
            pose proof (AH_disjoint_gen _ _ _ _ b (p, A, 104) HEAP2 (or_intror Hb) (or_introl eq_refl) NE) as DJ. cbn in DJ. lia. }
    split; [exact CR2|]. split; [exact BR2|].
    assert (HEAP9 : AHEAP Σ' ((p, A, 104) :: OW) LB m9).
    { eapply AH_frame; [exact HEAP2| exact MU9| apply wmono_refl || assumption|].
      constructor; [left; cbn; alia|]. constructor; [right; right; exists (p, A, 104); split; [left; reflexivity| cbn; lia]| constructor]. }
    split; [exact HEAP9|].
    split; [exact (proj2 (AH_acc _ _ _ _ (p, A, 104) HEAP9 (or_introl eq_refl)))|].
    unfold CtSctP.W_sct_new.sct_new_cells, MallocRep.wz.
    exact BLK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CRYPTO_memdup_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (bsrc : block) (P n : Z) (src : list (bv 8)) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_MEMDUP_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  In bsrc (OW ++ LB) -> blk_addr bsrc <= P -> P + n <= blk_addr bsrc + blk_size bsrc -> bytes_at ctasegs m P src -> length src = Z.to_nat n ->
  a0 = wz P -> a1 = wz n -> 0 < n < 2^31 - 1 ->
  mcost n <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_MEMDUP_A (bv_unsigned ra :: ras) ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB n lo m
                  (fun C m' => rw_cells ctasegs m' C [CB (Z.to_nat n) src] /\ bytes_at ctasegs m' P src) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc n k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_MEMDUP_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> CS INS S1 S2 SRC SLEN -> -> Hn CRED UW CTX K.
  unfold CRYPTO_MEMDUP_STACK_A, CRYPTO_MALLOC_STACK, RT_STACK, CRYPTO_MEMDUP_A, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  pose proof (AH_range_gen _ _ _ _ bsrc HEAP INS) as (BS0 & _ & _ & BSC & BSI).
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite SLEN, Z2Nat.id in SB by lia.
  assert (EP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 48%nat ST. do 7 step. step.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?EP in K0; lia|]. clear K0.
  step. step. step. step.
  step. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by lia; lia|]. clear K1.
  step. step. step. step.
  name_mem m1.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU1) | | exact CS].
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  apply evt_done.
  eapply CRYPTO_malloc_walkAp with (n := n) (lo := lo) (OW := OW) (LB := LB) (ras := bv_unsigned ra :: ras); try reflexivity.
  - exact HEAP1.
  - rewrite ESP. exact ST.
  - exact CEIL.
  - rewrite ESP. unfold CRYPTO_MALLOC_STACK, RT_STACK. lia.
  - rewrite ESP. unfold USTACK_TOP. lia.
  - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
  - exact MI.
  - exact CS1.
  - lia.
  - exact CRED.
  - rewrite ESP. uw_call_mu_tac m 48 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia].
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_dup_malloc CTX).
  - intros p Σ3 ms3 Hp PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & m3 & A & -> & MI3 & ST3 & AG3 & CR3 & BR3 & HEAP3 & ACC3 & (junkP & BLK)).
    unfold MallocRep.wz in *. rewrite ESP in ST3, AG3. rewrite (ret_pc_even 0x204020) by (clear; lia).
    pose proof BR3 as (A0 & A16 & _ & ACE & AIMG).
    assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; alia).
    apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros xa Hxa; cbn in Hxa; left; unfold USTACK_TOP; lia].
    apply (bytes_at_agree _ _ _ _ _ AG3) in SRC; [| intros xa Hxa; right; right; exists bsrc; split; [exact INS| lia]].
    assert (INS3 : In bsrc (((p, A, n) :: OW) ++ LB)) by (right; exact INS).
    pose proof (AH_disjoint_gen _ _ _ _ (p, A, n) bsrc HEAP3 (or_introl eq_refl) INS3
                  ltac:(cbn; intros E; apply Hp; rewrite E; apply in_map; exact INS)) as DJS. cbn [blk_addr blk_size blk_id fst snd] in DJS.
    assert (L1 : Z.of_nat (length src) = n) by (rewrite SLEN; lia).
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?EA in K0; lia|]. clear K0.
    do 3 step. step.
    apply evt_done. eapply implAp_step_same.
    { eapply (asan_memcpy_cpsA) with (d := A) (s := P) (bs := src) (bd := (p, A, n)) (bsrc := bsrc) (lo := lo) (OW := (p, A, n) :: OW) (LB := LB);
        try reflexivity; rewrite ?L1.
      - exact HEAP3.
      - rewrite ESP. exact ST3.
      - exact CEIL.
      - rewrite ESP. unfold RT_STACK. lia.
      - rewrite ESP. unfold USTACK_TOP. lia.
      - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
      - exact MI3.
      - left. reflexivity.
      - cbn [blk_addr blk_size fst snd]. lia.
      - exact INS3.
      - exact S1.
      - lia.
      - exact SRC.
      - lia.
      - lia.
      - unfold MallocRep.wz. reflexivity. }
    intros msM PO. unfold icall_post in PO. rewrite ?ESP, ?L1 in PO.
    destruct PO as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & m4 & -> & MI4 & ST4 & HEAP4 & WM4 & AG4 & BZ & WR4).
    rewrite (ret_pc_even 0x204034) by (clear; lia). unfold MallocRep.wz.
    apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; lia| lia]].
    apply (bytes_at_agree _ _ _ _ _ AG4) in SRC; [| intros xa Hxa; split; [right; right; exists bsrc; split; [exact INS3| lia]| lia]].
    destruct (AH_shb _ _ _ _ HEAP4) as [SHB1'' SHB2''].
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m4) as MU4. pose proof (wmono_refl ctasegs m4) as WM4'.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. step. do 5 step. release_frame FR ST4 (bv_unsigned sp). step. step.
    name_mem m9.
    apply evt_done. apply (K p Σ3 _ Hp).
    unfold calloc_postA, MallocRep.wz.
    do 16 eexists. exists m9, A. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|].
    split.
    { (* [comment removed for export] *)
      assert (FRM : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> outside [(bv_unsigned sp - 48, bv_unsigned sp)] a).
      { intros a [Ha|[Ha|(b & Hb & Hr)]]; cbn [outside]; (split; [|exact I]); [lia| |].
        - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). lia. }
      assert (SUB : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ LB) (bv_unsigned sp + -48) a).
      { intros a [Ha|[Ha|Ha]]; [left; lia| right; left; exact Ha| right; right; exact Ha]. }
      assert (NFB : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> ~ (A <= a < A + n)).
      { intros a [Ha|[Ha|(b & Hb & Hr)]] HA'.
        - unfold BnHeapA.ACEIL in *. lia.
        - eapply (blk_not_static _ ((p, A, n) :: OW) LB m3 (p, A, n) a HEAP3 (or_introl eq_refl)); [cbn; lia | exact Ha].
        - assert (NE : blk_id b <> p) by (intros E; apply Hp; rewrite <- E; apply in_map; exact Hb).
          pose proof (AH_disjoint_gen _ _ _ _ b (p, A, n) HEAP3 (or_intror Hb) (or_introl eq_refl) NE) as DJ. cbn in DJ. lia. }
      eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact FRM]|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact AG3| exact SUB]|].
      eapply agree_on_mono; [exact AG4|]. intros a Ha. split; [| exact (NFB a Ha)].
      destruct (SUB a Ha) as [Hb|[Hb|(b & Hb & Hr)]]; [left; exact Hb| right; left; exact Hb| right; right; exists b; split; [right; exact Hb| exact Hr]]. }
    split; [exact CR3|]. split; [exact BR3|].
    split; [exact HEAP4|].
    split; [exact (proj2 (AH_acc _ _ _ _ (p, A, n) HEAP4 (or_introl eq_refl)))|].
    split; [| exact SRC].
    rewrite <- SLEN. apply rw_cells_of_bytesA; [exact BZ| rewrite L1; exact WR4].
Qed.

End WithRT.
