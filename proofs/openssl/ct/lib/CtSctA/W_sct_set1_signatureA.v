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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG CtSizes CtWire.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface W_akit W_obj_free ApErrKitA2 W_prefix_create.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctRep W_sct_set1_signature.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import W_sct_newA.
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

Definition SCT_SET1_SIGNATURE_A : Z := 0x3376e4.
Definition SCT_SET1_SIGNATURE_STACK_A : Z := 80 + CRYPTO_MEMDUP_STACK_A.

Notation sct_cells := CtSctP.SctRep.sct_cells.
Notation set_sig_cells := CtSctP.W_sct_set1_signature.set_sig_cells.

Local Notation E_s1_free := (E_SCT_set1_signature_34bbe4 : uk_call 0x3376e4 0x337754 0x1fd334).     (* [comment removed for export] *)
Local Notation E_s1_memdup := (E_SCT_set1_signature_34bc48 : uk_call 0x3376e4 0x3377a8 0x203fd8).   (* [comment removed for export] *)

Lemma zero16_two_cells : forall m A,
  rw_cells ctasegs m A [CB 16%nat (repeat (Z_to_bv 8 0) 16%nat)] -> rw_cells ctasegs m A [C8 (wz 0); C8 (wz 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; repeat split; auto| unfold MallocRep.wz; bytes_lit_eq| reflexivity]. Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition s1_mid_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (lo : Z) (m : mem)
    (adr : bptr -> Z) (x : sctr bptr) (et : Z) (P n : Z) (ras : list Z) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' (j8 : list (bv 8)),
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz TP_A) t0 t1 t2 sp (wz n) a0 a1 a2 a3 a4 a5 a6 a7
                  (wz (adr (sc_blk x) + 72)) (wz (adr (sc_blk x))) (wz P) s5
                  (wz SHB) (Z_to_bv 64 (Z.shiftr (adr (sc_blk x) + 72) 3 + SHB)) s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x337780) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp + -80)
    /\ apres_but LB OW (bv_unsigned sp) (adr (sc_blk x)) SCT_SIZE m m'
    /\ AHEAP Σ OW LB m' /\ crypto_statics m'
    /\ rw_cells ctasegs m' (bv_unsigned sp + -80) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells ctasegs m' (adr (sc_blk x)) (set_sig_cells adr x et 0 0)
    /\ uw_chain USTACK_TOP m' (bv_unsigned sp) (bv_unsigned s0) ras.
  (* [comment removed for export] *)

Lemma s1_frontA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (adr : bptr -> Z) (x : sctr bptr) (et vs : Z) (P n : Z) (ras : list Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - SCT_SET1_SIGNATURE_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  In (sc_blk x, adr (sc_blk x), SCT_SIZE) (OW ++ LB) -> rw_cells ctasegs m (adr (sc_blk x)) (sct_cells adr x et vs) -> sc_sig x = None ->
  adr (sc_blk x) mod 16 = 0 ->                                                     (* [comment removed for export] *)
  a0 = wz (adr (sc_blk x)) -> a1 = wz P -> a2 = wz n ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_SET1_SIGNATURE_A (bv_unsigned ra :: ras) ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz SCT_SET1_SIGNATURE_A) fc None m (seg_rom ctasegs))))
      (ASTA RT Σ PMc (s1_mid_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m adr x et P n ras)).
Proof.
  intros until ras. intros HEAP ST CEIL LO SPT SP16 MI TP CS HXIN HX HSIG AL16 -> -> -> UW CTX.
  pose proof LO as LO'. unfold SCT_SET1_SIGNATURE_STACK_A, CRYPTO_MEMDUP_STACK_A, CRYPTO_MALLOC_STACK, RT_STACK, SCT_SET1_SIGNATURE_A, SCT_SIZE, MallocRep.wz in LO' |- *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HXIN) as (BX0 & _ & _ & BX3 & BX4). cbn [blk_addr blk_size fst snd] in BX0, BX3, BX4. unfold SCT_SIZE in *.
  remember (adr (sc_blk x)) as A eqn:EAd.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (EA72 : bv_unsigned (Z_to_bv 64 (A + 72)) = A + 72) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (EA80 : bv_unsigned (Z_to_bv 64 (A + 80)) = A + 80) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  ablock HEAP HXIN ACCX OFFX.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  unfold CtSctP.SctRep.sct_cells, sc_siglen in HX. rewrite HSIG in HX. cbn [optr] in HX. unfold MallocRep.wz in HX.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 80, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  ual.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  carve_frame 80%nat ST. do 12 step.
  step. step. step.
  step. step. step. step.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU1) | | exact CS].
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  apply evt_done. eapply cps_step_same.
  { eapply CRYPTO_free_null_cpsA with (lo := lo) (OW := OW) (LB := LB) (ras := bv_unsigned ra :: ras); try reflexivity;
      [exact HEAP1| rewrite ESP; exact ST| exact CEIL| rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; lia| rewrite ESP; unfold USTACK_TOP; lia
      | rewrite ESP; uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia| exact MI| exact TP| exact CS1
      | rewrite ESP; uw_call_mu_tac m 80 UW MU1 FR; [intros a Ha; cbn [outside fst snd]; lia | lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP in *; lia]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_s1_free CTX)]. }
  intros ms3 PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & m3 & -> & MI3 & ST3 & HEAP3 & AG3).
  unfold MallocRep.wz in *. rewrite ESP in ST3, AG3. rewrite (ret_pc_even 0x337754) by (clear; lia).
  apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; cbn in Ha; left; unfold USTACK_TOP; lia].
  apply (rw_cells_agree _ _ _ _ _ AG3) in HX; [| intros a Ha; cbn in Ha; right; right; exists (sc_blk x, A, 104); split; [exact HXIN| cbn; lia]].
  assert (CS3 : crypto_statics m3).
  { eapply crypto_statics_agree; [exact AG3| | exact CS1].
    intros a Ha. right; left; apply client_static_intro. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. lia. }
  assert (UW3 : uw_chain USTACK_TOP m3 (bv_unsigned sp) (bv_unsigned s0) ras).
  { eapply uw_chain_agreeP; [exact AG3| | intros a H1 Ha; left; unfold USTACK_TOP in *; lia].
    eapply uw_chain_munchP; [exact MU1| exact UW| intros a H1 Ha; cbn [outside fst snd]; lia]. }
  ablock HEAP3 HXIN ACCX3 OFFX3.
  destruct (AH_shb _ _ _ _ HEAP3) as [SHB1' SHB2'].
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 104)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  assert (OFF3 : offshW [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 104)]%Z) by (cbn [offshW]; alia).
  clear HEAP1 CS1 ACCX SHB1 SHB2.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. step. step.
  step. step.
  name_mem m4.
  match goal with H : munch _ m3 m4 |- _ => rename H into MU4 end. match goal with H : wmono ctasegs m3 m4 |- _ => rename H into WM4 end.
  match goal with H : mem_inv ctasegs m4 |- _ => rename H into MI4 end. match goal with H : stk ctasegs m4 _ _ |- _ => rename H into ST4 end.
  assert (HEAP4 : AHEAP Σ OW LB m4).
  { eapply AH_frame; [exact HEAP3| exact MU4| exact WM4|].
    constructor; [left; cbn; alia|]. constructor; [right; right; exists (sc_blk x, A, 104); split; [exact HXIN| cbn; lia]| constructor]. }
  match goal with H : rw_cells ctasegs m4 A _ |- _ => rename H into HX4 end.
  assert (CS4 : crypto_statics m4).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU4)| | exact CS3].
    intros a Ha. cbn [outside]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  assert (UW4 : uw_chain USTACK_TOP m4 (bv_unsigned sp) (bv_unsigned s0) ras).
  { eapply uw_chain_munchP; [exact MU4| exact UW3| intros a H1 Ha; cbn [outside fst snd]; unfold BnHeapA.ACEIL in *; lia]. }
  lazymatch type of HX4 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13; ?c14; ?c15; ?c16; ?c17] =>
    change (rw_cells ctasegs m4 A ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ [c12; c13] ++ [c14; c15; c16; c17])) in HX4 end.
  destruct (proj1 (rw_cells_app m4 A _ _) HX4) as [HXlo HXr]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HXr.
  destruct (proj1 (rw_cells_app m4 _ _ _) HXr) as [_ HXhi]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HXhi.
  replace (A + 72 + 16) with (A + 88) in HXhi by lia.
  clear HXr HX4.
  apply evt_done. eapply cps_step_same.
  { eapply (asan_memset_cpsA) with (d := A + 72) (n := 16) (c := Z_to_bv 8 0) (bd := (sc_blk x, A, 104)) (lo := lo) (OW := OW) (LB := LB); try reflexivity.
    - exact HEAP4.
    - rewrite ESP. exact ST4.
    - exact CEIL.
    - rewrite ESP. unfold RT_STACK. lia.
    - rewrite ESP. unfold USTACK_TOP. lia.
    - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
    - exact MI4.
    - exact HXIN.
    - cbn [blk_addr blk_size fst snd]. lia.
    - cbn [blk_addr blk_size fst snd]. lia.
    - lia. }
  intros msM PO. unfold icall_post in PO. rewrite ?ESP in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & FM & fcM & mM & -> & MIM & STM & HEAPM & WMM & AGM & BZ & WRM).
  rewrite (ret_pc_even 0x337780) by (clear; lia).
  apply (rw_cells_agree _ _ _ _ _ AGM) in FR; [| intros a Ha; cbn in Ha; split; [left; unfold USTACK_TOP; lia| unfold BnHeapA.ACEIL in *; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGM) in HXlo; [| intros a Ha; cbn in Ha; split; [right; right; exists (sc_blk x, A, 104); split; [exact HXIN| cbn; lia]| lia]].
  apply (rw_cells_agree _ _ _ _ _ AGM) in HXhi; [| intros a Ha; cbn in Ha; split; [right; right; exists (sc_blk x, A, 104); split; [exact HXIN| cbn; lia]| lia]].
  assert (HXmid : rw_cells ctasegs mM (A + 72) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply zero16_two_cells. split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BZ]| cbn; exact WRM]. }
  assert (HXM : rw_cells ctasegs mM A (set_sig_cells adr x et 0 0)).
  { unfold CtSctP.W_sct_set1_signature.set_sig_cells, MallocRep.wz. apply (proj2 (rw_cells_app mM A [_; _; _; _; _; _; _; _; _; _; _; _] _)). split; [exact HXlo|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
    apply (proj2 (rw_cells_app mM (A + 72) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] _)). split; [exact HXmid|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. replace (A + 72 + 16) with (A + 88) by lia. exact HXhi. }
  clear HXlo HXhi HXmid.
  assert (CSM : crypto_statics mM).
  { eapply crypto_statics_agree; [exact AGM| | exact CS4].
    intros a Ha. split.
    - right; left; apply client_static_intro. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. lia.
    - revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  assert (UWM : uw_chain USTACK_TOP mM (bv_unsigned sp) (bv_unsigned s0) ras).
  { eapply uw_chain_agreeP; [exact AGM| exact UW4| intros a H1 Ha; split; [left; unfold USTACK_TOP in *; lia| unfold BnHeapA.ACEIL in *; lia]]. }
  apply cps_post. intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-.
  unfold s1_mid_postA, MallocRep.wz, SCT_SIZE. subst A. rewrite ?EA72.
  do 18 eexists. exists mM. eexists.
  split; [reflexivity|].
  split; [exact MIM|]. split; [exact STM|].
  split.
  { unfold apres_but.
    assert (FRM : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (adr (sc_blk x) <= a < adr (sc_blk x) + 104) ->
                  outside [(bv_unsigned sp - 80, bv_unsigned sp); (adr (sc_blk x), adr (sc_blk x) + 104)]%Z a /\ outside [(bv_unsigned sp - 80, bv_unsigned sp)]%Z a).
    { intros a [Ha Hnb]. cbn [outside].
      assert (O1 : ~ (bv_unsigned sp - 80 <= a < bv_unsigned sp)).
      { destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
        - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). clear - Hr BC CEIL LO'. alia. }
      repeat split; try exact I; lia. }
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| intros a Ha; exact (proj2 (FRM a Ha))]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG3| intros a [[Ha|[Ha|Ha]] _]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Ha]]|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU4)| intros a Ha; exact (proj1 (FRM a Ha))]|].
    eapply agree_on_mono; [exact AGM|]. intros a [Ha Hnb]. split; [| lia].
    apply (aclient_addr_sub (OW ++ LB) (OW ++ LB) (bv_unsigned sp + -80) (bv_unsigned sp) a (fun b Hb => Hb)); [lia| exact Ha]. }
  split; [exact HEAPM|].
  split; [exact CSM|].
  split; [exact FR|].
  split; [exact HXM|].
  exact UWM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma SCT_set1_signature_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (adr : bptr -> Z) (x : sctr bptr) (et vs : Z) (bsrc : block) (P n : Z) (src : list (bv 8)) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - SCT_SET1_SIGNATURE_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  In (sc_blk x, adr (sc_blk x), SCT_SIZE) (OW ++ LB) -> rw_cells ctasegs m (adr (sc_blk x)) (sct_cells adr x et vs) -> sc_sig x = None ->
  adr (sc_blk x) mod 16 = 0 ->                                                     (* [comment removed for export] *)
  In bsrc (OW ++ LB) -> blk_id bsrc <> sc_blk x -> blk_addr bsrc <= P -> P + n <= blk_addr bsrc + blk_size bsrc ->
  bytes_at ctasegs m P src -> length src = Z.to_nat n ->
  a0 = wz (adr (sc_blk x)) -> a1 = wz P -> a2 = wz n -> 0 < n < 2^31 - 1 ->
  mcost n <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_SET1_SIGNATURE_A (bv_unsigned ra :: ras) ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     oalloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB (adr (sc_blk x)) SCT_SIZE n lo m 1
                  (fun C m' => rw_cells ctasegs m' C [CB (Z.to_nat n) src] /\ bytes_at ctasegs m' P src
                               /\ rw_cells ctasegs m' (adr (sc_blk x)) (set_sig_cells adr x et C n)) p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc n k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SCT_SET1_SIGNATURE_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI TP CS HXIN HX HSIG AL16 INS NPX S1 S2 SRC SLEN HA0 HA1 HA2 Hn CRED UW CTX K.
  eapply implAp_step_same.
  { eapply (s1_frontA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB lo adr x et vs P n ras);
      eassumption. }
  intros ms' PO.
  destruct PO as (x1' & u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & Fm & fcm & mm & j8m
                  & -> & MIm & STm & AGm & HEAPm & CSm & FRm & HXm & UWm).
  pose proof LO as LO'. unfold SCT_SET1_SIGNATURE_STACK_A, CRYPTO_MEMDUP_STACK_A, CRYPTO_MALLOC_STACK, RT_STACK, SCT_SET1_SIGNATURE_A, SCT_SIZE, MallocRep.wz in LO' |- *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HXIN) as (BX0 & _ & _ & BX3 & BX4). cbn [blk_addr blk_size fst snd] in BX0, BX3, BX4. unfold SCT_SIZE in *.
  pose proof (AH_range_gen _ _ _ _ bsrc HEAP INS) as (BS0 & _ & _ & BSC & BSI).
  pose proof (AH_disjoint_gen _ _ _ _ bsrc (sc_blk x, adr (sc_blk x), 104) HEAP INS HXIN NPX) as DJS. cbn [blk_addr blk_size blk_id fst snd] in DJS.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite SLEN, Z2Nat.id in SB by lia.
  remember (adr (sc_blk x)) as A eqn:EAd.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (EP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  subst a0 a1 a2.
  apply (bytes_at_agree _ _ _ _ _ AGm) in SRC; [| intros xa Hxa; split; [right; right; exists bsrc; split; [exact INS| lia]| lia]].
  (* [comment removed for export] *)
  assert (UW1 : uw_chain USTACK_TOP mm (bv_unsigned sp + -80) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame mm _ (bv_unsigned sp) 80 [CB 8 j8m; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; uchk_open; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FRm.
    - exact UWm. }
  destruct (AH_shb _ _ _ _ HEAPm) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z mm) as MU. pose proof (wmono_refl ctasegs mm) as WM.
  ual.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  step.
  step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EP in KA; lia|]. clear KA.
  step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]. clear KB.
  step. step. step. step. step. step.
  apply evt_done.
  eapply CRYPTO_memdup_walkA with (bsrc := bsrc) (P := P) (n := n) (src := src) (lo := lo) (OW := OW) (LB := LB) (ras := bv_unsigned ra :: ras); try reflexivity.
  - exact HEAPm.
  - rewrite ESP. exact STm.
  - exact CEIL.
  - rewrite ESP. unfold CRYPTO_MEMDUP_STACK_A, CRYPTO_MALLOC_STACK, RT_STACK. lia.
  - rewrite ESP. unfold USTACK_TOP. lia.
  - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
  - exact MIm.
  - exact CSm.
  - exact INS.
  - exact S1.
  - exact S2.
  - exact SRC.
  - exact SLEN.
  - exact Hn.
  - exact CRED.
  - rewrite ESP. exact UW1.
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_s1_memdup CTX).
  - intros p Σ6 ms6 Hp PO.
    destruct PO as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F6 & fc6 & m6 & C & -> & MI6 & ST6 & AG6 & CR6 & BR6 & HEAP6 & ACC6 & (BLK & SRC6)).
    unfold MallocRep.wz in *. rewrite ESP in ST6, AG6. rewrite (ret_pc_even 0x3377a8) by (clear; lia).
    pose proof BR6 as (Cq0 & Cq16 & _ & CqE & CqI).
    assert (EC : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; alia).
    apply (rw_cells_agree _ _ _ _ _ AG6) in FRm; [| intros xa Hxa; cbn in Hxa; left; unfold USTACK_TOP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG6) in HXm; [| intros xa Hxa; right; right; exists (sc_blk x, A, 104); split; [exact HXIN| cbn; cbn in Hxa; lia]].
    assert (HXIN6 : In (sc_blk x, A, 104) (((p, C, n) :: OW) ++ LB)) by (right; exact HXIN).
    pose proof (AH_disjoint_gen _ _ _ _ (p, C, n) (sc_blk x, A, 104) HEAP6 (or_introl eq_refl) HXIN6
                  ltac:(cbn; intros E; apply Hp; rewrite E; apply (in_map blk_id _ (sc_blk x, A, 104)); exact HXIN)) as DJC. cbn [blk_addr blk_size blk_id fst snd] in DJC.
    assert (INS6 : In bsrc (((p, C, n) :: OW) ++ LB)) by (right; exact INS).
    pose proof (AH_disjoint_gen _ _ _ _ (p, C, n) bsrc HEAP6 (or_introl eq_refl) INS6
                  ltac:(cbn; intros E; apply Hp; rewrite E; apply in_map; exact INS)) as DJP. cbn [blk_addr blk_size blk_id fst snd] in DJP.
    ablock HEAP6 HXIN6 ACCX6 OFFX6.
    destruct (AH_shb _ _ _ _ HEAP6) as [SHB1' SHB2'].
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 104)]%Z m6) as MU6. pose proof (wmono_refl ctasegs m6) as WM6.
    assert (OFF6 : offshW [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 104)]%Z) by (cbn [offshW]; alia).
    clear SHB1 SHB2 MU WM.
    unfold CtSctP.W_sct_set1_signature.set_sig_cells, MallocRep.wz in HXm.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step.
    step. if_cases KC; zify_cond KC; [exfalso; rewrite ?EC in KC; lia|]. clear KC.
    step. step. step.
    do 9 step. release_frame FRm ST6 (bv_unsigned sp). step. step.
    name_mem m9.
    apply evt_done. apply (K p Σ6 _ Hp).
    unfold oalloc_postA, MallocRep.wz.
    do 16 eexists. exists m9, C. split; [subst A; reflexivity|].
    assert (MU9 : munch [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 104)]%Z m6 m9) by assumption.
    split; [assumption|]. split; [assumption|].
    split.
    { unfold apres_but in *. subst A.
      eapply agree_on_trans; [eapply agree_on_mono; [exact AGm| intros a Ha; exact Ha]|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact AG6| intros a [[Ha|[Ha|Ha]] _]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Ha]]|].
      eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU9)|]. intros a [Ha Hnb]. cbn [outside]. split; [| split; [clear - Hnb; lia| exact I]].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). clear - Hr BC CEIL LO'. alia. }
    split; [exact CR6|]. split; [exact BR6|].
    assert (HEAP9 : AHEAP Σ6 ((p, C, n) :: OW) LB m9).
    { eapply AH_frame; [exact HEAP6| exact MU9| apply wmono_refl || assumption|].
      constructor; [left; cbn; alia|]. constructor; [right; right; exists (sc_blk x, A, 104); split; [exact HXIN6| cbn; lia]| constructor]. }
    split; [exact HEAP9|].
    split; [exact (proj2 (AH_acc _ _ _ _ (p, C, n) HEAP9 (or_introl eq_refl)))|].
    split; [exact BLK| split; [exact SRC6|]].
    unfold CtSctP.W_sct_set1_signature.set_sig_cells, MallocRep.wz. subst A. match goal with H : rw_cells ctasegs m9 (adr (sc_blk x)) _ |- _ => exact H end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition set1sig_zero_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (lo : Z) (m : mem) (adr : bptr -> Z) (x : sctr bptr) (et : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres_but LB OW (bv_unsigned sp) (adr (sc_blk x)) SCT_SIZE m m'
    /\ AHEAP Σ OW LB m' /\ crypto_statics m'
    /\ rw_cells ctasegs m' (adr (sc_blk x)) (set_sig_cells adr x et 0 0).

Lemma SCT_set1_signature_zero_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (adr : bptr -> Z) (x : sctr bptr) (et vs : Z) (P : Z) (ras : list Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - SCT_SET1_SIGNATURE_STACK_A ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
  In (sc_blk x, adr (sc_blk x), SCT_SIZE) (OW ++ LB) -> rw_cells ctasegs m (adr (sc_blk x)) (sct_cells adr x et vs) -> sc_sig x = None ->
  adr (sc_blk x) mod 16 = 0 ->                                                     (* [comment removed for export] *)
  a0 = wz (adr (sc_blk x)) -> a1 = wz P -> a2 = wz 0 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_SET1_SIGNATURE_A (bv_unsigned ra :: ras) ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz SCT_SET1_SIGNATURE_A) fc None m (seg_rom ctasegs))))
      (ASTA RT Σ PMc (set1sig_zero_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m adr x et)).
Proof.
  intros until ras. intros HEAP ST CEIL LO SPT SP16 MI TP CS HXIN HX HSIG AL16 HA0 HA1 HA2 UW CTX.
  eapply cps_step_same.
  { eapply (s1_frontA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB lo adr x et vs P 0 ras);
      eassumption. }
  intros ms' PO.
  destruct PO as (x1' & u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & Fm & fcm & mm & j8m
                  & -> & MIm & STm & AGm & HEAPm & CSm & FRm & HXm & UWm).
  pose proof LO as LO'. unfold SCT_SET1_SIGNATURE_STACK_A, CRYPTO_MEMDUP_STACK_A, CRYPTO_MALLOC_STACK, RT_STACK, SCT_SET1_SIGNATURE_A, SCT_SIZE, MallocRep.wz in LO' |- *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HXIN) as (BX0 & _ & _ & BX3 & BX4). cbn [blk_addr blk_size fst snd] in BX0, BX3, BX4. unfold SCT_SIZE in *.
  remember (adr (sc_blk x)) as A eqn:EAd.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  subst a0 a1 a2.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z mm) as MU. pose proof (wmono_refl ctasegs mm) as WM.
  ual.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. name_mem m3.
  assert (JOIN : forall (t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word) (F_ : bvmap 5 word) (fc_ : bv 32),
    evt ctasegs (fun ms'0 => cps ctasegs (ASTA RT Σ PMc (eq ms'0)) (ASTA RT Σ PMc (set1sig_zero_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m adr x et)))
      (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 TP_A) t0_ t1_ t2_ sp (Z_to_bv 64 0) a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_
               (Z_to_bv 64 (A + 72)) (Z_to_bv 64 A) (Z_to_bv 64 P) (Z_to_bv 64 1)
               (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (A + 72) 3 + SHB)) s8 s9 s10 s11 t3_ t4_ t5_ t6_)
          F_ (Z_to_bv 64 0x3377d8) fc_ None m3 (seg_rom ctasegs))).
  { intros. step. do 9 step. release_frame FRm STm (bv_unsigned sp). step. step.
    name_mem m5. apply evt_done. apply cps_post. intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-.
    unfold set1sig_zero_postA, MallocRep.wz, SCT_SIZE. subst A.
    do 16 eexists. exists m5. split; [reflexivity|].
    split; [exact MIm|]. split; [exact STm|]. split; [exact AGm|]. split; [exact HEAPm|]. split; [exact CSm|].
    unfold CtSctP.W_sct_set1_signature.set_sig_cells, MallocRep.wz in *. exact HXm. }
  step. if_cases KA; [apply JOIN|].
  step. if_cases KB; zify_cond KB; [| exfalso; rewrite ?unsigned_lit in KB by lia; lia]. apply JOIN.
Qed.

End WithRT.
