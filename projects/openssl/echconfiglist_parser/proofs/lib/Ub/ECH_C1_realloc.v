(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt ECH_C1_malloc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition CR_RA : Z := 0xe38b0.           (* [comment removed for export] *)

  Local Ltac prep_statics IM GM :=
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz in IM, GM.

  (* [comment removed for export] *)
  Definition cr1_post (sp gp tp t0 t1 t2 a2 a3 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
      (F : bvmap 5 word) (fc : bv 32) (A num lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1 j,
      ms' = MS (mkR (Z_to_bv 64 CR_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp a3
                   (Z_to_bv 64 A) (Z_to_bv 64 num) (Z_to_bv 64 P_CRYPTO_realloc) a3 (Z_to_bv 64 P_CRYPTO_realloc) a5 a6 a7
                   a2 (Z_to_bv 64 num) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 RREALLOC_SYM) fc None m1 (seg_rom usegs)
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
      /\ stk usegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells usegs m1 (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra)
      /\ IMPL_mem m1 /\ GOT_mem m1.

  Lemma cr_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A num lo : Z),
      0 < A < 2^64 -> 1 <= num < 2^32 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
      IMPL_mem m -> GOT_mem m ->
      evt usegs (cr1_post sp gp tp t0 t1 t2 a2 a3 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 F fc A num lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 num) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_realloc) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros HA HN ST CEIL LO MI IM GM. hcb.
    unfold P_CRYPTO_realloc, RREALLOC_SYM in *. prep_statics IM GM.
    pose proof (word_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 48%nat ST.
    do 15 step. step. try if_true.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. step. step.
    finish. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma cr_seg2 :
    forall (sp gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (j : list byte),
      0 < A < 2^64 ->
      rw_cells usegs m (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra) -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (ret_pc ra) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 CR_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 CR_RA)) fc None m (seg_rom usegs)).
  Proof.
    intros until j. intros HA FR MI. unfold CR_RA.
    replace (ret_pc (Z_to_bv 64 0xe38b0)) with (Z_to_bv 64 0xe38b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. unfold cm_frame in FR.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 8 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition rarr_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (v lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 v) a3 a4 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_realloc) fc None m1 (seg_rom usegs)
      /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp).

  Lemma rarr_prefix :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (num size lo : Z),
      0 <= num < 2^32 -> 0 <= size < 2^32 -> 1 <= num * size < 2^32 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
      evt usegs (rarr_post ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (num * size) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 num) (Z_to_bv 64 size) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_realloc_array) fc None m (seg_rom usegs)).
  Proof.
    unfold P_CRYPTO_realloc_array, P_CRYPTO_realloc. intros until lo; intros HN HS HP ST CEIL LO MI. hcb.
    pose proof (word_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 32%nat ST.
    do 8 step. zstep. rewrite (Z.shiftr_div_pow2 _ 64), Z.div_small by lia.
    step. if_true. zstep. do 8 step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.
  Hypothesis HRE : realloc_sr_stmt H.

  Lemma crealloc_post_back : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc s LB p old n obs lo B m m1 mo c,
    xpres (hs_lb_remove H p LB) (bv_unsigned sp) [] m m1 ->
    crealloc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p old n obs lo B m1 mo c ->
    crealloc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p old n obs lo B m mo c.
  Proof.
    intros until c. intros XP PO. unfold crealloc_post in *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p' & s' & E & REST).
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, junk, p', s'. split; [exact E|].
    repeat match goal with |- _ /\ _ => split end; try tauto.
    eapply xpres_trans; [exact XP| tauto].
  Qed.

  Lemma crealloc_spec : crealloc_stmt H.
  Proof.
    unfold crealloc_stmt, crealloc_stmt_gen. intros until errv.
    intros A0 A1 SZ HN HP KREL HIN OBS LEN BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP IM GM.
    subst size. rewrite Z.mul_1_r in *.
    unfold CREALLOC_STACK, FR_CRYPTO_realloc, RREALLOC_STACK, RMALLOC_STACK in LO. hcb. subst a0 a1.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP HIN) as (R1 & R2 & R3 & R4 & R5). cbn [blk_addr blk_size fst snd] in R1, R2, R3, R4, R5.
    pose proof (bytes_at_bound _ _ _ _ OBS) as OB. unfold zlength in LEN.
    assert (SUB : forall b, In b (hs_lb_remove H p LB) -> In b LB) by (intros b Hb; eapply (proj2 (proj2 (HH_lb_remove H HH))); exact Hb).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply cr_seg1; try eassumption; unfold RMMAP_THRESHOLD in HN; lia|].
    intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1 & IM1 & GM1).
    (* [comment removed for export] *)
    pose proof HRE as RE. unfold realloc_sr_stmt, realloc_sr_stmt_at in RE.
    eapply (sr_seq H HH).
    { eapply RE with (lo := lo) (B := B) (LB := LB) (s := s) (p := p) (n := old) (n' := num) (pre := obs);
        rewrite ?unsigned_lit by lia; try reflexivity; try eassumption.
      all: try (unfold RREALLOC_STACK, RMALLOC_STACK; lia).
      all: lazymatch goal with
           | |- hs_RHEAP _ _ _ _ =>
               eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]
           | |- hs_alloc_ok _ _ _ _ => eapply (HH_alloc_ok H HH); [exact HP| lia| lia| lia| lia]
           | |- bytes_at _ _ _ _ => eapply bytes_at_transport; [exact OBS| exact MU1| cbn; lia]
           | |- hs_rauxv_ok _ _ _ =>
               eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL;
               constructor; [cbn; lia| constructor]
           | |- rw_cells _ _ _ _ => subst tp; rewrite errno_RATP in *; eapply (rw_cells_transport usegs _ _ _ _ _ ERR MU1 WM1); unfold RERRNO; cbn; lia
           end. }
    intros [ms2 mo2] PO. unfold realloc_sr_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A' & junk & p' & s' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HPRES & BR & HEAP2 & BLK).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, HPRES by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    apply (rheap_pres_rw_cells _ _ _ _ _ _ HPRES) in FR1; [| left; cbn; lia].
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply cr_seg2; [lia| exact FR1| exact MI2]|].
    intros ms3 ->.
    apply (sr_done H HH). unfold crealloc_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A', junk, p', s'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|].
    split. { unfold cm_frame in FR1. release_frame FR1 ST2 (bv_unsigned sp). exact ST2. }
    split; [exact ERR2|]. split; [exact AUX2|].
    split.
    { eapply xpres_trans.
      - eapply xpres_of_munch; [exact MU1| exact WM1| |]. { constructor; [left; cbn; lia| constructor]. }
        intros b Hb. apply HB. apply SUB. exact Hb.
      - eapply (xpres_weaken _ _ _ _ []); [apply xpres_of_heap_pres; exact HPRES| lia| auto| auto]. }
    split; [exact BR|]. split; [exact HEAP2|]. split; [exact BLK|].
    split.
    - eapply rheap_pres_rw_cells; [exact HPRES| exact IM1|]. right; left. unfold A_malloc_impl, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
    - eapply rheap_pres_rw_cells; [exact HPRES| exact GM1|]. right; left. unfold A_got_CRYPTO_malloc, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
  Qed.

  Lemma crealloc_array_spec : crealloc_array_stmt H.
  Proof.
    unfold crealloc_array_stmt, crealloc_stmt_gen. intros until errv.
    intros A0 A1 (A2 & HN & HS) HNS HP KREL HIN OBS LEN BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP IM GM.
    unfold CREALLOC_ARRAY_STACK, CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, RREALLOC_STACK, RMALLOC_STACK in LO.
    hcb. subst a1 a2. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (SUB : forall b, In b (hs_lb_remove H p LB) -> In b LB) by (intros b Hb; eapply (proj2 (proj2 (HH_lb_remove H HH))); exact Hb).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP HIN) as (R1 & R2 & R3 & R4 & R5). cbn [blk_addr blk_size fst snd] in R1, R2, R3, R4, R5.
    pose proof (bytes_at_bound _ _ _ _ OBS) as OB.
    eapply (sr_evt_krel H HH); [exact KREL| eapply rarr_prefix; [exact HN| exact HS| unfold RMMAP_THRESHOLD in HNS; lia| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1).
    assert (XP1 : xpres (hs_lb_remove H p LB) (bv_unsigned sp) [] m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| |]. { constructor; [left; cbn; lia| constructor]. } intros b Hb. apply HB. apply SUB. exact Hb. }
    pose proof crealloc_spec as CR. unfold crealloc_stmt, crealloc_stmt_gen in CR.
    eapply (sr_mono H HH); [| intros c PO; eapply crealloc_post_back; [exact XP1|]; rewrite <- (Z.mul_1_r (num * size)); exact PO].
    eapply CR with (A := A); try reflexivity; rewrite ?Z.mul_1_r; try eassumption.
    - eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor].
    - eapply bytes_at_transport; [exact OBS| exact MU1| cbn; unfold zlength in LEN; lia].
    - eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor].
    - unfold CREALLOC_STACK, FR_CRYPTO_realloc, RREALLOC_STACK, RMALLOC_STACK. lia.
    - subst tp. rewrite errno_RATP in *. eapply (rw_cells_transport usegs _ _ _ _ _ ERR MU1 WM1). unfold RERRNO. cbn. lia.
    - eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM].
    - eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM].
  Qed.
End W.
