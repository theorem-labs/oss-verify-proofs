(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition CF_T1 : Z := 0x26ed2c.          (* [comment removed for export] *)
  Definition CF_A4 : Z := 0x2dad00.          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition cf1_post (ra sp gp tp t0 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 CF_T1) t2 s0 s1 a0 a1 a2 (Z_to_bv 64 P_CRYPTO_free) (Z_to_bv 64 CF_A4) a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 RFREE_SYM) fc None m1 (seg_rom rsegs)
      /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
      /\ stk rsegs m1 lo (bv_unsigned sp) /\ IMPL_mem m1 /\ GOT_mem m1.

  Lemma cf_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m -> IMPL_mem m -> GOT_mem m ->
      evt rsegs (cf1_post ra sp gp tp t0 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI IM GM. hcb. unfold P_CRYPTO_free.
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz in IM, GM.
    pose proof (word_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    do 9 step. if_true. do 5 step.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Lemma cfree_spec : cfree_stmt H.
  Proof.
    unfold cfree_stmt. intros until errv.
    intros A0 HP KREL HIN AUX SPB ST CEIL LO ERR MI TP IM GM.
    unfold CFREE_STACK, RFREE_STACK in LO. hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    eapply (sr_evt_krel H HH); [exact KREL| eapply cf_seg1; [exact ST| exact CEIL| lia| exact MI| exact IM| exact GM]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & IM1 & GM1).
    pose proof (HH_free H HH) as FR. unfold free_sr_stmt, free_sr_stmt_at in FR.
    eapply (sr_mono H HH).
    { eapply FR with (lo := lo) (B := B) (LB := LB) (s := s) (p := p) (n := n); try reflexivity; try eassumption.
      all: try (unfold RFREE_STACK; lia).
      - eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor].
      - eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor].
      - subst tp. rewrite errno_RATP in *. eapply (rw_cells_transport rsegs _ _ _ _ _ ERR MU1 WM1). unfold RERRNO. cbn. lia. }
    intros [ms2 mo2] PO. unfold free_sr_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HPRES & HEAP2).
    unfold cfree_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact ERR2|]. split; [exact AUX2|].
    assert (SUB : forall b, In b (hs_lb_remove H p LB) -> In b LB) by (intros b Hb; eapply (proj2 (proj2 (HH_lb_remove H HH))); exact Hb).
    split.
    { eapply xpres_trans.
      - eapply xpres_of_munch; [exact MU1| exact WM1| |]. { constructor; [left; cbn; lia| constructor]. }
        intros b Hb. apply HB. apply SUB. exact Hb.
      - apply xpres_of_heap_pres. exact HPRES. }
    split; [exact HEAP2|].
    split.
    - eapply rheap_pres_rw_cells; [exact HPRES| exact IM1|]. right; left. unfold A_malloc_impl, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
    - eapply rheap_pres_rw_cells; [exact HPRES| exact GM1|]. right; left. unfold A_got_CRYPTO_malloc, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
  Qed.

  Lemma cfree_null_spec : cfree_null_stmt H.
  Proof.
    unfold cfree_null_stmt. intros until lo. intros HALT LAZY ST CEIL LO MI IM GM.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    eapply (sr_evt_k H HH); [exact HALT| exact LAZY| eapply cf_seg1; [exact ST| exact CEIL| lia| exact MI| exact IM| exact GM]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & IM1 & GM1).
    pose proof (HH_free_null H HH) as FR. unfold free_null_sr_stmt, free_null_sr_stmt_at in FR.
    eapply (sr_mono H HH); [eapply FR; [exact HALT| exact LAZY]|].
    intros [ms2 mo2] [E EM]. cbn [cfg_ms cfg_model] in E, EM. subst ms2 mo2.
    unfold cfree_null_post. cbn [cfg_ms cfg_model].
    do 16 eexists. split; [reflexivity|]. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU1]. intros x Hx. cbn in Hx |- *. lia. }
    split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact IM1| exact GM1].
  Qed.
  (* [comment removed for export] *)
  Lemma cfree_null_evt_spec : cfree_null_evt_stmt.
  Proof.
    unfold cfree_null_evt_stmt. intros until lo. intros ST CEIL LO MI IM GM.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    eapply evt_cut; [eapply cf_seg1; [exact ST| exact CEIL| lia| exact MI| exact IM| exact GM]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & IM1 & GM1).
    eapply evt_cut; [eapply rfree_null_spec; reflexivity|].
    intros ms2 ->. apply evt_done.
    do 15 eexists. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU1]. intros x Hx. cbn in Hx |- *. lia. }
    split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact IM1| exact GM1].
  Qed.
End W.
