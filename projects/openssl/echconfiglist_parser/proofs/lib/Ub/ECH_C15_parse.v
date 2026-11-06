(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep ECH_C0_stmt ECH_C2_stmt ECH_C6_stmt ECH_LibState ECH_LibStateMF ECH_LibFrame ECH_LibMid ECH_C1_stmt ECH_C3_stmt ECH_C4_stmt ECH_C4_frame ECH_C4_frame2 ECH_C5_stmt ECH_C7_stmt ECH_C13_stmt ECH_C14_stmt ECH_C15_stmt ECH_C13_entry ECH_C13_store ECH_C13_small ECH_C7_newmembuf ECH_C7_biofree ECH_KitSeg ECH_C3_phase ECH_C3_newex.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition PO_R1 : Z := 0xe292c.
Definition PO_R2 : Z := 0xe2944.
Definition PO_R3 : Z := 0xe295c.
Definition PO_R4 : Z := 0xe2968.

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma p_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 PO_R1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 a1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                       a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OSSL_ECHSTORE_new) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells usegs m1 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_parse_one) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI.
    unfold P_parse_one, P_OSSL_ECHSTORE_new, PO_R1.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. carve_frame 32%nat ST.
    do 4 st1. do 4 step. step. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma p_seg2 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z),
      0 < A < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 PO_R2) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 s2 s1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_new_mem_buf) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PO_R1) fc None m (seg_rom usegs)).
  Proof.
    intros until A. intros AR MI. unfold PO_R1, PO_R2, P_BIO_new_mem_buf.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    do 5 step. apply evt_done. reflexivity.   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma p_seg3 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      0 < a < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 PO_R3) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) s0 (Z_to_bv 64 a) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PO_R2) fc None m (seg_rom usegs)).
  Proof.
    intros until a. intros AR MI. unfold PO_R2, PO_R3, P_OSSL_ECHSTORE_read_echconfiglist.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    do 3 step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma p_seg4 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 PO_R4) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OSSL_ECHSTORE_free) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PO_R3) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros MI. unfold PO_R3, PO_R4, P_OSSL_ECHSTORE_free.
    step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma p_seg5 :
    forall (rax sp gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s2 : word) (s1v : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      rw_cells usegs m (bv_unsigned sp + -32) (ef_frame s2 s1v s0 ra) ->
      stk usegs m lo (bv_unsigned sp + -32) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1v s1 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_free) fc None m (seg_rom usegs)
          /\ stk usegs m lo (bv_unsigned sp))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PO_R4) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros FR ST CEIL LO MI. unfold PO_R4, P_BIO_free. unfold ef_frame in FR.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. do 4 step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  (* [comment removed for export] *)
  Hypothesis CERTA : getdefctx_fresh_stmt H.
  (* [comment removed for export] *)
  Hypothesis RCFG : readcfg_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).

  Local Ltac errno_across ERR MU WM :=
    eapply (rw_cells_transport usegs _ _ _ _ _ ERR MU WM); unfold RERRNO; hcb; cbn; lia.

  Lemma parse_one_spec : parse_one_stmt H.
  Proof.
    unfold parse_one_stmt. intros until errv.
    intros A0 A1 NR DS DSL DP DH DIN DEMPTY LM SUBL HP KREL BUD BUDC BUDB AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE.
    unfold PARSE_BYTES, PARSE_CNT, PARSE_BIG, PARSE_STACK, FR_parse_one, DECODE_BYTES, DECODE_CNT, DECODE_BIG, ERRSTR_BYTES, ERRSTR_CNT in *.
    pose proof (readcfg_stack_lo M) as RSL. pose proof (ctxph_nonneg (mid_ctx M)) as (PHB & PHC & PHG & PHS). pose proof (errph_nonneg (mid_err M)) as (EHB & EHC & EHG).
    assert (NSK : 0 <= NEWMEMBUF_STACK (mid_ctx M)).
    { unfold NEWMEMBUF_STACK, BIONEW_STACK, FR_BIO_new_mem_buf, FR_BIO_new, FR_BIO_new_ex. lia. }
    set (RS := READCFG_STACK M) in *. set (NS := NEWMEMBUF_STACK (mid_ctx M)) in *.
    unfold mid_bytes, mid_cnt, mid_big in BUD, BUDC, BUDB.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    set (E0 := mid_errblocks M) in *. set (L0 := E0 ++ LB) in *.
    assert (SUB0 : forall b, In b LIB -> In b L0) by (intros b Hb; unfold L0; apply in_or_app; right; apply SUBL; exact Hb).
    assert (HB := HH_blocks_below H HH _ _ _ HP). subst tp. rewrite errno_RATP in ERR.
    pose proof LM as (IM0 & MF0 & CP0 & EPm0 & EX0 & VD0 & CL0 & FIT0 & GM0 & GE0 & GX0 & MM0 & MB0 & HT0 & RL0).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply p_seg1 with (lo := lo); [exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (XP1 : xpres L0 (bv_unsigned sp) [] m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (HP1 : hs_RHEAP H s L0 m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport usegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    pose proof (LIBMID_xpres0 _ _ _ _ _ _ LM XP1 SUB0) as LM1.
    pose proof LM1 as (IM1 & MF1 & _ & _ & _ & _ & _ & _ & GM1 & _).
    (* [comment removed for export] *)
    pose proof (storenew_spec H HH) as SN. unfold storenew_stmt in SN.
    eapply (sr_seq H HH).
    { eapply SN with (lo := lo) (B := B) (LB := L0) (s := s) (v := mid_flag M); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP1| exact KREL| exact AUX1| exact ST1| exact CEIL| exact MI1| exact MF1| exact IM1| exact GM1].
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => unfold STORE_SIZE; lia
           | |- rw_cells _ _ _ [C4 _] => rewrite errno_RATP; exact ERR1
           | |- _ <= _ - STORENEW_STACK => clear - LO RSL NSK; subst RS NS; unfold STORENEW_STACK, CZALLOC_STACK, CMALLOC_STACK, FR_OSSL_ECHSTORE_new, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia
           | |- _ mod 2 = 0 => unfold PO_R1; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try lia
           end. }
    clear SN. intros [ms2 mo2] PO. unfold storenew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p & s2' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BR & HP2 & SO2 & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia. rewrite errno_RATP in ERR2.
    replace (ret_pc (Z_to_bv 64 PO_R1)) with (Z_to_bv 64 PO_R1) by (symmetry; apply ret_pc_even; [unfold PO_R1; lia| reflexivity]).
    pose proof BR as (AP & _ & _ & AH & AOFF). unfold STORE_SIZE in AH, AOFF.
    set (sb := (p, A, STORE_SIZE)) in *. set (L1 := sb :: L0) in *.
    assert (SUB1 : forall b, In b LIB -> In b L1) by (intros b Hb; right; apply SUB0; exact Hb).
    assert (HB1 := HH_blocks_below H HH _ _ _ HP2).
    pose proof (LIBMID_mf _ _ _ _ _ _ LM1 XP2 SUB0 MF2) as LM2. cbn [mid_ctx mid_err mid_E mid_vdso] in LM2.
    pose proof LM2 as (_ & _ & CP2 & _ & _ & _ & _ & _ & _ & _ & _ & MM2 & _ & _ & RL2). cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in CP2.
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact FR1| left; cbn; lia|]. unfold memflag_foot, A_mem_inited. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    assert (DSX : forall L SP X m m', xpres L SP X m m' -> bytes_at usegs m D ds -> (forall b, In b LB -> In b L) ->
                  Forall (fun iv : Z * Z => IMG_LO <= fst iv /\ snd iv <= IMG_HI) X -> hceil <= SP -> bytes_at usegs m' D ds).
    { intros L SP X mm mm' XP BA SUB FX CE. destruct (Z.eq_dec N 0) as [N0|N0].
      - destruct ds; [| unfold zlength in DSL; cbn in DSL; lia]. destruct BA as (B1 & B2 & _). split; [exact B1|]. split; [exact B2|]. intros i Hi. cbn in Hi. lia.
      - destruct (DIN ltac:(lia)) as [pD [PIN _]]. unfold zlength in DSL.
        pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (in_or_app _ _ _ (or_intror PIN))) as PR. cbn [blk_addr blk_size fst snd] in PR.
        eapply xpres_bytes_at; [exact XP| exact BA|]. split.
        + right; right. exists (pD, D, N). split; [apply SUB; exact PIN| cbn; lia].
        + eapply Forall_impl; [| exact FX]. intros [lo' hi'] K. cbn in K |- *. destruct PR as (_ & _ & _ & _ & PO). unfold IMG_LO, IMG_HI in K. lia. }
    assert (DS1 : bytes_at usegs m1 D ds) by (eapply DSX; [exact XP1| exact DS| intros b Hb; apply in_or_app; right; exact Hb| apply Forall_nil| lia]).
    assert (DS2 : bytes_at usegs m2 D ds).
    { eapply DSX; [exact XP2| exact DS1| intros b Hb; apply in_or_app; right; exact Hb| | lia]. unfold memflag_foot, A_mem_inited, IMG_LO, IMG_HI. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply p_seg2; [lia| exact MI2]|].
    intros ms3 ->.
    (* [comment removed for export] *)
    pose proof (newmembuf_spec H HX (ECH_C3_phase.cnewex_spec H HX CERTA)) as NMB.   (* [comment removed for export] *) unfold newmembuf_stmt in NMB.
    eapply (sr_seq H HH).
    { eapply NMB with (lo := lo) (B := B) (LB := L1) (s := s2') (ph := mid_ctx M) (buf := D) (len := N) (v := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact A0| exact A1| exact HP2| exact KREL2| exact AUX2| exact ST2| exact CEIL| exact MI2| exact MF2| exact IM2| exact GM2| exact MM2| exact RL2].
      all: lazymatch goal with
           | |- lb_bytes _ + _ + _ <= _ => unfold L1; rewrite lb_bytes_cons; cbn [blk_size snd sb]; unfold STORE_SIZE, MEMBIO_BYTES, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; lia
           | |- Z.of_nat (length _) + _ + _ <= _ => unfold L1; cbn [length]; lia
           | |- lb_big _ + _ <= _ => unfold L1; rewrite lb_big_cons; cbn [blk_size snd sb]; rewrite big1_small by (unfold STORE_SIZE, BIGB; lia); lia
           | |- rw_cells _ _ _ [C4 _] => rewrite errno_RATP; exact ERR2
           | |- _ mod 16 = 0 => clear - SPA SPR LO RSL NSK; lia
           | |- _ <= _ - NEWMEMBUF_STACK _ => clear - LO RSL NSK; subst RS NS; lia
           | |- CTXPH _ _ _ => eapply ECH_LibMid.CTXPH_mono; [exact CP2| exact SUB1]
           | |- _ mod 2 = 0 => unfold PO_R2; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try lia
           end. }
    clear NMB. intros [ms4 mo4] PO. unfold newmembuf_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & errv3 & s3' & LA & x & a & R &
                    -> & KREL3 & MP3 & MI3 & ST3 & ERR3 & AUX3 & HP3 & DELTA & CPH3 & KEYS3 & MBO3 & RBUF & RLEN & RPOS & RNRD & RNXT & RPRV & APOS & APART
                    & MF3 & IM3 & GM3 & MM3 & RL3 & XP3).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST3, XP3 by lia. rewrite errno_RATP in ERR3.
    replace (ret_pc (Z_to_bv 64 PO_R2)) with (Z_to_bv 64 PO_R2) by (symmetry; apply ret_pc_even; [unfold PO_R2; lia| reflexivity]).
    pose proof (ctxph_delta_bounds _ _ _ DELTA) as (NB1 & NB2 & NB3).
    pose proof (membio_blocks_facts a R) as (MBB & MBL & MBG).
    set (MB := blocks_MEMBIO a R) in *. set (L2 := MB ++ LA ++ L1) in *.
    set (M2 := mkMID 1 (CtxReady x) (mid_err M) (mid_E M) (mid_vdso M)).
    assert (HB2 := HH_blocks_below H HH _ _ _ HP3).
    assert (ND2 := HH_RHEAP_blocks_nodup H HH _ _ _ HP3).
    assert (SUB12 : forall b, In b L1 -> In b L2) by (intros b Hb; unfold L2; apply in_or_app; right; apply in_or_app; right; exact Hb).
    assert (SUBA2 : forall b, In b (LA ++ LIB) -> In b L2).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [unfold L2; apply in_or_app; right; apply in_or_app; left; exact Hb| apply SUB12; apply SUB1; exact Hb]. }
    pose proof (LIBMID_newmembuf _ _ _ _ _ _ _ _ _ LM2 XP3 SUB1 CPH3 DELTA KEYS3 MF3) as LM3.
    cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in LM3. change (LIBMID (LA ++ LIB) m3 M2) in LM3.
    pose proof LM3 as (_ & _ & CP3 & _ & _ & _ & _ & _ & _ & GE3 & _ & _ & _ & _ & _). cbn [mid_ctx M2] in CP3.
    assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP3); [exact FR2| left; cbn; lia|]. apply avoid_of_img; [apply img_foot_nmb| unfold IMG_HI; cbn; lia]. }
    assert (DS3 : bytes_at usegs m3 D ds) by (eapply DSX; [exact XP3| exact DS2| intros b Hb; right; apply in_or_app; right; exact Hb| apply img_foot_nmb| lia]).
    assert (SO3 : STOREobj L2 m3 A (store_empty p)).
    { apply STOREobj_empty. apply STOREobj_empty in SO2. destruct SO2 as [SC2 _]. split; [| apply SUB12; left; reflexivity].
      eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP3); [exact SC2| right; right; exists sb; split; [left; reflexivity| cbn; unfold STORE_SIZE; lia]|].
      apply avoid_of_img; [apply img_foot_nmb| unfold IMG_LO, IMG_HI; cbn; lia]. }
    (* [comment removed for export] *)
    pose proof MBO3 as (_ & _ & _ & _ & BI1 & BI2 & BI3 & BI4 & BR1 & BR2 & BR3 & BR4 & _).
    pose proof (nd_app MB (LA ++ L1) ND2) as [DJM NDA1]. pose proof (nd_app LA L1 NDA1) as [DJA ND1].
    pose proof (nd_app [sb] L0 ND1) as [DJS ND0]. pose proof (nd_app E0 LB ND0) as [DJE NDB].
    (* [comment removed for export] *)
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP3 (SUB12 _ (or_introl eq_refl))) as SBR'.
    eapply (sr_evt_krel H HH); [exact KREL3| eapply p_seg3; [| exact MI3]|].
    { pose proof BR1 as (Q1 & _ & _ & Q4 & _). unfold BIO_SIZE in Q4. lia. }
    intros ms5 ->.
    (* [comment removed for export] *)
    set (LBr := MB ++ LA ++ sb :: LB).
    assert (PI1 : Permutation L2 (E0 ++ LBr)).
    { unfold L2, LBr, L1, L0. change (sb :: E0 ++ LB) with ([sb] ++ E0 ++ LB). change (sb :: LB) with ([sb] ++ LB).
      etransitivity; [apply Permutation_app_head; apply Permutation_app_head; apply Permutation_app_swap_app|].
      etransitivity; [apply Permutation_app_head; apply Permutation_app_swap_app|]. apply Permutation_app_swap_app. }
    assert (HP3r : hs_RHEAP H s3' (mid_errblocks M2 ++ LBr) m3) by (cbn [mid_errblocks mid_E M2]; eapply PERM; [exact HP3| exact PI1]).
    assert (SUBr : forall b, In b (LA ++ LIB) -> In b LBr).
    { intros b Hb. unfold LBr. apply in_or_app. right. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; right; apply SUBL; exact Hb]. }
    assert (SUB2r : forall b, In b L2 -> In b (E0 ++ LBr)) by (intros b Hb; eapply Permutation_in; [exact PI1| exact Hb]).
    assert (LBY0 : lb_bytes L0 = lb_bytes E0 + lb_bytes LB) by (unfold L0; apply lb_bytes_app).
    assert (LBC0 : length L0 = (length E0 + length LB)%nat) by (unfold L0; apply length_app).
    assert (LBG0 : lb_big L0 = lb_big E0 + lb_big LB) by (unfold L0; apply lb_big_app).
    assert (BYr : lb_bytes (E0 ++ LBr) = MEMBIO_BYTES + lb_bytes LA + STORE_SIZE + lb_bytes E0 + lb_bytes LB).
    { rewrite <- (lb_bytes_perm _ _ PI1). unfold L2, L1, L0. rewrite !lb_bytes_app, lb_bytes_cons, lb_bytes_app. cbn [blk_size snd sb]. lia. }
    assert (CNr : length (E0 ++ LBr) = (4 + (length LA + S (length E0 + length LB)))%nat).
    { rewrite <- (Permutation_length PI1). unfold L2, L1, L0. rewrite !length_app. cbn [length]. rewrite length_app, MBL. reflexivity. }
    assert (BGr : lb_big (E0 ++ LBr) = lb_big LA + lb_big E0 + lb_big LB).
    { rewrite <- (lb_big_perm _ _ PI1). unfold L2, L1, L0. rewrite !lb_big_app, lb_big_cons, lb_big_app. cbn [blk_size snd sb]. rewrite big1_small by (unfold STORE_SIZE, BIGB; lia). lia. }
    assert (NDsm : List.NoDup (map blk_id (sb :: MB))).
    { assert (P : Permutation L2 ((sb :: MB) ++ (LA ++ L0))).
      { unfold L2, L1. change (sb :: MB) with ([sb] ++ MB). change (sb :: L0) with ([sb] ++ L0).
        etransitivity; [apply Permutation_app_head; apply Permutation_app_swap_app| apply (Permutation_app_swap_app MB [sb] (LA ++ L0))]. }
      pose proof (Permutation_NoDup (Permutation_map blk_id P) ND2) as K. rewrite map_app in K. eapply NoDup_app_remove_r. exact K. }
    assert (SEP3 : MEMBIO_sep a R).
    { split; [exact APART|]. rewrite RBUF, RLEN.
      destruct (Z.eq_dec N 0) as [N0|N0].
      - rewrite N0, (DEMPTY N0). unfold P_FUZZ_EMPTY.
        destruct BR1 as (_ & _ & _ & _ & O1). destruct BR2 as (_ & _ & _ & _ & O2). destruct BR3 as (_ & _ & _ & _ & O3). destruct BR4 as (_ & _ & _ & _ & O4).
        unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *. lia.
      - destruct (DIN ltac:(lia)) as [pD [PIN _]].
        assert (PIN1 : In (pD, D, N) L1) by (right; apply in_or_app; right; exact PIN).
        assert (DJ : forall b, In b MB -> blk_addr b + blk_size b <= D \/ D + N <= blk_addr b).
        { intros b Hb. pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ b (pD, D, N) HP3 ltac:(unfold L2; apply in_or_app; left; exact Hb) (SUB12 _ PIN1)
                        (DJM _ _ Hb ltac:(apply in_or_app; right; exact PIN1))) as K. cbn [blk_addr blk_size fst snd] in K. lia. }
        pose proof (DJ _ ltac:(left; reflexivity)) as K1. pose proof (DJ _ ltac:(right; left; reflexivity)) as K2.
        pose proof (DJ _ ltac:(right; right; left; reflexivity)) as K3. pose proof (DJ _ ltac:(right; right; right; left; reflexivity)) as K4.
        cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4. lia. }
    assert (BEL3 : MEMBIO_below a R lo).
    { pose proof (HB2 _ BI1) as K1. pose proof (HB2 _ BI2) as K2. pose proof (HB2 _ BI3) as K3. pose proof (HB2 _ BI4) as K4.
      cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4. unfold MEMBIO_below. lia. }
    (* [comment removed for export] *)
    assert (DJ6 : forall b b', In b (LA ++ LIB) -> In b' (sb :: MB) -> blk_id b <> blk_id b').
    { intros b b' Hb Hb'. apply in_app_or in Hb.
      assert (HbL : In b LIB -> In b L0) by (intros K; unfold L0; apply in_or_app; right; exact (SUBL _ K)).
      destruct Hb' as [<-|Hb'].
      - destruct Hb as [Hb|Hb]; [exact (DJA _ _ Hb (or_introl eq_refl))| apply not_eq_sym; exact (DJS _ _ (or_introl eq_refl) (HbL Hb))].
      - apply not_eq_sym. apply (DJM _ _ Hb'). apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact (HbL Hb)]. }
    assert (DJP : 1 <= N -> exists pD, In (pD, D, N) LBr /\ forall b, In b (LA ++ LIB) -> blk_id b <> pD).
    { intros K. destruct (DIN K) as [pD [PIN PNL]]. exists pD. split; [unfold LBr; apply in_or_app; right; apply in_or_app; right; right; exact PIN|].
      intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (PNL _ Hb)].
      exact (DJA _ _ Hb (or_intror ltac:(unfold L0; apply in_or_app; right; exact PIN))). }
    pose proof RCFG as RC. unfold readcfg_stmt in RC.
    eapply (sr_seq H HH).
    { eapply RC with (lo := lo) (B := B) (LIB := LA ++ LIB) (LB := LBr) (M := M2) (x := x) (st := A) (mb := a) (S := store_empty p) (R := R) (ds := ds) (s := s3');
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP3r| exact KREL3| exact AUX3| exact ST3| exact CEIL| exact MI3| exact LM3| exact SUBr| exact RPOS| exact RNRD| exact SEP3| exact BEL3| exact NDsm| exact DJ6].
      all: lazymatch goal with
           | |- STOREobj _ _ _ _ => try (apply STOREobj_empty; apply STOREobj_empty in SO3; destruct SO3 as [SC3 _]; split; [exact SC3| unfold LBr; apply in_or_app; right; apply in_or_app; right; left; reflexivity])
           | |- _ + STORE_SIZE <= _ => try (unfold STORE_SIZE; lia)
           | |- MEMBIO _ _ _ _ => try (eapply (MEMBIO_frame0 _ _ hceil); [exact MBO3| intros b Hb; unfold LBr; apply in_or_app; left; exact Hb| apply xpres_refl])
           | |- bytes_at _ _ _ _ => try (rewrite RBUF; exact DS3)
           | |- zlength _ = _ => try (rewrite RLEN; exact DSL)
           | |- 1 <= _ -> exists pD, _ => try (rewrite RBUF, RLEN; exact DJP)
           | |- 1 <= _ -> forall pD, _ => try (rewrite RBUF, RLEN; cbn [es_id store_empty]; intros K pD Hp EQ; subst pD; unfold LBr, L1, L0 in Hp;
                 apply in_app_or in Hp; destruct Hp as [Hp|Hp]; [exact (DJM _ _ Hp ltac:(apply in_or_app; right; left; reflexivity) eq_refl)|];
                 apply in_app_or in Hp; destruct Hp as [Hp|Hp]; [exact (DJA _ _ Hp ltac:(left; reflexivity) eq_refl)|];
                 destruct Hp as [Hp|Hp]; [| exact (DJS _ _ ltac:(left; reflexivity) ltac:(unfold L0; apply in_or_app; right; exact Hp) eq_refl)];
                 destruct (DIN K) as [pD0 [PIN0 _]];
                 pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ sb (pD0, D, N) HP3 (SUB12 _ (or_introl eq_refl)) (SUB12 _ (or_intror (in_or_app _ _ _ (or_intror PIN0))))
                               (DJS _ _ ltac:(left; reflexivity) ltac:(unfold L0; apply in_or_app; right; exact PIN0))) as DD;
                 subst sb; injection Hp as E1 E2; cbn [blk_addr blk_size fst snd] in DD; unfold STORE_SIZE in *; clear - DD E1 E2 K; lia)
           | |- lb_bytes _ + _ + _ + _ <= _ => try (unfold M2, mid_bytes; cbn [mid_errblocks mid_ctx mid_err mid_E ctxph_bytes]; change (blocks_ERRST (mid_E M)) with E0; rewrite BYr; unfold MEMBIO_BYTES, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, STORE_SIZE, DECODE_BYTES, ERRSTR_BYTES; clear - BUD LBY0 NB1 PHB EHB; lia)
           | |- Z.of_nat (length _) + _ + _ + _ <= _ => try (unfold M2, mid_cnt; cbn [mid_errblocks mid_ctx mid_err mid_E ctxph_cnt]; change (blocks_ERRST (mid_E M)) with E0; rewrite CNr; unfold DECODE_CNT, ERRSTR_CNT; clear - BUDC LBC0 NB2 PHC EHC; rewrite LBC0 in BUDC; rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ, ?Nat2Z.inj_add in *; lia)
           | |- lb_big _ + _ + _ <= _ => try (unfold M2, mid_big; cbn [mid_errblocks mid_ctx mid_err mid_E ctxph_big]; change (blocks_ERRST (mid_E M)) with E0; rewrite BGr; unfold DECODE_BIG; clear - BUDB LBG0 NB3 PHG EHG; lia)
           | |- rw_cells _ _ _ [C4 _] => try (rewrite errno_RATP; exact ERR3)
           | |- _ mod 16 = 0 => try (clear - SPA SPR LO RSL NSK; lia)
           | |- _ <= _ - READCFG_STACK _ => try (pose proof (readcfg_stack_ready M 1 x (mid_E M) (mid_vdso M)) as K; clear - LO RSL NSK K; subst RS NS M2; lia)
           | |- _ mod 2 = 0 => try (unfold PO_R3; rewrite unsigned_lit by lia; reflexivity)
           | |- _ => try lia
           end. }
    clear RC. intros [ms6 mo6] PO. unfold readcfg_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & errv4 & s4' & rv & M4 & S4 & R4 & LE & NB &
                    -> & RV01 & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & HP4 & LM4 & STEP4 & NEW4 & CTX4 & SO4 & SID4 & PBS & NBC & NBB & NBG & EC4 & EB4 & EG4
                    & NDS4 & MBO4 & MBEQ & DS4 & XP4).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST4, XP4 by lia. rewrite errno_RATP in ERR4.
    replace (ret_pc (Z_to_bv 64 PO_R3)) with (Z_to_bv 64 PO_R3) by (symmetry; apply ret_pc_even; [unfold PO_R3; lia| reflexivity]).
    set (LB4 := NB ++ LE ++ LBr) in *. set (E4 := mid_errblocks M4) in *. set (F4 := E4 ++ LB4) in *.
    cbn [mid_ctx M2] in CTX4. cbn [mid_err M2] in XP4.
    assert (HB4 := HH_blocks_below H HH _ _ _ HP4). assert (ND4 := HH_RHEAP_blocks_nodup H HH _ _ _ HP4).
    pose proof (nd_app E4 LB4 ND4) as [DJ4E ND4L]. pose proof (nd_app NB (LE ++ LBr) ND4L) as [DJ4N ND4M]. pose proof (nd_app LE LBr ND4M) as [DJ4L _].
    pose proof LM4 as (IM4 & _ & CP4 & EPm4 & _ & _ & _ & _ & GM4 & GE4 & _ & MM4 & _ & _ & _). rewrite CTX4 in CP4.
    assert (SUBr4 : forall b, In b LBr -> In b F4) by (intros b Hb; unfold F4, LB4; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
    assert (SBIN4 : In sb F4) by (apply SUBr4; unfold LBr; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    assert (BSIN : forall b, In b (blocks_STORE A S4) -> In b F4).
    { intros b Hb. pose proof (Permutation_in _ PBS Hb) as K. cbn [es_id store_empty] in K. destruct K as [<-|K]; [exact SBIN4|].
      unfold F4, LB4. apply in_or_app. right. apply in_or_app. left. exact K. }
    (* [comment removed for export] *)
    assert (NOTST : forall b, In b (LE ++ MB ++ LA ++ LB) -> ~ In b (blocks_STORE A S4)).
    { intros b Hb K. pose proof (Permutation_in _ PBS K) as K'. cbn [es_id store_empty] in K'.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - destruct K' as [<-|K']; [exact (idsdisj_notin _ _ _ DJ4L Hb ltac:(unfold LBr; apply in_or_app; right; apply in_or_app; right; left; reflexivity))|].
        exact (DJ4N _ _ K' ltac:(apply in_or_app; left; exact Hb) eq_refl).
      - assert (HbLBr : In b (MB ++ LA ++ L1)).
        { apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
          apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; right; apply in_or_app; right; exact Hb]. }
        destruct K' as [<-|K'].
        + (* [comment removed for export] *)
          apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (DJM _ _ Hb ltac:(apply in_or_app; right; left; reflexivity) eq_refl)|].
          apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (DJA _ _ Hb ltac:(left; reflexivity) eq_refl)|].
          exact (DJS _ _ ltac:(left; reflexivity) ltac:(unfold L0; apply in_or_app; right; exact Hb) eq_refl).
        + refine (DJ4N _ _ K' _ eq_refl). apply in_or_app. right. unfold LBr.
          apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
          apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; right; exact Hb]. }
    (* [comment removed for export] *)
    assert (XB4 : Forall (fun iv : Z * Z => snd iv <= hceil) ([(A, A + STORE_SIZE)] ++ MEMBIO_foot a R ++ ERR_X ++ VDSO_X ++ errph_foot (mid_err M))).
    { apply Forall_app. split; [apply Forall_cons; [cbn; unfold STORE_SIZE; clear - AH; lia| apply Forall_nil]|].
      apply Forall_app. split.
      { unfold MEMBIO_foot. destruct BR1 as (_ & _ & _ & Q1 & _). destruct BR3 as (_ & _ & _ & Q3 & _).
        apply Forall_cons; [cbn; exact Q1|]. apply Forall_cons; [cbn; exact Q3| apply Forall_nil]. }
      apply Forall_app. split; [eapply Forall_impl; [| apply img_ERR_X]; intros [u v] K0; cbn in K0 |- *; unfold IMG_HI in K0; lia|].
      apply Forall_app. split; [eapply Forall_impl; [| apply img_VDSO_X]; intros [u v] K0; cbn in K0 |- *; unfold IMG_HI in K0; lia|].
      pose proof LM3 as (_ & _ & _ & EP3 & _). eapply errph_foot_below; [exact EP3| intros b Hb; exact (HB2 _ (SUBA2 _ Hb))]. }
    assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact FR3| left; cbn; lia|]. eapply Forall_impl; [| exact XB4]. intros [u v] K. cbn in K |- *. lia. }
    rewrite RBUF in DS4.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| eapply p_seg4; exact MI4|]. intros ms7 ->.
    (* [comment removed for export] *)
    pose proof (storefree_spec H HH) as SF. unfold storefree_stmt, efree_stmt_at in SF.
    eapply (sr_seq H HH).
    { eapply SF with (lo := lo) (B := B) (LB := F4) (s := s4') (p := A) (x := S4) (errv := errv4); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact NDS4| exact HP4| exact KREL4| exact AUX4| exact ST4| exact CEIL| exact MI4| exact IM4| exact GM4| exact GE4].
      all: lazymatch goal with
           | |- STOREobj _ _ _ _ => try (eapply STOREobj_frame_law; [exact SO4| exact BSIN| apply xpres_refl| intros b Hb; exact (HB4 _ (BSIN _ Hb))])
           | |- rw_cells _ _ _ [C4 _] => try (rewrite errno_RATP; exact ERR4)
           | |- _ <= _ - STOREFREE_STACK => try (clear - LO RSL NSK; subst RS NS; unfold STOREFREE_STACK, ENTRYFREE_STACK, EXTFREE_STACK; unfold SKPOPFREE_STACK, FR_OSSL_ECHSTORE_free,
                                                  FR_ossl_echstore_entry_free, FR_ossl_echext_free, FR_sk_pop_free, CFREE_STACK, RFREE_STACK, FR_EVP_PKEY_free; lia)
           | |- _ mod 2 = 0 => try (unfold PO_R4; rewrite unsigned_lit by lia; reflexivity)
           | |- _ => try lia
           end. }
    clear SF. intros [ms8 mo8] PO. unfold efree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m5 & s5' & LB5 &
                    -> & KREL5 & MP5 & MI5 & ST5 & ERR5 & AUX5 & PERM5 & HP5 & XP5 & IM5 & GM5 & GE5).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST5, XP5 by lia. rewrite errno_RATP in ERR5.
    replace (ret_pc (Z_to_bv 64 PO_R4)) with (Z_to_bv 64 PO_R4) by (symmetry; apply ret_pc_even; [unfold PO_R4; lia| reflexivity]).
    assert (KEEP5 : forall b, In b (LE ++ MB ++ LA ++ LB) -> In b LB5).
    { intros b Hb. eapply perm_in_rest; [exact PERM5| | exact (NOTST _ Hb)].
      unfold F4, LB4, LBr. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb|].
      apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; right; exact Hb]. }
    assert (SUB5 : forall b, In b (LE ++ LA ++ LIB) -> In b LB5).
    { intros b Hb. apply KEEP5. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right; apply in_or_app; right.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply SUBL; exact Hb]. }
    assert (HB5 := HH_blocks_below H HH _ _ _ HP5).
    pose proof (LIBMID_xpres0 _ _ _ _ _ _ LM4 XP5 SUB5) as LM5.
    pose proof LM5 as (_ & _ & CP5 & _ & _ & _ & _ & _ & _ & _ & _ & MM5 & _). rewrite CTX4 in CP5.
    assert (FR5 : rw_cells usegs m5 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP5); [exact FR4| left; cbn; lia| apply Forall_nil]. }
    assert (DS5 : bytes_at usegs m5 D ds).
    { eapply DSX; [exact XP5| exact DS4| intros b Hb; apply KEEP5; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb| apply Forall_nil| lia]. }
    assert (MBO5 : MEMBIO LB5 m5 a R4).
    { eapply MEMBIO_frame0; [exact MBO4| | exact XP5]. intros b Hb. rewrite MBEQ in Hb. apply KEEP5. apply in_or_app; right; apply in_or_app; left. exact Hb. }
    assert (APART4 : MEMBIO_apart a R4).
    { unfold blocks_MEMBIO in MBEQ. injection MBEQ as E1 E2 E3 E4' E5 E6 E7. unfold MEMBIO_apart in *. rewrite E3, E5, E7. exact APART. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL5| eapply p_seg5 with (lo := lo); [exact FR5| exact ST5| exact CEIL| lia| exact MI5]|].
    intros ms9 [-> ST5r].
    (* [comment removed for export] *)
    pose proof (biofree_spec H HH (@ECH_C3_newex.cfreeex_spec HCEIL)) as BF. unfold biofree_mem_stmt in BF.   (* [comment removed for export] *)
    eapply (sr_seq H HH).
    { eapply BF with (lo := lo) (B := B) (LB := LB5) (s := s5') (a := a) (R := R4) (x := x) (errv := errv4); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact MBO5| exact APART4| exact HP5| exact KREL5| exact AUX5| exact SPB| exact SPA| exact ST5r| exact CEIL| exact MI5| exact IM5| exact GM5| exact MM5| exact RAE].   (* [comment removed for export] *)
      all: lazymatch goal with
           | |- CTXPH _ _ _ => try (eapply ECH_LibMid.CTXPH_mono; [exact CP5| exact SUB5])
           | |- rw_cells _ _ _ [C4 _] => try (rewrite errno_RATP; exact ERR5)
           | |- _ <= _ - BIOFREE_STACK => try (clear - LO RSL NSK; subst RS NS; unfold BIOFREE_STACK, MEMFREE_STACK, BUFFREE_STACK, CFREE_STACK, CFREEEX_STACK, RFREE_STACK, FR_BIO_free, FR_BIO_free_int, FR_mem_free, FR_mem_buf_free,
                                                FR_BUF_MEM_free, FR_CRYPTO_free_ex_data, GETGLOBAL_READY_STACK, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, CUNLOCK_STACK,
                                                FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context;
                                                unfold CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CFREE_STACK, RFREE_STACK; lia)
           | |- _ => try lia
           end. }
    clear BF. intros [ms10 mo10] PO. unfold biofree_mem_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & z3 & z4 & z5 & z6 & m6 & errv6 & s6' & LBr6 &
                    -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & HP6 & PERM6 & IM6 & GM6 & MM6 & XP6).
    rewrite MBEQ in PERM6.
    assert (ND5 := HH_RHEAP_blocks_nodup H HH _ _ _ HP5).
    assert (KEEP6 : forall b, In b (LE ++ LA ++ LB) -> In b LBr6).
    { intros b Hb. eapply perm_in_rest; [apply Permutation_sym; exact PERM6| |].
      - apply KEEP5. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply in_or_app; right; exact Hb].
      - intros K. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        + exact (DJ4L _ _ Hb ltac:(unfold LBr; apply in_or_app; left; exact K) eq_refl).
        + refine (DJM _ _ K _ eq_refl). apply in_or_app. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; apply in_or_app; right; exact Hb]. }
    assert (SUB6 : forall b, In b (LE ++ LA ++ LIB) -> In b LBr6).
    { intros b Hb. apply KEEP6. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply SUBL; exact Hb]. }
    pose proof (LIBMID_xpres0 _ _ _ _ _ _ LM5 XP6 SUB6) as LM6.
    change (blocks_MEMBIO a R) with MB in PERM6. cbn [es_id store_empty] in PBS. change (p, A, STORE_SIZE) with sb in PBS.
    (* [comment removed for export] *)
    assert (P5 : Permutation LB5 (E4 ++ LE ++ MB ++ LA ++ LB)).
    { apply (Permutation_app_inv_l (sb :: NB)). transitivity F4.
      - transitivity (blocks_STORE A S4 ++ LB5); [apply Permutation_app_tail; symmetry; exact PBS| exact PERM5].
      - unfold F4, LB4, LBr. apply perm7. }
    assert (P6 : Permutation LBr6 (E4 ++ LE ++ LA ++ LB)).
    { apply (Permutation_app_inv_l MB). transitivity LB5; [symmetry; exact PERM6|]. transitivity (E4 ++ LE ++ MB ++ LA ++ LB); [exact P5| apply perm5]. }
    apply (sr_done H HH). unfold parse_one_post. cbn [cfg_ms cfg_model].
    exists z0, z1, z2, (Z_to_bv 64 1), f1, f2, f3, f4, f5, f6, f7, z3, z4, z5, z6, m6, errv6, s6', M4, (LE ++ LA).
    split; [reflexivity|]. split; [exact KREL6|].
    split; [eapply (mpres_trans H HH); [exact MP2| eapply (mpres_trans H HH); [exact MP3| eapply (mpres_trans H HH); [exact MP4| eapply (mpres_trans H HH); [exact MP5| exact MP6]]]]|].
    split; [exact MI6|]. split; [exact ST6|]. split; [rewrite errno_RATP; exact ERR6|]. split; [exact AUX6|].
    split; [eapply PERM; [exact HP6|]; rewrite <- !app_assoc; exact P6|].
    split; [rewrite <- !app_assoc; exact LM6|].
    split. { unfold mid_step in STEP4 |- *. unfold M2 in STEP4. cbn [mid_flag mid_ctx mid_err mid_vdso] in STEP4. destruct STEP4 as (F1 & C1 & E1 & V1).
             split; [exact F1|]. split; [| split; [exact E1| exact V1]].
             intros b Hb. rewrite CTX4. rewrite Hb in DELTA. cbn [ctxph_delta] in DELTA. destruct DELTA as [-> _]. reflexivity. }
    split. { unfold mid_newlib_ok in NEW4 |- *. unfold M2 in NEW4. cbn [mid_ctx mid_err] in NEW4. destruct NEW4 as (LA2 & LE2 & PN & CN & EN).
             try rewrite CTX4 in CN. cbn in CN. subst LA2. cbn [app] in PN.
             exists LA, LE2. split; [transitivity (LA ++ LE); [apply Permutation_app_comm| apply Permutation_app_head; exact PN]|].
             split; [| exact EN]. rewrite CTX4. clear - DELTA. revert DELTA. destruct (mid_ctx M) as [|b0]; intros DELTA; cbn [ctxph_delta] in DELTA |- *; [exact DELTA|].
             destruct DELTA as [_ E]. exact E. }
    split; [exists x; exact CTX4|].
    split; [exact EC4|]. split; [exact EB4|]. split; [exact EG4|].
    split; [eapply DSX; [exact XP6| exact DS5| intros b Hb; apply KEEP6; apply in_or_app; right; apply in_or_app; right; exact Hb| apply Forall_nil| lia]|].
    (* [comment removed for export] *)
    assert (DJMB : forall hb, In hb MB -> idsdisj [hb] LB).
    { intros hb Hhb b b' Hb Hb'. destruct Hb as [<-|[]]. apply DJM; [exact Hhb|]. apply in_or_app; right. right. apply in_or_app; right. exact Hb'. }
    assert (XP4' : xpres LB (bv_unsigned sp) ((memflag_foot ++ CTX_X ++ ERR_X ++ VDSO_X ++ errph_foot (mid_err M)) ++ ([(A, A + STORE_SIZE)] ++ MEMBIO_foot a R)) m3 m4).
    { eapply xpres_weaken; [exact XP4| lia| intros b Hb; unfold LBr; apply in_or_app; right; apply in_or_app; right; right; exact Hb|].
      intros q Hq. apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; right; apply rin_ivs_app; left; exact Hq|].
      apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; right; apply rin_ivs_app; right; exact Hq|].
      apply rin_ivs_app; left. apply rin_ivs_app; right. apply rin_ivs_app; right. exact Hq. }
    assert (XP4'' : xpres LB (bv_unsigned sp) (memflag_foot ++ CTX_X ++ ERR_X ++ VDSO_X ++ errph_foot (mid_err M)) m3 m4).
    { eapply xpres_drop_nonclient; [exact XP4'|]. intros q Hq [HC _]. apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq].
      { (* [comment removed for export] *)
        cbn [rin_ivs fst snd] in Hq. destruct Hq as [Hq|[]].
        pose proof (client_outside_block H HH _ _ _ sb LB (bv_unsigned sp) q HP3 (SUB12 _ (or_introl eq_refl)) (fun b Hb => SUB12 _ (or_intror (in_or_app _ _ _ (or_intror Hb))))
                      ltac:(intros b0 b' Hb0 Hb'; apply DJS; [exact Hb0| unfold L0; apply in_or_app; right; exact Hb']) ltac:(lia) HC) as K.
        cbv delta [sb] in K. cbn [blk_addr blk_size fst snd] in K. unfold STORE_SIZE in *. lia. }
      unfold MEMBIO_foot in Hq. cbn [rin_ivs fst snd] in Hq.
      destruct Hq as [Hq|[Hq|[]]].
      - pose proof (client_outside_block H HH _ _ _ (mb_id R, a, BIO_SIZE) LB (bv_unsigned sp) q HP3 BI1 (fun b Hb => SUB12 _ (or_intror (in_or_app _ _ _ (or_intror Hb))))
                      (DJMB _ ltac:(left; reflexivity)) ltac:(lia) HC) as K. cbn [blk_addr blk_size fst snd] in K. lia.
      - pose proof (client_outside_block H HH _ _ _ (mb_bmid R, mb_bm R, BUFMEM_SIZE) LB (bv_unsigned sp) q HP3 BI3 (fun b Hb => SUB12 _ (or_intror (in_or_app _ _ _ (or_intror Hb))))
                      (DJMB _ ltac:(right; right; left; reflexivity)) ltac:(lia) HC) as K. cbn [blk_addr blk_size fst snd] in K. lia. }
    eapply xpres_trans; [eapply xpres_weaken; [exact XP1| lia| intros b Hb; apply in_or_app; right; exact Hb| intros q Hq; destruct Hq]|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| intros b Hb; apply in_or_app; right; exact Hb| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
    eapply xpres_trans.
    { eapply xpres_weaken; [exact XP3| lia| intros b Hb; right; apply in_or_app; right; exact Hb|].
      intros q Hq. apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [apply rin_ivs_app; left; exact Hq|].
      apply rin_ivs_app; right. apply rin_ivs_app; left. apply (rin_ivs_ctxph_foot (mid_ctx M)). exact Hq. }
    eapply xpres_trans; [exact XP4''|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP5| lia| intros b Hb; apply KEEP5; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb| intros q Hq; destruct Hq]|].
    eapply xpres_weaken; [exact XP6| lia| intros b Hb; apply KEEP6; apply in_or_app; right; apply in_or_app; right; exact Hb| intros q Hq; destruct Hq].
  Qed.
End W.
