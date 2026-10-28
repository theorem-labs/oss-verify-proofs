(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA Image.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx D_rlkit D_hdr D_trdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition s_short : list byte := map (Z_to_bv 8) msg_short_hdr.
Definition s_over : list byte := map (Z_to_bv 8) msg_cfg_overrun.

Lemma s_short_len : Z.of_nat (length s_short) = 31.
Proof. reflexivity. Qed.
Lemma s_over_len : Z.of_nat (length s_over) = 31.
Proof. reflexivity. Qed.
Lemma s_short_msg : map bv_unsigned s_short = msg_short_hdr.
Proof. vm_compute. reflexivity. Qed.
Lemma s_over_msg : map bv_unsigned s_over = msg_cfg_overrun.
Proof. vm_compute. reflexivity. Qed.

Lemma s_short_ro : ro_bytes_b asegs S_SHORT s_short = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s_over_ro : ro_bytes_b asegs S_OVER s_over = true.
Proof. vm_compute. reflexivity. Qed.

Lemma s_short_at : forall m, mem_inv asegs m -> bytes_at asegs m S_SHORT s_short.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold S_SHORT; lia| rewrite s_short_len; unfold S_SHORT; lia|].
  apply ro_bytes_b_sound. exact s_short_ro.
Qed.
Lemma s_over_at : forall m, mem_inv asegs m -> bytes_at asegs m S_OVER s_over.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold S_OVER; lia| rewrite s_over_len; unfold S_OVER; lia|].
  apply ro_bytes_b_sound. exact s_over_ro.
Qed.

Section File3.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable CG : cgraph.                (* [comment removed for export] *)
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis FRE : free_contract RT.
Hypothesis FWR : fwrite_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, CREDIT_DRV, g_read_stage in *; lia.

(* [comment removed for export] *)
Definition FCTX (Σ : rts RT) (so : stdout_st) (usp buf cap : Z) (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ CLX OUT_rep ERR_rep XENV LIB so m /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7
  /\ stk asegs m (rt_sp0 RT Σ - STACK_WIN) (usp - 80)
  /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
  /\ In (buf, cap) (rt_live RT Σ) /\ rt_frames RT Σ = [] /\ usp + 16 <= USTACK_TOP.
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem ret_tail_cpsE : forall (Σ : rts RT) (so : stdout_st) (code usp buf cap : Z)
    (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  FCTX Σ so usp buf cap c0 c1 c2 c3 c4 c5 c6 c7 m -> 0 <= code < 256 ->
  (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
  cpsE asegs (ASTA RT Σ (PMfd fds0 fs)
               (eq (entry_st (Z_to_bv 64 0x1f2d90) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 code)
                     (Z_to_bv 64 buf) (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m)))
    (evw 1 (so_buf so)) (EXIT fs code).
Proof using AF AF_DRV FRE EXC OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros Σ so code usp buf cap gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7
    F fc m HF Hcode Hso T c HA Hk.
  destruct HF as (ART0 & MI0 & CLX0 & FR0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  apply (FRE Σ (PMfd fds0 fs) (Z_to_bv 64 0x1f2d90) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 code)
           (Z_to_bv 64 buf) (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf cap lo);
    try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - unfold unwind_ok, fp_invalid. rewrite EU, !unsigned_lit by ul. left. split; [cbn; tauto|]. left. ul.
  - intros cf1 (Σ1 & v & Hc1 & LV1 & FRS1 & SP1 & CR1 & _).
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PRES1) & Hc1').
    destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    rewrite EU in ST1, PRES1.
    rewrite (ret_pc_even 0x1f2d90) in Hc1' by lia.
    assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB so m1)
      by exact (CLX_pres_nw OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img _ m m1 _ _ _ CLX0 PRES1).
    pose proof CLX1 as (OUT1 & ERR1 & XE1 & _).
    destruct FR0 as (junk & FR0).
    assert (FR1 : rw_cells asegs m1 (usp - 80) [CB 8 junk; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 (Z_to_bv 64 MAIN_RA)]).
    { apply (rw_cells_agree_nw asegs m m1 _ _ FR0). apply (agree_of_pres _ _ _ _ _ _ PRES1).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (main_ret_walk usp gp (Z_to_bv 64 code) (Z_to_bv 64 buf) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v u0 u1 u2 b1 b2 b3 b4 b5 b6
                  b7 u3 u4 u5 u6 F1 fc1 m1 lo c0 c1 c2 c3 c4 c5 c6 c7 junk ST1 ltac:(ul) ltac:(ul) B16 ltac:(ul) FR1 MI1) as W1.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & (-> & ST2) & Hc2').
    apply (EXC Σ1 fds0 fs (Z_to_bv 64 0x51a954) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) u0 u1 u2 c0 c1 (Z_to_bv 64 code) b1 b2 b3
             b4 b5 b6 b7 c2 c3 c4 c5 c6 c7 s8 s9 s10 s11 u3 u4 u5 u6 F1 fc1 m1 so code lo); try reflexivity; try assumption.
    + unfold call_ok. rewrite unsigned_lit by ul. rewrite SP1. split; [exact ST2|]. ul.
    + io_ssp_tac AF_DRV.
Qed.

(* [comment removed for export] *)
Theorem diag_tail_cpsE : forall (Σ : rts RT) (usp buf cap sa : Z) (s : list byte)
    (gp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  FCTX Σ stdout_init usp buf cap c0 c1 c2 c3 c4 c5 c6 c7 m ->
  bytes_at asegs m sa s -> acc asegs m sa (Z.of_nat (length s)) -> 0x10000 <= sa -> sa + Z.of_nat (length s) <= SEGTOP_A ->
  0 < Z.of_nat (length s) <= 64 -> (sa = 0x4406e \/ sa = 0x212b3) ->
  cpsE asegs (ASTA RT Σ (PMfd fds0 fs)
               (eq (entry_st (Z_to_bv 64 0x1f2d88) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2)
                     (Z_to_bv 64 buf) (Z_to_bv 64 sa) (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 1) (Z_to_bv 64 STDERR_FILE)
                     a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fwrite m)))
    (evw 2 (map bv_unsigned s)) (EXIT fs 2).
Proof using AF AF_DRV FRE FWR EXC OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros Σ usp buf cap sa s gp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 F fc m
    HF HB HAC H1 H2 H3 HSA.
  pose proof HF as (ART0 & MI0 & CLX0 & FR0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & UT0).
  pose proof CLX0 as (_ & ERR0 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  intros T c HA Hk.
  replace (evw 2 (map bv_unsigned s)) with (evw 2 (map bv_unsigned s) ++ evw 1 (so_buf stdout_init))
    by (cbn [so_buf stdout_init evw map]; rewrite app_nil_r; reflexivity).
  eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
  apply (FWR Σ fds0 fs (Z_to_bv 64 0x1f2d88) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
           (Z_to_bv 64 sa) (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 1) (Z_to_bv 64 STDERR_FILE) a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sa s STDERR_FILE lo); try reflexivity; try assumption.
  - split; [intros _; split; [exact HAC| right; right; right; ul]| left; ul].
  - io_ssp_tac AF_DRV.
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - intros cf1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (v & m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & ERR1 & OUTP1) & Hc1').
    destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    rewrite EU in ST1, PRES1.
    rewrite (ret_pc_even 0x1f2d88) in Hc1' by lia.
    pose proof CLX0 as (OUT0 & _).
    assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB stdout_init m1)
      by exact (CLX_io OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                  _ _ m m1 _ _ _ CLX0 PRES1 WM1 (OUTP1 _ OUT0) ERR1).
    pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES1 ltac:(intros x Hx; apply outside_of_not_in_ranges'; intros Hin;
                  pose proof (client_static_range _ (proj1 (IO_img _ Hin))); ul)) as AG1.
    pose proof (diag_free_walk usp gp u0 u1 u2 v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 2) (Z_to_bv 64 buf) s2 s3 s4 s5 s6 s7
                  s8 s9 s10 s11 u3 u4 u5 u6 F1 fc1 m1 MI1) as W1.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
    apply (ret_tail_cpsE Σ stdout_init 2 usp buf cap gp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
             c0 c1 c2 c3 c4 c5 c6 c7 F1 fc1 m1); [| lia| left; reflexivity| exact Hc2'| exact Hk].
    split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
    split; [apply (main_frame_agree m m1 usp _ _ _ _ _ _ _ _ FR0); [eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; ul| exact WM1]|].
    split; [exact ST1|]. tauto.
Qed.

End File3.
