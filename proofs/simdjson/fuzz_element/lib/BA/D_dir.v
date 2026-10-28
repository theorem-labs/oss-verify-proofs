(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_aex D_libiface D_clx. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import D_usage D_open D_read. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_rlkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Dir.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract RT.
Hypothesis RDIR : read_icontract_dir RT.
Hypothesis FPR : fprintf_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis VARGV : valid_argv argvb.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : xenv_laws XENV XENV_FP.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.

Lemma errno_A : errno_cell (Z_to_bv 64 TP_A) = ERRNO_A.
Proof. unfold errno_cell, ERRNO_A, TP_A. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma errno_static : forall i, 0 <= i < 4 -> client_static (errno_cell (Z_to_bv 64 TP_A) + i).
Proof. intros i Hi. rewrite errno_A. apply client_static_intro. unfold ERRNO_A, TP_A. lia. Qed.

Theorem dir_cpsE : Z.of_nat (length argvb) = 2 -> open_class (nth 1 (argv_Z argvb) []) fs = OCDir ->
  cpsE asegs (OPENED RT OUT_rep ERR_rep XENV LIB argvb fs) (evw 2 (msg_read_error (nth 1 (argv_Z argvb) []))) (EXIT fs 2).
Proof using AF AF_DRV MAL RDIR FPR EXC VARGV OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros HL HCL T c HO Hk.
  destruct HO as (Σ & usp & ap & path & gp & s1 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7
                  & m & ent & HA & HCTX & HSIG & HB & Hap & Hhi & HENT & HSLK).
  rewrite nth1_argv_Z in HCL. pose proof (oc_dir _ _ HCL) as HD. unfold path_b in HENT. rewrite HD in HENT.
  injection HENT as <-.
  pose proof HCTX as (ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof HSIG as (LV & FRS & CR & USP0' & SPW).
  destruct (path_b_facts argvb VARGV HL) as (NZ & NSL & NDD & LEN).
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  set (F1 := fd_insert fds0 (Z_to_bv 64 3) FdDir) in *.
  rewrite nth1_argv_Z.
  replace (evw 2 (msg_read_error (map bv_unsigned (nth 1 argvb []))))
    with (evw 2 (fp_msg (FPread_error path (path_b argvb))) ++ evw 1 (so_buf stdout_init))
    by (cbn [fp_msg so_buf stdout_init]; rewrite app_nil_r; reflexivity).

  destruct (ASTA_unpack RT Σ _ _ c HA) as (ms0 & RS0 & HA').
  destruct RS0 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & -> & FRM).
  rewrite (ret_pc_even RET_OPEN) in HA' by (unfold RET_OPEN; lia).
  pose proof (opened_walk usp gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m MI0) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ F1 fs _ _ W1') HA').
  intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & <- & Hc1').
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  apply (MAL Σ (PMfd F1 fs) (Z_to_bv 64 0xb11bc) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
           (Z_to_bv 64 65536) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 (Z_to_bv 64 3) (Z_to_bv 64 65536) s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m 65536 lo); try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - lia.
  - rewrite LV. reflexivity.
  - unfold mcost, DCOST, CREDIT_DRV in *. cbn. lia.
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - unfold unwind_ok. rewrite EU, !unsigned_lit by lia. left. ul.
  - intros cf2 (Σ' & p & Hc2 & LV' & FRS' & SP' & CR' & Pp & Pal & Ptop).
    destruct (ASTA_unpack RT Σ' _ _ cf2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2) & Hc2').
    destruct RS2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & ->). pose (fc' := fc).
    rewrite EU in ST2, PRES2.
    pose proof (af_live_range RT AF Σ' m2 p 65536 ART2 ltac:(rewrite LV'; left; reflexivity)) as (PR1 & PR2 & PR3).
    assert (CLX2 : CLX OUT_rep ERR_rep XENV LIB stdout_init m2)
      by exact (CLX_pres OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                  _ m m2 _ _ _ CLX0 PRES2 WM2).
    pose proof (agree_stack_pres _ _ _ _ _ PRES2) as AG2.

    pose proof (first_read_walk usp p gp t0' t1' t2' s1 a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path) s3 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6' F' fc' m2 ltac:(ul) MI2) as W2.
    rewrite (ret_pc_even 0xb11bc) in Hc2' by lia.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ' F1 fs _ _ W2') Hc2').
    intros cf3 Hc3.
    destruct (ASTA_unpack RT Σ' _ _ cf3 Hc3) as (ms3 & <- & Hc3').
    pose proof CLX2 as (_ & _ & _ & _ & _ & _ & RS2).

    apply (RDIR Σ' F1 fs (Z_to_bv 64 0xb1250) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 2)
             (Z_to_bv 64 p) (Z_to_bv 64 3) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 65536) a3' a4' a5' a6' a7' (Z_to_bv 64 path)
             (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 p) s8 s9 s10 s11
             t3' t4' t5' t6' F' fc' m2 3 g_read_stage 65536 lo); try reflexivity; try assumption.
    + lia.
    + lia.
    + ul.
    + exact (checked_dst_stage RT AF Σ' m2 _ 65536 ART2 RS2 ltac:(lia)).
    + apply errno_static.
    + rewrite errno_A. pose proof CLX2 as (_ & _ & _ & _ & _ & ERRN2 & _). exact ERRN2.
    + unfold call_ok. rewrite EU, SP'. split; [exact ST2|]. ul.
    + intros cf4 Hc4.
      destruct (ASTA_unpack RT Σ' _ _ cf4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4) & Hc4').
      destruct RS4 as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & F'' & ->). pose (fc'' := fc').
      rewrite EU in ST4, PRES4. rewrite errno_A in PRES4.
      destruct (CLX_errno_pres OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                  _ m2 m4 _ _ _ CLX2 PRES4 WM4) as (OUT4 & ERR4 & XE4 & LIB4).
      pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRES4 ltac:(intros x Hx; cbn; split; [unfold ERRNO_A, TP_A; ul| exact I])) as AG4.
      assert (HB4 : bytes_at asegs m4 path (path_b argvb ++ [Z_to_bv 8 0])).
      { apply (path_agree m2 m4 usp path); [| lia| rewrite length_app; cbn [length]; ul| exact AG4].
        apply (path_agree m m2 usp path); [exact HB| lia| rewrite length_app; cbn [length]; ul| exact AG2]. }
      assert (HSLK4 : path_slack argvb m4 path).
      { destruct HSLK as (sl & SL & SLM & SLB). exists sl. split; [| split; assumption].
        apply (path_agree m2 m4 usp); [| lia| ul| exact AG4].
        apply (path_agree m m2 usp); [exact SL| lia| ul| exact AG2]. }
      pose proof (AF_DRV Σ' m4 ART4) as (SC4 & _).
      assert (SSP4 : io_ssp m4).
      { pose proof CLX2 as (_ & _ & _ & _ & (g2 & G2) & _). exists g2. split; [exact (proj1 (proj2 (AF_DRV Σ' m4 ART4)))|].
        apply (ro_cells_agree asegs m2 m4 _ _ G2). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES4). intros x Hx. cbn in Hx.
        split; [right; left; apply client_static_intro; unfold SSP_GUARD in *; lia| cbn; unfold ERRNO_A, TP_A, SSP_GUARD in *; split; [lia| exact I]]. }

      pose proof (read_err_walk usp gp t0'' t1'' t2'' (Z_to_bv 64 p) a1'' a2'' a3'' a4'' a5'' a6'' a7'' (Z_to_bv 64 path)
                    (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 p) s8 s9 s10 s11
                    t3'' t4'' t5'' t6'' F'' fc'' m4 SC4 MI4) as W3.
      rewrite (ret_pc_even 0xb1250) in Hc4' by lia.
      lazymatch type of W3 with evt asegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ' F1 fs _ _ W3') Hc4').
      intros cf5 Hc5.
      destruct (ASTA_unpack RT Σ' _ _ cf5 Hc5) as (ms5 & <- & Hc5').
      eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
      apply (FPR Σ' F1 fs (Z_to_bv 64 0xb13cc) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0'' t1'' t2'' (Z_to_bv 64 2)
               (Z_to_bv 64 p) (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 FMT_read_error) (Z_to_bv 64 path) a3'' a4'' a5'' a6'' a7''
               (Z_to_bv 64 path) (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 p)
               s8 s9 s10 s11 t3'' t4'' t5'' t6'' F'' fc'' m4 (FPread_error path (path_b argvb)) STDERR_FILE lo);
        try reflexivity; try assumption.
      * intros a s Hs. cbn [fp_str] in Hs. injection Hs as <- <-. split; [exact HB4|]. split; [exact NZ|].
        split; [lia|]. split; [apply (checked_src_stack RT AF Σ' m4); [exact ART4| rewrite SP'; ul| ul| rewrite EU; lia]|].
        split; [rewrite EU; lia| exact HSLK4].
      * unfold call_ok. rewrite EU, SP'. split; [exact ST4|]. ul.
      * intros cf6 Hc6.
        destruct (ASTA_unpack RT Σ' _ _ cf6 Hc6) as (ms6 & (v & m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ERR6 & OUTP6) & Hc6').
        destruct RS6 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F6 & fc6 & ->).
        rewrite EU in ST6, PRES6.
        pose proof (OUTP6 stdout_init OUT4) as OUT6.
        assert (XE6 : XENV m6).
        { apply (xl_loc XENV_loc m4 m6 XE4). intros a Ha. apply PRES6; [right; left; exact (proj1 (XENV_img _ Ha))|].
          exact (proj1 (proj2 (proj2 (XENV_img _ Ha)))). }

        pose proof (failed_walk2 usp gp (Z_to_bv 64 p) (Z_to_bv 64 path) (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 65536)
                      (Z_to_bv 64 g_read_stage) (Z_to_bv 64 p) s8 s9 s10 s11 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6
                      F6 fc6 m6 MI6) as W4.
        rewrite (ret_pc_even 0xb13cc) in Hc6' by lia.
        lazymatch type of W4 with evt asegs _ ?X =>
          assert (W4' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W4) end.
        clear W4.
        apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ' F1 fs _ _ W4') Hc6').
        intros cf7 Hc7.
        destruct (ASTA_unpack RT Σ' _ _ cf7 Hc7) as (ms7 & <- & Hc7').
        apply (EXC Σ' F1 fs (Z_to_bv 64 0xb13f8) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 2)
                 (Z_to_bv 64 p) (Z_to_bv 64 2) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 path) (Z_to_bv 64 0) (Z_to_bv 64 3)
                 (Z_to_bv 64 65536) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 p) s8 s9 s10 s11 u3 u4 u5 u6 F6 fc6
                 m6 stdout_init 2 lo); try reflexivity; try assumption.
        -- lia.
        -- left. reflexivity.
        -- unfold call_ok. rewrite EU, SP'. split; [exact ST6|]. ul.
        -- eapply (io_ssp_pres_fp IO_FP _ _ _ m4 m6); [| exact SSP4| exact (AF_DRV _ _ ART6)| exact PRES6].
           intros x Hx. apply outside_of_not_in_ranges'. intros Hin. apply (proj1 (proj2 (IO_img x Hin))). unfold drv_cell. right; left; exact Hx.
Qed.

End Dir.
