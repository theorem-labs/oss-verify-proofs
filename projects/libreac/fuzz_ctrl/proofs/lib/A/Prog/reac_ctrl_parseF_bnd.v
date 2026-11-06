(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3501 of its 3539 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_ctrl_parseF.v, with its module paths, module names and numbers changed; 273 of its 338 lines of code are new or changed and 3474 lines of the source are left out. *)
(* reac_ctrl_parse, image A (asan, fuzz_ctrl v1.9.0): the two cut points of the footprint run of
   reac_ctrl_parseF.v at its fake-stack events, for the cgif-form walk (route (a): a mechanical split of the proved
   v1.9 run; no new proof obligation; the output feeds only the ported cgif-form walk).
   - PreCall: the state at the entry of __asan_stack_malloc_1, just after `jal __asan_stack_malloc_1` at 0x835e8
     (ra = 0x835ec, a0 = 128, sp = A), with what the entry's script keeps up to there (reac_ctrl_parseF.v
     :1543-1572): memory apart from the window as at m, wmono / rd_mono from m, mem_inv, the 12 saved registers at
     [S - 96, S), the window below A a stack window.
   - RelSt / RelFacts: the state at the release store `sb zero, 0(a1)` at 0x83990 of a side-stack frame fra =
     fs_frame FS 1 j (a1 = its flag address fs_flag FS 1 j, read at 0x8398c from fra + 120), with what L_exit's
     script holds there (reac_ctrl_parseF.v :2327-2534).
   Provenance, the image and the const-cell check: reac_ctrl_parseF_cut.v's header. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib RcLib RcParse RcParseLib RcAsan RcAsanLib RcBoxLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c memcmp_c bcmp_wrap_c kind_of_link1_c kind_of_link1F
  asan_memset_cF asan_memcpy_cF reac_ctrl_parse_c.
(* Last: StepF's step / if_cases (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_parseF.

Section BndF.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte) (RNG : ExecF.footprint).
  (* the callees, in their image-A footprint forms (above: __asan_memset / __asan_memcpy a Theorem Labs lane's shared texts;
     kind_of_link1's from kind_of_link1_c.v) *)
  Hypothesis HMSET : asan_memset_contract_F.
  Hypothesis HMCPY : asan_memcpy_contract_F.
  Hypothesis HBCMPW : bcmp_wrap_contract_F.
  Hypothesis HKOL : kind_of_link1_contract_F.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Rn : 0 <= n < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis RS : 8800 <= S < 2^64.
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (S - 8800) S.
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis Lfr : length fr = 50%nat.
  Hypothesis HF : 50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - 8800 \/ S <= f).
  Hypothesis Hrd : forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i.
  Hypothesis HOK : o <> 0 ->
    o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
    (o + 36 <= S - 8800 \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o).
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= S - 8800.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW0 : addressable m (S - 8800) 8800.
  Hypothesis AF0 : 50 <= n -> addressable m f 50.
  Hypothesis AO0 : o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o).
  Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
  Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
  Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
  Hypothesis HGCF : bytes_at rsegs m GOT_CF (le8 (wa CF)).
  Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
  Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
  (* The free frames X (class-1 frames in use by the caller, flag 1 at m, index below fs_M 1) and the side-stack
     premise in the free-frame form (fpx: the data ranges are apart from fp_wx [1] FS X, which leaves out X's frames
     and their shadow). *)
  Variable X : list (nat * Z).
  Hypothesis XF0 : Forall (fun ci => fst ci = 1%nat /\ bytes_at rsegs m (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X.
  Hypothesis XB0 : Forall (fun ci => 0 <= snd ci < fs_M 1) X.
  Hypothesis FP0 : fpx [1%nat] m (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X.
  Hypothesis TLS0 : reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - 8800) S.

  (* ---- The footprint premises of the run.  The shadow covers are QUANTIFIED (shcov / shblk / shkov): a ground
     rng premise whose bounds hold a division would make every later lia pay for that division's Euclidean
     equations.  The ranges without a division stay ground, since StepF's solve_acc1 matches them in the
     context. SKW covers [S - 288, S - 128) only: the span of the real-stack frame [A - 128, A), its one use. ---- *)
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RWIN : rng RNG (S - 8800) 8800.
  Hypothesis SCW : shcov RNG (S - 8800) 8800.
  Hypothesis SKW : shkov RNG (S - 288) 160.
  Hypothesis RINF : 50 <= n -> rng RNG f 50.
  Hypothesis SCF : 50 <= n -> shcov RNG f 50.
  Hypothesis SKF : 50 <= n -> shkov RNG f 50.
  Hypothesis ROUT : o <> 0 -> rng RNG o 36.
  Hypothesis SCO : o <> 0 -> shcov RNG o 36.
  Hypothesis SKO : o <> 0 -> shkov RNG o 36.
  Hypothesis RBC : rng RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis SKBC : shkov RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis RFSS : rng RNG FS (fs_frame FS 0 0 - FS).
  Hypothesis RFLG : rng RNG (fs_flag FS 1 0) (fs_M 1).
  Hypothesis RFRM : rng RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SCFR : shcov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SKFR : shkov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis RFW1 : Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS).
  Hypothesis RTLS : forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
    Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k).

  (* reac_ctrl_parseF.v's Section SetupF names at this Section's variables (their generalized forms, applied to
     the same-named variables and hypotheses; read off `About` of each). *)
  Local Notation A := (@reac_ctrl_parseF.A S).
  Local Notation HA1 := (@reac_ctrl_parseF.HA1 f n o S fr Rf Rn Ro RS S16 Lfr).
  Local Notation STW0 := (@reac_ctrl_parseF.STW0 m S ST0).
  Local Notation SAVES := (@reac_ctrl_parseF.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).
  Local Notation Wf := (@reac_ctrl_parseF.Wf S FS).
  Local Notation FK := (@reac_ctrl_parseF.FK m S FS).
  Local Notation FLG := (@reac_ctrl_parseF.FLG FS).
  Local Notation OB := (@reac_ctrl_parseF.OB o).
  Local Notation app_range := (@reac_ctrl_parseF.app_range f n o S fr Rf Rn Ro Lfr).
  Local Notation fk_facts := (@reac_ctrl_parseF.fk_facts tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0).
  Local Notation rngF_frame := (@reac_ctrl_parseF.rngF_frame m f n o S FS fr RNG Rf Rn Ro RS S16 Lfr RWIN RFRM).
  Local Notation rngF_frame_cov := (@reac_ctrl_parseF.rngF_frame_cov m f n o S FS fr RNG Rf Rn Ro RS S16 Lfr SCW SCFR).
  Local Notation rngF_frame_kov := (@reac_ctrl_parseF.rngF_frame_kov m f n o S FS fr RNG Rf Rn Ro RS S16 Lfr SKW SKFR).
  Local Notation rngF_win_sh8 := (@reac_ctrl_parseF.rngF_win_sh8 f n o S fr RNG Rf Rn Ro S16 Lfr HHM HAE RBY SCW).
  Local Notation rngF_frame_blk := (@reac_ctrl_parseF.rngF_frame_blk tp m f n o S FS fr RNG Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0 SCW SCFR).
  Local Notation rngF_ob := (@reac_ctrl_parseF.rngF_ob m f n o S FS fr RNG Rf Rn Ro RS S16 Lfr RWIN ROUT RFRM).
  Local Notation rngF_ob_cov := (@reac_ctrl_parseF.rngF_ob_cov m f n o S FS fr RNG Rf Rn Ro RS S16 Lfr SCW SCO SCFR).
  Local Notation rngF_ob_kov := (@reac_ctrl_parseF.rngF_ob_kov m f n o S FS fr RNG Rf Rn Ro RS S16 Lfr SKW SKO SKFR).
  Local Notation x_flag_in := (@reac_ctrl_parseF.x_flag_in m FS X XF0 XB0).
  Local Notation x_ne_j := (@reac_ctrl_parseF.x_ne_j m f n o S FS fr Rf Rn Ro Lfr X XF0).
  Local Notation D_apart_frame := (@reac_ctrl_parseF.D_apart_frame tp m f n o S FS fr Rf Rn Ro RS Lfr X XF0 FP0).
  Local Notation dj_pair := (@reac_ctrl_parseF.dj_pair tp m f n o S FS X FP0).
  Local Notation BI := (@reac_ctrl_parseF.BI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m S).
  Local Notation KB := (@reac_ctrl_parseF.KB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS RNG).
  Local Notation fwords := (@reac_ctrl_parseF.fwords ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0 RWIN SCW RFRM SCFR).
  Local Notation aJ := (@reac_ctrl_parseF.aJ tp f n o S FS X).
  Local Notation aCL := reac_ctrl_parseF.aCL.
  Local Notation Qp := (@reac_ctrl_parseF.Qp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr X).
  Local Notation L_restore := (@reac_ctrl_parseF.L_restore ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG Rf Rn Ro Lfr X XF0 XB0 RWIN).
  Local Notation aout_rt := (@reac_ctrl_parseF.aout_rt tp m f n o S FS fr Rf Rn Ro RS Lfr HHM HAE AO0 X FP0).
  Local Notation aJ_free := (@reac_ctrl_parseF.aJ_free tp m f n o S FS fr Rf Rn Ro RS Lfr AC0 SR0 HHM HAE AO0 X FP0 TLS0).
  Local Notation Wex := (@reac_ctrl_parseF.Wex o S FS X).
  Local Notation Wexw := (@reac_ctrl_parseF.Wexw o S FS).
  Local Notation Wex_sub_w := (@reac_ctrl_parseF.Wex_sub_w o S FS X).
  Local Notation sh_hi_small_out := (@reac_ctrl_parseF.sh_hi_small_out m f n o S fr junk Rf Rn Ro RS Lfr HOK HHM AO0).
  Local Notation wex_sh_out := (@reac_ctrl_parseF.wex_sh_out tp m f n o S FS fr junk Rf Rn Ro RS S16 Lfr HOK HHM HAE AO0 X FP0).
  Local Notation Wex_free := (@reac_ctrl_parseF.Wex_free tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr AC0 SR0 HHM HAE AO0 X FP0 TLS0).
  Local Notation Wex_subfp := (@reac_ctrl_parseF.Wex_subfp tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X XF0 FP0).
  Local Notation subWf_Wex := (@reac_ctrl_parseF.subWf_Wex m f n o S FS fr Rf Rn Ro RS Lfr X).
  Local Notation Wsmall_outside := (@reac_ctrl_parseF.Wsmall_outside f n o S fr Rf Rn Ro Lfr).
  Local Notation ob_facts := (@reac_ctrl_parseF.ob_facts tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AO0 X XF0 FP0).
  Local Notation ob_wex := (@reac_ctrl_parseF.ob_wex m f n o S FS fr Rf Rn Ro RS S16 Lfr X).
  Local Notation Wex_subW := (@reac_ctrl_parseF.Wex_subW tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X XF0 FP0).
  Local Notation L_exit := (@reac_ctrl_parseF.L_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW RFLG RFRM SCFR).
  Local Notation Wall := (@reac_ctrl_parseF.Wall S FS).
  Local Notation mu_all := (@reac_ctrl_parseF.mu_all m f n o S FS fr Rf Rn Ro RS S16 Lfr).
  Local Notation f_facts := (@reac_ctrl_parseF.f_facts tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AF0 AO0 X XF0 FP0).
  Local Notation body_rt := (@reac_ctrl_parseF.body_rt tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AW0 AO0 X XF0 FP0).
  Local Notation flag_out_Wf := (@reac_ctrl_parseF.flag_out_Wf tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0).
  Local Notation L_join := (@reac_ctrl_parseF.L_join ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW RFLG RFRM SCFR).
  Local Notation BJ := (@reac_ctrl_parseF.BJ S).
  Local Notation stk_join_call := (@reac_ctrl_parseF.stk_join_call f n o S fr Rf Rn Ro RS Lfr).
  Local Notation bj_call := (@reac_ctrl_parseF.bj_call f n o S fr Rf Rn Ro RS Lfr).
  Local Notation bj_call0 := (@reac_ctrl_parseF.bj_call0 f n o S fr Rf Rn Ro RS Lfr).
  Local Notation ob_mx := (@reac_ctrl_parseF.ob_mx m f n o S FS fr Rf Rn Ro RS S16 Lfr AW0).
  Local Notation af_mx := (@reac_ctrl_parseF.af_mx tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AW0 AF0 AO0 X XF0 FP0).
  Local Notation af_mx2 := (@reac_ctrl_parseF.af_mx2 tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AW0 AF0 AO0 X XF0 FP0).
  Local Notation ro_mx := (@reac_ctrl_parseF.ro_mx tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK SR0 HHM HAE AF0 AO0 X XF0 FP0).
  Local Notation abc_mx := (@reac_ctrl_parseF.abc_mx tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AW0 AO0 ABC X XF0 FP0).
  Local Notation cl_mx := (@reac_ctrl_parseF.cl_mx tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AO0 HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 FP0).
  Local Notation abc_mx2 := (@reac_ctrl_parseF.abc_mx2 tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AW0 AO0 ABC X XF0 FP0).
  Local Notation cl_mx2 := (@reac_ctrl_parseF.cl_mx2 tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AO0 HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 FP0).
  Local Notation L_kind := (@reac_ctrl_parseF.L_kind ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW SKW ROUT SCO SKO RFLG RFRM SCFR SKFR).
  Local Notation L_be0 := (@reac_ctrl_parseF.L_be0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW SKW ROUT SCO SKO RFLG RFRM SCFR SKFR).
  Local Notation L_bdc := (@reac_ctrl_parseF.L_bdc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW SKW ROUT SCO SKO RFLG RFRM SCFR SKFR).
  Local Notation body_copy := (@reac_ctrl_parseF.body_copy ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR).
  Local Notation body_tail := (@reac_ctrl_parseF.body_tail ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR).
  Local Notation body_main := (@reac_ctrl_parseF.body_main ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMSET HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR).
  Local Notation body_holds := (@reac_ctrl_parseF.body_holds ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMSET HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR).

  (* The state at the entry of __asan_stack_malloc_1 (pc 0x3d72c), after the jal at 0x835e8. *)
  Definition PreCall : machine_state -> Prop :=
    fun ms => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 0x835ec) (Z_to_bv 64 A) gp tp t0' t1' t2' (Z_to_bv 64 S) (Z_to_bv 64 A)
                   (Z_to_bv 64 128) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n)
                   s7 s8 (wa ASAN_K) s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 ASAN_STACK_MALLOC_1) fc None m1 (seg_rom rsegs) /\
      munch [(S - 8800, S)] m m1 /\ wmono rsegs m m1 /\ rd_mono m m1 /\ mem_inv rsegs m1 /\
      rw_cells rsegs m1 (S - 96) SAVES /\ stk rsegs m1 (S - 8800) A.

  (* What holds at the release store of the side-stack frame fra = fs_frame FS 1 j: mc is the memory at 0x83920
     (the exit), m1 the memory at the store (mc with the frame's 16 shadow bytes and its word at fra rewritten). *)
  Definition RelFacts (fra j : Z) (mc m1 : word -> option byte) : Prop :=
    FK fra fra A j 1 (Z_to_bv 64 (fs_flag FS 1 j)) /\
    munch (Wex fra) m mc /\
    munch [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128)] mc m1 /\
    munch [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128); (fs_flag FS 1 j, fs_flag FS 1 j + 1)] mc m1 /\
    wmono rsegs mc m1 /\ wmono rsegs m m1 /\ rd_mono m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 (S - 8800) S /\
    rw_cells rsegs m1 (S - 96) SAVES /\
    (o <> 0 -> rw_cells rsegs mc o [CB 36 (snd (ctrlparse n fr))]) /\
    (exists h', bytes_at rsegs mc (fs_hint FS 1) (le8 h')) /\
    (exists flags', bytes_at rsegs mc (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') /\
    (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> ~ (fs_flag FS 1 j <= x < fs_flag FS 1 j + 1) ->
       mrd rsegs mc (wa x) = mrd rsegs m (wa x)) /\
    bytes_at rsegs m1 (fra + 120) (le8 (Z_to_bv 64 (fs_flag FS 1 j))).

  (* The state at the release store 0x83990 (before it): s2 = s8 = fra, a1 = fs_flag FS 1 j, sp = A. *)
  Definition RelSt : machine_state -> Prop :=
    fun ms => exists (fra j : Z) (mc m1 : word -> option byte)
                     (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
      ms = MS (mkR x1 (Z_to_bv 64 A) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
                   (Z_to_bv 64 (fs_flag FS 1 j)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fra) x19 x20 x21 x22
                   (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x83990) fc None m1 (seg_rom rsegs) /\
      RelFacts fra j mc m1.
End BndF.

(* ==== Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery) and its 09:58Z ruling): Module BndFOn
   re-derives Section BndF above, with the same names and scripts, for reac_ctrl_parseF.v's Module ParseFOn: the
   callees' `_F_on` contracts, SR0 : shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m, every reac_ctrl_parseF.v /
   split-file Section name redirected to its route-(C) module (ParseFOn, BndFOn, PreFOn, RelFOn, BodyFOn, PostFOn; the
   notation arguments read off `About` of each), and reac_ctrl_parseF.v's shadow edits where these scripts carry them
   (the region lemmas srw_* / frame_in_R; the post's forall-P form). Section BndF above stays identical outside comments.
   rule 24: no function proved beyond reac_ctrl_parseF.v's own run (proof-index reac_ctrl_parse 2026-10-29
   00:3xZ, exit 0: 12 named files + 8 lemma rows, plain / ubsan builds of other units; checker a Theorem Labs lane: CONFIRM). ==== *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF_on
  asan_memcpy_cF_on bcmp_wrap_c_on.
Local Open Scope Z_scope.

Module BndFOn.

Section BndF.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte) (RNG : ExecF.footprint).
  (* the callees, in their image-A footprint forms (above: __asan_memset / __asan_memcpy a Theorem Labs lane's shared texts;
     kind_of_link1's from kind_of_link1_c.v) *)
  Hypothesis HMSET : asan_memset_contract_F_on.
  Hypothesis HMCPY : asan_memcpy_contract_F_on.
  Hypothesis HBCMPW : bcmp_wrap_contract_F_on.
  Hypothesis HKOL : kind_of_link1_contract_F.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Rn : 0 <= n < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis RS : 8800 <= S < 2^64.
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (S - 8800) S.
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis Lfr : length fr = 50%nat.
  Hypothesis HF : 50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - 8800 \/ S <= f).
  Hypothesis Hrd : forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i.
  Hypothesis HOK : o <> 0 ->
    o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
    (o + 36 <= S - 8800 \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o).
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m.
  Hypothesis HHM : HIGHMEM_BEG <= S - 8800.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW0 : addressable m (S - 8800) 8800.
  Hypothesis AF0 : 50 <= n -> addressable m f 50.
  Hypothesis AO0 : o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o).
  Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
  Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
  Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
  Hypothesis HGCF : bytes_at rsegs m GOT_CF (le8 (wa CF)).
  Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
  Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
  (* The free frames X (class-1 frames in use by the caller, flag 1 at m, index below fs_M 1) and the side-stack
     premise in the free-frame form (fpx: the data ranges are apart from fp_wx [1] FS X, which leaves out X's frames
     and their shadow). *)
  Variable X : list (nat * Z).
  Hypothesis XF0 : Forall (fun ci => fst ci = 1%nat /\ bytes_at rsegs m (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X.
  Hypothesis XB0 : Forall (fun ci => 0 <= snd ci < fs_M 1) X.
  Hypothesis FP0 : fpx [1%nat] m (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X.
  Hypothesis TLS0 : reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - 8800) S.

  (* ---- The footprint premises of the run.  The shadow covers are QUANTIFIED (shcov / shblk / shkov): a ground
     rng premise whose bounds hold a division would make every later lia pay for that division's Euclidean
     equations.  The ranges without a division stay ground, since StepF's solve_acc1 matches them in the
     context. SKW covers [S - 288, S - 128) only: the span of the real-stack frame [A - 128, A), its one use. ---- *)
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RWIN : rng RNG (S - 8800) 8800.
  Hypothesis SCW : shcov RNG (S - 8800) 8800.
  Hypothesis SKW : shkov RNG (S - 288) 160.
  Hypothesis RINF : 50 <= n -> rng RNG f 50.
  Hypothesis SCF : 50 <= n -> shcov RNG f 50.
  Hypothesis SKF : 50 <= n -> shkov RNG f 50.
  Hypothesis ROUT : o <> 0 -> rng RNG o 36.
  Hypothesis SCO : o <> 0 -> shcov RNG o 36.
  Hypothesis SKO : o <> 0 -> shkov RNG o 36.
  Hypothesis RBC : rng RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis SKBC : shkov RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis RFSS : rng RNG FS (fs_frame FS 0 0 - FS).
  Hypothesis RFLG : rng RNG (fs_flag FS 1 0) (fs_M 1).
  Hypothesis RFRM : rng RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SCFR : shcov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SKFR : shkov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis RFW1 : Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS).
  Hypothesis RTLS : forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
    Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k).

  (* reac_ctrl_parseF.v's Section SetupF names at this Section's variables (their generalized forms, applied to
     the same-named variables and hypotheses; read off `About` of each). *)
  Local Notation A := (@reac_ctrl_parseF.ParseFOn.A S).
  Local Notation HA1 := (@reac_ctrl_parseF.ParseFOn.HA1 f n o S fr Rf Rn Ro RS S16 Lfr).
  Local Notation STW0 := (@reac_ctrl_parseF.ParseFOn.STW0 m S ST0).
  Local Notation SAVES := (@reac_ctrl_parseF.ParseFOn.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).
  Local Notation Wf := (@reac_ctrl_parseF.ParseFOn.Wf S FS).
  Local Notation FK := (@reac_ctrl_parseF.ParseFOn.FK m S FS).
  Local Notation FLG := (@reac_ctrl_parseF.ParseFOn.FLG FS).
  Local Notation OB := (@reac_ctrl_parseF.ParseFOn.OB o).
  Local Notation app_range := (@reac_ctrl_parseF.ParseFOn.app_range f n o S fr Rf Rn Ro Lfr).
  Local Notation fk_facts := (@reac_ctrl_parseF.ParseFOn.fk_facts tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0).
  Local Notation rngF_frame := (@reac_ctrl_parseF.ParseFOn.rngF_frame m f n o S FS fr RNG Rf Rn Ro RS S16 Lfr RWIN RFRM).
  Local Notation rngF_frame_cov := (@reac_ctrl_parseF.ParseFOn.rngF_frame_cov m f n o S FS fr RNG Rf Rn Ro RS S16 Lfr SCW SCFR).
  Local Notation rngF_frame_kov := (@reac_ctrl_parseF.ParseFOn.rngF_frame_kov m f n o S FS fr RNG Rf Rn Ro RS S16 Lfr SKW SKFR).
  Local Notation rngF_win_sh8 := (@reac_ctrl_parseF.ParseFOn.rngF_win_sh8 f n o S fr RNG Rf Rn Ro S16 Lfr HHM HAE RBY SCW).
  Local Notation rngF_frame_blk := (@reac_ctrl_parseF.ParseFOn.rngF_frame_blk tp m f n o S FS fr RNG Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0 SCW SCFR).
  Local Notation rngF_ob := (@reac_ctrl_parseF.ParseFOn.rngF_ob m f n o S FS fr RNG Rf Rn Ro RS S16 Lfr RWIN ROUT RFRM).
  Local Notation rngF_ob_cov := (@reac_ctrl_parseF.ParseFOn.rngF_ob_cov m f n o S FS fr RNG Rf Rn Ro RS S16 Lfr SCW SCO SCFR).
  Local Notation rngF_ob_kov := (@reac_ctrl_parseF.ParseFOn.rngF_ob_kov m f n o S FS fr RNG Rf Rn Ro RS S16 Lfr SKW SKO SKFR).
  Local Notation x_flag_in := (@reac_ctrl_parseF.ParseFOn.x_flag_in m FS X XF0 XB0).
  Local Notation x_ne_j := (@reac_ctrl_parseF.ParseFOn.x_ne_j m f n o S FS fr Rf Rn Ro Lfr X XF0).
  Local Notation D_apart_frame := (@reac_ctrl_parseF.ParseFOn.D_apart_frame tp m f n o S FS fr Rf Rn Ro RS Lfr X XF0 FP0).
  Local Notation dj_pair := (@reac_ctrl_parseF.ParseFOn.dj_pair tp m f n o S FS X FP0).
  Local Notation BI := (@reac_ctrl_parseF.ParseFOn.BI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m S).
  Local Notation KB := (@reac_ctrl_parseF.ParseFOn.KB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS RNG).
  Local Notation fwords := (@reac_ctrl_parseF.ParseFOn.fwords ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0 RWIN SCW RFRM SCFR).
  Local Notation aJ := (@reac_ctrl_parseF.ParseFOn.aJ tp m f n o S FS X).
  Local Notation aCL := reac_ctrl_parseF.ParseFOn.aCL.
  Local Notation Qp := (@reac_ctrl_parseF.ParseFOn.Qp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr X).
  Local Notation L_restore := (@reac_ctrl_parseF.ParseFOn.L_restore ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG Rf Rn Ro Lfr X XF0 XB0 RWIN).
  Local Notation aout_rt := (@reac_ctrl_parseF.ParseFOn.aout_rt tp m f n o S FS fr Rf Rn Ro RS Lfr HHM HAE AO0 X FP0).
  Local Notation aJ_free := (@reac_ctrl_parseF.ParseFOn.aJ_free tp m f n o S FS fr Rf Rn Ro RS Lfr AC0 HHM HAE AO0 X FP0 TLS0).
  Local Notation Wex := (@reac_ctrl_parseF.ParseFOn.Wex o S FS X).
  Local Notation Wexw := (@reac_ctrl_parseF.ParseFOn.Wexw o S FS).
  Local Notation Wex_sub_w := (@reac_ctrl_parseF.ParseFOn.Wex_sub_w o S FS X).
  Local Notation sh_hi_small_out := (@reac_ctrl_parseF.ParseFOn.sh_hi_small_out m f n o S fr junk Rf Rn Ro RS Lfr HOK HHM AO0).
  Local Notation wex_sh_out := (@reac_ctrl_parseF.ParseFOn.wex_sh_out tp m f n o S FS fr junk Rf Rn Ro RS S16 Lfr HOK HHM HAE AO0 X FP0).
  Local Notation Wex_free := (@reac_ctrl_parseF.ParseFOn.Wex_free tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr AC0 SR0 HHM HAE AO0 X FP0 TLS0).
  Local Notation Wex_subfp := (@reac_ctrl_parseF.ParseFOn.Wex_subfp tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X XF0 FP0).
  Local Notation subWf_Wex := (@reac_ctrl_parseF.ParseFOn.subWf_Wex m f n o S FS fr Rf Rn Ro RS Lfr X).
  Local Notation Wsmall_outside := (@reac_ctrl_parseF.ParseFOn.Wsmall_outside f n o S fr Rf Rn Ro Lfr).
  Local Notation ob_facts := (@reac_ctrl_parseF.ParseFOn.ob_facts tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AO0 X XF0 FP0).
  Local Notation ob_wex := (@reac_ctrl_parseF.ParseFOn.ob_wex m f n o S FS fr Rf Rn Ro RS S16 Lfr X).
  Local Notation Wex_subW := (@reac_ctrl_parseF.ParseFOn.Wex_subW tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X XF0 FP0).
  Local Notation L_exit := (@reac_ctrl_parseF.ParseFOn.L_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW RFLG RFRM SCFR).
  Local Notation Wall := (@reac_ctrl_parseF.ParseFOn.Wall S FS).
  Local Notation mu_all := (@reac_ctrl_parseF.ParseFOn.mu_all m f n o S FS fr Rf Rn Ro RS S16 Lfr).
  Local Notation f_facts := (@reac_ctrl_parseF.ParseFOn.f_facts tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AF0 AO0 X XF0 FP0).
  Local Notation body_rt := (@reac_ctrl_parseF.ParseFOn.body_rt tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AW0 AO0 X XF0 FP0).
  Local Notation flag_out_Wf := (@reac_ctrl_parseF.ParseFOn.flag_out_Wf tp m f n o S FS fr Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0).
  Local Notation L_join := (@reac_ctrl_parseF.ParseFOn.L_join ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW RFLG RFRM SCFR).
  Local Notation BJ := (@reac_ctrl_parseF.ParseFOn.BJ S).
  Local Notation stk_join_call := (@reac_ctrl_parseF.ParseFOn.stk_join_call f n o S fr Rf Rn Ro RS Lfr).
  Local Notation bj_call := (@reac_ctrl_parseF.ParseFOn.bj_call f n o S fr Rf Rn Ro RS Lfr).
  Local Notation bj_call0 := (@reac_ctrl_parseF.ParseFOn.bj_call0 f n o S fr Rf Rn Ro RS Lfr).
  Local Notation ob_mx := (@reac_ctrl_parseF.ParseFOn.ob_mx m f n o S FS fr Rf Rn Ro RS S16 Lfr AW0).
  Local Notation af_mx := (@reac_ctrl_parseF.ParseFOn.af_mx tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AW0 AF0 AO0 X XF0 FP0).
  Local Notation af_mx2 := (@reac_ctrl_parseF.ParseFOn.af_mx2 tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AW0 AF0 AO0 X XF0 FP0).
  Local Notation ro_mx := (@reac_ctrl_parseF.ParseFOn.ro_mx tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK SR0 HHM HAE AF0 AO0 X XF0 FP0).
  Local Notation abc_mx := (@reac_ctrl_parseF.ParseFOn.abc_mx tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AW0 AO0 ABC X XF0 FP0).
  Local Notation cl_mx := (@reac_ctrl_parseF.ParseFOn.cl_mx tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AO0 HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 FP0).
  Local Notation abc_mx2 := (@reac_ctrl_parseF.ParseFOn.abc_mx2 tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AW0 AO0 ABC X XF0 FP0).
  Local Notation cl_mx2 := (@reac_ctrl_parseF.ParseFOn.cl_mx2 tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HF HOK SR0 HHM HAE AO0 HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 FP0).
  Local Notation L_kind := (@reac_ctrl_parseF.ParseFOn.L_kind ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW SKW ROUT SCO SKO RFLG RFRM SCFR SKFR).
  Local Notation L_be0 := (@reac_ctrl_parseF.ParseFOn.L_be0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW SKW ROUT SCO SKO RFLG RFRM SCFR SKFR).
  Local Notation L_bdc := (@reac_ctrl_parseF.ParseFOn.L_bdc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG Rf Rn Ro RS S16 ST0 Lfr HF HOK AC0 SR0 HHM HAE AW0 AO0 X XF0 XB0 FP0 TLS0 RWIN SCW SKW ROUT SCO SKO RFLG RFRM SCFR SKFR).
  Local Notation body_copy := (@reac_ctrl_parseF.ParseFOn.body_copy ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR).
  Local Notation body_tail := (@reac_ctrl_parseF.ParseFOn.body_tail ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR).
  Local Notation body_main := (@reac_ctrl_parseF.ParseFOn.body_main ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMSET HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR).
  Local Notation body_holds := (@reac_ctrl_parseF.ParseFOn.body_holds ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMSET HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR).

  (* The state at the entry of __asan_stack_malloc_1 (pc 0x3d72c), after the jal at 0x835e8. *)
  Definition PreCall : machine_state -> Prop :=
    fun ms => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 0x835ec) (Z_to_bv 64 A) gp tp t0' t1' t2' (Z_to_bv 64 S) (Z_to_bv 64 A)
                   (Z_to_bv 64 128) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n)
                   s7 s8 (wa ASAN_K) s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 ASAN_STACK_MALLOC_1) fc None m1 (seg_rom rsegs) /\
      munch [(S - 8800, S)] m m1 /\ wmono rsegs m m1 /\ rd_mono m m1 /\ mem_inv rsegs m1 /\
      rw_cells rsegs m1 (S - 96) SAVES /\ stk rsegs m1 (S - 8800) A.

  (* What holds at the release store of the side-stack frame fra = fs_frame FS 1 j: mc is the memory at 0x83920
     (the exit), m1 the memory at the store (mc with the frame's 16 shadow bytes and its word at fra rewritten). *)
  Definition RelFacts (fra j : Z) (mc m1 : word -> option byte) : Prop :=
    FK fra fra A j 1 (Z_to_bv 64 (fs_flag FS 1 j)) /\
    munch (Wex fra) m mc /\
    munch [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128)] mc m1 /\
    munch [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128); (fs_flag FS 1 j, fs_flag FS 1 j + 1)] mc m1 /\
    wmono rsegs mc m1 /\ wmono rsegs m m1 /\ rd_mono m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 (S - 8800) S /\
    rw_cells rsegs m1 (S - 96) SAVES /\
    (o <> 0 -> rw_cells rsegs mc o [CB 36 (snd (ctrlparse n fr))]) /\
    (exists h', bytes_at rsegs mc (fs_hint FS 1) (le8 h')) /\
    (exists flags', bytes_at rsegs mc (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') /\
    (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> ~ (fs_flag FS 1 j <= x < fs_flag FS 1 j + 1) ->
       mrd rsegs mc (wa x) = mrd rsegs m (wa x)) /\
    bytes_at rsegs m1 (fra + 120) (le8 (Z_to_bv 64 (fs_flag FS 1 j))).

  (* The state at the release store 0x83990 (before it): s2 = s8 = fra, a1 = fs_flag FS 1 j, sp = A. *)
  Definition RelSt : machine_state -> Prop :=
    fun ms => exists (fra j : Z) (mc m1 : word -> option byte)
                     (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
      ms = MS (mkR x1 (Z_to_bv 64 A) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
                   (Z_to_bv 64 (fs_flag FS 1 j)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fra) x19 x20 x21 x22
                   (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x83990) fc None m1 (seg_rom rsegs) /\
      RelFacts fra j mc m1.
End BndF.

End BndFOn.
