(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3501 of its 3539 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_ctrl_parseF.v, with its module paths, module names, addresses and numbers changed; 1785 of its 2030 lines of code are new or changed and 3294 lines of the source are left out. *)
(* reac_ctrl_parse, image A (asan, fuzz_ctrl v1.9.0): the stretch after __asan_stack_malloc_1, RE-BASED for the
   cgif-form walk (a Theorem Labs lane 23:53Z ruling (2): a re-based Section copy, the instruction proofs verbatim, every
   re-proved helper named here).  The walk instantiates the Section's base memory m with the memory at the return of
   __asan_stack_malloc_1 with flag jj read as 0 (so FK's flag fact, x_ne_j and Qp's class-1 flag clause hold as
   in reac_ctrl_parseF.v), and needs the run's EXACT writes for its journal step.  From reac_ctrl_parseF_post.v /
   _rel.v / reac_ctrl_parseF.v, with these changes only:
   - the body is reac_ctrl_parseF_rbody.v's (Wf2: Wf without the hint word; HEXIT with the exact-writes premise);
   - RelSt2 (new): reac_ctrl_parseF_bnd.v's RelSt for the frame fra, plus the exact writes from m to the memory at
     the release store (munch (Wf2 fra j 1 ++ [(ob, ob + 36)]) m m1); QX uses it;
   - L_exit_x: reac_ctrl_parseF_post.v's, with HEXIT's extra premise (intro'd as HXW) and its last lines building
     RelSt2 (the exact writes: munch_trans of HXW and the exit's own MUe);
   - L_restore2: reac_ctrl_parseF.v's L_restore (:1825) whose post also states the final memory (ms_mem ms = m');
   - post_release_F2: reac_ctrl_parseF_rel.v's post_release_F with L_restore2 for L_restore, so its post states the
     final memory too;
   - post_call_F2 (new): the entry's side arm (reac_ctrl_parseF.v :1792-1796 steps, verbatim) from premises the walk
     supplies at the return memory (flag jj 1 there, 0 at m; the back pointer; the class-1 flag array; SAVES);
   - post_all_F2 (new): post_call_F2, the release store (reac_ctrl_parseF.v :2512-2538, as reac_ctrl_parseF_cut.v (not in this delivery)
     steps it) and post_release_F2, to QF: Qp, the exact writes from m, and flag jj back to 0.
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_parseF_bnd.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_parseF_rbody.

(* This file's step hooks: reac_ctrl_parseF.v's (its acc_hint / mem_after_store_opt redefinitions are Local there). *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= acc_hintF.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= rcpF_store_opt.

(* reac_ctrl_parseF.v:373-383, the store tracking of the rd_mono facts, here as this file's own. *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [lib.Lib.Frame.inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Section RPostF.
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
  Local Notation aout_rt := (@reac_ctrl_parseF.aout_rt tp m f n o S FS fr junk Rf Rn Ro RS Lfr HOK HHM HAE AO0 X FP0).
  Local Notation aJ_free := (@reac_ctrl_parseF.aJ_free tp m f n o S FS fr junk Rf Rn Ro RS Lfr HOK AC0 SR0 HHM HAE AO0 X FP0 TLS0).
  Local Notation Wex := (@reac_ctrl_parseF.Wex o S FS X).
  Local Notation Wexw := (@reac_ctrl_parseF.Wexw o S FS).
  Local Notation Wex_sub_w := (@reac_ctrl_parseF.Wex_sub_w o S FS X).
  Local Notation sh_hi_small_out := (@reac_ctrl_parseF.sh_hi_small_out m f n o S fr junk Rf Rn Ro RS Lfr HOK HHM AO0).
  Local Notation wex_sh_out := (@reac_ctrl_parseF.wex_sh_out tp m f n o S FS fr junk Rf Rn Ro RS S16 Lfr HOK HHM HAE AO0 X FP0).
  Local Notation Wex_free := (@reac_ctrl_parseF.Wex_free tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HOK AC0 SR0 HHM HAE AO0 X FP0 TLS0).
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
  (* the cut points of reac_ctrl_parseF_bnd.v, at this Section's variables *)
  Local Notation PreCall := (@reac_ctrl_parseF_bnd.PreCall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S).
  Local Notation RelFacts := (@reac_ctrl_parseF_bnd.RelFacts ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m n o S FS fr X).
  Local Notation RelSt := (@reac_ctrl_parseF_bnd.RelSt ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n o S FS fr X).


  (* reac_ctrl_parseF_rbody.v's KBx, fwords_x and Wf2 at this Section's variables (body_holds_x is applied by eapply). *)
  Local Notation Wf2 := (@reac_ctrl_parseF_rbody.Wf2 S FS).
  Local Notation KBx := (@reac_ctrl_parseF_rbody.KBx ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS RNG).
  Local Notation fwords_x := (@reac_ctrl_parseF_rbody.fwords_x ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0 RWIN SCW RFRM SCFR).

  (* reac_ctrl_parseF.v :1412-1438, the store tactics of the frame block and the exit *)
  Ltac wst a nn tac :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; tac | eassumption | lia | lia ])
    end.

  Ltac wstb a nn base fact :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
                  match goal with |- wview _ _ (wa ?X) <> None => replace X with (base + (X - base)) by lia end;
                  apply fact; lia
                | eassumption | lia | lia ])
    end.

  (* A tracked poison store of one shadow byte at base + off (= base + Z.of_nat nn): the stored byte joins the
     frame-shadow cells so that the box's addressability can be read back. *)
  Ltac sstep base off nn fact :=
    wstb (base + off) 1%nat base fact; step;
    replace (base + off) with (base + Z.of_nat nn) by lia;
    rewrite rc_le1_lit; mem_after_store.

  (* RelSt of reac_ctrl_parseF_bnd.v for the frame fra, with the exact writes from m to the memory at the store. *)
  Definition RelSt2 (fra : Z) : machine_state -> Prop :=
    fun ms => exists (j : Z) (mc m1 : word -> option byte)
                     (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
      ms = MS (mkR x1 (Z_to_bv 64 A) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
                   (Z_to_bv 64 (fs_flag FS 1 j)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fra) x19 x20 x21 x22
                   (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x83990) fc None m1 (seg_rom rsegs) /\
      RelFacts fra j mc m1 /\
      (exists ob, OB fra ob /\ munch (Wf2 fra j 1 ++ [(ob, ob + 36)]) m m1).

  (* The exit's post: Qp for the real-stack frame (fv = 0), RelSt2 at the release store for a side-stack frame. *)
  Definition QX (fv : Z) : machine_state -> Prop :=
    fun ms => (fv = 0 /\ Qp ms) \/ (fv <> 0 /\ RelSt2 fv ms).

  (* reac_ctrl_parseF_post.v's (not in this delivery) L_exit_x (L_exit of reac_ctrl_parseF.v :2308 up to the release store), with HEXIT's
     exact-writes premise, which it carries to RelSt2. *)
  Lemma L_exit_x : forall fra fv spc j nn w120 mc
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 ->
    munch (Wex fra) m mc ->
    wmono rsegs m mc -> rd_mono m mc -> mem_inv rsegs mc ->
    asan_cells mc -> shadow_rw mc -> stk rsegs mc (S - 8800) S ->
    rw_cells rsegs mc (S - 96) SAVES ->
    (o <> 0 -> rw_cells rsegs mc o [CB 36 (snd (ctrlparse n fr))]) ->
    (exists h', bytes_at rsegs mc (fs_hint FS 1) (le8 h')) ->
    (exists flags', bytes_at rsegs mc (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') ->
    (nn = 1 -> bytes_at rsegs mc (fra + 120) (le8 w120)) ->
    (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> ~ (fs_flag FS 1 j <= x < fs_flag FS 1 j + nn) ->
       mrd rsegs mc (wa x) = mrd rsegs m (wa x)) ->
    (exists ob, OB fra ob /\ munch (Wf2 fra j nn ++ [(ob, ob + 36)]) m mc) ->
    evtF rsegs RNG (QX fv)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fv) x19 x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K))
               (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83920) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31
      HK MU WM RM MI AC SR ST SV HBox Hhint Hflags Hw120 FKP HXW.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _ & HFSb & _ & HWd & HDd).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (Ush : bv_unsigned (Z_to_bv 64 (fra / 8 + ASAN_K)) = fra / 8 + ASAN_K)
      by (apply unsigned_lit; clear -SH1 SH2; lia).
    assert (Ufra : bv_unsigned (Z_to_bv 64 fra) = fra)
      by (apply unsigned_lit; clear -FRlo FRhi HAhi RS Pfs0; lia).
    assert (HHMl : 17594333495296 <= S - 8800)
      by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    (* the munch from m (over Wex, whose fp_wx part has an abstract X) is kept out of the store tracking; the exit's
       own writes are tracked from mc on the tight footprints MUe / MUx, and the two are composed at the end *)
    pose proof (conj MU I) as MUn. clear MU.
    pose proof HK as HKc.
    pose proof (munch_refl [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 128)] mc) as MUe.
    pose proof (munch_refl [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 128);
                            (fs_flag FS 1 j, fs_flag FS 1 j + 1)] mc) as MUx.
    pose proof (wmono_refl rsegs mc) as WMe.
    pose proof (munch_refl [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 8)] mc) as MUw.
    unfold shadow_addr in MUe, MUx, MUw.
    step.
    wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    step. step.
    wstb fra 8%nat fra FW. step. store_done.
    destruct HK as [(Efv & Efra & Espc & Ej & Enn) | (Hj & Efra & Efv & Espc & Ew120 & Enn & Hfl0)].
    - (* real-stack frame: fv = 0 *)
      subst fv. step.
      replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbv iota.
      match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        pose proof (shadow_rw_mono m mcur SR0 WM RM) as SRc;
        pose proof (shadow16_stk mcur fra SRc ltac:(clear -FRlo Pfs0; lia) FRA
                      ltac:(clear -SH1; lia) ltac:(clear -SH2; lia)) as STsh
      end.
      pose proof (stk_carve rsegs _ (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16) 16%nat STsh ltac:(clear -SH1; lia))
        as [STsh' [junkS SHC]].
      replace (fra / 8 + ASAN_K + 16 - Z.of_nat 16) with (fra / 8 + ASAN_K) in SHC by lia.
      sstep (fra / 8 + ASAN_K) 4 4%nat SW. sstep (fra / 8 + ASAN_K) 5 5%nat SW.
      sstep (fra / 8 + ASAN_K) 6 6%nat SW. sstep (fra / 8 + ASAN_K) 7 7%nat SW.
      sstep (fra / 8 + ASAN_K) 0 0%nat SW. sstep (fra / 8 + ASAN_K) 1 1%nat SW.
      sstep (fra / 8 + ASAN_K) 2 2%nat SW. sstep (fra / 8 + ASAN_K) 3 3%nat SW.
      sstep (fra / 8 + ASAN_K) 12 12%nat SW. sstep (fra / 8 + ASAN_K) 13 13%nat SW.
      sstep (fra / 8 + ASAN_K) 14 14%nat SW. sstep (fra / 8 + ASAN_K) 15 15%nat SW.
      sstep (fra / 8 + ASAN_K) 8 8%nat SW. sstep (fra / 8 + ASAN_K) 9 9%nat SW.
      sstep (fra / 8 + ASAN_K) 10 10%nat SW. sstep (fra / 8 + ASAN_K) 11 11%nat SW.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      assert (EFL : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      pose proof (FAP 0 ltac:(lia)) as Hfraapp. rewrite Z.add_0_r in Hfraapp.
      assert (Hfe : fra + 128 <= APPMEM_END) by (clear -FRhi HAhi RS HAE; unfold APPMEM_END in *; lia).
      destruct SHC as [[_ HB16] _]. cbn [cells_bytes cbytes app] in HB16.
      destruct Hhint as [h' Hh]. destruct Hflags as [flags' (Hfl & Hfllen & HflF)].
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
        assert (MU : munch (Wex fra) m mf)
          by (apply (munch_trans _ m mc mf (proj1 MUn)); eapply munch_weaken; [|exact MUe];
              intros y Hy; unfold reac_ctrl_parseF.Wex, shadow_addr in Hy; cbn [outside] in Hy |- *;
              destruct Hy as (H1 & H2 & _); exact (conj H1 (conj H2 I)))
      end.
      apply (evtF_mono _ _ Qp); [| intros ms' Hq; left; split; [reflexivity | exact Hq]].
      eapply L_restore.
      + exact SV.
      + eapply munch_weaken; [exact (Wex_subfp fra 0 spc j nn w120 HKc) | exact MU].
      + exact WM.
      + exact MI.
      + exact ST.
      + intros Ho. eapply acl_rw; [exact (HBox Ho) | exact MUe | exact WMe |].
        intros y Hy. apply Wsmall_outside; [clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2 | |].
        * destruct (AO0 Ho) as (AOa & _ & _). pose proof (acl_app_in m o 36 (y - o) AOa ltac:(cbn [cells_size csize] in Hy; lia)) as Hya.
          replace (o + (y - o)) with y in Hya by lia. exact Hya.
        * destruct (HOK Ho) as (_ & _ & _ & HowS & _). rewrite Efra.
          cbn [cells_size csize] in Hy. destruct HowS as [Hc|Hc]; [left | right]; clear -Hy Hc HAlo HAhi RS; lia.
      + lazymatch goal with |- aJ ?mf =>
          assert (Hz16 : forall g, 0 <= g <= 15 ->
                    exists b, mrd rsegs mf (wa (fra / 8 + ASAN_K + g)) = Some b /\ bv_signed b = 0);
          [ destruct HB16 as (_ & _ & Hr); intros g Hg; exists (Z_to_bv 8 0); split; [|vm_compute; reflexivity];
            pose proof (Hr (Z.to_nat g) ltac:(cbn [length]; lia)) as Hg';
            replace (fra / 8 + ASAN_K + Z.of_nat (Z.to_nat g)) with (fra / 8 + ASAN_K + g) in Hg' by lia;
            rewrite Hg';
            assert (Hc : g=0\/g=1\/g=2\/g=3\/g=4\/g=5\/g=6\/g=7\/g=8\/g=9\/g=10\/g=11\/g=12\/g=13\/g=14\/g=15) by lia;
            repeat (destruct Hc as [Hc|Hc]); subst g; vm_compute; reflexivity
          | ];
          assert (AFR : addressable mf fra 128)
            by (apply frame_all_addr; [clear -FRlo Pfs0; lia | exact FR8 | exact Hfe | exact FAP | exact Hz16]);
          assert (ABLO : addressable mf (S - 8800) (fra - (S - 8800)));
          [ apply (acl_addr_munch (Wex fra) m mf (S - 8800) (fra - (S - 8800)));
            [ apply (acl_addr_sub m (S - 8800) 8800 (S - 8800) (fra - (S - 8800)) AW0);
                [ lia | clear -FRlo HAlo HAhi RS Efra; rewrite Efra; lia | clear -FRlo HAlo HAhi RS Efra; rewrite Efra; lia ]
            | exact MU
            | intros i Hi; apply wex_sh_out;
                [ clear -FRlo Pfs0; lia | exact FR8 | exact Hfraapp | exact Hfe
                | clear -Hi FRlo HAlo HAhi RS Efra; rewrite Efra in *; lia | left; clear -Hi; lia ] ]
          | ];
          assert (AABOVE : addressable mf (fra + 128) (S - (fra + 128)));
          [ apply (acl_addr_munch (Wex fra) m mf (fra + 128) (S - (fra + 128)));
            [ apply (acl_addr_sub m (S - 8800) 8800 (fra + 128) (S - (fra + 128)) AW0);
                [ clear -FRlo HAlo HAhi RS Efra; rewrite Efra; lia | clear -FRhi HAhi RS Efra; rewrite Efra; lia
                | clear -FRhi HAhi RS Efra; rewrite Efra; lia ]
            | exact MU
            | intros i Hi; apply wex_sh_out;
                [ clear -FRlo Pfs0; lia | exact FR8 | exact Hfraapp | exact Hfe
                | clear -Hi FRhi HAlo HAhi RS Efra; rewrite Efra in *; lia | right; clear -Hi; lia ] ]
          | ];
          assert (AWfinal : addressable mf (S - 8800) 8800);
          [ pose proof (acl_addr_join mf (S - 8800) (fra - (S - 8800)) 128 ABLO
                         ltac:(replace (S - 8800 + (fra - (S - 8800))) with fra by (clear; lia); exact AFR)
                         ltac:(lia)) as J1;
            pose proof (acl_addr_join mf (S - 8800) (fra - (S - 8800) + 128) (S - (fra + 128)) J1
                         ltac:(replace (S - 8800 + (fra - (S - 8800) + 128)) with (fra + 128) by (clear; lia); exact AABOVE)
                         ltac:(clear -FRhi HAhi RS Efra; rewrite Efra; lia)) as J2;
            exact (acl_addr_sub mf (S - 8800) (fra - (S - 8800) + 128 + (S - (fra + 128))) (S - 8800) 8800 J2
                     ltac:(lia) ltac:(lia) ltac:(clear; lia))
          | ];
          assert (Hfree : asan_cells mf /\ shadow_rw mf /\
                    fpx [1%nat] mf (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
                    reac_ctrl_parse_tls mf (bv_unsigned tp) FS (S - 8800) S);
          [ apply (Wex_free fra 0 spc j nn w120 mf HKc MU WM RM);
            [ exists h'; eapply fl_bytes; [exact Hh | exact MUe |];
              intros y Hy; unfold fs_hint in Hy; rewrite length_le8 in Hy; cbn [Z.of_nat] in Hy;
              apply Wsmall_outside;
                [ clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2
                | apply Pfsapp; unfold FS_SIZE; lia
                | left; lia ]
            | exists flags'; split; [|split; [exact Hfllen | exact HflF]];
              eapply fl_bytes; [exact Hfl | exact MUe |];
              intros y Hy; rewrite Hfllen, EM1, EFL in Hy;
              apply Wsmall_outside;
                [ clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2
                | apply Pfsapp; unfold FS_SIZE; lia
                | left; lia ] ]
          | ];
          destruct Hfree as (Hac & Hsw & Hfp & Htl);
          split; [exact Hac|]; split; [exact Hsw|]; split; [exact AWfinal|]; split; [exact Hfp | exact Htl]
        end.
      + intros x Hx.
        assert (Hxr : FS + 20480 <= x < FS + 28672) by (rewrite EFL, EM1 in Hx; clear -Hx; lia).
        lazymatch goal with |- mrd rsegs ?mf (wa x) = _ =>
          rewrite (munch_mrd_out _ mc mf x MUe ltac:(clear -Hxr Pfs0 HFSb RS; lia)
                     ltac:(apply Wsmall_outside;
                             [ clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2
                             | apply Pfsapp; unfold FS_SIZE; clear -Hxr; lia
                             | left; clear -Hxr FRlo; lia ]))
        end.
        apply FKP; [exact Hx | rewrite Enn; clear; lia].
    - (* side-stack frame: fv = fra <> 0 *)
      subst fv.
      pose proof (Hw120 Enn) as Hw120'.
      step.
      rewrite (rc_neq0_64 fra) by (clear -FRlo FRhi HAhi RS Pfs0; lia). cbn [negb]. cbv iota.
      step.
      wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 0) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 1) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 2) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 3) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 12) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 13) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 14) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 15) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 9) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 10) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 11) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      pose proof (fl_bytes _ mc _ (fra + 120) (le8 w120) Hw120' MUw
        ltac:(intros x Hx; rewrite length_le8 in Hx; cbn [Z.of_nat] in Hx; cbn [outside];
              split; [| split; [| exact I]];
              [ intros [HL HR]; apply (acl_app_not_shadow x);
                [ replace x with (fra + (x - fra)) by lia; apply FAP; lia
                | replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia;
                  apply frame_shadow_in;
                  [ clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia ] ]
              | intros [HL HR]; clear -Hx HL HR; lia ])) as Hw120m.
      pose proof (bytes_ro8 _ (fra + 120) w120 Hw120m) as Hw120c.
      step.
      subst w120.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      rewrite EM1 in Hj.
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (EFLj : fs_flag FS 1 j = FS + 20480 + j)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (Rfl : 0 <= fs_flag FS 1 j < 2 ^ 64)
        by (rewrite EFLj; clear -Pfs0 HFSb HAE Hj; unfold APPMEM_END in *; lia).
      assert (Uflag : bv_unsigned (Z_to_bv 64 (fs_flag FS 1 j)) = fs_flag FS 1 j)
        by (apply unsigned_lit; exact Rfl).
      assert (SOK : store_ok rsegs m1 (wa (fs_flag FS 1 j)) 1 = true).
      { eapply (wv_store_ok m m1 (fs_flag FS 1 j) 1%nat).
        - intros i Hi. replace (fs_flag FS 1 j + i) with (fs_flag FS 1 j) by (cbn in Hi; lia).
          apply (stk_wv m FS (FS + FS_SIZE) (fs_flag FS 1 j) Pfsstk).
          rewrite EFLj; clear -Pfs0 HFSb Hj; unfold FS_SIZE; lia.
        - exact WM.
        - clear -Rfl; lia.
        - clear -Rfl; cbn; lia. }
      assert (RGFLj : rng RNG (fs_flag FS 1 j) 1).
      { assert (EMj : fs_M 1 = 8192) by reflexivity.
        eapply rng_sub; [exact RFLG | rewrite !fs_flag1; lia | rewrite !fs_flag1; lia]. }
      apply evtF_done. right. split; [clear -FRlo Pfs0; lia|].
      subst spc nn. unfold RelSt2.
      exists j, mc, m1, x1, x5, x6, x7, x9, x11, x12, x13, x14, x15, x16, x19, x20, x21, x22, x25, x26, x28, x29,
        x30, x31.
      split; [reflexivity|].
      split.
      { unfold reac_ctrl_parseF_bnd.RelFacts.
        refine (conj HKc (conj (proj1 MUn) (conj MUe (conj MUx (conj WMe (conj WM (conj RM (conj MI (conj ST
          (conj SV (conj HBox (conj Hhint (conj Hflags (conj FKP Hw120m)))))))))))))). }
      (* the exact writes from m: the body's (HXW) and the exit's own (MUe: the frame shadow and the frame) *)
      destruct HXW as [ob [HOB MUa]]. exists ob. split; [exact HOB|].
      eapply munch_trans; [exact MUa|].
      eapply munch_weaken; [|exact MUe]. intros x Hx. unfold reac_ctrl_parseF_rbody.Wf2 in Hx. cbn [app outside] in Hx |- *.
      destruct Hx as (_ & _ & _ & H4 & H5 & _ & _). unfold shadow_addr in H5.
      split; [exact H5|]. split; [exact H4 | exact I].
  Qed.


  (* L_restore of reac_ctrl_parseF.v (:1825), its post also stating the final memory (the restore stores nothing). *)
  Lemma L_restore2 : forall (m' : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (spc : Z),
    rw_cells rsegs m' (S - 96) SAVES ->
    munch (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++ [(shadow_addr (S - 8800), shadow_addr S)]) m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - 8800) S ->
    (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) -> aJ m' ->
    (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> mrd rsegs m' (wa x) = mrd rsegs m (wa x)) ->
    evtF rsegs RNG (fun ms => Qp ms /\ ms_mem ms = m')
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x839d8) fc None m' (seg_rom rsegs)).
  Proof.
    intros m' x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 spc
      FR MU WM MI ST HBox HaJ HFK.
    unfold SAVES in FR.
    replace (S - 96) with (S + -96) in FR by lia.
    do 14 step. step.
    apply evtF_done. split; [|reflexivity]. unfold Qp. destruct HaJ as (AC & SW & AW & FP & TL).
    do 14 eexists. exists m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact HBox|]. split; [exact AC|]. split; [exact SW|]. split; [exact AW|].
    split; [exact FP|]. split; [|split; [|exact TL]].
    - apply Forall_forall. intros ci Hin. destruct (proj1 (Forall_forall _ _) XF0 ci Hin) as (_ & Hb).
      destruct (x_flag_in ci Hin) as (E & L1 & L2).
      apply (bytes_keep m m' _ _ Hb). intros x Hx. cbn [length Z.of_nat Pos.of_succ_nat] in Hx.
      rewrite E in Hx. apply HFK. clear -Hx L1 L2. lia.
    - intros fl Hl Hb. apply (bytes_keep m m' _ _ Hb). intros x Hx. apply HFK.
      pose proof (len_le_M fl Hl) as Hl'. clear -Hx Hl'. lia.
  Qed.

  (* reac_ctrl_parseF_rel.v's post_release_F with L_restore2 (its post states the final memory): L_exit's side arm
     after the release store: `j 0x839d8`, then L_restore. *)
  Lemma post_release_F2 : forall (fra j : Z) (mc m1 : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    RelFacts fra j mc m1 ->
    evtF rsegs RNG (fun ms => Qp ms /\ ms_mem ms = write_to_mem m1 (wa (fs_flag FS 1 j)) [Z_to_bv 8 0])
      (MS (mkR x1 (Z_to_bv 64 A) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               (Z_to_bv 64 (fs_flag FS 1 j)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fra) x19 x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83994) fc None (write_to_mem m1 (wa (fs_flag FS 1 j)) [Z_to_bv 8 0]) (seg_rom rsegs)).
  Proof.
    intros fra j mc m1 x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 HR.
    unfold reac_ctrl_parseF_bnd.RelFacts in HR.
    destruct HR as (HKc & MUn0 & MUe & MUx & WMe & WM & RM & MI & ST & SV & HBox & Hhint & Hflags & FKP & Hw120m).
    pose proof (conj MUn0 I) as MUn. clear MUn0.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _ & HFSb & _ & HWd & HDd).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fra A j 1 (Z_to_bv 64 (fs_flag FS 1 j)) HKc) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HKc as HK.
    destruct HK as [(Efv & _) | (Hj & Efra & _ & _ & _ & _ & Hfl0)]; [exfalso; clear -Efv FRlo Pfs0; lia|].
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      rewrite EM1 in Hj.
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (EFLj : fs_flag FS 1 j = FS + 20480 + j)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (Rfl : 0 <= fs_flag FS 1 j < 2 ^ 64)
        by (rewrite EFLj; clear -Pfs0 HFSb HAE Hj; unfold APPMEM_END in *; lia).
      assert (Uflag : bv_unsigned (Z_to_bv 64 (fs_flag FS 1 j)) = fs_flag FS 1 j)
        by (apply unsigned_lit; exact Rfl).
      assert (SOK : store_ok rsegs m1 (wa (fs_flag FS 1 j)) 1 = true).
      { eapply (wv_store_ok m m1 (fs_flag FS 1 j) 1%nat).
        - intros i Hi. replace (fs_flag FS 1 j + i) with (fs_flag FS 1 j) by (cbn in Hi; lia).
          apply (stk_wv m FS (FS + FS_SIZE) (fs_flag FS 1 j) Pfsstk).
          rewrite EFLj; clear -Pfs0 HFSb Hj; unfold FS_SIZE; lia.
        - exact WM.
        - clear -Rfl; lia.
        - clear -Rfl; cbn; lia. }
    replace (wa (fs_flag FS 1 j)) with (wa (fs_flag FS 1 0 + j)) by (unfold wa; f_equal; rewrite EFLj, EFL0; lia).
      destruct Hflags as [flags' (Hfl & Hfllen & HflF)].
      destruct Hhint as [h' Hh].
      pose proof (FAP 0 ltac:(lia)) as Hfrapp. rewrite Z.add_0_r in Hfrapp.
      assert (EFR1 : fs_frame FS 1 0 = FS + 1085440)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
        by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
      assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
      assert (Hfrw : fra + 128 <= S - 8800)
        by (rewrite Efra, EFRj; clear -Pfs0 HFSb Hj; unfold FS_SIZE in HFSb; lia).
      assert (Hfrge : FS + 1085440 <= fra) by (rewrite Efra, EFRj; clear -Hj; lia).
      assert (Afl : 0 <= fs_flag FS 1 0 + j /\ fs_flag FS 1 0 + j + 1 <= 2 ^ 64)
        by (rewrite EFL0; clear -Pfs0 HFSb HAE Hj; unfold APPMEM_END in *; lia).
      assert (Hfe : fra + 128 <= APPMEM_END) by (clear -Hfrw HAE; unfold APPMEM_END in *; lia).
      (* the flag array [fs_flag FS 1 0, +fs_M 1) is apart from the frame and its shadow *)
      assert (Hdj : forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + Z.of_nat (length flags') ->
                    outside [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128)] x).
      { intros x Hx. rewrite Hfllen, EM1 in Hx.
        assert (Hxa : app_mem x) by (apply Pfsapp; rewrite EFL0 in Hx; unfold FS_SIZE; clear -Hx Pfs0 HFSb; lia).
        cbn [outside]. split; [| split; [| exact I]].
        - intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
        - intros [HL HR]. rewrite EFL0 in Hx. clear -Hx HL Hfrge; lia. }
      pose proof (fl_bytes _ mc m1 (fs_flag FS 1 0) flags' Hfl MUe Hdj) as Hflm1.
      pose proof (bytes_at_write_inside rsegs m1 (fs_flag FS 1 0) flags' j [Z_to_bv 8 0] Hflm1
        ltac:(clear -Hj; lia)
        ltac:(cbn [length]; pose proof Hfllen as HL; rewrite EM1 in HL; clear -HL Hj; lia)) as Hnfl.
      (* facts about m2 = write_to_mem m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] *)
      pose proof (rw_cells_frame rsegs m1 (S - 96) SAVES (fs_flag FS 1 0 + j) [Z_to_bv 8 0] SV
        ltac:(clear -Afl; lia) ltac:(clear -Afl; cbn [length]; lia)
        ltac:(right; cbn [length]; rewrite EFL0; clear -Pfs0 HFSb Hj; lia)) as SV2.
      pose proof (wmono_write rsegs m m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] WM) as WM2.
      pose proof (mem_inv_store rsegs m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] MI
        ltac:(cbn [length]; replace (fs_flag FS 1 0 + j) with (fs_flag FS 1 j) by (rewrite EFLj, EFL0; lia);
              exact SOK)) as MI2.
      pose proof (stk_write rsegs m1 (S - 8800) S (fs_flag FS 1 0 + j) [Z_to_bv 8 0] ST
        ltac:(clear -Afl; lia) ltac:(clear -Afl; cbn [length]; lia)) as ST2.
      pose proof (rd_mono_write m m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] RM) as RM2.
      pose proof (munch_write _ mc m1 (fs_flag FS 1 0 + j) [Z_to_bv 8 0] MUx
        ltac:(clear -Afl; lia) ltac:(clear -Afl; cbn [length]; lia)
        ltac:(cbn [lib.Lib.Frame.inside length]; right; right; left; split; [rewrite EFLj, EFL0; clear -Hj; lia | rewrite EFLj, EFL0; clear -Hj; lia])) as MUx2.
      pose proof (wmono_write rsegs mc m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] WMe) as WMe2.
      set (m2 := write_to_mem m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0]) in *.
      assert (MU2 : munch (Wex fra) m m2).
      { apply (munch_trans _ m mc m2 (proj1 MUn)). eapply munch_weaken; [|exact MUx2].
        intros y Hy. unfold Wex, shadow_addr in Hy. cbn [outside] in Hy |- *.
        destruct Hy as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. split; [|exact I].
        apply acl_out_app_inv in H3 as [_ H4]. destruct (wx_out_hint_flag FS X y H4) as (_ & Hfa).
        intros [HL HR]. apply Hfa. rewrite EFLj in HL, HR. rewrite EFL0, EM1. clear -HL HR Hj; lia. }
      step.
      eapply L_restore2.
      + exact SV2.
      + eapply munch_weaken; [exact (Wex_subfp fra fra A j 1 (Z_to_bv 64 (fs_flag FS 1 j)) HKc) | exact MU2].
      + exact WM2.
      + exact MI2.
      + exact ST2.
      + intros Ho.
        eapply acl_rw; [exact (HBox Ho) | exact MUx2 | exact WMe2 |].
        intros x Hx. cbn [cells_size csize] in Hx.
        assert (Hxa : app_mem x)
          by (destruct (AO0 Ho) as (AOa & _ & _); pose proof (acl_app_in m o 36 (x - o) AOa ltac:(lia)) as H;
              replace (o + (x - o)) with x in H by lia; exact H).
        assert (HinO : In (o, o + 36) (reac_ctrl_parse_D f n o))
          by (unfold reac_ctrl_parse_D; apply in_or_app; right;
              rewrite (proj2 (Z.eqb_neq o 0) Ho); left; reflexivity).
        pose proof (D_apart_frame o (o + 36) j HinO ltac:(clear; lia) ltac:(rewrite EM1; exact Hj) Hfl0) as Hofr.
        pose proof (dj_pair o (o + 36) _ _ HinO (proj2 (fp_wx_hint_flag_in FS X))) as Hofl.
        cbn [outside]. split; [| split; [| split; [| exact I]]].
        * intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
        * intros [HL HR]. rewrite Efra in HL, HR. clear -Hx HL HR Hofr; lia.
        * intros [HL HR]. rewrite EFLj in HL, HR. rewrite EFL0, EM1 in Hofl. clear -Hx HL HR Hofl Hj; lia.
      + (* aJ m2 *)
        assert (AWfinal : addressable m2 (S - 8800) 8800).
        { apply (acl_addr_munch (Wex fra) m m2 (S - 8800) 8800 AW0 MU2).
          intros i Hi. apply wex_sh_out;
            [ clear -FRlo Pfs0; lia | exact FR8 | exact Hfrapp | exact Hfe
            | clear -Hi; lia | right; clear -Hi Hfrw; lia ]. }
        assert (Hfree : asan_cells m2 /\ shadow_rw m2 /\
                  fpx [1%nat] m2 (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
                  reac_ctrl_parse_tls m2 (bv_unsigned tp) FS (S - 8800) S).
        { apply (Wex_free fra fra A j 1 (Z_to_bv 64 (fs_flag FS 1 j)) m2 HKc MU2 WM2 RM2).
          - exists h'. eapply fl_bytes; [exact Hh | exact MUx2 |].
            intros y Hy. unfold fs_hint in Hy. rewrite length_le8 in Hy. cbn [Z.of_nat] in Hy.
            cbn [outside]. split; [| split; [| split; [| exact I]]].
            + intros [HL HR]. apply (acl_app_not_shadow y).
              * apply Pfsapp. unfold FS_SIZE; clear -Hy Pfs0; lia.
              * replace y with (fra / 8 + ASAN_K + (y - (fra / 8 + ASAN_K))) by lia.
                apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
            + intros [HL HR]. clear -Hy HL HR Hfrge; lia.
            + intros [HL HR]. rewrite EFLj in HL, HR. clear -Hy HL HR Hj; lia.
          - exists (upd_bytes flags' (Z.to_nat j) [Z_to_bv 8 0]). split; [exact Hnfl|]. split.
            + rewrite upd_bytes_length by (cbn [length]; pose proof Hfllen as HL; rewrite EM1 in HL; clear -HL Hj; lia). exact Hfllen.
            + unfold upd_bytes. apply Forall_app. split; [| apply Forall_app; split].
              * pose proof HflF as HFa. rewrite <- (firstn_skipn (Z.to_nat j) flags') in HFa.
                apply Forall_app in HFa. exact (proj1 HFa).
              * constructor; [left; reflexivity | constructor].
              * pose proof HflF as HFb.
                rewrite <- (firstn_skipn (Z.to_nat j + length [Z_to_bv 8 0])%nat flags') in HFb.
                apply Forall_app in HFb. exact (proj2 HFb). }
        destruct Hfree as (Hac & Hsw & Hfp & Htl).
        split; [exact Hac|]. split; [exact Hsw|]. split; [exact AWfinal|]. split; [exact Hfp | exact Htl].
      + (* the flag array: flag j is 0 again (as at m, FK), the rest as at mc (FKP) *)
        intros x Hx.
        assert (Hxr : FS + 20480 <= x < FS + 28672) by (rewrite EFL0, EM1 in Hx; clear -Hx; lia).
        destruct (Z.eq_dec x (fs_flag FS 1 0 + j)) as [Exj|Exj].
        * subst x.
          assert (A0 : mrd rsegs m (wa (fs_flag FS 1 0 + j)) = Some (Z_to_bv 8 0)).
          { destruct Hfl0 as (_ & _ & H0). pose proof (H0 0%nat ltac:(cbn [length]; lia)) as A0.
            cbn [Z.of_nat nth_error] in A0. rewrite Z.add_0_r in A0.
            replace (fs_flag FS 1 0 + j) with (fs_flag FS 1 j) by (rewrite EFLj, EFL0; lia). exact A0. }
          rewrite A0. unfold m2, mrd. cbn [write_to_mem].
          first [rewrite bv_eqb_refl | unfold bv_eqb; rewrite Z.eqb_refl]. reflexivity.
        * assert (Hout : outside [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128);
                                  (fs_flag FS 1 j, fs_flag FS 1 j + 1)] x).
          { pose proof (Hdj x ltac:(rewrite Hfllen; exact Hx)) as (Ho1 & Ho2 & _).
            cbn [outside]. split; [exact Ho1|]. split; [exact Ho2|]. split; [|exact I].
            rewrite EFLj. rewrite EFL0 in Exj. clear -Exj; lia. }
          rewrite (munch_mrd_out _ mc m2 x MUx2 ltac:(clear -Hxr Pfs0 HFSb RS; lia) Hout).
          apply FKP; [exact Hx | rewrite EFLj; rewrite EFL0 in Exj; clear -Exj; lia].
  Qed.

  (* RE-BASED entry of the stretch after __asan_stack_malloc_1 (new).  The walk supplies these premises from the world
     at the return: m is the return memory with flag jj read as 0, mc0 the return memory; ra is any word (the callee
     need not keep it; the epilogue reloads it from SAVES).  The four steps (0x835ec .. 0x835f8) and the branch are
     entry's side arm (reac_ctrl_parseF.v :1792-1793), verbatim; the end is reac_ctrl_parseF_post.v's (not in this delivery) post_call_F's. *)
  Lemma post_call_F2 : forall (xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word) (mc0 : word -> option byte)
      (flags : list byte) (jj : Z),
    0 <= jj < fs_M 1 ->
    munch [(fs_flag FS 1 jj, fs_flag FS 1 jj + 1)] m mc0 -> wmono rsegs m mc0 -> rd_mono m mc0 ->
    mem_inv rsegs mc0 -> rw_cells rsegs mc0 (S - 96) SAVES ->
    bytes_at rsegs m (fs_flag FS 1 jj) [Z_to_bv 8 0] ->
    bytes_at rsegs mc0 (fs_flag FS 1 0) flags -> Z.of_nat (length flags) = fs_M 1 ->
    Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
    bytes_at rsegs mc0 (fs_frame FS 1 jj + 120) (le8 (Z_to_bv 64 (fs_flag FS 1 jj))) ->
    evtF rsegs RNG (RelSt2 (fs_frame FS 1 jj))
      (MS (mkR xra (Z_to_bv 64 A) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 A) (Z_to_bv 64 (fs_frame FS 1 jj))
               x1 x2 x3 x4 x5 x6 x7 s2 s3 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n) s7 s8 (wa ASAN_K) s10 s11
               u3 u4 u5 u6)
          F (Z_to_bv 64 0x835ec) fc None mc0 (seg_rom rsegs)).
  Proof.
    intros xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 mc0 flags jj Hjj MU0 WM0 RM0 MI2 FR2 HFj0 HFl HFln HFb H120.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFSb & _).
    unfold ASAN_GT in P3. unfold FS_SIZE in HFSb.
    assert (HKs : FK (fs_frame FS 1 jj) (fs_frame FS 1 jj) A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj))).
    { right. split; [exact Hjj|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact HFj0]. }
    destruct (fk_facts _ _ _ _ _ _ HKs) as (FR8s & FRlos & FRhis & _ & _ & FAPs & FRAs & _ & SH1s & SH2s).
    assert (FL2 : FLG (fs_frame FS 1 jj) 1 (Z_to_bv 64 (fs_flag FS 1 jj)) mc0).
    { split; [exists flags; split; [exact HFl | split; [exact HFln | exact HFb]] | intros _; exact H120]. }
    assert (MU3 : munch (Wf2 (fs_frame FS 1 jj) jj 1) m mc0).
    { eapply munch_weaken; [|exact MU0]. intros x Hx. unfold reac_ctrl_parseF_rbody.Wf2 in Hx. cbn [outside] in Hx |- *.
      destruct Hx as (_ & _ & H3 & _). split; [exact H3 | exact I]. }
    step. step. step. step.
    rewrite (rc_neq0_64 (fs_frame FS 1 jj)) by lia. cbn [negb]. cbv iota.
    assert (KBQ : KBx QX)
      by (eapply reac_ctrl_parseF_rbody.body_holds_x; first [exact L_exit_x | eassumption]).
    apply (evtF_mono _ _ (QX (fs_frame FS 1 jj))).
    2:{ intros ms' [[E _] | [_ Hr]]; [exfalso; clear -E FRlos P1; lia | exact Hr]. }
    eapply (fwords_x (fs_frame FS 1 jj) (fs_frame FS 1 jj) A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)));
      [exact HKs | | exact FL2 | exact KBQ].
    refine (conj MU3 (conj WM0 (conj RM0 (conj MI2 FR2)))).
  Qed.

  (* The post of the whole stretch after the call: Qp, the exact writes from m, and flag jj read as 0 again. *)
  Definition QF (jj : Z) : machine_state -> Prop :=
    fun ms => Qp ms /\
      (exists ob, OB (fs_frame FS 1 jj) ob /\
         munch (Wf2 (fs_frame FS 1 jj) jj 1 ++ [(ob, ob + 36)]) m (ms_mem ms)) /\
      bytes_at rsegs (ms_mem ms) (fs_flag FS 1 jj) [Z_to_bv 8 0].

  (* The stretch after the call, whole (new composition): post_call_F2, the release store `sb zero, 0(a1)` at 0x83990
     (reac_ctrl_parseF.v :2512-2538, stepped as reac_ctrl_parseF_cut.v (not in this delivery) steps it), post_release_F2. *)
  Lemma post_all_F2 : forall (xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word) (mc0 : word -> option byte)
      (flags : list byte) (jj : Z),
    0 <= jj < fs_M 1 ->
    munch [(fs_flag FS 1 jj, fs_flag FS 1 jj + 1)] m mc0 -> wmono rsegs m mc0 -> rd_mono m mc0 ->
    mem_inv rsegs mc0 -> rw_cells rsegs mc0 (S - 96) SAVES ->
    bytes_at rsegs m (fs_flag FS 1 jj) [Z_to_bv 8 0] ->
    bytes_at rsegs mc0 (fs_flag FS 1 0) flags -> Z.of_nat (length flags) = fs_M 1 ->
    Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
    bytes_at rsegs mc0 (fs_frame FS 1 jj + 120) (le8 (Z_to_bv 64 (fs_flag FS 1 jj))) ->
    evtF rsegs RNG (QF jj)
      (MS (mkR xra (Z_to_bv 64 A) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 A) (Z_to_bv 64 (fs_frame FS 1 jj))
               x1 x2 x3 x4 x5 x6 x7 s2 s3 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n) s7 s8 (wa ASAN_K) s10 s11
               u3 u4 u5 u6)
          F (Z_to_bv 64 0x835ec) fc None mc0 (seg_rom rsegs)).
  Proof.
    intros xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 mc0 flags jj Hjj MU0 WM0 RM0 MI2 FR2 HFj0 HFl HFln HFb H120.
    eapply evtF_cut;
      [exact (post_call_F2 xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 mc0 flags jj Hjj MU0 WM0 RM0 MI2 FR2 HFj0
                HFl HFln HFb H120) |].
    intros ms RSt. unfold RelSt2 in RSt.
    destruct RSt as (j & mc & mr & y1 & y5 & y6 & y7 & y9 & y11 & y12 & y13 & y14 & y15 & y16 & y19 & y20 & y21
                     & y22 & y25 & y26 & y28 & y29 & y30 & y31 & Ems & RF & (ob & HOB & MUa)).
    subst ms.
    pose proof RF as RF'. unfold reac_ctrl_parseF_bnd.RelFacts in RF'.
    destruct RF' as (HKc & _ & _ & _ & _ & WMr & _).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts _ _ _ _ _ _ HKc) as (FR8 & FRlo & _).
    pose proof HKc as HK.
    destruct HK as [(Efv & _) | (Hj & Efra & _ & _ & _ & _ & _)]; [exfalso; clear -Efv FRlo Pfs0; lia|].
    assert (EFRk : forall k, fs_frame FS 1 k = FS + 1085440 + k * 128)
      by (intros k; unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
    assert (Ejj : jj = j) by (rewrite !EFRk in Efra; clear -Efra; lia).
    subst jj.
    (* the release store `sb zero, 0(a1)` at 0x83990: reac_ctrl_parseF.v :2512-2538, as reac_ctrl_parseF_cut.v (not in this delivery) *)
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    rewrite EM1 in Hj.
    assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (EFLj : fs_flag FS 1 j = FS + 20480 + j)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (Rfl : 0 <= fs_flag FS 1 j < 2 ^ 64)
      by (rewrite EFLj; clear -Pfs0 HFSb HAE Hj; unfold APPMEM_END in *; lia).
    assert (Uflag : bv_unsigned (Z_to_bv 64 (fs_flag FS 1 j)) = fs_flag FS 1 j)
      by (apply unsigned_lit; exact Rfl).
    assert (SOK : store_ok rsegs mr (wa (fs_flag FS 1 j)) 1 = true).
    { eapply (wv_store_ok m mr (fs_flag FS 1 j) 1%nat).
      - intros i0 Hi0. replace (fs_flag FS 1 j + i0) with (fs_flag FS 1 j) by (cbn in Hi0; lia).
        apply (stk_wv m FS (FS + FS_SIZE) (fs_flag FS 1 j) Pfsstk).
        rewrite EFLj; clear -Pfs0 HFSb Hj; unfold FS_SIZE; lia.
      - exact WMr.
      - clear -Rfl; lia.
      - clear -Rfl; cbn; lia. }
    assert (RGFLj : rng RNG (fs_flag FS 1 j) 1).
    { assert (EMj : fs_M 1 = 8192) by reflexivity.
      eapply rng_sub; [exact RFLG | rewrite !fs_flag1; lia | rewrite !fs_flag1; lia]. }
    step.
    replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
    (* the stretch [just after the release store .. ret], then the post's exact writes and flag *)
    eapply evtF_mono;
      [exact (post_release_F2 (fs_frame FS 1 j) j mc mr y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y19 y20 y21 y22 y25
                y26 y28 y29 y30 y31 RF) |].
    intros ms' [HQ Hm]. split; [exact HQ|]. rewrite Hm. split.
    - exists ob. split; [exact HOB|]. eapply munch_trans; [exact MUa|].
      apply (munch_write _ mr mr (fs_flag FS 1 j) [Z_to_bv 8 0] (munch_refl _ mr));
        [clear -Rfl; lia | cbn [length Z.of_nat]; clear -Rfl; lia |].
      unfold reac_ctrl_parseF_rbody.Wf2. cbn [app lib.Lib.Frame.inside length Z.of_nat]. right; right; left. lia.
    - apply bytes_at_write_same; [clear -Rfl; lia | cbn [length Z.of_nat]; clear -Rfl; lia].
  Qed.

End RPostF.

(* ==== Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery) and its 09:58Z ruling): Module RPostFOn
   re-derives Section RPostF above, with the same names and scripts, for reac_ctrl_parseF.v's Module ParseFOn: the
   callees' `_F_on` contracts, SR0 : shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m, every reac_ctrl_parseF.v /
   split-file Section name redirected to its route-(C) module (ParseFOn, BndFOn, PreFOn, RelFOn, BodyFOn, PostFOn, RBodyFOn; the
   notation arguments read off `About` of each), and reac_ctrl_parseF.v's shadow edits where these scripts carry them
   (the region lemmas srw_* / frame_in_R; the post's forall-P form). Section RPostF above stays byte-identical outside comments.
   rule 24: no function proved beyond reac_ctrl_parseF.v's own run (proof-index reac_ctrl_parse 2026-10-29
   00:3xZ, exit 0: 12 named files + 8 lemma rows, plain / ubsan builds of other units; checker a Theorem Labs lane: CONFIRM). ==== *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF_on
  asan_memcpy_cF_on bcmp_wrap_c_on.
Local Open Scope Z_scope.

Module RPostFOn.

Section RPostF.
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
  Local Notation aout_rt := (@reac_ctrl_parseF.ParseFOn.aout_rt tp m f n o S FS fr junk Rf Rn Ro RS Lfr HOK HHM HAE AO0 X FP0).
  Local Notation aJ_free := (@reac_ctrl_parseF.ParseFOn.aJ_free tp m f n o S FS fr junk Rf Rn Ro RS Lfr HOK AC0 HHM HAE AO0 X FP0 TLS0).
  Local Notation Wex := (@reac_ctrl_parseF.ParseFOn.Wex o S FS X).
  Local Notation Wexw := (@reac_ctrl_parseF.ParseFOn.Wexw o S FS).
  Local Notation Wex_sub_w := (@reac_ctrl_parseF.ParseFOn.Wex_sub_w o S FS X).
  Local Notation sh_hi_small_out := (@reac_ctrl_parseF.ParseFOn.sh_hi_small_out m f n o S fr junk Rf Rn Ro RS Lfr HOK HHM AO0).
  Local Notation wex_sh_out := (@reac_ctrl_parseF.ParseFOn.wex_sh_out tp m f n o S FS fr junk Rf Rn Ro RS S16 Lfr HOK HHM HAE AO0 X FP0).
  Local Notation Wex_free := (@reac_ctrl_parseF.ParseFOn.Wex_free tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HOK AC0 SR0 HHM HAE AO0 X FP0 TLS0).
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
  (* Route (C): Module ParseFOn's region lemmas, at this Section's variables (arguments read off `About`). *)
  Local Notation srw_frame := (@reac_ctrl_parseF.ParseFOn.srw_frame m f n o S FS fr Rf Rn Ro Lfr).
  (* the cut points of reac_ctrl_parseF_bnd.v, at this Section's variables *)
  Local Notation PreCall := (@reac_ctrl_parseF_bnd.BndFOn.PreCall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S).
  Local Notation RelFacts := (@reac_ctrl_parseF_bnd.BndFOn.RelFacts ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m n o S FS fr X).
  Local Notation RelSt := (@reac_ctrl_parseF_bnd.BndFOn.RelSt ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n o S FS fr X).


  (* reac_ctrl_parseF_rbody.v's KBx, fwords_x and Wf2 at this Section's variables (body_holds_x is applied by eapply). *)
  Local Notation Wf2 := (@reac_ctrl_parseF_rbody.RBodyFOn.Wf2 S FS).
  Local Notation KBx := (@reac_ctrl_parseF_rbody.RBodyFOn.KBx ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS RNG).
  Local Notation fwords_x := (@reac_ctrl_parseF_rbody.RBodyFOn.fwords_x ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG Rf Rn Ro RS S16 ST0 Lfr SR0 HHM HAE X FP0 RWIN SCW RFRM SCFR).

  (* reac_ctrl_parseF.v :4823-4849, the store tactics of the frame block and the exit *)
  Ltac wst a nn tac :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; tac | eassumption | lia | lia ])
    end.

  Ltac wstb a nn base fact :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
                  match goal with |- wview _ _ (wa ?X) <> None => replace X with (base + (X - base)) by lia end;
                  apply fact; lia
                | eassumption | lia | lia ])
    end.

  (* A tracked poison store of one shadow byte at base + off (= base + Z.of_nat nn): the stored byte joins the
     frame-shadow cells so that the box's addressability can be read back. *)
  Ltac sstep base off nn fact :=
    wstb (base + off) 1%nat base fact; step;
    replace (base + off) with (base + Z.of_nat nn) by lia;
    rewrite rc_le1_lit; mem_after_store.

  (* RelSt of reac_ctrl_parseF_bnd.v for the frame fra, with the exact writes from m to the memory at the store. *)
  Definition RelSt2 (fra : Z) : machine_state -> Prop :=
    fun ms => exists (j : Z) (mc m1 : word -> option byte)
                     (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
      ms = MS (mkR x1 (Z_to_bv 64 A) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
                   (Z_to_bv 64 (fs_flag FS 1 j)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fra) x19 x20 x21 x22
                   (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x83990) fc None m1 (seg_rom rsegs) /\
      RelFacts fra j mc m1 /\
      (exists ob, OB fra ob /\ munch (Wf2 fra j 1 ++ [(ob, ob + 36)]) m m1).

  (* The exit's post: Qp for the real-stack frame (fv = 0), RelSt2 at the release store for a side-stack frame. *)
  Definition QX (fv : Z) : machine_state -> Prop :=
    fun ms => (fv = 0 /\ Qp ms) \/ (fv <> 0 /\ RelSt2 fv ms).

  (* reac_ctrl_parseF_post.v's (not in this delivery) L_exit_x (L_exit of reac_ctrl_parseF.v :5721 up to the release store), with HEXIT's
     exact-writes premise, which it carries to RelSt2. *)
  Lemma L_exit_x : forall fra fv spc j nn w120 mc
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 ->
    munch (Wex fra) m mc ->
    wmono rsegs m mc -> rd_mono m mc -> mem_inv rsegs mc ->
    asan_cells mc -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc -> stk rsegs mc (S - 8800) S ->
    rw_cells rsegs mc (S - 96) SAVES ->
    (o <> 0 -> rw_cells rsegs mc o [CB 36 (snd (ctrlparse n fr))]) ->
    (exists h', bytes_at rsegs mc (fs_hint FS 1) (le8 h')) ->
    (exists flags', bytes_at rsegs mc (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') ->
    (nn = 1 -> bytes_at rsegs mc (fra + 120) (le8 w120)) ->
    (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> ~ (fs_flag FS 1 j <= x < fs_flag FS 1 j + nn) ->
       mrd rsegs mc (wa x) = mrd rsegs m (wa x)) ->
    (exists ob, OB fra ob /\ munch (Wf2 fra j nn ++ [(ob, ob + 36)]) m mc) ->
    evtF rsegs RNG (QX fv)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fv) x19 x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K))
               (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83920) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31
      HK MU WM RM MI AC SR ST SV HBox Hhint Hflags Hw120 FKP HXW.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _ & HFSb & _ & HWd & HDd).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (Ush : bv_unsigned (Z_to_bv 64 (fra / 8 + ASAN_K)) = fra / 8 + ASAN_K)
      by (apply unsigned_lit; clear -SH1 SH2; lia).
    assert (Ufra : bv_unsigned (Z_to_bv 64 fra) = fra)
      by (apply unsigned_lit; clear -FRlo FRhi HAhi RS Pfs0; lia).
    assert (HHMl : 17594333495296 <= S - 8800)
      by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    (* the munch from m (over Wex, whose fp_wx part has an abstract X) is kept out of the store tracking; the exit's
       own writes are tracked from mc on the tight footprints MUe / MUx, and the two are composed at the end *)
    pose proof (conj MU I) as MUn. clear MU.
    pose proof HK as HKc.
    pose proof (munch_refl [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 128)] mc) as MUe.
    pose proof (munch_refl [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 128);
                            (fs_flag FS 1 j, fs_flag FS 1 j + 1)] mc) as MUx.
    pose proof (wmono_refl rsegs mc) as WMe.
    pose proof (munch_refl [(shadow_addr fra, shadow_addr fra + 16); (fra, fra + 8)] mc) as MUw.
    unfold shadow_addr in MUe, MUx, MUw.
    step.
    wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
    step. step.
    wstb fra 8%nat fra FW. step. store_done.
    destruct HK as [(Efv & Efra & Espc & Ej & Enn) | (Hj & Efra & Efv & Espc & Ew120 & Enn & Hfl0)].
    - (* real-stack frame: fv = 0 *)
      subst fv. step.
      replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbv iota.
      match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        pose proof (shadow_rw_mono_on _ m mcur SR0 WM RM) as SRc;
        pose proof (shadow16_stk_on mcur fra (srw_frame fra _ _ _ _ _ mcur HKc SRc) ltac:(clear -FRlo Pfs0; lia) FRA
                      ltac:(clear -SH1; lia) ltac:(clear -SH2; lia)) as STsh
      end.
      pose proof (stk_carve rsegs _ (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16) 16%nat STsh ltac:(clear -SH1; lia))
        as [STsh' [junkS SHC]].
      replace (fra / 8 + ASAN_K + 16 - Z.of_nat 16) with (fra / 8 + ASAN_K) in SHC by lia.
      sstep (fra / 8 + ASAN_K) 4 4%nat SW. sstep (fra / 8 + ASAN_K) 5 5%nat SW.
      sstep (fra / 8 + ASAN_K) 6 6%nat SW. sstep (fra / 8 + ASAN_K) 7 7%nat SW.
      sstep (fra / 8 + ASAN_K) 0 0%nat SW. sstep (fra / 8 + ASAN_K) 1 1%nat SW.
      sstep (fra / 8 + ASAN_K) 2 2%nat SW. sstep (fra / 8 + ASAN_K) 3 3%nat SW.
      sstep (fra / 8 + ASAN_K) 12 12%nat SW. sstep (fra / 8 + ASAN_K) 13 13%nat SW.
      sstep (fra / 8 + ASAN_K) 14 14%nat SW. sstep (fra / 8 + ASAN_K) 15 15%nat SW.
      sstep (fra / 8 + ASAN_K) 8 8%nat SW. sstep (fra / 8 + ASAN_K) 9 9%nat SW.
      sstep (fra / 8 + ASAN_K) 10 10%nat SW. sstep (fra / 8 + ASAN_K) 11 11%nat SW.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      assert (EFL : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      pose proof (FAP 0 ltac:(lia)) as Hfraapp. rewrite Z.add_0_r in Hfraapp.
      assert (Hfe : fra + 128 <= APPMEM_END) by (clear -FRhi HAhi RS HAE; unfold APPMEM_END in *; lia).
      destruct SHC as [[_ HB16] _]. cbn [cells_bytes cbytes app] in HB16.
      destruct Hhint as [h' Hh]. destruct Hflags as [flags' (Hfl & Hfllen & HflF)].
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
        assert (MU : munch (Wex fra) m mf)
          by (apply (munch_trans _ m mc mf (proj1 MUn)); eapply munch_weaken; [|exact MUe];
              intros y Hy; unfold reac_ctrl_parseF.ParseFOn.Wex, shadow_addr in Hy; cbn [outside] in Hy |- *;
              destruct Hy as (H1 & H2 & _); exact (conj H1 (conj H2 I)))
      end.
      apply (evtF_mono _ _ Qp); [| intros ms' Hq; left; split; [reflexivity | exact Hq]].
      eapply L_restore.
      + exact SV.
      + eapply munch_weaken; [exact (Wex_subfp fra 0 spc j nn w120 HKc) | exact MU].
      + exact WM.
      + exact MI.
      + exact ST.
      + intros Ho. eapply acl_rw; [exact (HBox Ho) | exact MUe | exact WMe |].
        intros y Hy. apply Wsmall_outside; [clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2 | |].
        * destruct (AO0 Ho) as (AOa & _ & _). pose proof (acl_app_in m o 36 (y - o) AOa ltac:(cbn [cells_size csize] in Hy; lia)) as Hya.
          replace (o + (y - o)) with y in Hya by lia. exact Hya.
        * destruct (HOK Ho) as (_ & _ & _ & HowS & _). rewrite Efra.
          cbn [cells_size csize] in Hy. destruct HowS as [Hc|Hc]; [left | right]; clear -Hy Hc HAlo HAhi RS; lia.
      + lazymatch goal with |- aJ ?mf =>
          assert (Hz16 : forall g, 0 <= g <= 15 ->
                    exists b, mrd rsegs mf (wa (fra / 8 + ASAN_K + g)) = Some b /\ bv_signed b = 0);
          [ destruct HB16 as (_ & _ & Hr); intros g Hg; exists (Z_to_bv 8 0); split; [|vm_compute; reflexivity];
            pose proof (Hr (Z.to_nat g) ltac:(cbn [length]; lia)) as Hg';
            replace (fra / 8 + ASAN_K + Z.of_nat (Z.to_nat g)) with (fra / 8 + ASAN_K + g) in Hg' by lia;
            rewrite Hg';
            assert (Hc : g=0\/g=1\/g=2\/g=3\/g=4\/g=5\/g=6\/g=7\/g=8\/g=9\/g=10\/g=11\/g=12\/g=13\/g=14\/g=15) by lia;
            repeat (destruct Hc as [Hc|Hc]); subst g; vm_compute; reflexivity
          | ];
          assert (AFR : addressable mf fra 128)
            by (apply frame_all_addr; [clear -FRlo Pfs0; lia | exact FR8 | exact Hfe | exact FAP | exact Hz16]);
          assert (ABLO : addressable mf (S - 8800) (fra - (S - 8800)));
          [ apply (acl_addr_munch (Wex fra) m mf (S - 8800) (fra - (S - 8800)));
            [ apply (acl_addr_sub m (S - 8800) 8800 (S - 8800) (fra - (S - 8800)) AW0);
                [ lia | clear -FRlo HAlo HAhi RS Efra; rewrite Efra; lia | clear -FRlo HAlo HAhi RS Efra; rewrite Efra; lia ]
            | exact MU
            | intros i Hi; apply wex_sh_out;
                [ clear -FRlo Pfs0; lia | exact FR8 | exact Hfraapp | exact Hfe
                | clear -Hi FRlo HAlo HAhi RS Efra; rewrite Efra in *; lia | left; clear -Hi; lia ] ]
          | ];
          assert (AABOVE : addressable mf (fra + 128) (S - (fra + 128)));
          [ apply (acl_addr_munch (Wex fra) m mf (fra + 128) (S - (fra + 128)));
            [ apply (acl_addr_sub m (S - 8800) 8800 (fra + 128) (S - (fra + 128)) AW0);
                [ clear -FRlo HAlo HAhi RS Efra; rewrite Efra; lia | clear -FRhi HAhi RS Efra; rewrite Efra; lia
                | clear -FRhi HAhi RS Efra; rewrite Efra; lia ]
            | exact MU
            | intros i Hi; apply wex_sh_out;
                [ clear -FRlo Pfs0; lia | exact FR8 | exact Hfraapp | exact Hfe
                | clear -Hi FRhi HAlo HAhi RS Efra; rewrite Efra in *; lia | right; clear -Hi; lia ] ]
          | ];
          assert (AWfinal : addressable mf (S - 8800) 8800);
          [ pose proof (acl_addr_join mf (S - 8800) (fra - (S - 8800)) 128 ABLO
                         ltac:(replace (S - 8800 + (fra - (S - 8800))) with fra by (clear; lia); exact AFR)
                         ltac:(lia)) as J1;
            pose proof (acl_addr_join mf (S - 8800) (fra - (S - 8800) + 128) (S - (fra + 128)) J1
                         ltac:(replace (S - 8800 + (fra - (S - 8800) + 128)) with (fra + 128) by (clear; lia); exact AABOVE)
                         ltac:(clear -FRhi HAhi RS Efra; rewrite Efra; lia)) as J2;
            exact (acl_addr_sub mf (S - 8800) (fra - (S - 8800) + 128 + (S - (fra + 128))) (S - 8800) 8800 J2
                     ltac:(lia) ltac:(lia) ltac:(clear; lia))
          | ];
          assert (Hfree : asan_cells mf /\ (forall P, shadow_rw_on P m -> shadow_rw_on P mf) /\
                    fpx [1%nat] mf (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
                    reac_ctrl_parse_tls mf (bv_unsigned tp) FS (S - 8800) S);
          [ apply (Wex_free fra 0 spc j nn w120 mf HKc MU WM RM);
            [ exists h'; eapply fl_bytes; [exact Hh | exact MUe |];
              intros y Hy; unfold fs_hint in Hy; rewrite length_le8 in Hy; cbn [Z.of_nat] in Hy;
              apply Wsmall_outside;
                [ clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2
                | apply Pfsapp; unfold FS_SIZE; lia
                | left; lia ]
            | exists flags'; split; [|split; [exact Hfllen | exact HflF]];
              eapply fl_bytes; [exact Hfl | exact MUe |];
              intros y Hy; rewrite Hfllen, EM1, EFL in Hy;
              apply Wsmall_outside;
                [ clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2
                | apply Pfsapp; unfold FS_SIZE; lia
                | left; lia ] ]
          | ];
          destruct Hfree as (Hac & Hsw & Hfp & Htl);
          split; [exact Hac|]; split; [exact Hsw|]; split; [exact AWfinal|]; split; [exact Hfp | exact Htl]
        end.
      + intros x Hx.
        assert (Hxr : FS + 20480 <= x < FS + 28672) by (rewrite EFL, EM1 in Hx; clear -Hx; lia).
        lazymatch goal with |- mrd rsegs ?mf (wa x) = _ =>
          rewrite (munch_mrd_out _ mc mf x MUe ltac:(clear -Hxr Pfs0 HFSb RS; lia)
                     ltac:(apply Wsmall_outside;
                             [ clear -FRlo Pfs0; lia | exact FRA | exact SH1 | exact SH2
                             | apply Pfsapp; unfold FS_SIZE; clear -Hxr; lia
                             | left; clear -Hxr FRlo; lia ]))
        end.
        apply FKP; [exact Hx | rewrite Enn; clear; lia].
    - (* side-stack frame: fv = fra <> 0 *)
      subst fv.
      pose proof (Hw120 Enn) as Hw120'.
      step.
      rewrite (rc_neq0_64 fra) by (clear -FRlo FRhi HAhi RS Pfs0; lia). cbn [negb]. cbv iota.
      step.
      wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 0) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 1) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 2) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 3) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 12) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 13) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 14) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 15) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 9) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 10) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      wstb (fra / 8 + ASAN_K + 11) 1%nat (fra / 8 + ASAN_K) SW. step. rewrite ?Ush. store_done.
      pose proof (fl_bytes _ mc _ (fra + 120) (le8 w120) Hw120' MUw
        ltac:(intros x Hx; rewrite length_le8 in Hx; cbn [Z.of_nat] in Hx; cbn [outside];
              split; [| split; [| exact I]];
              [ intros [HL HR]; apply (acl_app_not_shadow x);
                [ replace x with (fra + (x - fra)) by lia; apply FAP; lia
                | replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia;
                  apply frame_shadow_in;
                  [ clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia ] ]
              | intros [HL HR]; clear -Hx HL HR; lia ])) as Hw120m.
      pose proof (bytes_ro8 _ (fra + 120) w120 Hw120m) as Hw120c.
      step.
      subst w120.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      rewrite EM1 in Hj.
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (EFLj : fs_flag FS 1 j = FS + 20480 + j)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (Rfl : 0 <= fs_flag FS 1 j < 2 ^ 64)
        by (rewrite EFLj; clear -Pfs0 HFSb HAE Hj; unfold APPMEM_END in *; lia).
      assert (Uflag : bv_unsigned (Z_to_bv 64 (fs_flag FS 1 j)) = fs_flag FS 1 j)
        by (apply unsigned_lit; exact Rfl).
      assert (SOK : store_ok rsegs m1 (wa (fs_flag FS 1 j)) 1 = true).
      { eapply (wv_store_ok m m1 (fs_flag FS 1 j) 1%nat).
        - intros i Hi. replace (fs_flag FS 1 j + i) with (fs_flag FS 1 j) by (cbn in Hi; lia).
          apply (stk_wv m FS (FS + FS_SIZE) (fs_flag FS 1 j) Pfsstk).
          rewrite EFLj; clear -Pfs0 HFSb Hj; unfold FS_SIZE; lia.
        - exact WM.
        - clear -Rfl; lia.
        - clear -Rfl; cbn; lia. }
      assert (RGFLj : rng RNG (fs_flag FS 1 j) 1).
      { assert (EMj : fs_M 1 = 8192) by reflexivity.
        eapply rng_sub; [exact RFLG | rewrite !fs_flag1; lia | rewrite !fs_flag1; lia]. }
      apply evtF_done. right. split; [clear -FRlo Pfs0; lia|].
      subst spc nn. unfold RelSt2.
      exists j, mc, m1, x1, x5, x6, x7, x9, x11, x12, x13, x14, x15, x16, x19, x20, x21, x22, x25, x26, x28, x29,
        x30, x31.
      split; [reflexivity|].
      split.
      { unfold reac_ctrl_parseF_bnd.BndFOn.RelFacts.
        refine (conj HKc (conj (proj1 MUn) (conj MUe (conj MUx (conj WMe (conj WM (conj RM (conj MI (conj ST
          (conj SV (conj HBox (conj Hhint (conj Hflags (conj FKP Hw120m)))))))))))))). }
      (* the exact writes from m: the body's (HXW) and the exit's own (MUe: the frame shadow and the frame) *)
      destruct HXW as [ob [HOB MUa]]. exists ob. split; [exact HOB|].
      eapply munch_trans; [exact MUa|].
      eapply munch_weaken; [|exact MUe]. intros x Hx. unfold reac_ctrl_parseF_rbody.RBodyFOn.Wf2 in Hx. cbn [app outside] in Hx |- *.
      destruct Hx as (_ & _ & _ & H4 & H5 & _ & _). unfold shadow_addr in H5.
      split; [exact H5|]. split; [exact H4 | exact I].
  Qed.


  (* L_restore of reac_ctrl_parseF.v (:1825), its post also stating the final memory (the restore stores nothing). *)
  Lemma L_restore2 : forall (m' : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (spc : Z),
    rw_cells rsegs m' (S - 96) SAVES ->
    munch (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++ [(shadow_addr (S - 8800), shadow_addr S)]) m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - 8800) S ->
    (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) -> aJ m' ->
    (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> mrd rsegs m' (wa x) = mrd rsegs m (wa x)) ->
    evtF rsegs RNG (fun ms => Qp ms /\ ms_mem ms = m')
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x839d8) fc None m' (seg_rom rsegs)).
  Proof.
    intros m' x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 spc
      FR MU WM MI ST HBox HaJ HFK.
    unfold SAVES in FR.
    replace (S - 96) with (S + -96) in FR by lia.
    do 14 step. step.
    apply evtF_done. split; [|reflexivity]. unfold Qp. destruct HaJ as (AC & SW & AW & FP & TL).
    do 14 eexists. exists m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact HBox|]. split; [exact AC|]. split; [exact SW|]. split; [exact AW|].
    split; [exact FP|]. split; [|split; [|exact TL]].
    - apply Forall_forall. intros ci Hin. destruct (proj1 (Forall_forall _ _) XF0 ci Hin) as (_ & Hb).
      destruct (x_flag_in ci Hin) as (E & L1 & L2).
      apply (bytes_keep m m' _ _ Hb). intros x Hx. cbn [length Z.of_nat Pos.of_succ_nat] in Hx.
      rewrite E in Hx. apply HFK. clear -Hx L1 L2. lia.
    - intros fl Hl Hb. apply (bytes_keep m m' _ _ Hb). intros x Hx. apply HFK.
      pose proof (len_le_M fl Hl) as Hl'. clear -Hx Hl'. lia.
  Qed.

  (* reac_ctrl_parseF_rel.v's post_release_F with L_restore2 (its post states the final memory): L_exit's side arm
     after the release store: `j 0x839d8`, then L_restore. *)
  Lemma post_release_F2 : forall (fra j : Z) (mc m1 : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    RelFacts fra j mc m1 ->
    evtF rsegs RNG (fun ms => Qp ms /\ ms_mem ms = write_to_mem m1 (wa (fs_flag FS 1 j)) [Z_to_bv 8 0])
      (MS (mkR x1 (Z_to_bv 64 A) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               (Z_to_bv 64 (fs_flag FS 1 j)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fra) x19 x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83994) fc None (write_to_mem m1 (wa (fs_flag FS 1 j)) [Z_to_bv 8 0]) (seg_rom rsegs)).
  Proof.
    intros fra j mc m1 x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 HR.
    unfold reac_ctrl_parseF_bnd.BndFOn.RelFacts in HR.
    destruct HR as (HKc & MUn0 & MUe & MUx & WMe & WM & RM & MI & ST & SV & HBox & Hhint & Hflags & FKP & Hw120m).
    pose proof (conj MUn0 I) as MUn. clear MUn0.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _ & HFSb & _ & HWd & HDd).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fra A j 1 (Z_to_bv 64 (fs_flag FS 1 j)) HKc) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HKc as HK.
    destruct HK as [(Efv & _) | (Hj & Efra & _ & _ & _ & _ & Hfl0)]; [exfalso; clear -Efv FRlo Pfs0; lia|].
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      rewrite EM1 in Hj.
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (EFLj : fs_flag FS 1 j = FS + 20480 + j)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (Rfl : 0 <= fs_flag FS 1 j < 2 ^ 64)
        by (rewrite EFLj; clear -Pfs0 HFSb HAE Hj; unfold APPMEM_END in *; lia).
      assert (Uflag : bv_unsigned (Z_to_bv 64 (fs_flag FS 1 j)) = fs_flag FS 1 j)
        by (apply unsigned_lit; exact Rfl).
      assert (SOK : store_ok rsegs m1 (wa (fs_flag FS 1 j)) 1 = true).
      { eapply (wv_store_ok m m1 (fs_flag FS 1 j) 1%nat).
        - intros i Hi. replace (fs_flag FS 1 j + i) with (fs_flag FS 1 j) by (cbn in Hi; lia).
          apply (stk_wv m FS (FS + FS_SIZE) (fs_flag FS 1 j) Pfsstk).
          rewrite EFLj; clear -Pfs0 HFSb Hj; unfold FS_SIZE; lia.
        - exact WM.
        - clear -Rfl; lia.
        - clear -Rfl; cbn; lia. }
    replace (wa (fs_flag FS 1 j)) with (wa (fs_flag FS 1 0 + j)) by (unfold wa; f_equal; rewrite EFLj, EFL0; lia).
      destruct Hflags as [flags' (Hfl & Hfllen & HflF)].
      destruct Hhint as [h' Hh].
      pose proof (FAP 0 ltac:(lia)) as Hfrapp. rewrite Z.add_0_r in Hfrapp.
      assert (EFR1 : fs_frame FS 1 0 = FS + 1085440)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
        by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
      assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
      assert (Hfrw : fra + 128 <= S - 8800)
        by (rewrite Efra, EFRj; clear -Pfs0 HFSb Hj; unfold FS_SIZE in HFSb; lia).
      assert (Hfrge : FS + 1085440 <= fra) by (rewrite Efra, EFRj; clear -Hj; lia).
      assert (Afl : 0 <= fs_flag FS 1 0 + j /\ fs_flag FS 1 0 + j + 1 <= 2 ^ 64)
        by (rewrite EFL0; clear -Pfs0 HFSb HAE Hj; unfold APPMEM_END in *; lia).
      assert (Hfe : fra + 128 <= APPMEM_END) by (clear -Hfrw HAE; unfold APPMEM_END in *; lia).
      (* the flag array [fs_flag FS 1 0, +fs_M 1) is apart from the frame and its shadow *)
      assert (Hdj : forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + Z.of_nat (length flags') ->
                    outside [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128)] x).
      { intros x Hx. rewrite Hfllen, EM1 in Hx.
        assert (Hxa : app_mem x) by (apply Pfsapp; rewrite EFL0 in Hx; unfold FS_SIZE; clear -Hx Pfs0 HFSb; lia).
        cbn [outside]. split; [| split; [| exact I]].
        - intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
        - intros [HL HR]. rewrite EFL0 in Hx. clear -Hx HL Hfrge; lia. }
      pose proof (fl_bytes _ mc m1 (fs_flag FS 1 0) flags' Hfl MUe Hdj) as Hflm1.
      pose proof (bytes_at_write_inside rsegs m1 (fs_flag FS 1 0) flags' j [Z_to_bv 8 0] Hflm1
        ltac:(clear -Hj; lia)
        ltac:(cbn [length]; pose proof Hfllen as HL; rewrite EM1 in HL; clear -HL Hj; lia)) as Hnfl.
      (* facts about m2 = write_to_mem m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] *)
      pose proof (rw_cells_frame rsegs m1 (S - 96) SAVES (fs_flag FS 1 0 + j) [Z_to_bv 8 0] SV
        ltac:(clear -Afl; lia) ltac:(clear -Afl; cbn [length]; lia)
        ltac:(right; cbn [length]; rewrite EFL0; clear -Pfs0 HFSb Hj; lia)) as SV2.
      pose proof (wmono_write rsegs m m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] WM) as WM2.
      pose proof (mem_inv_store rsegs m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] MI
        ltac:(cbn [length]; replace (fs_flag FS 1 0 + j) with (fs_flag FS 1 j) by (rewrite EFLj, EFL0; lia);
              exact SOK)) as MI2.
      pose proof (stk_write rsegs m1 (S - 8800) S (fs_flag FS 1 0 + j) [Z_to_bv 8 0] ST
        ltac:(clear -Afl; lia) ltac:(clear -Afl; cbn [length]; lia)) as ST2.
      pose proof (rd_mono_write m m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] RM) as RM2.
      pose proof (munch_write _ mc m1 (fs_flag FS 1 0 + j) [Z_to_bv 8 0] MUx
        ltac:(clear -Afl; lia) ltac:(clear -Afl; cbn [length]; lia)
        ltac:(cbn [lib.Lib.Frame.inside length]; right; right; left; split; [rewrite EFLj, EFL0; clear -Hj; lia | rewrite EFLj, EFL0; clear -Hj; lia])) as MUx2.
      pose proof (wmono_write rsegs mc m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0] WMe) as WMe2.
      set (m2 := write_to_mem m1 (wa (fs_flag FS 1 0 + j)) [Z_to_bv 8 0]) in *.
      assert (MU2 : munch (Wex fra) m m2).
      { apply (munch_trans _ m mc m2 (proj1 MUn)). eapply munch_weaken; [|exact MUx2].
        intros y Hy. unfold Wex, shadow_addr in Hy. cbn [outside] in Hy |- *.
        destruct Hy as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. split; [|exact I].
        apply acl_out_app_inv in H3 as [_ H4]. destruct (wx_out_hint_flag FS X y H4) as (_ & Hfa).
        intros [HL HR]. apply Hfa. rewrite EFLj in HL, HR. rewrite EFL0, EM1. clear -HL HR Hj; lia. }
      step.
      eapply L_restore2.
      + exact SV2.
      + eapply munch_weaken; [exact (Wex_subfp fra fra A j 1 (Z_to_bv 64 (fs_flag FS 1 j)) HKc) | exact MU2].
      + exact WM2.
      + exact MI2.
      + exact ST2.
      + intros Ho.
        eapply acl_rw; [exact (HBox Ho) | exact MUx2 | exact WMe2 |].
        intros x Hx. cbn [cells_size csize] in Hx.
        assert (Hxa : app_mem x)
          by (destruct (AO0 Ho) as (AOa & _ & _); pose proof (acl_app_in m o 36 (x - o) AOa ltac:(lia)) as H;
              replace (o + (x - o)) with x in H by lia; exact H).
        assert (HinO : In (o, o + 36) (reac_ctrl_parse_D f n o))
          by (unfold reac_ctrl_parse_D; apply in_or_app; right;
              rewrite (proj2 (Z.eqb_neq o 0) Ho); left; reflexivity).
        pose proof (D_apart_frame o (o + 36) j HinO ltac:(clear; lia) ltac:(rewrite EM1; exact Hj) Hfl0) as Hofr.
        pose proof (dj_pair o (o + 36) _ _ HinO (proj2 (fp_wx_hint_flag_in FS X))) as Hofl.
        cbn [outside]. split; [| split; [| split; [| exact I]]].
        * intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
        * intros [HL HR]. rewrite Efra in HL, HR. clear -Hx HL HR Hofr; lia.
        * intros [HL HR]. rewrite EFLj in HL, HR. rewrite EFL0, EM1 in Hofl. clear -Hx HL HR Hofl Hj; lia.
      + (* aJ m2 *)
        assert (AWfinal : addressable m2 (S - 8800) 8800).
        { apply (acl_addr_munch (Wex fra) m m2 (S - 8800) 8800 AW0 MU2).
          intros i Hi. apply wex_sh_out;
            [ clear -FRlo Pfs0; lia | exact FR8 | exact Hfrapp | exact Hfe
            | clear -Hi; lia | right; clear -Hi Hfrw; lia ]. }
        assert (Hfree : asan_cells m2 /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m2) /\
                  fpx [1%nat] m2 (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
                  reac_ctrl_parse_tls m2 (bv_unsigned tp) FS (S - 8800) S).
        { apply (Wex_free fra fra A j 1 (Z_to_bv 64 (fs_flag FS 1 j)) m2 HKc MU2 WM2 RM2).
          - exists h'. eapply fl_bytes; [exact Hh | exact MUx2 |].
            intros y Hy. unfold fs_hint in Hy. rewrite length_le8 in Hy. cbn [Z.of_nat] in Hy.
            cbn [outside]. split; [| split; [| split; [| exact I]]].
            + intros [HL HR]. apply (acl_app_not_shadow y).
              * apply Pfsapp. unfold FS_SIZE; clear -Hy Pfs0; lia.
              * replace y with (fra / 8 + ASAN_K + (y - (fra / 8 + ASAN_K))) by lia.
                apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
            + intros [HL HR]. clear -Hy HL HR Hfrge; lia.
            + intros [HL HR]. rewrite EFLj in HL, HR. clear -Hy HL HR Hj; lia.
          - exists (upd_bytes flags' (Z.to_nat j) [Z_to_bv 8 0]). split; [exact Hnfl|]. split.
            + rewrite upd_bytes_length by (cbn [length]; pose proof Hfllen as HL; rewrite EM1 in HL; clear -HL Hj; lia). exact Hfllen.
            + unfold upd_bytes. apply Forall_app. split; [| apply Forall_app; split].
              * pose proof HflF as HFa. rewrite <- (firstn_skipn (Z.to_nat j) flags') in HFa.
                apply Forall_app in HFa. exact (proj1 HFa).
              * constructor; [left; reflexivity | constructor].
              * pose proof HflF as HFb.
                rewrite <- (firstn_skipn (Z.to_nat j + length [Z_to_bv 8 0])%nat flags') in HFb.
                apply Forall_app in HFb. exact (proj2 HFb). }
        destruct Hfree as (Hac & Hsw & Hfp & Htl).
        split; [exact Hac|]. split; [exact Hsw|]. split; [exact AWfinal|]. split; [exact Hfp | exact Htl].
      + (* the flag array: flag j is 0 again (as at m, FK), the rest as at mc (FKP) *)
        intros x Hx.
        assert (Hxr : FS + 20480 <= x < FS + 28672) by (rewrite EFL0, EM1 in Hx; clear -Hx; lia).
        destruct (Z.eq_dec x (fs_flag FS 1 0 + j)) as [Exj|Exj].
        * subst x.
          assert (A0 : mrd rsegs m (wa (fs_flag FS 1 0 + j)) = Some (Z_to_bv 8 0)).
          { destruct Hfl0 as (_ & _ & H0). pose proof (H0 0%nat ltac:(cbn [length]; lia)) as A0.
            cbn [Z.of_nat nth_error] in A0. rewrite Z.add_0_r in A0.
            replace (fs_flag FS 1 0 + j) with (fs_flag FS 1 j) by (rewrite EFLj, EFL0; lia). exact A0. }
          rewrite A0. unfold m2, mrd. cbn [write_to_mem].
          first [rewrite bv_eqb_refl | unfold bv_eqb; rewrite Z.eqb_refl]. reflexivity.
        * assert (Hout : outside [(fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fra, fra + 128);
                                  (fs_flag FS 1 j, fs_flag FS 1 j + 1)] x).
          { pose proof (Hdj x ltac:(rewrite Hfllen; exact Hx)) as (Ho1 & Ho2 & _).
            cbn [outside]. split; [exact Ho1|]. split; [exact Ho2|]. split; [|exact I].
            rewrite EFLj. rewrite EFL0 in Exj. clear -Exj; lia. }
          rewrite (munch_mrd_out _ mc m2 x MUx2 ltac:(clear -Hxr Pfs0 HFSb RS; lia) Hout).
          apply FKP; [exact Hx | rewrite EFLj; rewrite EFL0 in Exj; clear -Exj; lia].
  Qed.

  (* RE-BASED entry of the stretch after __asan_stack_malloc_1 (new).  The walk supplies these premises from the world
     at the return: m is the return memory with flag jj read as 0, mc0 the return memory; ra is any word (the callee
     need not keep it; the epilogue reloads it from SAVES).  The four steps (0x835ec .. 0x835f8) and the branch are
     entry's side arm (reac_ctrl_parseF.v :5205-5206), verbatim; the end is reac_ctrl_parseF_post.v's (not in this delivery) post_call_F's. *)
  Lemma post_call_F2 : forall (xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word) (mc0 : word -> option byte)
      (flags : list byte) (jj : Z),
    0 <= jj < fs_M 1 ->
    munch [(fs_flag FS 1 jj, fs_flag FS 1 jj + 1)] m mc0 -> wmono rsegs m mc0 -> rd_mono m mc0 ->
    mem_inv rsegs mc0 -> rw_cells rsegs mc0 (S - 96) SAVES ->
    bytes_at rsegs m (fs_flag FS 1 jj) [Z_to_bv 8 0] ->
    bytes_at rsegs mc0 (fs_flag FS 1 0) flags -> Z.of_nat (length flags) = fs_M 1 ->
    Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
    bytes_at rsegs mc0 (fs_frame FS 1 jj + 120) (le8 (Z_to_bv 64 (fs_flag FS 1 jj))) ->
    evtF rsegs RNG (RelSt2 (fs_frame FS 1 jj))
      (MS (mkR xra (Z_to_bv 64 A) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 A) (Z_to_bv 64 (fs_frame FS 1 jj))
               x1 x2 x3 x4 x5 x6 x7 s2 s3 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n) s7 s8 (wa ASAN_K) s10 s11
               u3 u4 u5 u6)
          F (Z_to_bv 64 0x835ec) fc None mc0 (seg_rom rsegs)).
  Proof.
    intros xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 mc0 flags jj Hjj MU0 WM0 RM0 MI2 FR2 HFj0 HFl HFln HFb H120.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFSb & _).
    unfold ASAN_GT in P3. unfold FS_SIZE in HFSb.
    assert (HKs : FK (fs_frame FS 1 jj) (fs_frame FS 1 jj) A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj))).
    { right. split; [exact Hjj|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact HFj0]. }
    destruct (fk_facts _ _ _ _ _ _ HKs) as (FR8s & FRlos & FRhis & _ & _ & FAPs & FRAs & _ & SH1s & SH2s).
    assert (FL2 : FLG (fs_frame FS 1 jj) 1 (Z_to_bv 64 (fs_flag FS 1 jj)) mc0).
    { split; [exists flags; split; [exact HFl | split; [exact HFln | exact HFb]] | intros _; exact H120]. }
    assert (MU3 : munch (Wf2 (fs_frame FS 1 jj) jj 1) m mc0).
    { eapply munch_weaken; [|exact MU0]. intros x Hx. unfold reac_ctrl_parseF_rbody.RBodyFOn.Wf2 in Hx. cbn [outside] in Hx |- *.
      destruct Hx as (_ & _ & H3 & _). split; [exact H3 | exact I]. }
    step. step. step. step.
    rewrite (rc_neq0_64 (fs_frame FS 1 jj)) by lia. cbn [negb]. cbv iota.
    assert (KBQ : KBx QX)
      by (eapply reac_ctrl_parseF_rbody.RBodyFOn.body_holds_x; first [exact L_exit_x | eassumption]).
    apply (evtF_mono _ _ (QX (fs_frame FS 1 jj))).
    2:{ intros ms' [[E _] | [_ Hr]]; [exfalso; clear -E FRlos P1; lia | exact Hr]. }
    eapply (fwords_x (fs_frame FS 1 jj) (fs_frame FS 1 jj) A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)));
      [exact HKs | | exact FL2 | exact KBQ].
    refine (conj MU3 (conj WM0 (conj RM0 (conj MI2 FR2)))).
  Qed.

  (* The post of the whole stretch after the call: Qp, the exact writes from m, and flag jj read as 0 again. *)
  Definition QF (jj : Z) : machine_state -> Prop :=
    fun ms => Qp ms /\
      (exists ob, OB (fs_frame FS 1 jj) ob /\
         munch (Wf2 (fs_frame FS 1 jj) jj 1 ++ [(ob, ob + 36)]) m (ms_mem ms)) /\
      bytes_at rsegs (ms_mem ms) (fs_flag FS 1 jj) [Z_to_bv 8 0].

  (* The stretch after the call, whole (new composition): post_call_F2, the release store `sb zero, 0(a1)` at 0x83990
     (reac_ctrl_parseF.v :5925-5951, stepped as reac_ctrl_parseF_cut.v (not in this delivery) steps it), post_release_F2. *)
  Lemma post_all_F2 : forall (xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word) (mc0 : word -> option byte)
      (flags : list byte) (jj : Z),
    0 <= jj < fs_M 1 ->
    munch [(fs_flag FS 1 jj, fs_flag FS 1 jj + 1)] m mc0 -> wmono rsegs m mc0 -> rd_mono m mc0 ->
    mem_inv rsegs mc0 -> rw_cells rsegs mc0 (S - 96) SAVES ->
    bytes_at rsegs m (fs_flag FS 1 jj) [Z_to_bv 8 0] ->
    bytes_at rsegs mc0 (fs_flag FS 1 0) flags -> Z.of_nat (length flags) = fs_M 1 ->
    Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
    bytes_at rsegs mc0 (fs_frame FS 1 jj + 120) (le8 (Z_to_bv 64 (fs_flag FS 1 jj))) ->
    evtF rsegs RNG (QF jj)
      (MS (mkR xra (Z_to_bv 64 A) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 A) (Z_to_bv 64 (fs_frame FS 1 jj))
               x1 x2 x3 x4 x5 x6 x7 s2 s3 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n) s7 s8 (wa ASAN_K) s10 s11
               u3 u4 u5 u6)
          F (Z_to_bv 64 0x835ec) fc None mc0 (seg_rom rsegs)).
  Proof.
    intros xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 mc0 flags jj Hjj MU0 WM0 RM0 MI2 FR2 HFj0 HFl HFln HFb H120.
    eapply evtF_cut;
      [exact (post_call_F2 xra u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 mc0 flags jj Hjj MU0 WM0 RM0 MI2 FR2 HFj0
                HFl HFln HFb H120) |].
    intros ms RSt. unfold RelSt2 in RSt.
    destruct RSt as (j & mc & mr & y1 & y5 & y6 & y7 & y9 & y11 & y12 & y13 & y14 & y15 & y16 & y19 & y20 & y21
                     & y22 & y25 & y26 & y28 & y29 & y30 & y31 & Ems & RF & (ob & HOB & MUa)).
    subst ms.
    pose proof RF as RF'. unfold reac_ctrl_parseF_bnd.BndFOn.RelFacts in RF'.
    destruct RF' as (HKc & _ & _ & _ & _ & WMr & _).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts _ _ _ _ _ _ HKc) as (FR8 & FRlo & _).
    pose proof HKc as HK.
    destruct HK as [(Efv & _) | (Hj & Efra & _ & _ & _ & _ & _)]; [exfalso; clear -Efv FRlo Pfs0; lia|].
    assert (EFRk : forall k, fs_frame FS 1 k = FS + 1085440 + k * 128)
      by (intros k; unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
    assert (Ejj : jj = j) by (rewrite !EFRk in Efra; clear -Efra; lia).
    subst jj.
    (* the release store `sb zero, 0(a1)` at 0x83990: reac_ctrl_parseF.v :5925-5951, as reac_ctrl_parseF_cut.v (not in this delivery) *)
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    rewrite EM1 in Hj.
    assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (EFLj : fs_flag FS 1 j = FS + 20480 + j)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (Rfl : 0 <= fs_flag FS 1 j < 2 ^ 64)
      by (rewrite EFLj; clear -Pfs0 HFSb HAE Hj; unfold APPMEM_END in *; lia).
    assert (Uflag : bv_unsigned (Z_to_bv 64 (fs_flag FS 1 j)) = fs_flag FS 1 j)
      by (apply unsigned_lit; exact Rfl).
    assert (SOK : store_ok rsegs mr (wa (fs_flag FS 1 j)) 1 = true).
    { eapply (wv_store_ok m mr (fs_flag FS 1 j) 1%nat).
      - intros i0 Hi0. replace (fs_flag FS 1 j + i0) with (fs_flag FS 1 j) by (cbn in Hi0; lia).
        apply (stk_wv m FS (FS + FS_SIZE) (fs_flag FS 1 j) Pfsstk).
        rewrite EFLj; clear -Pfs0 HFSb Hj; unfold FS_SIZE; lia.
      - exact WMr.
      - clear -Rfl; lia.
      - clear -Rfl; cbn; lia. }
    assert (RGFLj : rng RNG (fs_flag FS 1 j) 1).
    { assert (EMj : fs_M 1 = 8192) by reflexivity.
      eapply rng_sub; [exact RFLG | rewrite !fs_flag1; lia | rewrite !fs_flag1; lia]. }
    step.
    replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
    (* the stretch [just after the release store .. ret], then the post's exact writes and flag *)
    eapply evtF_mono;
      [exact (post_release_F2 (fs_frame FS 1 j) j mc mr y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y19 y20 y21 y22 y25
                y26 y28 y29 y30 y31 RF) |].
    intros ms' [HQ Hm]. split; [exact HQ|]. rewrite Hm. split.
    - exists ob. split; [exact HOB|]. eapply munch_trans; [exact MUa|].
      apply (munch_write _ mr mr (fs_flag FS 1 j) [Z_to_bv 8 0] (munch_refl _ mr));
        [clear -Rfl; lia | cbn [length Z.of_nat]; clear -Rfl; lia |].
      unfold reac_ctrl_parseF_rbody.RBodyFOn.Wf2. cbn [app lib.Lib.Frame.inside length Z.of_nat]. right; right; left. lia.
    - apply bytes_at_write_same; [clear -Rfl; lia | cbn [length Z.of_nat]; clear -Rfl; lia].
  Qed.

End RPostF.

End RPostFOn.

(* ==== Route (C) (a Theorem Labs lane 09:20Z; two Theorem Labs lanes 13:03Z step 3): Module RCutFOn, the composition check of the re-based
   route under route (C), in reac_ctrl_parseF_cut.v's (not in this delivery) CutFOn form: this Section's premises are CutFOn's (the callees'
   `_F_on` contracts, SR0 : shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m at the entry memory m), and
   parse_run_rcut proves reac_ctrl_parseF.v's parse_run statement through PreFOn.pre_call_F, SMAL
   (asan_stack_malloc_1_contract_F_on of a Theorem Labs lane's asan_stack_malloc_cF_on.v) and RPostFOn.post_all_F2.
   rule 24: no function proved beyond reac_ctrl_parseF.v's own run (proof-index reac_ctrl_parse 2026-10-29
   00:3xZ, exit 0; checker a Theorem Labs lane: CONFIRM). ==== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_parseF_pre asan_stack_malloc_cF_on
  asan_memset_cF_on asan_memcpy_cF_on bcmp_wrap_c_on.
Local Open Scope Z_scope.

Module RCutFOn.

Section RCutF.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte) (RNG : ExecF.footprint).
  (* the callees, in their image-A footprint forms (above: __asan_memset / __asan_memcpy a Theorem Labs lane's shared texts;
     kind_of_link1's from kind_of_link1_c.v) *)
  Hypothesis SMAL : asan_stack_malloc_1_contract_F_on.
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
  Local Notation aout_rt := (@reac_ctrl_parseF.ParseFOn.aout_rt tp m f n o S FS fr junk Rf Rn Ro RS Lfr HOK HHM HAE AO0 X FP0).
  Local Notation aJ_free := (@reac_ctrl_parseF.ParseFOn.aJ_free tp m f n o S FS fr junk Rf Rn Ro RS Lfr HOK AC0 HHM HAE AO0 X FP0 TLS0).
  Local Notation Wex := (@reac_ctrl_parseF.ParseFOn.Wex o S FS X).
  Local Notation Wexw := (@reac_ctrl_parseF.ParseFOn.Wexw o S FS).
  Local Notation Wex_sub_w := (@reac_ctrl_parseF.ParseFOn.Wex_sub_w o S FS X).
  Local Notation sh_hi_small_out := (@reac_ctrl_parseF.ParseFOn.sh_hi_small_out m f n o S fr junk Rf Rn Ro RS Lfr HOK HHM AO0).
  Local Notation wex_sh_out := (@reac_ctrl_parseF.ParseFOn.wex_sh_out tp m f n o S FS fr junk Rf Rn Ro RS S16 Lfr HOK HHM HAE AO0 X FP0).
  Local Notation Wex_free := (@reac_ctrl_parseF.ParseFOn.Wex_free tp m f n o S FS fr junk Rf Rn Ro RS S16 ST0 Lfr HOK AC0 SR0 HHM HAE AO0 X FP0 TLS0).
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
  (* Route (C): Module ParseFOn's region lemmas, at this Section's variables (arguments read off `About`). *)
  Local Notation srw_smal := (@reac_ctrl_parseF.ParseFOn.srw_smal f n o S FS).
  (* the cut points of reac_ctrl_parseF_bnd.v, at this Section's variables *)
  Local Notation PreCall := (@reac_ctrl_parseF_bnd.BndFOn.PreCall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S).
  Local Notation RelFacts := (@reac_ctrl_parseF_bnd.BndFOn.RelFacts ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m n o S FS fr X).
  Local Notation RelSt := (@reac_ctrl_parseF_bnd.BndFOn.RelSt ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n o S FS fr X).
  (* the stretch to the call, at this Section's variables *)
  Local Notation pre_call_F := (@reac_ctrl_parseF_pre.PreFOn.pre_call_F ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr RNG Rf Rn Ro RS S16 ST0 MI0 Lfr AC0 HHM HAE X FP0 RIMG RWIN).

  (* The check of the RE-BASED route (the cgif-form walk's): PreFOn.pre_call_F to the call, SMAL (the class-1 _F_on)
     at the call, then for the side-stack frame fs_frame FS 1 jj RPostFOn.post_all_F2 with its Section base at mB, the
     return memory with flag jj read as 0 (write_to_mem of the flag byte), every premise of that Section at mB from
     this Section's at m (m -> mB writes only inside Wf (fs_frame FS 1 jj) jj 1: the window, the class-1 hint word,
     flag jj, the frame's cells and its 16 shadow bytes); QF jj (Qp from mB) gives Qp from m, since m -> mB stays
     inside Qp's footprint. The statement is parse_run's, in the same Section context: the re-based split loses
     nothing. The real-stack arm (the a0 = 0 arm of __asan_stack_malloc_1) is reac_ctrl_parseF.v's own, as in
     reac_ctrl_parseF_cut.v's parse_run_cut. *)
  Lemma parse_run_rcut : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    evtF rsegs RNG Qp (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o)
                     a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
    (* the stretch [entry .. the jal at 0x835e8] *)
    eapply evtF_cut; [exact (pre_call_F t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m eq_refl) |].
    intros ms PC. unfold reac_ctrl_parseF_bnd.BndFOn.PreCall in PC.
    destruct PC as (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m1 & Ems & MU & WM
                    & RM & MI & FR & STA).
    subst ms.
    (* __asan_stack_malloc_1 by SMAL, as entry applies it (reac_ctrl_parseF.v :4964-4966, :4992-4999, :5002-5065) *)
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (fpx_fp_nil _ _ _ _ _ _ _ _ _ FP0) as FPm. unfold reac_ctrl_parse_W in FPm.
    pose proof (fl_fp [1%nat] m m1 _ FS _ _ _ _ _ FPm MU WM ltac:(intros x Hx; exact Hx)) as FP1.
    destruct FP1 as (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
    pose proof HCL as HCL0. apply Forall_cons_iff in HCL0.
    destruct HCL0 as [(_ & h & flags & HH & HFl & HFln & HFb) _].
    pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
    cbn [fp_tls app] in Hw0.
    repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    (* the thread cells' pointers at m1 are those at m (the prologue wrote only the window), so the statement's rng
       facts on the cells of fp_tls (RTLS, at m) name the cells the frame routine reads *)
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd0 & _).
    pose proof (fl_cols (reac_ctrl_parse_W o S) [(S - 8800, S)] _ HWd0
                  ltac:(unfold sub_fp, reac_ctrl_parse_W; intros xq Hxq; cbn [outside] in Hxq |- *;
                        split; [exact (proj1 Hxq) | exact I])) as HCOLa.
    assert (HCOL0 : Forall (fun d => forall x, fst d <= x < snd d -> outside [(S - 8800, S)] x)
                      (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0))
      by (rewrite Forall_forall in HCOLa |- *; intros dq Hdq; apply HCOLa, in_or_app; left; exact Hdq).
    destruct (fl_tls_same m m1 [(S - 8800, S)] (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k
                HT0 HT MU HCOL0) as (EDT & ETS & EC & ET & EDB & Ekq).
    subst DT0 TS0 C0 T0 DB0 k0.
    pose proof SMAL as HM.
    unfold asan_stack_malloc_1_contract_F_on, asan_stack_malloc_contract_F_on in HM. cbv zeta in HM.
    specialize (HM (proj1 (Nat.leb_le 1 10) eq_refl)).
    eapply evtF_cut.
    { destruct (rcpF_tls_rng RNG _ DT TS C T DB k (RTLS DT TS C T DB k HT0))
        as (RTdt & RTts & RTc & RTt & RTdb & RTp88 & RTp8).
      eapply HM with (lo := S - 8800) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
        (DB := DB) (k := k) (flags := flags); unfold ASAN_STACK_MALLOC_K; rewrite ?(unsigned_lit A) by lia.
      - rewrite unsigned_lit by lia. unfold fs_B. cbn. lia.
      - rewrite unsigned_lit by lia. reflexivity.
      - exact (fl_asan_cells _ m m1 AC0 MU ltac:(intros x Hx; cbn [outside]; unfold RT_LO, RT_HI in Hx; split; [lia | exact I])).
      - exact (srw_smal m1 (shadow_rw_mono_on _ m m1 SR0 WM RM)).
      - exact MI.
      - exact HT.
      - intros Hc. lia.
      - exact HTP.
      - exact HP.
      - exact H88.
      - exact H96.
      - exact HH.
      - exact HFl.
      - exact HFln.
      - exact HFb.
      - exact STA.
      - lia.
      - lia.
      - intros a Ha. apply HAPP. lia.
      - cbn [disjoint_from].
        repeat split; try exact I;
          match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
            match goal with Hd : RcLay.ly_dj _ _ lo hi |- _ => unfold RcLay.ly_dj in Hd; lia end end.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* the callee's window [A - K, A) inside this function's window *)
        eapply rng_sub; [exact RWIN | lia | lia].
      - (* the runtime pointer cell at DT + 8 *) exact RTdt.
      - (* the runtime pointer cell at TS + 8 k *) exact RTts.
      - (* the runtime pointer cell at C + 152 *) exact RTc.
      - (* the runtime pointer cells at T + 48 *) exact RTt.
      - (* the runtime pointer cell at DB + 24 *) exact RTdb.
      - (* the side stack's header *) exact RFSS.
      - (* the class-1 frame area, from the frames' range in fp_w [1%nat] FS *) exact (rcpF_frame_area RNG FS RFW1).
      - (* the shadow of the class-1 frame area *) exact (rcpF_frame_sh RNG FS RFW1).
      - (* the thread-pointer cell at TP - 88 *) exact RTp88.
      - (* the thread-pointer cells at TP - 8 .. TP + 16 *) exact RTp8. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E & WM2 & MI2 & ST2
                    & HP2 & (h2 & HH2) & ALT).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 0x835ec)) with (Z_to_bv 64 0x835ec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite (unsigned_lit A) in ST2 by lia. unfold ASAN_STACK_MALLOC_K in *.
    unfold fs_hint in HH2. cbn [Z.of_nat] in HH2.
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    destruct ALT as [(Hall & Ex0 & MU2) | (i & Hi & Hpre & Hnth & FRM)].
    - (* the real-stack frame [A - 128, A) *)
      subst x0. rewrite (unsigned_lit A) in MU2 by lia. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2). constructor; [|constructor; [|constructor]]; cbn [fst snd].
        - intros y Hy. apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - intros y Hy. apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf (A - 128) 0 0) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, reac_ctrl_parseF.ParseFOn.Wf, fs_hint. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, reac_ctrl_parseF.ParseFOn.Wf, fs_hint. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add reac_ctrl_parseF.ParseFOn.SAVES];
        lia)) as FR2.
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (FL2 : FLG (A - 128) 0 (Z_to_bv 64 0) m2).
      { split; [|intros HC; discriminate HC].
        exists flags. split; [|split; [exact HFln | exact HFb]].
        eapply fl_bytes; [exact HFl | exact MU2 |].
        intros x Hx. rewrite HFln in Hx. change (fs_M 1) with 8192 in Hx. rewrite EFL0 in Hx.
        cbn [outside]. split; [|split; [|exact I]]; clear -Hx HFS' HAlo HAhi RS P1; lia. }
      pose proof (munch_refl [(A - 4096, A - 4088)] m2) as MUp.
      clear MU MU2 WM WM2 RM RM2 FR STA MI.
      unfold reac_ctrl_parseF.ParseFOn.Wf, shadow_addr in MU3.
      step. step. step. step.
      replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
      step. step. step.
      match goal with |- context [Z.land ?x 18446744073709551584] =>
        replace (Z.land x 18446744073709551584) with (A - 128)
          by (rewrite ?(unsigned_lit A), ?unsigned_lit by lia; rewrite land_align32 by lia;
              Z.div_mod_to_equations; lia) end.
      step.
      assert (HSp : store_ok rsegs m2 (wa (A - 4096)) 8 = true)
        by (eapply wv_store_ok with (m := m2);
              [ intros i Hi; apply (stk_wv m2 (S - 8800) A); [exact ST2 | lia] | apply wmono_refl | lia | lia ]).
      rewrite (unsigned_lit A) by lia.
      step. store_done.
      step.
      rewrite (rc_lts_signed (A - 128) (A - 4096)) by lia.
      replace (A - 128 <? A - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      step.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
        assert (FL3 : FLG (A - 128) 0 (Z_to_bv 64 0) mf) end.
      { destruct FL2 as [(flg & Hfl & Hfln & HflF) _]. split; [|intros HC; discriminate HC].
        exists flg. split; [|split; [exact Hfln | exact HflF]].
        eapply fl_bytes; [exact Hfl | exact MUp |].
        intros x Hx. rewrite Hfln, EFL0 in Hx. change (fs_M 1) with 8192 in Hx.
        cbn [outside]. split; [clear -Hx HFS' HAlo HAhi RS P1; lia | exact I]. }
      eapply (fwords (A - 128) 0 (A - 128) 0 0 (Z_to_bv 64 0)); [left; repeat split; lia | | exact FL3 | exact body_holds].
      refine (conj _ (conj WM3 (conj RM3 (conj MI2 FR2)))). unfold reac_ctrl_parseF.ParseFOn.Wf, shadow_addr. exact MU3.
    - (* the side-stack frame fs_frame FS 1 jj: the RE-BASED stretch RPostFOn.post_all_F2, at the walk's base mB (the
         return memory with flag jj read as 0) *)
      unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
      rewrite (unsigned_lit A) in FRM by lia.
      replace (fs_B 1) with 128 in FRM by reflexivity.
      change (bv_unsigned (Z_to_bv 64 128)) with 128 in FRM.
      replace (fs_shadow_n 1 128) with 16 in FRM by reflexivity.
      destruct FRM as (Ex0 & Hm64 & _ & HFLg & H24 & H120 & HSH & HADD & STF & APF & FSlo & FShi & GT & FRA' & DIS
                       & MU2).
      remember ((bv_unsigned h + i) mod fs_M 1) as jj eqn:Ejj.
      assert (Hjj : 0 <= jj < fs_M 1) by (subst jj; apply Z.mod_pos_bound; reflexivity).
      remember (fs_frame FS 1 jj) as fra eqn:Efr.
      subst x0. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      unfold ASAN_GT in GT. unfold FS_SIZE in FShi.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      assert (Hjj' : 0 <= jj < 8192) by (rewrite EM1 in Hjj; exact Hjj).
      assert (SHb : shadow_addr fra + 16 <= S - 8800)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      assert (EFl : fs_flag FS 1 jj = FS + 20480 + jj)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2).
        repeat constructor; cbn [fst snd]; intros y Hy.
        - apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HFLg). cbn. lia.
        - apply (rd_of_bytes _ _ _ H24). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ H120). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
        - apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf fra jj 1) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, reac_ctrl_parseF.ParseFOn.Wf, fs_hint. cbn [outside].
          intros x Hout. repeat split; try exact I; clear -Hout HAlo HAhi RS; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, reac_ctrl_parseF.ParseFOn.Wf, fs_hint. cbn [outside].
          intros x Hout. repeat split; try exact I; clear -Hout HAlo HAhi RS; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2
        ltac:(cbn [disjoint_from cells_size csize Nat.add reac_ctrl_parseF.ParseFOn.SAVES]; rewrite EFl;
              clear -HFS' FShi Hjj' SHb HAlo HAhi RS; lia)) as FR2.
      (* flag jj was 0 at m1 (the frame __asan_stack_malloc_1 took was free), and the prologue wrote only the window *)
      assert (HFl0 : bytes_at rsegs m (fs_flag FS 1 0) flags).
      { pose proof HFl as (Ba & Bl & BH). split; [exact Ba|]. split; [exact Bl|].
        intros kk Hk. rewrite <- (BH kk Hk). unfold mrd.
        rewrite (MU (wa (fs_flag FS 1 0 + Z.of_nat kk))); [reflexivity|].
        rewrite wa_unsigned by (rewrite EFL0; rewrite EM1 in HFln; clear -Hk HFln P1 HFS' HAlo HAhi RS; lia).
        cbn [outside]. rewrite EFL0. rewrite EM1 in HFln. split; [clear -Hk HFln P1 HFS' HAlo HAhi RS; lia | exact I]. }
      assert (HFj0 : bytes_at rsegs m (fs_flag FS 1 jj) [Z_to_bv 8 0]).
      { pose proof HFl0 as (Ba & Bl & BH).
        assert (HJ : (Z.to_nat jj < length flags)%nat) by (rewrite EM1 in HFln; lia).
        pose proof (BH (Z.to_nat jj) HJ) as E1. rewrite Hnth in E1. rewrite Z2Nat.id in E1 by lia.
        replace (fs_flag FS 1 0 + jj) with (fs_flag FS 1 jj) in E1 by (rewrite EFl, EFL0; lia).
        split; [rewrite EFl; lia|]. split; [cbn [length Z.of_nat Pos.of_succ_nat]; rewrite EFl; lia|].
        intros i0 Hi0. cbn [length] in Hi0. destruct i0 as [|i0]; [|lia].
        cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact E1. }
      assert (HKs : FK fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj))).
      { right. split; [exact Hjj|]. split; [exact Efr|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact HFj0]. }
      destruct (fk_facts fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)) HKs)
        as (FR8 & FRlo & FRhi & _ & FW & FAP & FRA & _ & SH1 & SH2).
      pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                         & HFSb & _ & _ & _).
      unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
      (* the flag array at the return memory: flag jj set to 1 *)
      set (flags2 := upd_bytes flags (Z.to_nat jj) [Z_to_bv 8 1]).
      assert (HFl2 : bytes_at rsegs m2 (fs_flag FS 1 0) flags2).
      { eapply (bytes_at_munch_upd _ m1 m2 (fs_flag FS 1 0) flags (Z.to_nat jj) (Z_to_bv 8 1)).
        - exact HFl.
        - exact MU2.
        - clear -HFln Hjj'; change (fs_M 1) with 8192 in HFln; lia.
        - replace (fs_flag FS 1 0 + Z.of_nat (Z.to_nat jj)) with (fs_flag FS 1 jj)
            by (rewrite EFl, EFL0; clear -Hjj'; lia).
          exact HFLg.
        - intros x Hx Hne. rewrite HFln in Hx. change (fs_M 1) with 8192 in Hx. rewrite EFL0 in Hx.
          rewrite EFL0 in Hne.
          assert (Hxa : app_mem x) by (apply P4; clear -Hx P1 HFS'; unfold FS_SIZE; lia).
          cbn [outside]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
          + clear -Hx P1; lia.
          + rewrite EFl. clear -Hx Hne Hjj'; lia.
          + clear -Hx FRlo; lia.
          + clear -Hx FRlo; lia.
          + intros [HL HR]. apply (acl_app_not_shadow x Hxa). unfold shadow_addr in HL, HR.
            replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
            apply frame_shadow_in;
              [clear -FRlo P1; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
          + clear -Hx HFS' HAlo HAhi RS P1; lia. }
      assert (HFln2 : Z.of_nat (length flags2) = fs_M 1)
        by (unfold flags2; rewrite upd_bytes_length by (cbn [length]; clear -HFln Hjj';
              change (fs_M 1) with 8192 in HFln; lia); exact HFln).
      assert (HFb2 : Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags2)
        by (unfold flags2; apply upd_bytes_01; [exact HFb | right; reflexivity]).
      assert (H120' : bytes_at rsegs m2 (fs_frame FS 1 jj + 120) (le8 (Z_to_bv 64 (fs_flag FS 1 jj))))
        by (rewrite <- Efr; replace (fra + 120) with (fra + 128 - 8) by lia; exact H120).
      (* ---- the base mB: the return memory with flag jj read as 0 (the cgif-form walk's base) ---- *)
      assert (Rfl : 0 <= fs_flag FS 1 jj /\ fs_flag FS 1 jj + 1 <= 2 ^ 64)
        by (rewrite EFl; clear -P1 HFS' HAlo HAhi RS Hjj'; lia).
      set (mB := write_to_mem m2 (wa (fs_flag FS 1 jj)) [Z_to_bv 8 0]).
      assert (MUB : munch (Wf fra jj 1) m mB).
      { apply (munch_write _ m m2 (fs_flag FS 1 jj) [Z_to_bv 8 0] MU3);
          [ clear -Rfl; lia | cbn [length Z.of_nat Pos.of_succ_nat]; clear -Rfl; lia |].
        unfold reac_ctrl_parseF.ParseFOn.Wf. cbn [lib.Lib.Frame.inside length Z.of_nat Pos.of_succ_nat].
        right; right; left. lia. }
      assert (WMB : wmono rsegs m mB) by (apply wmono_write; exact WM3).
      assert (RMB : rd_mono m mB) by (apply rd_mono_write; exact RM3).
      assert (SUBall : sub_fp (Wf fra jj 1)
                         (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++ [(shadow_addr (S - 8800), shadow_addr S)]))
        by (intros x Hx; apply (subWf_Wex _ _ _ _ _ _ HKs); apply (Wex_subfp _ _ _ _ _ _ HKs); exact Hx).
      assert (MUBe : munch (Wex fra) m mB)
        by (eapply munch_weaken; [exact (subWf_Wex _ _ _ _ _ _ HKs) | exact MUB]).
      pose (ob := if o =? 0 then fra + 32 else o).
      assert (HOB : OB fra ob)
        by (unfold reac_ctrl_parseF.ParseFOn.OB, ob; destruct (Z.eqb_spec o 0) as [Eo|Eo];
            [left; split; [exact Eo | reflexivity] | right; split; [exact Eo | reflexivity]]).
      assert (MUBa : munch (Wall fra jj 1 ob) m mB).
      { eapply munch_weaken; [|exact MUB]. unfold sub_fp, reac_ctrl_parseF.ParseFOn.Wall. intros x Hx.
        unfold reac_ctrl_parseF.ParseFOn.Wf in *. cbn [app outside] in Hx |- *.
        destruct Hx as (H1 & H2 & H3 & H4 & H5 & _). repeat split; assumption. }
      assert (AobX : exists mcX, addressable mcX ob 36).
      { unfold ob. destruct (Z.eqb_spec o 0) as [Eo|Eo].
        - exists m2. apply (acl_addr_sub m2 fra 128 (fra + 32) 36 HADD); lia.
        - exists m. exact (proj1 (AO0 Eo)). }
      destruct AobX as (mcX & AobX).
      (* the base's links to the return memory m2: m2 is mB with flag jj set to 1 *)
      assert (MU0 : munch [(fs_flag FS 1 jj, fs_flag FS 1 jj + 1)] mB m2).
      { intros x Hx. unfold mB. rewrite write_to_mem_spec by (cbn [length Z.of_nat Pos.of_succ_nat]; clear -Rfl; lia).
        cbn [outside length Z.of_nat Pos.of_succ_nat] in Hx |- *. destruct Hx as [Hx _].
        destruct (Z.leb_spec0 (fs_flag FS 1 jj) (bv_unsigned x)); cbn [andb]; [|reflexivity].
        destruct (Z.ltb_spec0 (bv_unsigned x) (fs_flag FS 1 jj + Z.of_nat 1)); [exfalso; lia | reflexivity]. }
      assert (STfs2 : stk rsegs m2 FS (FS + FS_SIZE)) by (destruct HP2 as (_ & _ & _ & _ & HS2); exact HS2).
      assert (WM0 : wmono rsegs mB m2).
      { intros x Hx. destruct (Z.eq_dec (bv_unsigned x) (fs_flag FS 1 jj)) as [Ex|Ex].
        - rewrite <- (wa_of_var x _ Ex).
          apply (stk_wv m2 FS (FS + FS_SIZE)); [exact STfs2 | rewrite EFl; unfold FS_SIZE; clear -Hjj'; lia].
        - unfold wview in *. rewrite (MU0 x ltac:(cbn [outside]; split; [lia | exact I])). exact Hx. }
      assert (RM0 : rd_mono mB m2).
      { apply (rd_mono_list _ _ _ MU0). constructor; [|constructor]. cbn [fst snd]. intros y Hy.
        apply (rd_of_bytes _ _ _ HFLg). cbn. lia. }
      assert (HFjB : bytes_at rsegs mB (fs_flag FS 1 jj) [Z_to_bv 8 0])
        by (apply bytes_at_write_same; [clear -Rfl; lia | cbn [length Z.of_nat Pos.of_succ_nat]; clear -Rfl; lia]).
      (* ---- the re-based Section's premises at mB, from this Section's at m ---- *)
      pose proof (stk_mono m mB (S - 8800) S ST0 WMB RMB) as STB.
      assert (HrdB : forall kk, In kk (cp_rd n fr) -> mrd rsegs mB (wa (f + Z.of_nat kk)) = nth_error fr kk).
      { intros kk Hk. rewrite <- (Hrd kk Hk).
        assert (Hn50 : 50 <= n)
          by (unfold cp_rd in Hk; destruct (50 <=? n) eqn:E50; cbn [negb] in Hk;
              [apply Z.leb_le; exact E50 | destruct Hk]).
        pose proof (cp_rd_lt39 n fr kk Hk) as Hk39.
        destruct (f_facts Hn50 fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)) ob HKs HOB)
          as (Hf0 & Hf1 & _ & _ & HdjW).
        unfold mrd. rewrite (MUB (wa (f + Z.of_nat kk))); [reflexivity|].
        rewrite wa_unsigned by lia.
        unfold reac_ctrl_parseF.ParseFOn.Wall, reac_ctrl_parseF.ParseFOn.Wf in HdjW.
        unfold reac_ctrl_parseF.ParseFOn.Wf. cbn [app disjoint_from] in HdjW. cbn [outside].
        destruct HdjW as (D1 & D2 & D3 & D4 & D5 & _).
        repeat split; try exact I; intros [HL HR]; lia. }
      assert (HOKB : o <> 0 ->
          o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs mB o [CB 36 junk] /\
          (o + 36 <= S - 8800 \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)).
      { intros Eo. destruct (HOK Eo) as (Ho4 & Ho36 & HOrw & HoS & Hof).
        split; [exact Ho4|]. split; [exact Ho36|]. split; [|split; [exact HoS | exact Hof]].
        assert (HinO : In (o, o + 36) (reac_ctrl_parse_D f n o))
          by (unfold reac_ctrl_parse_D; apply in_or_app; right;
              rewrite (proj2 (Z.eqb_neq o 0) Eo); left; reflexivity).
        assert (Hdjo : forall x, o <= x < o + 36 -> outside (Wf fra jj 1) x).
        { intros x Hx.
          destruct (AO0 Eo) as (AOa & _ & _).
          assert (Hxapp : app_mem x)
            by (pose proof (acl_app_in m o 36 (x - o) AOa ltac:(lia)) as Ha;
                replace (o + (x - o)) with x in Ha by lia; exact Ha).
          pose proof (dj_pair o (o + 36) _ _ HinO (proj1 (fp_wx_hint_flag_in FS X))) as Hoh.
          pose proof (dj_pair o (o + 36) _ _ HinO (proj2 (fp_wx_hint_flag_in FS X))) as Hofl.
          unfold reac_ctrl_parseF.ParseFOn.Wf. cbn [outside].
          split; [| split; [| split; [| split; [| split; [| exact I]]]]].
          - clear -Hx HoS; destruct HoS; lia.
          - intros [HL HR]. clear -Hx HL HR Hoh; lia.
          - intros [HL HR]. rewrite EFl in HL, HR. rewrite EM1, EFL0 in Hofl. clear -Hx HL HR Hofl Hjj'; lia.
          - intros [HL HR].
            destruct (D_apart_frame o (o + 36) jj HinO ltac:(clear; lia) Hjj HFj0) as [Hc|Hc];
              rewrite <- Efr in Hc; clear -Hx HL HR Hc; lia.
          - intros [HL HR]. apply (acl_app_not_shadow x Hxapp). unfold shadow_addr in HL, HR.
            replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
            apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia]. }
        eapply acl_rw; [exact HOrw | exact MUB | exact WMB |
          intros x Hx; apply Hdjo; cbn [cells_size csize] in Hx; lia]. }
      assert (AOB : o <> 0 -> addressable mB o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)).
      { intros Eo. destruct (AO0 Eo) as (AOa & AOapp & AOcf). split; [|split; [exact AOapp | exact AOcf]].
        destruct (HOK Eo) as (_ & _ & _ & HoS & _).
        assert (HinO : In (o, o + 36) (reac_ctrl_parse_D f n o))
          by (unfold reac_ctrl_parse_D; apply in_or_app; right;
              rewrite (proj2 (Z.eqb_neq o 0) Eo); left; reflexivity).
        apply (acl_addr_munch (Wf fra jj 1) m mB o 36 AOa MUB).
        intros kk Hk.
        pose proof (acl_app_in m o 36 kk AOa Hk) as Hoi.
        pose proof (rt_app_shadow (o + kk) Hoi) as Hsh.
        unfold reac_ctrl_parseF.ParseFOn.Wf. cbn [outside].
        split; [| split; [| split; [| split; [| split; [| exact I]]]]].
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + kk))); [| exact Hsh].
          unfold app_mem, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *; clear -HL HR HHM HAE; right; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + kk))); [| exact Hsh].
          apply Pfsapp. unfold fs_hint in HL, HR; cbn [Z.of_nat] in HL, HR;
            unfold FS_SIZE; clear -HL HR Pfs0; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + kk))); [| exact Hsh].
          apply Pfsapp. rewrite EFl in HL, HR. unfold FS_SIZE; clear -HL HR Pfs0 Hjj'; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + kk))); [| exact Hsh].
          replace (shadow_addr (o + kk)) with (fra + (shadow_addr (o + kk) - fra)) by lia.
          apply FAP; clear -HL HR; lia.
        + intros HC.
          assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
            by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
          rewrite E16 in HC.
          apply (acl_win_sh (o + kk) fra (fra + 128) FR8); [| exact HC].
          intros [HL HR].
          destruct (D_apart_frame o (o + 36) jj HinO ltac:(clear; lia) Hjj HFj0) as [Hc|Hc];
            rewrite <- Efr in Hc; clear -Hk HL HR Hc; lia. }
      assert (AWB : addressable mB (S - 8800) 8800).
      { apply (acl_addr_munch (Wex fra) m mB (S - 8800) 8800 AW0 MUBe).
        intros kk Hk. apply wex_sh_out;
          [ clear -FRlo Pfs0; lia | exact FR8 | | clear -FRhi HAlo HAhi HAE; unfold APPMEM_END in *; lia
          | lia | clear -FShi HFSb Hk; unfold FS_SIZE in *; lia ].
        replace fra with (fra + 0) by lia. apply FAP. lia. }
      assert (AFB : 50 <= n -> addressable mB f 50)
        by (intros Hn50; exact (af_mx Hn50 fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)) ob mcX mB HKs HOB AobX MUBa)).
      pose proof (abc_mx fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)) ob mcX mB HKs HOB AobX MUBa) as ABCB.
      destruct (cl_mx fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)) ob mB HKs HOB MUBa)
        as (HBCMPB & HMEMCMPB & HGCFB & HCF254B & HCF255B).
      assert (XFB : Forall (fun ci => fst ci = 1%nat /\ bytes_at rsegs mB (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1])
                      X).
      { pose proof (x_ne_j jj HFj0) as Hne. pose proof XF0 as XF0'. rewrite Forall_forall in XF0', Hne |- *.
        intros ci Hci. destruct (XF0' ci Hci) as [H1 Hb]. split; [exact H1|].
        destruct (x_flag_in ci Hci) as (Ef & Hlo & Hhi).
        eapply fl_bytes; [exact Hb | exact MUB |].
        intros x Hx. cbn [length Z.of_nat Pos.of_succ_nat] in Hx. rewrite Ef in Hx.
        apply (flag_out_Wf fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)) x HKs).
        - rewrite EFL0, EM1 in *. clear -Hx Hlo Hhi; lia.
        - intros [HL HR]. apply (Hne ci Hci).
          assert (Eci : fs_flag FS 1 (snd ci) = FS + 20480 + snd ci)
            by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
          rewrite Eci in Hx. rewrite EFl in HL, HR. clear -Hx HL HR; lia. }
      assert (HHB : exists h', bytes_at rsegs mB (fs_hint FS 1) (le8 h')).
      { exists h2. unfold mB. apply bytes_at_write_other; [exact HH2 | clear -Rfl; lia | cbn; clear -Rfl; lia |].
        rewrite length_le8. unfold fs_hint. cbn [Z.of_nat length]. rewrite EFl. clear -Hjj'; lia. }
      assert (FLB : forall fl, bytes_at rsegs m (fs_flag FS 1 0) fl -> (length fl <= Z.to_nat (fs_M 1))%nat ->
                bytes_at rsegs mB (fs_flag FS 1 0) fl).
      { intros fl (B0 & B1 & B2) Hl. split; [exact B0|]. split; [exact B1|]. intros kk Hk.
        rewrite <- (B2 kk Hk).
        assert (Rk : 0 <= fs_flag FS 1 0 + Z.of_nat kk < 2 ^ 64)
          by (rewrite EFL0; rewrite EM1 in Hl; clear -Hk Hl P1 HFS' HAlo HAhi RS; lia).
        destruct (Z.eq_dec (fs_flag FS 1 0 + Z.of_nat kk) (fs_flag FS 1 jj)) as [E|E].
        - rewrite E. pose proof HFjB as (_ & _ & Hw). pose proof HFj0 as (_ & _ & H0).
          specialize (Hw 0%nat ltac:(cbn; lia)). specialize (H0 0%nat ltac:(cbn; lia)).
          cbn [Z.of_nat] in Hw, H0. rewrite Z.add_0_r in Hw, H0. rewrite Hw, H0. reflexivity.
        - unfold mrd. rewrite (MUB (wa (fs_flag FS 1 0 + Z.of_nat kk))); [reflexivity|].
          rewrite wa_unsigned by exact Rk.
          apply (flag_out_Wf fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)) _ HKs).
          + rewrite EFL0. rewrite EM1 in Hl. clear -Hk Hl; lia.
          + intros [HL HR]. apply E. clear -HL HR; lia. }
      assert (HFLB : exists flags', bytes_at rsegs mB (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
                       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags').
      { exists flags. split; [|split; [exact HFln | exact HFb]].
        apply FLB; [exact HFl0 | rewrite EM1 in HFln; lia]. }
      destruct (Wex_free fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)) mB HKs MUBe WMB RMB HHB HFLB)
        as (ACB & SRBall & FPB & TLSB).
      pose proof (SRBall _ SR0) as SRB.
      clear MU MU2 WM WM2 RM RM2 FR STA MI.
      (* ---- the re-based stretch at the base mB, to QF jj ---- *)
      subst fra.
      eapply evtF_mono.
      { eapply (reac_ctrl_parseF_rpost.RPostFOn.post_all_F2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mB
                  f n o S FS fr junk RNG HMSET HMCPY HBCMPW HKOL Rf Rn Ro RS S16 STB Lfr HF HrdB HOKB ACB SRB HHM HAE
                  AWB AFB AOB ABCB HBCMPB HMEMCMPB HGCFB HCF254B HCF255B X XFB XB0 FPB TLSB RBY RIMG RWIN SCW SKW
                  RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR);
          [ exact Hjj | exact MU0 | exact WM0 | exact RM0 | exact MI2 | exact FR2 | exact HFjB | exact HFl2
          | exact HFln2 | exact HFb2 | exact H120' ]. }
      (* QF jj is Qp from mB, the exact writes and flag jj; Qp from m follows (m -> mB is inside Qp's footprint) *)
      intros ms' (HQ & _ & _).
      destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ems'
                      & MUf & WMf & MIf & STf & RWo & ACf & SRf & AWf & FPf & XFf & FLf & TLSf).
      exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [exact Ems'|].
      split; [exact (munch_trans _ m mB m' (munch_weaken _ _ m mB SUBall MUB) MUf)|].
      split; [exact (wmono_trans rsegs _ _ _ WMB WMf)|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact RWo|]. split; [exact ACf|].
      split; [intros Pq HPq; exact (SRf Pq (shadow_rw_mono_on Pq m mB HPq WMB RMB))|].
      split; [exact AWf|]. split; [exact FPf|]. split; [exact XFf|].
      split; [intros fl Hl Hb; exact (FLf fl Hl (FLB fl Hb Hl))|].
      exact TLSf.
  Qed.

End RCutF.

End RCutFOn.
