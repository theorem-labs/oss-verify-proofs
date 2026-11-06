(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3501 of its 3539 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_ctrl_parseF.v, with its module paths, module names, addresses and numbers changed; 264 of its 382 lines of code are new or changed and 3421 lines of the source are left out. *)
(* reac_ctrl_parse, image A (asan, fuzz_ctrl v1.9.0): the stretch [entry 0x83578 .. the jal __asan_stack_malloc_1
   at 0x835e8] of the footprint run of reac_ctrl_parseF.v, ending at the entry of __asan_stack_malloc_1 (PreCall of
   reac_ctrl_parseF_bnd.v). Route (a): the proof is the script of reac_ctrl_parseF.v's entry (:1550-1579, then the
   stack facts of :1588-1589), unchanged, cut at its call (no new proof obligation); the callee is not walked.
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

Section PreF.
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
  (* the cut points of reac_ctrl_parseF_bnd.v, at this Section's variables *)
  Local Notation PreCall := (@reac_ctrl_parseF_bnd.PreCall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S).
  Local Notation RelFacts := (@reac_ctrl_parseF_bnd.RelFacts ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m n o S FS fr X).
  Local Notation RelSt := (@reac_ctrl_parseF_bnd.RelSt ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n o S FS fr X).


  (* reac_ctrl_parseF.v's entry (:1545) up to the jal at 0x835e8: the prologue, the GOT loads of the shadow offset and
     the use-after-return flag, a0 = 128, the jal (ra = 0x835ec). *)
  Lemma pre_call_F : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m0 : word -> option byte), m0 = m ->
    evtF rsegs RNG PreCall
      (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m0 Em0.
    unfold REAC_CTRL_PARSE.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (fpx_fp_nil _ _ _ _ _ _ _ _ _ FP0) as FPm. unfold reac_ctrl_parse_W in FPm.
    assert (MU : munch [(S - 8800, S)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rd_mono m m0) by (subst m0; apply rd_mono_refl).
    assert (MI : mem_inv rsegs m0) by (subst m0; exact MI0).
    pose proof AC0 as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST0 as ST0c. rewrite <- Em0 in ST0c.
    pose proof (stk_split rsegs m0 _ (S - 96) _ ST0c ltac:(lia)) as [STw STs].
    pose proof (stk_split rsegs m0 _ (S - 128) _ STw ltac:(lia)) as [STw2 STz].
    clear ST0c.
    carve_frame 96%nat STs.
    carve_frame 32%nat STz.
    step.
    steps_to 0x835b4.
    step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = A)
      by (rewrite unsigned_lit, land_align32 by lia; unfold A; f_equal; f_equal; lia).
    rewrite EA.
    steps_to 0x835e0.
    step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (stk_merge rsegs m1 _ _ _ STw2 STz ltac:(lia)) as STzc.
    destruct (stk_split rsegs m1 _ A _ STzc ltac:(lia)) as [STA _].
    apply evtF_done. unfold reac_ctrl_parseF_bnd.PreCall.
    do 14 eexists. exists m1. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact RM|]. split; [exact MI|]. split; [exact FR | exact STA].
  Qed.

End PreF.

(* ==== Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery) and its 09:58Z ruling): Module PreFOn
   re-derives Section PreF above, with the same names and scripts, for reac_ctrl_parseF.v's Module ParseFOn: the
   callees' `_F_on` contracts, SR0 : shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m, every reac_ctrl_parseF.v /
   split-file Section name redirected to its route-(C) module (ParseFOn, BndFOn, PreFOn, RelFOn, BodyFOn, PostFOn; the
   notation arguments read off `About` of each), and reac_ctrl_parseF.v's shadow edits where these scripts carry them
   (the region lemmas srw_* / frame_in_R; the post's forall-P form). Section PreF above keeps its code byte-identical.
   rule 24: no function proved beyond reac_ctrl_parseF.v's own run (proof-index reac_ctrl_parse 2026-10-29
   00:3xZ, exit 0: 12 named files + 8 lemma rows, plain / ubsan builds of other units; checker a Theorem Labs lane: CONFIRM). ==== *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF_on
  asan_memcpy_cF_on bcmp_wrap_c_on.
Local Open Scope Z_scope.

Module PreFOn.

Section PreF.
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
  (* the cut points of reac_ctrl_parseF_bnd.v, at this Section's variables *)
  Local Notation PreCall := (@reac_ctrl_parseF_bnd.BndFOn.PreCall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S).
  Local Notation RelFacts := (@reac_ctrl_parseF_bnd.BndFOn.RelFacts ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m n o S FS fr X).
  Local Notation RelSt := (@reac_ctrl_parseF_bnd.BndFOn.RelSt ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n o S FS fr X).


  (* reac_ctrl_parseF.v's entry (:4957) up to the jal at 0x835e8: the prologue, the GOT loads of the shadow offset and
     the use-after-return flag, a0 = 128, the jal (ra = 0x835ec). *)
  Lemma pre_call_F : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m0 : word -> option byte), m0 = m ->
    evtF rsegs RNG PreCall
      (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m0 Em0.
    unfold REAC_CTRL_PARSE.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (fpx_fp_nil _ _ _ _ _ _ _ _ _ FP0) as FPm. unfold reac_ctrl_parse_W in FPm.
    assert (MU : munch [(S - 8800, S)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rd_mono m m0) by (subst m0; apply rd_mono_refl).
    assert (MI : mem_inv rsegs m0) by (subst m0; exact MI0).
    pose proof AC0 as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST0 as ST0c. rewrite <- Em0 in ST0c.
    pose proof (stk_split rsegs m0 _ (S - 96) _ ST0c ltac:(lia)) as [STw STs].
    pose proof (stk_split rsegs m0 _ (S - 128) _ STw ltac:(lia)) as [STw2 STz].
    clear ST0c.
    carve_frame 96%nat STs.
    carve_frame 32%nat STz.
    step.
    steps_to 0x835b4.
    step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = A)
      by (rewrite unsigned_lit, land_align32 by lia; unfold A; f_equal; f_equal; lia).
    rewrite EA.
    steps_to 0x835e0.
    step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (stk_merge rsegs m1 _ _ _ STw2 STz ltac:(lia)) as STzc.
    destruct (stk_split rsegs m1 _ A _ STzc ltac:(lia)) as [STA _].
    apply evtF_done. unfold reac_ctrl_parseF_bnd.BndFOn.PreCall.
    do 14 eexists. exists m1. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact RM|]. split; [exact MI|]. split; [exact FR | exact STA].
  Qed.

End PreF.

End PreFOn.
