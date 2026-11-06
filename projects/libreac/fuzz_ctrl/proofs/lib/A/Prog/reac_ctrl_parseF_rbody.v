(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 2093 of its 2111 lines of code are new or changed and 230 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/C_reac_ctrl_parseLib.v, with its module paths, module names, addresses and numbers changed; 2748 of its 2983 lines of code are new or changed and 1876 lines of the source are left out. *)
(* reac_ctrl_parse, image A (asan, fuzz_ctrl v1.9.0): the body of reac_ctrl_parseF_body.v (not in this delivery), RE-BASED for the cgif-form
   walk (a Theorem Labs lane 23:53Z ruling (2): a re-based Section copy of the stretch after the fake-stack call, the instruction
   proofs verbatim, every re-proved helper named below).  The walk instantiates the Section's base memory m with the
   memory at the return of __asan_stack_malloc_1 (flag jj read as 0), so the frame block's write set no longer needs
   the class-1 hint word: __asan_stack_malloc_1 wrote it before the base.  The journal step after the lift needs the
   EXACT write set (every written byte an awr_byte or the released flag; the hint word is allocator-owned), so:
   - Wf2 is Wf (reac_ctrl_parseF.v:1196) with the hint interval (fs_hint FS 1, fs_hint FS 1 + 8) replaced by the
     empty interval (fs_hint FS 1, fs_hint FS 1) (the list keeps its shape, so every `outside` proof keeps its shape);
     Wf2_sub (new, 3 lines): Wf2 is inside Wf;
   - KBx, fwords_x, L_join, L_kind, L_be0, L_bdc, body_copy, body_tail, body_main, body_holds_x: BI (Wf2 fra j nn) ->
     BI (Wf2 fra j nn) in the statements; in fwords_x the two `unfold reac_ctrl_parseF.Wf` read `unfold Wf2`; in
     body_holds_x the four uses of `Wf fra j nn` / `unfold reac_ctrl_parseF.Wf` read Wf2;
   - HEXIT gains one premise, the exact writes from m: exists ob, OB fra ob /\ munch (Wf2 fra j nn ++ [(ob, ob + 36)])
     m mc; L_join keeps the Wf2 munch (MUw), weakens a copy to Wf for its unchanged script (Wf2_sub), and proves the
     new premise (one bullet, munch_trans of MUw and its box/window munch).
   Every instruction step is reac_ctrl_parseF_body.v's (and so reac_ctrl_parseF.v's), unchanged.  Provenance, the
   image and the const-cell check: reac_ctrl_parseF_cut.v's header. *)
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

Section RBodyF.
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
  Local Notation body_holds := (@reac_ctrl_parseF.body_holds ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMSET HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR).
  (* Speed: hide_sec turns the Section's implications (and S16's mod) into @id Prop T, which lia does not split on; each stays usable by name and in the Notations above. *)
  Local Ltac hide_h H := let T := type of H in change (@id Prop T) in H.  Local Ltac hide_sec := hide_h HF; hide_h HOK; hide_h AF0; hide_h AO0; hide_h RINF; hide_h SCF; hide_h SKF; hide_h ROUT; hide_h SCO; hide_h SKO; hide_h S16.
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

  (* Wf of reac_ctrl_parseF.v (:1189) without the class-1 hint word: its interval is empty here. *)
  Definition Wf2 (fa j nn : Z) : list ivl :=
    [(S - 8800, S); (fs_hint FS 1, fs_hint FS 1); (fs_flag FS 1 j, fs_flag FS 1 j + nn);
     (fa, fa + 128); (shadow_addr fa, shadow_addr fa + 16)].

  Lemma Wf2_sub : forall fa j nn, sub_fp (Wf2 fa j nn) (Wf fa j nn).
  Proof.
    intros fa j nn x Hx. unfold reac_ctrl_parseF.Wf in Hx. unfold Wf2. cbn [outside] in Hx |- *.
    destruct Hx as (H1 & H2 & H3 & H4 & H5 & _). repeat split; try assumption; lia.
  Qed.

  (* KB of reac_ctrl_parseF.v (:1395), with the post depending on the frame's kind fv (the frame binder is named
     fra here, as it shadows nothing). *)
  Definition KBx (Q : Z -> machine_state -> Prop) : Prop :=
    forall (fra fv spc j nn : Z) (w120 : word) (mc : word -> option byte)
           (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
      FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> addressable mc (fra + 32) 36 ->
      evtF rsegs RNG (Q fv) (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
                         x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 (Z_to_bv 64 o) (Z_to_bv 64 f)
                         (Z_to_bv 64 n) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
                         (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x8369c) fc None mc (seg_rom rsegs)).

  (* fwords of reac_ctrl_parseF.v (:1434), with KBx *)
  Lemma fwords_x : forall fra fv spc j nn w120 mc
    (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 : word) (Q : Z -> machine_state -> Prop),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> KBx Q ->
    evtF rsegs RNG (Q fv) (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
                       x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 (Z_to_bv 64 o) (Z_to_bv 64 f)
                       (Z_to_bv 64 n) x23 (Z_to_bv 64 fra) (wa ASAN_K) x26 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x8361c) fc None mc (seg_rom rsegs)).
  Proof. hide_sec.
    intros fra fv spc j nn w120 mc rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 Q HK HB HFL K.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (HFSpos & _ & _ & Pfsapp & _) & _ & _ & _ & HFSb & _).
    unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    assert (HHMl : 17594333495296 <= S - 8800) by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    unfold Wf2, shadow_addr in MU.
    (* the writes of this block, for carrying FLG from mc *)
    pose proof (munch_refl [(A + 24, A + 32); (fra, fra + 24); (fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16)] mc) as MUf.
    wst (A + 24) 8%nat ltac:(apply STW0; lia). step. store_done.
    steps_to 0x83644.
    wstb fra 8%nat fra FW. step. store_done.
    wstb (fra + 8) 8%nat fra FW. step. store_done.
    wstb (fra + 16) 8%nat fra FW. step. store_done.
    step. step.
    rewrite (unsigned_lit fra) by lia. rewrite rc_shr3.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
      pose proof (shadow_rw_mono m mcur SR0 WM RM) as SRmc;
      pose proof (shadow16_stk mcur fra SRmc ltac:(lia) FRA ltac:(lia) ltac:(lia)) as STsh
    end.
    pose proof (stk_carve rsegs m1 (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16) 16%nat STsh ltac:(lia))
      as [STsh' [junkS SHC]].
    replace (fra / 8 + ASAN_K + 16 - Z.of_nat 16) with (fra / 8 + ASAN_K) in SHC by lia.
    sstep (fra / 8 + ASAN_K) 0 0%nat SW.
    sstep (fra / 8 + ASAN_K) 1 1%nat SW.
    sstep (fra / 8 + ASAN_K) 2 2%nat SW.
    sstep (fra / 8 + ASAN_K) 3 3%nat SW.
    step.
    sstep (fra / 8 + ASAN_K) 12 12%nat SW.
    sstep (fra / 8 + ASAN_K) 13 13%nat SW.
    sstep (fra / 8 + ASAN_K) 14 14%nat SW.
    sstep (fra / 8 + ASAN_K) 15 15%nat SW.
    sstep (fra / 8 + ASAN_K) 8 8%nat SW.
    sstep (fra / 8 + ASAN_K) 9 9%nat SW.
    sstep (fra / 8 + ASAN_K) 10 10%nat SW.
    sstep (fra / 8 + ASAN_K) 11 11%nat SW.
    sstep (fra / 8 + ASAN_K) 4 4%nat SW.
    sstep (fra / 8 + ASAN_K) 5 5%nat SW.
    sstep (fra / 8 + ASAN_K) 6 6%nat SW.
    sstep (fra / 8 + ASAN_K) 7 7%nat SW.
    destruct SHC as [[_ HB16] _]. cbn [cells_bytes cbytes app] in HB16.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) => assert (FLf : FLG fra nn w120 mf) end.
    { destruct HFL as [(flg & Hfl & Hfln & HflF) Hw].
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      split.
      - exists flg. split; [|split; [exact Hfln | exact HflF]].
        eapply fl_bytes; [exact Hfl | exact MUf |].
        intros x Hx. rewrite Hfln, EFL0 in Hx. change (fs_M 1) with 8192 in Hx.
        assert (Hxa : app_mem x) by (apply Pfsapp; unfold FS_SIZE; clear -Hx HFSpos; lia).
        cbn [outside]. split; [|split; [|split; [|exact I]]].
        + clear -Hx HAlo HFSb RS; lia.
        + clear -Hx FRlo; lia.
        + intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo HFSpos; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
      - intros En. eapply fl_bytes; [exact (Hw En) | exact MUf |].
        intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
        assert (Hxa : app_mem x) by (replace x with (fra + (x - fra)) by lia; apply FAP; lia).
        cbn [outside]. split; [|split; [|split; [|exact I]]].
        + clear -Hx FRhi; lia.
        + clear -Hx; lia.
        + intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo HFSpos; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia]. }
    eapply K.
    - exact HK.
    - unfold reac_ctrl_parseF.BI, Wf2, shadow_addr. refine (conj MU (conj WM (conj RM (conj MI SV)))).
    - exact FLf.
    - apply frame_shadow_addr.
      + lia.
      + exact FR8.
      + unfold APPMEM_END in *; lia.
      + intros i Hi. replace (fra + 32 + i) with (fra + (32 + i)) by lia. apply FAP; lia.
      + intros g Hg. destruct HB16 as (_ & _ & Hr). exists (Z_to_bv 8 0). split; [|reflexivity].
        assert (Hc : g = 4 \/ g = 5 \/ g = 6 \/ g = 7) by lia.
        destruct Hc as [H|[H|[H|H]]]; rewrite H;
          [ replace (fra / 8 + ASAN_K + 4) with (fra / 8 + ASAN_K + Z.of_nat 4) by lia;
            rewrite (Hr 4%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 5) with (fra / 8 + ASAN_K + Z.of_nat 5) by lia;
            rewrite (Hr 5%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 6) with (fra / 8 + ASAN_K + Z.of_nat 6) by lia;
            rewrite (Hr 6%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 7) with (fra / 8 + ASAN_K + Z.of_nat 7) by lia;
            rewrite (Hr 7%nat ltac:(cbn [length]; lia)) ]; reflexivity.
      + destruct HB16 as (_ & _ & Hr). exists (Z_to_bv 8 4). split; [|reflexivity].
        replace (fra / 8 + ASAN_K + 8) with (fra / 8 + ASAN_K + Z.of_nat 8) by lia.
        rewrite (Hr 8%nat ltac:(cbn [length]; lia)). reflexivity.
  Qed.

  (* The body (0x8369c .. 0x83920) with the exit as a hypothesis. *)
    Variable QE : Z -> machine_state -> Prop.
    Hypothesis HEXIT : forall fra fv spc j nn w120 mc
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
    evtF rsegs RNG (QE fv)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fv) x19 x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K))
               (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83920) fc None mc (seg_rom rsegs)).

    Local Notation P1 := (@reac_ctrl_parseF.P1 fr).

  (* Every exit of the body reaches 0x83920 in a memory mx that the body produced from mc writing only the box
     and the callee windows, with a0 = the parse's kind and the box holding the parse's bytes: HEXIT's
     premises, assembled once. *)
  Lemma L_join : forall fra fv spc j nn w120 mc ob (mx : word -> option byte)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx -> wmono rsegs mc mx ->
    mem_inv rsegs mx -> stk rsegs mx (S - 8800) S ->
    rw_cells rsegs mx ob [CB 36 (snd (ctrlparse n fr))] ->
    evtF rsegs RNG (QE fv)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fv) x19 x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K))
               (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83920) fc None mx (seg_rom rsegs)).
  Proof. hide_sec.
    intros fra fv spc j nn w120 mc ob mx x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26
      x28 x29 x30 x31 HK HB HFL HO MUb WMb MIx STx RWx.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct HB as (MU & WM & RM & MI & SV).
    pose proof MU as MUw. apply (munch_weaken _ _ _ _ (Wf2_sub fra j nn)) in MU.
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc;
          clear -HAlo HAhi; lia).
    (* the box bytes and the window are readable at mx, so every byte readable at mc still is *)
    assert (RMb : rd_mono mc mx).
    { pose proof RWx as RWbk. destruct RWbk as [[_ Hbx] _]. cbn [cells_bytes cbytes] in Hbx.
      rewrite app_nil_r in Hbx.
      apply (rd_mono_list _ mc mx MUb). constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - intros y Hy. apply (rd_of_bytes _ _ _ Hbx). rewrite ctrlparse_length. clear -Hy; cbn; lia.
      - intros y Hy. apply (rd_of_stk _ _ _ STx). clear -Hy Hspcr RS; lia. }
    assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    assert (MUx : munch (Wex fra) m mx).
    { eapply munch_trans;
        [ eapply munch_weaken; [exact (subWf_Wex fra fv spc j nn w120 HK) | exact MU]
        | eapply munch_weaken; [exact (ob_wex fra fv spc j nn w120 ob HK HO) | exact MUb] ]. }
    assert (WMx : wmono rsegs m mx) by (eapply wmono_trans; [exact WM | exact WMb]).
    assert (RMx : rd_mono m mx) by (eapply rd_mono_trans; [exact RM | exact RMb]).
    assert (STfs : stk rsegs mx FS (FS + FS_SIZE)) by (exact (stk_mono m mx _ _ Pfsstk WMx RMx)).
    eapply HEXIT.
    - exact HK.
    - exact MUx.
    - exact WMx.
    - exact RMx.
    - exact MIx.
    - exact (fl_asan_cells (Wex fra) m mx AC0 MUx
               (fun x Hx => aout_rt (Wex fra) x (Wex_subW fra fv spc j nn w120 HK) Hx)).
    - exact (shadow_rw_mono m mx SR0 WMx RMx).
    - exact STx.
    - apply (rw_cells_transport rsegs _ mc mx (S - 96) SAVES SV MUb WMb).
      cbn [disjoint_from cells_size csize reac_ctrl_parseF.SAVES fst snd].
      split; [clear -Obsv RS; lia|]. split; [right; clear -Hspcr; lia | exact I].
    - intros Ho. destruct HO as [(Eo & _) | (_ & Eob)]; [exfalso; exact (Ho Eo) | rewrite <- Eob; exact RWx].
    - destruct (rd8_le8 mx (fs_hint FS 1)
                 ltac:(unfold fs_hint; cbn [Z.of_nat]; clear -Pfs0; lia)
                 ltac:(unfold fs_hint; cbn [Z.of_nat]; clear -Pfs0 HFSb RS; lia)
                 ltac:(intros i Hi; apply (rd_of_stk _ _ _ STfs);
                       unfold fs_hint, FS_SIZE; cbn [Z.of_nat]; clear -Hi Pfs0; lia)) as [hh Hhint].
      exists hh. exact Hhint.
    - destruct HFL as [(flg & Hfl & Hfln & HflF) _].
      exists flg. split; [|split; [exact Hfln | exact HflF]].
      eapply fl_bytes; [exact Hfl | exact MUb |].
      intros x Hx. rewrite Hfln, EM1, EFL0 in Hx.
      cbn [outside]. split; [|split; [|exact I]].
      + clear -Hx Obfl EFL0 EM1; rewrite EFL0, EM1 in Obfl; lia.
      + clear -Hx HFSb Pfs0 Hspcr RS; lia.
    - intros Enn. destruct HFL as [_ Hw]. pose proof (Hw Enn) as Hw120.
      assert (Hfrside : fra + 128 <= S - 8800).
      { destruct HK as [(_ & _ & _ & _ & Enn0) | (Hj & Efra & _)]; [clear -Enn Enn0; lia|].
        rewrite EM1 in Hj. rewrite Efra. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
        change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. clear -Hj HFSb Pfs0; lia. }
      eapply fl_bytes; [exact Hw120 | exact MUb |].
      intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
      cbn [outside]. split; [|split; [|exact I]].
      + destruct Obfr as [Eob | Hout]; [clear -Hx Eob; lia | clear -Hx Hout; lia].
      + clear -Hx Hfrside Hspcr RS; lia.
    - (* the class-1 flag array: the frame block wrote only flag j there, the body none of it *)
      intros x Hx Hnj.
      assert (Hxr : FS + 20480 <= x < FS + 28672) by (rewrite EFL0, EM1 in Hx; clear -Hx; lia).
      assert (Hbd : 0 <= x < 2 ^ 64) by (clear -Hxr Pfs0 HFSb RS; lia).
      rewrite (munch_mrd_out _ mc mx x MUb Hbd).
      + exact (munch_mrd_out _ m mc x MU Hbd (flag_out_Wf fra fv spc j nn w120 x HK Hxr Hnj)).
      + cbn [outside]. split; [|split; [|exact I]].
        * clear -Hxr Obfl EFL0 EM1; rewrite EFL0, EM1 in Obfl; lia.
        * clear -Hxr HFSb Pfs0 Hspcr RS; lia.
    - (* the exact writes from m: the frame block's (MUw, Wf2) and the body's (MUb, the box and the window) *)
      exists ob. split; [exact HO|].
      eapply munch_trans.
      + eapply munch_weaken; [|exact MUw]. intros x Hx. unfold Wf2 in *. cbn [app outside] in Hx |- *. clear - Hx; tauto.
      + eapply munch_weaken; [|exact MUb]. intros x Hx. unfold Wf2 in Hx. cbn [app outside] in Hx |- *.
        destruct Hx as (H1 & H2 & H3 & H4 & H5 & H6 & _). split; [exact H6|]. split; [|exact I].
        intros [HL HR]. apply H1. clear -HL HR Hspcr; lia.
  Qed.

  (* The frame bytes [lo, lo + len), read back in the memory the run reached. *)
  Ltac rdb lo len tac :=
    let HIN := fresh "HIN" in
    assert (HIN : forall jx, (jx < len)%nat -> In (lo + jx)%nat (cp_rd n fr)) by tac;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        let R := fresh "RO" in
        assert (R : ro_cells rsegs mcur (f + Z.of_nat lo) (map C1 (map (cp_b fr) (seq lo len))))
          by (eapply ro_mx;
              [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
              | exact HIN | cbn [Nat.add]; lia ]);
        cbn [map seq] in R;
        let z := eval vm_compute in (Z.of_nat lo) in change (Z.of_nat lo) with z in R;
        rewrite ?Z.add_0_r in R
    end;
    clear HIN.

  (* `mv r,s10; beqz s4; mv r,s4` at a join: r holds the box pointer on both paths, continuing at tgt. *)
  Ltac obsel r tgt :=
    lazymatch goal with
    | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm _ ?fcc ?rv ?mm ?ro) =>
        match goal with
        | HOb : OB ?fraq ?obq |- _ =>
            enough (G : forall w : word, w = Z_to_bv 64 obq ->
                          evtF segs rgq Q (MS (bvmap_set r w R) Fm (Z_to_bv 64 tgt) fcc rv mm ro));
            [ step; step; rewrite (rc_eqb_lit o 0) by lia;
              destruct HOb as [(Eo & Eob) | (Eo & Eob)];
              [ rewrite (proj2 (Z.eqb_eq o 0) Eo); cbv iota;
                apply (G (Z_to_bv 64 (fraq + 32)) ltac:(rewrite Eob; reflexivity))
              | rewrite (proj2 (Z.eqb_neq o 0) Eo); cbv iota; step;
                apply (G (Z_to_bv 64 o) ltac:(rewrite Eob; reflexivity)) ]
            | intros w Hw; subst w; simp_regs ]
        end
    end.

  (* the addressable ranges at the memory the run reached *)
  Ltac refresh :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        let A1 := fresh "AFx" in
        assert (A1 : addressable mcur f 50) by (eapply af_mx2; eassumption);
        match goal with
        | HOb : OB _ ?obq |- _ =>
            let A2 := fresh "Aobx" in
            assert (A2 : addressable mcur obq 36) by (eapply ob_mx; eassumption)
        end
    end.

  (* the shadow check of the one-byte load of frame byte i *)
  Ltac chkf i r :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) => try (match goal with HSC : shcov _ f 50 |- _ => move HSC at bottom end);
        let RX := fresh "RX" in let SH := fresh "SH" in
        assert (RX : 0 <= f + i < 2 ^ 64)
          by (match goal with Hb : 0 <= f /\ f + 50 <= 2 ^ 64 |- _ => clear -Hb; lia end);
        pose proof (acl_shadow mcur f 50 i 1 (f + i) ltac:(eassumption) ltac:(clear; lia) ltac:(clear; lia)
                      ltac:(clear; lia)
                      ltac:(let MB := fresh "MB" in
                            pose proof (Z.mod_pos_bound (f + i) 8 ltac:(clear; lia)) as MB; clear -MB; lia)
                      ltac:(clear; lia)) as SH;
        chk_core (f + i) RX r SH pre_sr no_extra
    end.

  (* the shadow check of the four-byte access at the box pointer itself (offset 0: the address register holds ob,
     with no added literal) *)
  Ltac chkb0 r extra :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        match goal with
        | AO : addressable mcur ?obq 36 |- _ => try (match goal with HSC : shcov _ obq 36 |- _ => move HSC at bottom end);
            let RX := fresh "RX" in let SH := fresh "SH" in
            assert (RX : 0 <= obq < 2 ^ 64)
              by (match goal with Hb : 0 <= obq /\ obq + 36 <= 2 ^ 64 |- _ => clear -Hb; lia end);
            pose proof (acl_shadow mcur obq 36 0 4 obq AO ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(apply acl_mod_al0; eassumption) ltac:(clear; lia)) as SH;
            chk_core obq RX r SH pre_sr extra
        end
    end.

  (* the same check where the fast path is the TAKEN branch (`beqz` instead of `bnez`, at 0x83a90) *)
  Ltac chkb0inv r :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        match goal with
        | AO : addressable mcur ?obq 36 |- _ => try (match goal with HSC : shcov _ obq 36 |- _ => move HSC at bottom end);
            let RX := fresh "RX" in let SH := fresh "SH" in
            assert (RX : 0 <= obq < 2 ^ 64)
              by (match goal with Hb : 0 <= obq /\ obq + 36 <= 2 ^ 64 |- _ => clear -Hb; lia end);
            pose proof (acl_shadow mcur obq 36 0 4 obq AO ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(apply acl_mod_al0; eassumption) ltac:(clear; lia)) as SH;
            let kk := fresh "kk" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
            destruct SH as (kk & RK & OK & KR);
            pre_sr obq RX; steps_until_if; clear RK;
            unfold sxb; rewrite (rc_eqb0_signed (bv_signed kk)) by (clear -KR; lia);
            lazymatch goal with
            | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm (if _ then ?B1 else _) ?fcc ?rv ?mm ?ro) =>
                let G := fresh "G" in
                enough (G : forall rr : word, evtF segs rgq Q (MS (bvmap_set r rr R) Fm B1 fcc rv mm ro));
                [ destruct (Z.eqb_spec (bv_signed kk) 0) as [K0|K0]; cbv iota;
                  [ bjoin G r
                  | step; rewrite ?(unsigned_lit obq) by (clear -RX; lia); rewrite rc_land7; add3 obq;
                    step;
                    let MB := fresh "MB" in pose proof (Z.mod_pos_bound obq 8 eq_refl) as MB;
                    rewrite (rc_lts_signed (obq mod 8 + 3) (bv_signed kk)) by (clear -MB KR; lia);
                    replace (obq mod 8 + 3 <? bv_signed kk) with true
                      by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK];
                          [exfalso; exact (K0 OK) | clear -OK; lia]);
                    clear MB; cbv iota; bjoin G r ]
                | intros ?; simp_regs; clear OK KR ]
            end
        end
    end.

  (* `beqz s4; mv r,s4` (0x83c38): r holds the box pointer on both paths *)
  Ltac obsel2 r tgt :=
    lazymatch goal with
    | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm _ ?fcc ?rv ?mm ?ro) =>
        match goal with
        | HOb : OB ?fraq ?obq |- _ =>
            enough (G : forall w : word, w = Z_to_bv 64 obq ->
                          evtF segs rgq Q (MS (bvmap_set r w R) Fm (Z_to_bv 64 tgt) fcc rv mm ro));
            [ step; rewrite (rc_eqb_lit o 0) by lia;
              destruct HOb as [(Eo & Eob) | (Eo & Eob)];
              [ rewrite (proj2 (Z.eqb_eq o 0) Eo); cbv iota;
                apply (G (Z_to_bv 64 (fraq + 32)) ltac:(rewrite Eob; reflexivity))
              | rewrite (proj2 (Z.eqb_neq o 0) Eo); cbv iota; step;
                apply (G (Z_to_bv 64 o) ltac:(rewrite Eob; reflexivity)) ]
            | intros w Hw; subst w; simp_regs ]
        end
    end.

  (* the shadow check of a w-byte access at ob + k *)
  Ltac chkb k w r extra :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        match goal with
        | AO : addressable mcur ?obq 36 |- _ => try (match goal with HSC : shcov _ obq 36 |- _ => move HSC at bottom end);
            let RX := fresh "RX" in let SH := fresh "SH" in
            assert (RX : 0 <= obq + k < 2 ^ 64)
              by (match goal with Hb : 0 <= obq /\ obq + 36 <= 2 ^ 64 |- _ => clear -Hb; lia end);
            pose proof (acl_shadow mcur obq 36 k w (obq + k) AO ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(clear; lia)
                          ltac:(apply (acl_mod_al obq k w); [eassumption | clear; lia | clear; lia])
                          ltac:(clear; lia)) as SH;
            chk_core (obq + k) RX r SH pre_sr extra
        end
    end.

  (* 0x83ac8: the kind is stored into the box (its shadow check was done before the jump), then the exit. *)
  Lemma L_kind : forall fra fv spc j nn w120 mc ob (mx : word -> option byte) k tg amp
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    BJ ob spc mc mx ->
    rw_cells rsegs mx ob [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mx (ob + 4) [CB 24 P1] ->
    rw_cells rsegs mx (ob + 28) [CB 2 tg] -> rw_cells rsegs mx (ob + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG (QE fv)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               (Z_to_bv 64 k) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob)
               x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x83ac8) fc None mx (seg_rom rsegs)).
  Proof. hide_sec.
    intros fra fv spc j nn w120 mc ob mx k tg amp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26
      x28 x29 x30 x31 HK HB HFL HO HBJ HKc HP HTG HAMP Ek Hk EB.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    destruct HBJ as (MUb & WMb & MIx & STx).
    step. step.
    match goal with H : rw_cells rsegs _ ob [C4 _] |- _ => rename H into HKc' end.
    pose proof (rc_rw_join rsegs _ ob (ob + 4) _ _ HKc' ltac:(cbn [cells_size csize app]; lia) HP) as J1.
    pose proof (rc_rw_join rsegs _ ob (ob + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HTG) as J2.
    pose proof (rc_rw_join rsegs _ ob (ob + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HAMP) as J3.
    apply (rc_rw_flat rsegs _ ob _ (snd (ctrlparse n fr))) in J3.
    - rewrite ctrlparse_length in J3. rewrite <- Ek.
      eapply (L_join fra fv spc j nn w120 mc ob);
        [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx
        | exact J3 ].
    - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      rewrite !app_nil_r. cbn [app]. reflexivity.
  Qed.

  (* 0x83ca8: the stored kind is checked, read back, and the run exits. *)
  Lemma L_be0 : forall fra fv spc j nn w120 mc ob (mx : word -> option byte) k tg amp
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    BJ ob spc mc mx -> addressable mc ob 36 ->
    rw_cells rsegs mx ob [C4 (Z_to_bv 64 k)] -> rw_cells rsegs mx (ob + 4) [CB 24 P1] ->
    rw_cells rsegs mx (ob + 28) [CB 2 tg] -> rw_cells rsegs mx (ob + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG (QE fv)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob)
               x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x83ca8) fc None mx (seg_rom rsegs)).
  Proof. hide_sec.
    intros fra fv spc j nn w120 mc ob mx k tg amp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22
      x26 x28 x29 x30 x31 HK HB HFL HO HBJ Aob HKc' HP HTG HAMP Ek Hk EB.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof MU as MUw. apply (munch_weaken _ _ _ _ (Wf2_sub fra j nn)) in MU.
    destruct HBJ as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO) as (Ob0 & Ob64 & Obmod & _).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        assert (Aobx : addressable mcur ob 36) by (eapply ob_mx; eassumption)
    end.
    chkb0 (Z_to_bv 5 11) add3.
    step. rewrite (rcp_sx32 k) by (clear -Hk; lia).
    step.
    pose proof (rc_rw_join rsegs _ ob (ob + 4) _ _ HKc' ltac:(cbn [cells_size csize app]; lia) HP) as J1.
    pose proof (rc_rw_join rsegs _ ob (ob + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HTG) as J2.
    pose proof (rc_rw_join rsegs _ ob (ob + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HAMP) as J3.
    apply (rc_rw_flat rsegs _ ob _ (snd (ctrlparse n fr))) in J3.
    - rewrite ctrlparse_length in J3. rewrite <- Ek.
      eapply (L_join fra fv spc j nn w120 mc ob);
        [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx
        | exact J3 ].
    - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      rewrite !app_nil_r. cbn [app]. reflexivity.
  Qed.

  (* 0x83ca4: the kind is stored into the box, checked, read back, then the exit. *)
  Lemma L_bdc : forall fra fv spc j nn w120 mc ob (mx : word -> option byte) k tg amp
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    BJ ob spc mc mx -> addressable mc ob 36 ->
    rw_cells rsegs mx ob [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mx (ob + 4) [CB 24 P1] ->
    rw_cells rsegs mx (ob + 28) [CB 2 tg] -> rw_cells rsegs mx (ob + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG (QE fv)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               (Z_to_bv 64 k) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob)
               x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x83ca4) fc None mx (seg_rom rsegs)).
  Proof. hide_sec.
    intros fra fv spc j nn w120 mc ob mx k tg amp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26
      x28 x29 x30 x31 HK HB HFL HO HBJ Aob HKc HP HTG HAMP Ek Hk EB.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof MU as MUw. apply (munch_weaken _ _ _ _ (Wf2_sub fra j nn)) in MU.
    pose proof HBJ as HBJ'. destruct HBJ' as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO) as (Ob0 & Ob64 & Obmod & _).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    step.
    match goal with H : rw_cells rsegs _ ob [C4 _] |- _ => rename H into HK4 end.
    eapply (L_be0 fra fv spc j nn w120 mc ob _ k tg amp);
      [ exact HK | exact HB | exact HFL | exact HO
      | refine (conj _ (conj _ (conj _ _))); eassumption
      | exact Aob | exact HK4 | eassumption | eassumption | eassumption
      | exact Ek | exact Hk | exact EB ].
  Qed.

  (* the plain proof's condition normaliser and branch splitter (lib/Prog/reac_ctrl_parse.v) *)
  Ltac cond_norm :=
    rewrite ?rc_lor0;
    rewrite ?rc_eqb_zxb by (clear; lia);
    repeat match goal with
    | |- context [bv_unsigned (cp_b fr ?i)] => change (bv_unsigned (cp_b fr i)) with (cp_v fr i)
    end.

  Ltac br :=
    cond_norm;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if negb (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
    | |- evtF _ _ _ (MS _ _ (if (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
    end.

  (* walk the kind dispatch, stopping at every leaf (each leaf checks the box before it stores the kind) *)
  Ltac drive :=
    repeat (lazymatch goal with
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539172) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539212) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539276) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539316) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539344) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539368) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539744) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539768) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539792) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => br
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
            end).

  (* the kind and the box bytes of a leaf (kfact / bfact of the plain proof) *)
  Ltac kfact :=
    match goal with HE0 : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE0 end; cbn [fst];
    unfold cp_kind, cp_type, cp_amp; zeval; reflexivity.
  Ltac bfact :=
    match goal with HE0 : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE0 end; cbn [snd];
    unfold cp_struct, cp_rec, cp_kind, cp_type, cp_amp, reac_ctrl_parseF.P1; zeval; zeval; reflexivity.

  Ltac leafk :=
    eapply L_kind;
    first [ eassumption
          | refine (conj _ (conj _ (conj _ _))); eassumption
          | clear; lia
          | match goal with KR0 : 2 <= KL1 ?x <= 13 /\ _ |- _ => clear -KR0; lia end
          | kfact
          | bfact ].
  Ltac leafb :=
    eapply L_bdc;
    first [ eassumption
          | refine (conj _ (conj _ (conj _ _))); eassumption
          | clear; lia
          | match goal with KR0 : 2 <= KL1 ?x <= 13 /\ _ |- _ => clear -KR0; lia end
          | kfact
          | bfact ].

  (* after the two tag bytes are stored, the box's [ob + 28] cell is a C2: flatten it back to the two
     bytes cp_struct names, so that a leaf below the record can still apply L_kind / L_bdc *)
  Ltac flat_tg :=
    match goal with
    | HOb : OB _ ?obq |- _ =>
        match goal with
        | Hq : rw_cells rsegs _ (obq + 28) [C2 _] |- _ =>
            apply (rc_rw_flat rsegs _ (obq + 28) _ [cp_b fr 35; cp_b fr 34]) in Hq;
            [ cbn [length] in Hq
            | first [ cbn [cells_bytes cbytes]; rewrite rc_le2_pack; reflexivity
                    | cbn [cells_bytes cbytes app]; rewrite rc_le2_pack; reflexivity
                    | vm_compute; reflexivity ] ]
        end
    end.

  Ltac leaves :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539172) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafk
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539212) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafk
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539316) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; leafk
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539344) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafb
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539744) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafb
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539768) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafb
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539792) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; leafb
    end.

  (* 0x8370c .. 0x8375c: the two copies into the box, the broadcast comparison and its 4-byte store. *)
  Lemma body_copy : 50 <= n -> cp_hdr n fr = true ->
    forall fra fv spc j nn w120 mc ob (mx : word -> option byte)
      (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    addressable mc ob 36 -> asan_cells mc -> shadow_rw mc ->
    BJ ob spc mc mx -> rw_cells rsegs mx ob [CB 36 (repeat cp_z 36)] ->
    evtF rsegs RNG (QE fv)
      (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 ob) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8370c) fc None mx (seg_rom rsegs)).
  Proof. hide_sec.
    intros Hn50 HE fra fv spc j nn w120 mc ob mx rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB HFL HO Aob ACc SRc HBJ RWx.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof (RINF Hn50) as RGINF. pose proof (SCF Hn50) as SCINF. pose proof (SKF Hn50) as SKINF.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof MU as MUw. apply (munch_weaken _ _ _ _ (Wf2_sub fra j nn)) in MU.
    pose proof HBJ as HBJ'. destruct HBJ' as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    destruct (f_facts Hn50 fra fv spc j nn w120 ob HK HO) as (Hf0 & Hf64 & Fapp & AFm & DFf).
    destruct (HF Hn50) as (_ & _ & HfS).
    pose proof (Obf Hn50) as Hobf.
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc; clear -HAlo HAhi; lia).
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -Hspcr RS; lia).
    assert (Rob : 0 <= ob < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rfb : 0 <= f /\ f + 50 <= 2 ^ 64) by (clear -Hf0 Hf64; lia).
    assert (Rob10 : 0 <= ob + 10 < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rob4 : 0 <= ob + 4 < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rf6 : 0 <= f + 6 < 2 ^ 64) by (clear -Hf0 Hf64; lia).
    assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
    assert (STsp : stk rsegs mx (S - 8800) spc)
      by (apply (stk_sub mx (S - 8800) S (S - 8800) spc STx); clear -Hspcr RS; lia).
    destruct (body_rt fra fv spc j nn w120 ob mc mx HK HO Aob ACc SRc MUb WMb) as (ACx & SRx).
    pose proof (ob_mx fra fv spc j nn w120 ob mc mx HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc mx HK HO MU Aob MUb) as AFx.
    rdb 0%nat 23%nat ltac:(intros jx Hjx; apply cp_rd_e; [exact HE | lia]).
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 0 6 RO ltac:(cbn; lia)) as BD0.
    cbn [map seq firstn skipn] in BD0. rewrite Z.add_0_r in BD0.
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 6 6 RO ltac:(cbn; lia)) as BD1.
    cbn [map seq firstn skipn] in BD1. change (Z.of_nat 6) with 6 in BD1.
    clear RO.
    (* the pieces of the box the body writes *)
    destruct (rc_rw_cut_at rsegs _ ob cp_z 36 4 (ob + 4) RWx ltac:(lia) ltac:(lia)) as [HKc HZ1];
      cbn [Nat.sub] in HZ1.
    destruct (rc_rw_cut_at rsegs _ (ob + 4) cp_z 32 6 (ob + 10) HZ1 ltac:(lia) ltac:(lia)) as [HSRC HZ2];
      cbn [Nat.sub] in HZ2.
    destruct (rc_rw_cut_at rsegs _ (ob + 10) cp_z 26 6 (ob + 16) HZ2 ltac:(lia) ltac:(lia)) as [HDST HZ3];
      cbn [Nat.sub] in HZ3.
    destruct (rc_rw_cut_at rsegs _ (ob + 16) cp_z 20 12 (ob + 28) HZ3 ltac:(lia) ltac:(lia)) as [HMID HZ4];
      cbn [Nat.sub] in HZ4.
    destruct (rc_rw_cut_at rsegs _ (ob + 28) cp_z 8 2 (ob + 30) HZ4 ltac:(lia) ltac:(lia)) as [HTG HAMP];
      cbn [Nat.sub] in HAMP.
    clear HZ1 HZ2 HZ3 HZ4 RWx.
    pose proof HMCPY as HMC. unfold asan_memcpy_contract_F, ASAN_MEMCPY_K in HMC. cbv zeta in HMC.
    unfold rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HMC.
    (* 0x8370c: __asan_memcpy(ob + 10, f, 6) *)
    do 4 step.
    eapply evtF_cut.
    { eapply HMC with (src := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5])
                      (junk := repeat cp_z 6) (lo := S - 8800);
        rewrite ?(unsigned_lit (ob + 10) Rob10), ?(unsigned_lit f Rf), ?U6, ?(unsigned_lit spc Rspc).
      - exact BD0.
      - reflexivity.
      - change (Z.to_nat 6) with 6%nat. exact HDST.
      - clear -Hobf; lia.
      - clear; lia.
      - apply (acl_addr_sub mx f 50 f 6 AFx); clear; lia.
      - apply (acl_addr_sub mx ob 36 (ob + 10) 6 Aobx); clear; lia.
      - right. apply (acl_app_in mx f 50 6 AFx); clear; lia.
      - right. replace (ob + 10 + 6) with (ob + 16) by lia. apply (acl_app_in mx ob 36 16 Aobx); clear; lia.
      - right. split; [ apply (acl_app_in mx f 50 7 AFx); clear; lia
                      | replace (ob + 10 + 7) with (ob + 17) by lia;
                        apply (acl_app_in mx ob 36 17 Aobx); clear; lia ].
      - clear -Obrt; lia.
      - clear -Obsp; lia.
      - clear -HfS Hspcr RS; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact ACx.
      - exact SRx.
      - exact MIx.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* __asan_memcpy's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the destination bytes in the box *) eapply rng_sub; [exact RGOB | clear; lia | clear; lia].
      - (* the source bytes in the input *) eapply rng_sub; [exact RGINF | clear; lia | clear; lia].
      - (* the destination's aligned shadow word cover *) right. unfold shadow_addr. apply SKOB; clear; lia.
      - (* the source's aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; clear; lia.
      - (* the shadow of __asan_memcpy's window *)
        right. unfold shadow_addr. apply rngF_win_sh8; clear -Hspcr RS; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 &
                       Hms & MU1 & WM1 & MI1 & ST1 & RW1 & BS1 & AC1 & SR1).
    subst ms'.
    rewrite (ret_pc_even 538396 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit _ Rob10), U6, (unsigned_lit spc Rspc) in MU1.
    rewrite (unsigned_lit _ Rob10), U6 in RW1.
    rewrite (unsigned_lit _ Rf) in BS1.
    rewrite (unsigned_lit spc Rspc) in ST1.
    unfold ASAN_MEMCPY_K in MU1. change (Z.to_nat 6) with 6%nat in RW1.
    pose proof (bj_call ob spc mc mx m1 (ob + 10) 6 2224 _ HBJ MU1 WM1 MI1 ST1 RW1
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Hspcr RS; lia) ltac:(clear -Hspcr RS; lia)) as HBJ1.
    pose proof (rw_cells_transport rsegs _ mx m1 ob [CB 4 (repeat cp_z 4)] HKc MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HKc1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 4) [CB 6 (repeat cp_z 6)] HSRC MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HSRC1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 16) [CB 12 (repeat cp_z 12)] HMID MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HMID1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 28) [CB 2 (repeat cp_z 2)] HTG MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HTG1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 30) [CB 6 (repeat cp_z 6)] HAMP MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HAMP1.
    pose proof (bytes_at_transport rsegs _ mx m1 (f + 6) [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9;
                                                          cp_b fr 10; cp_b fr 11] BD1 MU1
                  ltac:(cbn [disjoint_from length]; clear -Hobf Hf0 Hf64 HfS Hspcr RS; lia)) as BD1a.
    clear HKc HSRC HMID HTG HAMP BD0 BD1 MU1 WM1 MI1 ST1 HBJ MUb WMb MIx STx STsp ACx SRx Aobx AFx.
    pose proof HBJ1 as HBJ1'. destruct HBJ1' as (MUb & WMb & MIx & STx).
    assert (STsp : stk rsegs m1 (S - 8800) spc)
      by (apply (stk_sub m1 (S - 8800) S (S - 8800) spc STx); clear -Hspcr RS; lia).
    pose proof (ob_mx fra fv spc j nn w120 ob mc m1 HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc m1 HK HO MU Aob MUb) as AFx.
    (* 0x8371c: __asan_memcpy(ob + 4, f + 6, 6) *)
    do 4 step.
    eapply evtF_cut.
    { eapply HMC with (src := [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11])
                      (junk := repeat cp_z 6) (lo := S - 8800);
        rewrite ?(unsigned_lit (ob + 4) Rob4), ?(unsigned_lit (f + 6) Rf6), ?U6, ?(unsigned_lit spc Rspc).
      - exact BD1a.
      - reflexivity.
      - change (Z.to_nat 6) with 6%nat. exact HSRC1.
      - clear -Hobf; lia.
      - clear; lia.
      - apply (acl_addr_sub m1 f 50 (f + 6) 6 AFx); clear; lia.
      - apply (acl_addr_sub m1 ob 36 (ob + 4) 6 Aobx); clear; lia.
      - right. replace (f + 6 + 6) with (f + 12) by lia. apply (acl_app_in m1 f 50 12 AFx); clear; lia.
      - right. replace (ob + 4 + 6) with (ob + 10) by lia. apply (acl_app_in m1 ob 36 10 Aobx); clear; lia.
      - right. split; [ replace (f + 6 + 7) with (f + 13) by lia; apply (acl_app_in m1 f 50 13 AFx); clear; lia
                      | replace (ob + 4 + 7) with (ob + 11) by lia;
                        apply (acl_app_in m1 ob 36 11 Aobx); clear; lia ].
      - clear -Obrt; lia.
      - clear -Obsp; lia.
      - clear -HfS Hspcr RS; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact AC1.
      - exact SR1.
      - exact MIx.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* __asan_memcpy's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the destination bytes in the box *) eapply rng_sub; [exact RGOB | clear; lia | clear; lia].
      - (* the source bytes in the input *) eapply rng_sub; [exact RGINF | clear; lia | clear; lia].
      - (* the destination's aligned shadow word cover *) right. unfold shadow_addr. apply SKOB; clear; lia.
      - (* the source's aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; clear; lia.
      - (* the shadow of __asan_memcpy's window *)
        right. unfold shadow_addr. apply rngF_win_sh8; clear -Hspcr RS; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 &
                       Hms & MU2 & WM2 & MI2 & ST2 & RW2 & BS2 & AC2 & SR2).
    subst ms'.
    rewrite (ret_pc_even 538412 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit _ Rob4), U6, (unsigned_lit spc Rspc) in MU2.
    rewrite (unsigned_lit _ Rob4), U6 in RW2.
    rewrite (unsigned_lit _ Rf6) in BS2.
    rewrite (unsigned_lit spc Rspc) in ST2.
    unfold ASAN_MEMCPY_K in MU2. change (Z.to_nat 6) with 6%nat in RW2.
    pose proof (bj_call ob spc mc m1 m2 (ob + 4) 6 2224 _ HBJ1 MU2 WM2 MI2 ST2 RW2
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Hspcr RS; lia) ltac:(clear -Hspcr RS; lia)) as HBJ2.
    pose proof (rw_cells_transport rsegs _ m1 m2 ob [CB 4 (repeat cp_z 4)] HKc1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HKc2.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 10) [CB 6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3;
                                                                 cp_b fr 4; cp_b fr 5]] RW1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as RW1b.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 16) [CB 12 (repeat cp_z 12)] HMID1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HMID2.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 28) [CB 2 (repeat cp_z 2)] HTG1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HTG2.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 30) [CB 6 (repeat cp_z 6)] HAMP1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HAMP2.
    clear HKc1 HSRC1 HMID1 HTG1 HAMP1 RW1 BD1a MU2 WM2 MI2 ST2 HBJ1 MUb WMb MIx STx STsp Aobx AFx
      AC1 SR1.
    pose proof HBJ2 as HBJ2'. destruct HBJ2' as (MUb & WMb & MIx & STx).
    assert (STsp : stk rsegs m2 (S - 8800) spc)
      by (apply (stk_sub m2 (S - 8800) S (S - 8800) spc STx); clear -Hspcr RS; lia).
    pose proof (ob_mx fra fv spc j nn w120 ob mc m2 HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc m2 HK HO MU Aob MUb) as AFx.
    (* 0x8372c .. 0x8373c: the bcmp wrapper on the 6 bytes at f and the 6 bytes of .str.4 *)
    destruct (cl_mx2 fra fv spc j nn w120 ob mc m2 HK HO MU MUb) as (CLa & CLb & CLc & CLd & CLe).
    pose proof (abc_mx2 fra fv spc j nn w120 ob mc m2 HK HO MU Aob MUb) as ABCx.
    rdb 0%nat 23%nat ltac:(intros jx Hjx; apply cp_rd_e; [exact HE | lia]).
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 0 6 RO ltac:(cbn; lia)) as BD0c.
    cbn [map seq firstn skipn] in BD0c. rewrite Z.add_0_r in BD0c.
    clear RO.
    destruct (rc_memcmp_ff (cp_b fr 0) (cp_b fr 1) (cp_b fr 2) (cp_b fr 3) (cp_b fr 4) (cp_b fr 5))
      as (v & Hv & Hvr & Hvb).
    pose proof HBCMPW as HBW. unfold bcmp_wrap_contract_F, BCMP_WRAP_K in HBW. cbv zeta in HBW.
    assert (UBC : bv_unsigned (Z_to_bv 64 135680) = 135680) by reflexivity.
    do 5 step.
    eapply evtF_cut.
    { eapply HBW with (ls := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5])
                      (rs := repeat (Z_to_bv 8 255) 6) (v := v) (lo := S - 8800);
        rewrite ?(unsigned_lit f Rf), ?U6, ?(unsigned_lit spc Rspc), ?UBC.
      - exact BD0c.
      - apply (rc_ro_in_image rsegs _ _ (repeat (Z_to_bv 8 255) 6)); [exact MIx | vm_compute; reflexivity].
      - exact Hv.
      - exact MIx.
      - clear; lia.
      - apply (acl_addr_sub m2 f 50 f 6 AFx); clear; lia.
      - exact ABCx.
      - right. apply (acl_app_in m2 f 50 6 AFx); clear; lia.
      - right. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; clear; lia.
      - right. apply (acl_app_in m2 f 50 7 AFx); clear; lia.
      - right. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; clear; lia.
      - clear -HfS Hspcr RS; lia.
      - left. pose proof HHM as HH0. unfold HIGHMEM_BEG in HH0. clear -HH0 Hspcr RS; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact AC2.
      - exact SR2.
      - exact CLa.
      - exact CLb.
      - exact CLc.
      - exact CLd.
      - exact CLe.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) exact RIMG.
      - (* the bcmp wrapper's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the 6 input bytes *) eapply rng_sub; [exact RGINF | clear; lia | clear; lia].
      - (* their aligned shadow word cover *) right. apply (rcpF_kov8 RNG f 50 _ _ SKINF); clear; lia.
      - (* the 6 bytes at .str.4 *) exact RBC.
      - (* their aligned shadow word cover *)
        right. apply (rcpF_kov8 RNG REAC_CTRL_PARSE_BC 6 _ _ SKBC); unfold REAC_CTRL_PARSE_BC; clear; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 &
                       Hms & MU3 & WM3 & MI3 & ST3 & AC3 & SR3 & BSl & BSr).
    subst ms'.
    rewrite (ret_pc_even 538432 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit spc Rspc) in MU3. rewrite (unsigned_lit spc Rspc) in ST3.
    unfold BCMP_WRAP_K in MU3.
    pose proof (bj_call0 ob spc mc m2 m3 4560 HBJ2 MU3 WM3 MI3 ST3
                  ltac:(clear; lia) ltac:(clear -Hspcr RS; lia) ltac:(clear -Hspcr RS; lia)) as HBJ3.
    pose proof (rw_cells_transport rsegs _ m2 m3 ob [CB 4 (repeat cp_z 4)] HKc2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HKc3.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 4) [CB 6 [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9;
                                                                cp_b fr 10; cp_b fr 11]] RW2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as RW2b.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 10) [CB 6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3;
                                                                 cp_b fr 4; cp_b fr 5]] RW1b MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as RW1c.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 16) [CB 12 (repeat cp_z 12)] HMID2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HMID3.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 28) [CB 2 (repeat cp_z 2)] HTG2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HTG3.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 30) [CB 6 (repeat cp_z 6)] HAMP2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HAMP3.
    clear HKc2 RW2 RW1b HMID2 HTG2 HAMP2 BD0c MU3 WM3 MI3 ST3 HBJ2 MUb WMb MIx STx STsp Aobx AFx
      AC2 SR2 BSl BSr ABCx CLa CLb CLc CLd CLe.
    pose proof HBJ3 as HBJ3'. destruct HBJ3' as (MUb & WMb & MIx & STx).
    pose proof (ob_mx fra fv spc j nn w120 ob mc m3 HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc m3 HK HO MU Aob MUb) as AFx.
    (* 0x83740 .. 0x83758: the 4-byte store of the broadcast flag at ob + 16, checked *)
    step.
    assert (RX16 : 0 <= ob + 16 < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    pose proof (acl_shadow m3 ob 36 16 4 (ob + 16) Aobx ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Obmod; Z.div_mod_to_equations; lia) ltac:(clear; lia)) as SH16.
    move SCOB at bottom. chk_core (ob + 16) RX16 (Z_to_bv 5 13) SH16 pre_sr add3.
    move HMID3 at bottom. step. step.
    (* 0x8375c .. 0x83900: the frame's fields, each load and each store behind its shadow check *)
    rdb 0%nat 23%nat ltac:(intros jx Hjx; apply cp_rd_e; [exact HE | lia]).
    refresh.
    step.                                      (* 0x8375c addi a0,s5,14 *)
    chkf 14%Z (Z_to_bv 5 12).
    step.                                      (* 0x83770 addi a0,s5,15 *)
    chkf 15%Z (Z_to_bv 5 13).
    obsel (Z_to_bv 5 11) 538516.               (* 0x83788 .. 0x83794: a1 = ob *)
    step.                                      (* 0x83794 addi a1,a1,20 *)
    chkb 20%Z 2%Z (Z_to_bv 5 14) add1.
    do 4 step.                                 (* slli, or, addi a0,s5,18, sh a2,0(a1) *)
    refresh.
    chkf 18%Z (Z_to_bv 5 12).
    obsel (Z_to_bv 5 11) 538584.               (* 0x837cc .. 0x837d8 *)
    step.                                      (* 0x837d8 addi a1,a1,22 *)
    chkb 22%Z 1%Z (Z_to_bv 5 10) no_extra.
    do 2 step.                                 (* sb a2,0(a1), addi a0,s5,19 *)
    refresh.
    chkf 19%Z (Z_to_bv 5 13).
    obsel (Z_to_bv 5 11) 538644.               (* 0x83808 .. 0x83814 *)
    step.                                      (* 0x83814 addi a1,a1,23 *)
    chkb 23%Z 1%Z (Z_to_bv 5 10) no_extra.
    do 2 step.                                 (* sb a3,0(a1), addi a0,s5,20 *)
    refresh.
    chkf 20%Z (Z_to_bv 5 14).
    step.                                      (* 0x83844 addi a0,s5,21 *)
    chkf 21%Z (Z_to_bv 5 15).
    obsel (Z_to_bv 5 11) 538728.               (* 0x8385c .. 0x83868 *)
    step.                                      (* 0x83868 addi a1,a1,24 *)
    chkb 24%Z 2%Z (Z_to_bv 5 16) add1.
    do 4 step.                                 (* slli, or, addi a0,s5,22, sh a4,0(a1) *)
    refresh.
    chkf 22%Z (Z_to_bv 5 14).
    obsel (Z_to_bv 5 11) 538796.               (* 0x838a0 .. 0x838ac *)
    step.                                      (* 0x838ac addi a1,a1,26 *)
    chkb 26%Z 1%Z (Z_to_bv 5 15) no_extra.
    do 2 step.                                 (* sb a0,0(a1), addi a1,s5,16 *)
    refresh.
    chkf 16%Z (Z_to_bv 5 15).
    step.                                      (* 0x838dc addi a1,s5,17 *)
    chkf 17%Z (Z_to_bv 5 16).
    do 3 step.                                 (* lbu a1, zext.b, or a5,a4,a1 *)
    (* 0x83900: (fr[16] | fr[17]) = 0 is the filler, kind 1; else the kind dispatch at 0x83a14 *)
    rewrite ?rc_zextb.
    step.
    rewrite rc_lor0.
    change (bv_unsigned (cp_b fr 16)) with (cp_v fr 16).
    change (bv_unsigned (cp_b fr 17)) with (cp_v fr 17).
    match goal with H : rw_cells rsegs _ (ob + 4) [CB 6 _] |- _ => rename H into HSRCf end.
    match goal with H : rw_cells rsegs _ (ob + 10) [CB 6 _] |- _ => rename H into HDSTf end.
    match goal with H : rw_cells rsegs _ (ob + 16) _ |- _ => rename H into HMIDf end.
    pose proof (rc_rw_join rsegs _ (ob + 4) (ob + 10) _ _ HSRCf
                  ltac:(cbn [cells_size csize app]; lia) HDSTf) as J1.
    pose proof (rc_rw_join rsegs _ (ob + 4) (ob + 16) _ _ J1
                  ltac:(cbn [cells_size csize app]; lia) HMIDf) as J2.
    apply (rc_rw_flat rsegs _ (ob + 4) _ P1) in J2.
    2:{ cbn [app cells_bytes cbytes]. rewrite rc_le4_seqz by lia. rewrite !rc_le2_pack. rewrite Hvb.
        cbn [skipn repeat app]. unfold reac_ctrl_parseF.P1. reflexivity. }
    change (length P1) with 24%nat in J2.
    destruct ((cp_v fr 16 =? 0) && (cp_v fr 17 =? 0)) eqn:T0; cbn [negb]; cbv iota.
    { idtac "F0".
      (* the filler: 0x83904 the 4-byte check at the box, 0x83914 li a0,1, 0x83918 -> 0x83ac8 *)
    rewrite andb_true_iff, !Z.eqb_eq in T0. destruct T0 as [T0a T0b].
    refresh. idtac "F1".
    chkb0 (Z_to_bv 5 11) add3. idtac "F2".
    step. step. idtac "F3".
    assert (EK1 : cp_kind fr = 1)
      by (unfold cp_kind, cp_type; rewrite T0a, T0b; cbn [Z.eqb andb Pos.eqb]; reflexivity).
    assert (ERC : cp_rec fr = false)
      by (unfold cp_rec, cp_type; rewrite T0a; cbn [Z.eqb andb Pos.eqb]; reflexivity).
    match goal with H : rw_cells rsegs _ ob [CB 4 _] |- _ => rename H into HKf end.
    match goal with H : rw_cells rsegs _ (ob + 28) [CB 2 _] |- _ => rename H into HTGf end.
    match goal with H : rw_cells rsegs _ (ob + 30) [CB 6 _] |- _ => rename H into HAMPf end.
    eapply (L_kind fra fv spc j nn w120 mc ob _ 1 (repeat cp_z 2) (repeat cp_z 6));
      [ exact HK | exact HB | exact HFL | exact HO
      | refine (conj MUb (conj WMb (conj MIx STx)))
      | exact HKf | exact J2 | exact HTGf | exact HAMPf
      | unfold ctrlparse; rewrite HE; cbn [fst]; exact EK1
      | clear; lia
      | unfold ctrlparse; rewrite HE; cbn [snd]; unfold cp_struct; rewrite EK1, ERC;
        cbn [Z.eqb Pos.eqb repeat app]; unfold reac_ctrl_parseF.P1; reflexivity ]. }
    (* 0x83a14 ..: the kind dispatch *)
    pose proof (cp_v_range fr 16) as R16. pose proof (cp_v_range fr 17) as R17.
    pose proof (cp_v_range fr 18) as R18. pose proof (cp_v_range fr 19) as R19.
    pose proof (cp_v_range fr 22) as R22. pose proof (KL1_range (cp_v fr 22)) as KR.
    assert (KL6 : KL1 (cp_v fr 22) <> 6) by (clear -KR; lia).
    (* the dispatch does no more calls: drop the disjunctive premises, they make every store's
       transport (slia) split the context *)
    clear DFf Fapp Obrt Obsp Obsv Obfr Obcf Obf HfS AFm.
    drive.
    all: try leaves.
    (* goal 2: 0x83a8c, kind_of_link1 *)
    2:{ step.
        eapply evtF_cut; [eapply HKOL | intros ? [? ->]].
        rewrite rc_signed_zxb.
        change (bv_unsigned (cp_b fr 22)) with (cp_v fr 22).
        rewrite (ret_pc_even 539280 ltac:(clear; lia) ltac:(clear; lia)).
        refresh.
        chkb0inv (Z_to_bv 5 12).
        leafb. }
    (* goal 1: 0x83ae8, the record: fr[19] = 3, the two tag bytes, then the amp test *)
    step. step. cond_norm.
    destruct (Z.eqb_spec (cp_v fr 19) 3) as [E19|E19]; cbn [negb]; cbv iota.
    2:{ drive. all: leaves. }
    assert (HRC : cp_rec fr = true) by (unfold cp_rec, cp_type; zeval; reflexivity).
    rdb 34%nat 2%nat ltac:(intros jx Hjx; apply cp_rd_rec; [exact HE | exact HRC | lia]).
    rdb 32%nat 1%nat ltac:(intros jx Hjx; replace (32 + jx)%nat with 32%nat by lia;
                           apply cp_rd_rec; [exact HE | exact HRC | lia]).
    refresh.
    step. chkf 34%Z (Z_to_bv 5 12).
    step. chkf 35%Z (Z_to_bv 5 13).
    obsel (Z_to_bv 5 11) 539432.
    step. chkb 28%Z 2%Z (Z_to_bv 5 14) add1.
    try (match goal with H : rw_cells rsegs _ (ob + 28) _ |- _ => move H at bottom end). do 4 step.
    refresh.
    chkf 32%Z (Z_to_bv 5 13).
    do 3 step. cond_norm.
    destruct (Z.eqb_spec (cp_v fr 32) 18) as [E32|E32]; cbn [negb]; cbv iota.
    2:{ flat_tg. drive. all: leaves. }
    rdb 33%nat 1%nat ltac:(intros jx Hjx; replace (33 + jx)%nat with 33%nat by lia;
                           apply cp_rd_33; [exact HE | exact HRC | exact E32]).
    step. chkf 33%Z (Z_to_bv 5 13).
    do 3 step. cond_norm.
    destruct (Z.eqb_spec (cp_v fr 33) 18) as [E33|E33]; cbn [negb]; cbv iota.
    2:{ flat_tg. drive. all: leaves. }
    do 2 step.
    rewrite rc_pack_eqb by (clear; lia).
    change (bv_unsigned (cp_b fr 34)) with (cp_v fr 34).
    change (bv_unsigned (cp_b fr 35)) with (cp_v fr 35).
    destruct (Z.eqb_spec (cp_v fr 34 * 256 + cp_v fr 35) 257) as [EP|EP]; cbn [negb]; cbv iota.
    2:{ flat_tg.
        destruct (Z.eqb_spec (cp_v fr 34) 1) as [E34a|E34a];
          [ assert (E35a : cp_v fr 35 <> 1)
              by (pose proof (cp_v_range fr 34) as A34; pose proof (cp_v_range fr 35) as A35;
                  clear -A34 A35 EP E34a; lia)
          | ];
          drive; leaves. }
    assert (E34 : cp_v fr 34 = 1)
      by (pose proof (cp_v_range fr 34) as A34; pose proof (cp_v_range fr 35) as A35;
          clear -A34 A35 EP; lia).
    assert (E35 : cp_v fr 35 = 1)
      by (pose proof (cp_v_range fr 34) as A34; pose proof (cp_v_range fr 35) as A35;
          clear -A34 A35 EP; lia).
    refresh. chkb0 (Z_to_bv 5 11) add3.
    try (match goal with H : rw_cells rsegs _ ob _ |- _ => move H at bottom end). do 3 step.
    assert (EK6 : cp_kind fr = 6) by (unfold cp_kind, cp_type, cp_amp; zeval; reflexivity).
    rdb 36%nat 3%nat ltac:(intros jx Hjx; apply cp_rd_amp; [exact HE | exact HRC | exact EK6 | lia]).
    refresh.
    chkf 36%Z (Z_to_bv 5 12).
    obsel (Z_to_bv 5 11) 539596.
    step. chkb 30%Z 1%Z (Z_to_bv 5 13) no_extra.
    do 2 step.
    refresh.
    chkf 37%Z (Z_to_bv 5 12).
    obsel (Z_to_bv 5 11) 539656.
    step. chkb 31%Z 1%Z (Z_to_bv 5 13) no_extra.
    do 2 step.
    refresh.
    chkf 38%Z (Z_to_bv 5 12).
    obsel2 (Z_to_bv 5 26) 539712.
    step. chkb 32%Z 1%Z (Z_to_bv 5 13) no_extra.
    do 2 step.
    flat_tg.
    match goal with
    | HOb : OB ?fraq ?obq |- _ =>
        match goal with Hq : rw_cells rsegs _ (obq + 30) _ |- _ => rename Hq into HAMPr end;
        apply (rc_rw_flat rsegs _ (obq + 30) _
                 ([cp_b fr 36; cp_b fr 37; cp_b fr 38] ++ repeat cp_z 3)) in HAMPr;
        [ cbn [length app repeat] in HAMPr
        | first [ reflexivity
                | cbn [cells_bytes cbytes app repeat skipn firstn]; reflexivity
                | vm_compute; reflexivity ] ];
        eapply (L_be0 fraq _ _ _ _ _ _ obq _ 6 [cp_b fr 35; cp_b fr 34]
                      ([cp_b fr 36; cp_b fr 37; cp_b fr 38] ++ repeat cp_z 3))
    end;
    first [ eassumption
          | refine (conj _ (conj _ (conj _ _))); eassumption
          | clear; lia
          | kfact
          | bfact ].
  Qed.


  (* 0x836c0 .. 0x8370c: the two header bytes (12 = 0x88, 13 = 0x19), each behind its shadow check; a byte that
     differs leaves with the kind 0 and the zeroed box. *)
  Lemma body_tail : 50 <= n -> forall fra fv spc j nn w120 mc ob (mx : word -> option byte)
      (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    addressable mc ob 36 -> asan_cells mc -> shadow_rw mc ->
    BJ ob spc mc mx -> rw_cells rsegs mx ob [CB 36 (repeat cp_z 36)] ->
    evtF rsegs RNG (QE fv)
      (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 n) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x836c0) fc None mx (seg_rom rsegs)).
  Proof. hide_sec.
    intros Hn50 fra fv spc j nn w120 mc ob mx rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB HFL HO Aob ACc SRc HBJ RWx.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof (RINF Hn50) as RGINF. pose proof (SCF Hn50) as SCINF. pose proof (SKF Hn50) as SKINF.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof MU as MUw. apply (munch_weaken _ _ _ _ (Wf2_sub fra j nn)) in MU.
    pose proof HBJ as HBJ'. destruct HBJ' as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    destruct (f_facts Hn50 fra fv spc j nn w120 ob HK HO) as (Hf0 & Hf64 & Fapp & AFm & DFf).
    assert (Hjnn : 0 <= j < 8192 /\ nn <= 1)
      by (destruct HK as [(_ & _ & _ & Ej & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)];
          [lia | change (fs_M 1) with 8192 in Hjb; lia]).
    pose proof DFf as DFf'. unfold reac_ctrl_parseF.Wall, reac_ctrl_parseF.Wf in DFf'. cbn [disjoint_from app fst snd] in DFf'.
    destruct DFf' as (Dwin & Dhint & Dflag & Dfr & Dsh & Dbox & _).
    assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rfb : 0 <= f /\ f + 50 <= 2 ^ 64) by (clear -Hf0 Hf64; lia).
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc mx HK HO MU Aob MUb) as AFx.
    (* 0x836c0: byte 12 of the frame, checked *)
    rdb 12%nat 1%nat ltac:(intros jx Hjx; replace (12 + jx)%nat with 12%nat by lia;
                                     apply cp_rd_12; lia).
    step.
    assert (RX12 : 0 <= f + 12 < 2 ^ 64) by (clear -Hf0 Hf64; lia).
    pose proof (acl_shadow mx f 50 12 1 (f + 12) AFx ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(pose proof (Z.mod_pos_bound (f + 12) 8 ltac:(clear; lia)) as MB; clear -MB; lia)
                  ltac:(clear; lia)) as SH12.
    chk_core (f + 12) RX12 (Z_to_bv 5 12) SH12 pre_sr no_extra.
    do 3 step.
    rewrite (rc_eqb_zxb (cp_b fr 12) 136) by (clear; lia).
    change (bv_unsigned (cp_b fr 12)) with (cp_v fr 12).
    destruct (Z.eqb_spec (cp_v fr 12) 136) as [E12|E12]; cbn [negb]; cbv iota.
    2:{ assert (Hcphdr : cp_hdr n fr = false)
          by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E12), andb_false_r; reflexivity).
        assert (Hcp0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite Hcphdr; reflexivity).
        step.
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite Hcp0; reflexivity).
        eapply L_join;
          [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx | ].
        rewrite (ctrlparse_bytes_none n fr Hcphdr). exact RWx. }
    (* 0x836e0: byte 13 of the frame, checked *)
    rdb 13%nat 1%nat ltac:(intros jx Hjx; replace (13 + jx)%nat with 13%nat by lia;
                                     apply cp_rd_13; lia).
    step.
    assert (RX13 : 0 <= f + 13 < 2 ^ 64) by (clear -Hf0 Hf64; lia).
    pose proof (acl_shadow mx f 50 13 1 (f + 13) AFx ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(pose proof (Z.mod_pos_bound (f + 13) 8 ltac:(clear; lia)) as MB; clear -MB; lia)
                  ltac:(clear; lia)) as SH13.
    chk_core (f + 13) RX13 (Z_to_bv 5 12) SH13 pre_sr no_extra.
    do 3 step.
    rewrite (rc_eqb_zxb (cp_b fr 13) 25) by (clear; lia).
    change (bv_unsigned (cp_b fr 13)) with (cp_v fr 13).
    destruct (Z.eqb_spec (cp_v fr 13) 25) as [E13|E13]; cbn [negb]; cbv iota.
    2:{ assert (Hcphdr : cp_hdr n fr = false)
          by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E13), andb_false_r; reflexivity).
        assert (Hcp0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite Hcphdr; reflexivity).
        step.
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite Hcp0; reflexivity).
        eapply L_join;
          [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx | ].
        rewrite (ctrlparse_bytes_none n fr Hcphdr). exact RWx. }
    assert (HE : cp_hdr n fr = true) by (apply cp_hdr_spec; repeat split; lia).
    (* 0x83700 .. 0x8370c: s6 = the box pointer, on both paths of `beqz s4` *)
    lazymatch goal with
    | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm _ ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w : word, w = Z_to_bv 64 ob ->
                      evtF segs rgq Q (MS (bvmap_set (Z_to_bv 5 22) w R) Fm (Z_to_bv 64 0x8370c) fcc rv mm ro));
        [ step; step; rewrite (rc_eqb_lit o 0) by (clear -Ro; lia);
          destruct HO as [(Eo & Eob) | (Eo & Eob)];
          [ rewrite (proj2 (Z.eqb_eq o 0) Eo); cbv iota;
            apply (G (Z_to_bv 64 (fra + 32)) ltac:(rewrite Eob; reflexivity))
          | rewrite (proj2 (Z.eqb_neq o 0) Eo); cbv iota; step;
            apply (G (Z_to_bv 64 o) ltac:(rewrite Eob; reflexivity)) ]
        | intros w Hw; subst w; simp_regs ]
    end.
    eapply (body_copy Hn50 HE fra fv spc j nn w120 mc ob mx);
      [ exact HK | exact HB | exact HFL | exact HO | exact Aob | exact ACc | exact SRc | exact HBJ | exact RWx ].
  Qed.


  (* 0x836a8 .. : __asan_memset(ob, 0, 36) zeroes the output box, then the header test n < 50. ob is the box the
     run chose at 0x8369c/0x836a0 (the frame's redzone when o = 0, else o). *)
  Lemma body_main : forall fra fv spc j nn w120 mc ob jb
      (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    rw_cells rsegs mc ob [CB 36 jb] -> addressable mc ob 36 -> stk rsegs mc (S - 8800) S ->
    asan_cells mc -> shadow_rw mc ->
    evtF rsegs RNG (QE fv)
      (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 n) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x836a8) fc None mc (seg_rom rsegs)).
  Proof. hide_sec.
    intros fra fv spc j nn w120 mc ob jb rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB HFL HO HOrw Aob STw ACc SRc.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    pose proof MU as MUw. apply (munch_weaken _ _ _ _ (Wf2_sub fra j nn)) in MU.
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc;
          clear -HAlo HAhi; lia).
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -Hspcr RS; lia).
    assert (Rob : 0 <= ob < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (U36 : bv_unsigned (Z_to_bv 64 36) = 36) by reflexivity.
    assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (STsp : stk rsegs mc (S - 8800) spc)
      by (apply (stk_sub mc (S - 8800) S (S - 8800) spc STw); clear -Hspcr RS; lia).
    pose proof HMSET as HM. unfold asan_memset_contract_F, ASAN_MEMSET_K in HM. cbv zeta in HM.
    unfold rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HM.
    (* 0x836a8 li a2,36; 0x836ac mv a0,s3; 0x836b0 li a1,0; 0x836b4 jal -> 0x524c4 *)
    do 4 step.
    eapply evtF_cut.
    { eapply HM with (junk := jb) (lo := S - 8800);
        rewrite ?(unsigned_lit _ Rob), ?(unsigned_lit spc Rspc), ?U36, ?U0.
      - change (Z.to_nat 36) with 36%nat. exact HOrw.
      - clear; lia.
      - exact Aob.
      - right; exact Obapp.
      - right; apply (acl_app_in mc _ 36 7 Aob); clear; lia.
      - exact Obrt.
      - clear -Obsp; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact ACc.
      - exact SRc.
      - exact MI.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* __asan_memset's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the 36 bytes of the box *) exact RGOB.
      - (* their aligned shadow word cover *) right. unfold shadow_addr. apply SKOB; clear; lia.
      - (* the shadow of __asan_memset's window *)
        right. unfold shadow_addr. apply rngF_win_sh8; clear -Hspcr RS; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1m & a2m & a3m & a4m & a5m & a6m & a7m & t3' & t4' & t5' & t6' & m' &
                       Hms & MUm & WMm & MIm & STm & RWm & ACm & SRm).
    subst ms'.
    rewrite (ret_pc_even 538296 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit _ Rob), U36, (unsigned_lit spc Rspc) in MUm. unfold ASAN_MEMSET_K in MUm.
    rewrite (unsigned_lit _ Rob), U36 in RWm. change (Z.to_nat 36) with 36%nat in RWm.
    rewrite (unsigned_lit spc Rspc) in STm.
    (* the body's running footprint: the box and the callee windows *)
    pose proof RWm as RWbk. destruct RWbk as [[_ Hbox] _]. cbn [cells_bytes cbytes] in Hbox.
    rewrite app_nil_r in Hbox.
    assert (RMc : rd_mono mc m').
    { apply (rd_mono_list _ mc m' MUm). constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - intros y Hy. apply (rd_of_bytes _ _ _ Hbox). rewrite repeat_length. clear -Hy; cbn; lia.
      - intros y Hy. apply (rd_of_stk _ _ _ STm). clear -Hy Hspcr; lia. }
    assert (MUx : munch [(ob, ob + 36); (S - 8800, spc)] mc m').
    { eapply munch_weaken; [| exact MUm].
      intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & _).
      split; [exact H1|]. split; [clear -H2 Hspcr; lia | exact I]. }
    assert (STx : stk rsegs m' (S - 8800) S) by (exact (stk_mono mc m' (S - 8800) S STw WMm RMc)).
    (* 0x836b8: li a0,50; 0x836bc: bltu s6,a0 -> n < 50 exits at 0x8391c *)
    step. step. rewrite (rc_ltu_lit n 50) by lia.
    destruct (Z.ltb_spec n 50) as [Hlt|Hge]; cbv iota.
    - (* n < 50: no header, the box stays zero, a0 = 0 *)
      step.
      assert (Hcphdr : cp_hdr n fr = false)
        by (unfold cp_hdr; rewrite (proj2 (Z.leb_gt 50 n) Hlt); reflexivity).
      assert (Hcp0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite Hcphdr; reflexivity).
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite Hcp0; reflexivity).
      eapply (L_join fra fv spc j nn w120 mc ob m');
        [ exact HK | exact HB | exact HFL | exact HO | exact MUx | exact WMm | exact MIm | exact STx | ].
      rewrite (ctrlparse_bytes_none n fr Hcphdr). exact RWm.
    - (* 50 <= n: the header checks, the copies, the comparison and the kind *)
      eapply (body_tail Hge fra fv spc j nn w120 mc ob m');
        [ exact HK | exact HB | exact HFL | exact HO | exact Aob | exact ACc | exact SRc
        | refine (conj MUx (conj WMm (conj MIm STx))) | ].
      replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with cp_z in RWm
        by (vm_compute; reflexivity).
      exact RWm.
  Qed.

  (* 0x8369c .. 0x836a8: the box pointer s3 = o (or the frame's redzone when o = 0). *)
  Lemma body_holds_x : KBx QE.
  Proof. hide_sec.
    unfold KBx. intros fra fv spc j nn w120 mc rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31
      HK HB HFL HBaddr.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _ & HWd & HDd).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    assert (EMt : fs_M 1 = 8192) by reflexivity.
    assert (Hjb0 : 0 <= j < 8192)
      by (destruct HK as [(_ & _ & _ & Ej & _) | (Hjb & _ & _ & _ & _ & _)];
          [lia | rewrite EMt in Hjb; lia]).
    assert (Hnn1 : nn <= 1)
      by (destruct HK as [(_ & _ & _ & _ & Enn) | (_ & _ & _ & _ & _ & Enn & _)]; lia).
    pose proof (stk_mono m mc (S - 8800) S ST0 WM RM) as STw.
    assert (STfr : stk rsegs mc fra (fra + 128)).
    { destruct HK as [(Efv & Efra & _) | (Hj & Efra & _)].
      - apply (stk_sub mc (S - 8800) S fra (fra + 128) STw);
          [ clear -Efra HAlo HAhi RS; rewrite Efra; lia | clear -Efra HAlo HAhi RS; rewrite Efra; lia | lia ].
      - pose proof (stk_mono m mc FS (FS + FS_SIZE) Pfsstk WM RM) as STfs.
        assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
          by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
              change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
        rewrite EMt in Hj.
        apply (stk_sub mc FS (FS + FS_SIZE) fra (fra + 128) STfs);
          [ rewrite Efra, EFRj; clear -Pfs0 Hj; lia
          | rewrite Efra, EFRj; unfold FS_SIZE; clear -Pfs0 HFSb Hj; lia | lia ]. }
    assert (ACc : asan_cells mc).
    { apply (asan_cells_kept (Wf2 fra j nn) m mc AC0 MU).
      unfold Wf2, RT_LO, RT_HI, fs_hint, fs_flag, shadow_addr;
        cbn [disjoint_from fst snd Z.of_nat Pos.of_succ_nat].
      try (change (2 ^ 15) with 32768); try (change (2 ^ (15 - 1)) with 16384).
      repeat split; try exact I; left;
        unfold HIGHMEM_BEG, APPMEM_END in *;
        clear -HHM HAE Pfs2 Hjb0 FRlo SH1; lia. }
    pose proof (shadow_rw_mono m mc SR0 WM RM) as SRc.
    (* 0x8369c: mv s3,s10; 0x836a0: beqz s4 -> the box pointer *)
    step.
    step. rewrite (rc_eqb_lit o 0) by lia.
    destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbv iota.
    - (* o = 0: the box is the frame's redzone fra + 32, carved from the frame's stack bytes *)
      assert (STbox : stk rsegs mc (fra + 32) (fra + 68))
        by (apply (stk_sub mc fra (fra + 128) (fra + 32) (fra + 68) STfr); lia).
      destruct (stk_carve rsegs mc (fra + 32) (fra + 68) 36%nat STbox ltac:(lia)) as [_ [jb Hrw]].
      replace (fra + 68 - Z.of_nat 36) with (fra + 32) in Hrw by lia.
      eapply (body_main fra fv spc j nn w120 mc (fra + 32) jb);
        [ exact HK | exact HB | exact HFL | left; split; [exact Eo | reflexivity]
        | exact Hrw | exact HBaddr | exact STw | exact ACc | exact SRc ].
    - (* o <> 0: the box is o, transported from the caller's rw_cells *)
      step.
      destruct (HOK Eo) as (Ho4 & Ho36 & HOrw & HoS & Hof).
      assert (HinO : In (o, o + 36) (reac_ctrl_parse_D f n o))
        by (unfold reac_ctrl_parse_D; apply in_or_app; right;
            rewrite (proj2 (Z.eqb_neq o 0) Eo); left; reflexivity).
      assert (Hdjo : forall x, o <= x < o + 36 -> outside (Wf2 fra j nn) x).
      { intros x Hx.
        destruct (AO0 Eo) as (AOa & _ & _).
        assert (Hxapp : app_mem x)
          by (pose proof (acl_app_in m o 36 (x - o) AOa ltac:(lia)) as Ha;
              replace (o + (x - o)) with x in Ha by lia; exact Ha).
        pose proof (dj_pair o (o + 36) _ _ HinO (proj1 (fp_wx_hint_flag_in FS X))) as Hoh.
        pose proof (dj_pair o (o + 36) _ _ HinO (proj2 (fp_wx_hint_flag_in FS X))) as Hofl.
        unfold Wf2. cbn [outside]. split; [| split; [| split; [| split; [| split; [| exact I]]]]].
        - clear -Hx HoS; destruct HoS; lia.
        - intros [HL HR]. clear -Hx HL HR Hoh; lia.
        - intros [HL HR]. destruct HK as [(_ & _ & _ & _ & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)].
          + rewrite Enn in HR. clear -HL HR; lia.
          + rewrite Enn in HR.
            assert (EFL : fs_flag FS 1 j = fs_flag FS 1 0 + j) by (rewrite !fs_flag1; lia).
            rewrite EFL in HL, HR. rewrite EMt in Hjb, Hofl. clear -Hx HL HR Hofl Hjb; lia.
        - intros [HL HR]. destruct HK as [(_ & Efr & _ & _ & _) | (Hjb & Efr & _ & _ & _ & _ & Hfl0)].
          + rewrite Efr in HL, HR. clear -Hx HoS HL HR HAlo HAhi; destruct HoS; lia.
          + destruct (D_apart_frame o (o + 36) j HinO ltac:(clear; lia) Hjb Hfl0) as [Hc|Hc];
              rewrite <- Efr in Hc; clear -Hx HL HR Hc; lia.
        - intros [HL HR]. apply (acl_app_not_shadow x Hxapp). unfold shadow_addr in HL, HR.
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia]. }
      assert (Hbox : rw_cells rsegs mc o [CB 36 junk])
        by (eapply acl_rw; [exact HOrw | exact MU | exact WM |
              intros x Hx; apply Hdjo; cbn [cells_size csize] in Hx; lia]).
      assert (Aob : addressable mc o 36).
      { destruct (AO0 Eo) as (AOa & _ & _).
        apply (acl_addr_munch (Wf2 fra j nn) m mc o 36 AOa MU).
        intros i Hi.
        pose proof (acl_app_in m o 36 i AOa Hi) as Hoi.
        pose proof (rt_app_shadow (o + i) Hoi) as Hsh.
        unfold Wf2. cbn [outside]. split; [| split; [| split; [| split; [| split; [| exact I]]]]].
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          unfold app_mem, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *; clear -HL HR HHM HAE; right; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          apply Pfsapp. unfold fs_hint in HL, HR; cbn [Z.of_nat] in HL, HR;
            unfold FS_SIZE; clear -HL HR Pfs0; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          apply Pfsapp. unfold fs_flag in HL, HR; cbn [Z.of_nat Pos.of_succ_nat] in HL, HR;
            change (2 ^ 15) with 32768 in HL, HR; change (2 ^ (15 - 1)) with 16384 in HL, HR;
            unfold FS_SIZE; clear -HL HR Pfs0 Hjb0 Hnn1; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          replace (shadow_addr (o + i)) with (fra + (shadow_addr (o + i) - fra)) by lia.
          apply FAP; clear -HL HR; lia.
        + intros HC.
          assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
            by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
          rewrite E16 in HC.
          apply (acl_win_sh (o + i) fra (fra + 128) FR8); [| exact HC].
          intros [HL HR].
          destruct HK as [(_ & Efr & _ & _ & _) | (Hjb & Efr & _ & _ & _ & _ & Hfl0)].
          * destruct HoS as [Hc|Hc]; rewrite Efr in HL, HR; clear -Hi Hc HL HR HAlo HAhi; lia.
          * destruct (D_apart_frame o (o + 36) j HinO ltac:(clear; lia) Hjb Hfl0) as [Hc|Hc];
              rewrite <- Efr in Hc; clear -Hi HL HR Hc; lia. }
      eapply (body_main fra fv spc j nn w120 mc o junk);
        [ exact HK | exact HB | exact HFL | right; split; [exact Eo | reflexivity]
        | exact Hbox | exact Aob | exact STw | exact ACc | exact SRc ].
  Qed.

End RBodyF.

(* ==== Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery) and its 09:58Z ruling): Module RBodyFOn
   re-derives Section RBodyF above, with the same names and scripts, for reac_ctrl_parseF.v's Module ParseFOn: the
   callees' `_F_on` contracts, SR0 : shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m, every reac_ctrl_parseF.v /
   split-file Section name redirected to its route-(C) module (ParseFOn, BndFOn, PreFOn, RelFOn, BodyFOn, PostFOn, RBodyFOn; the
   notation arguments read off `About` of each), and reac_ctrl_parseF.v's shadow edits where these scripts carry them
   (the region lemmas srw_* / frame_in_R; the post's forall-P form). Section RBodyF above keeps its own text; since Module RBodyFOn was added, Section RBodyF gained the hide_h / hide_sec tactics, `Proof. hide_sec.` openings, the junk / HOK notation arguments and a few proof steps.
   rule 24: no function proved beyond reac_ctrl_parseF.v's own run (proof-index reac_ctrl_parse 2026-10-29
   00:3xZ, exit 0: 12 named files + 8 lemma rows, plain / ubsan builds of other units; checker a Theorem Labs lane: CONFIRM). ==== *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_cF_on
  asan_memcpy_cF_on bcmp_wrap_c_on.
Local Open Scope Z_scope.

Module RBodyFOn.

Section RBodyF.
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
  Local Notation body_holds := (@reac_ctrl_parseF.ParseFOn.body_holds ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f n o S FS fr junk RNG HMSET HMCPY HBCMPW HKOL Rf Rn Ro RS S16 ST0 Lfr HF Hrd HOK AC0 SR0 HHM HAE AW0 AF0 AO0 ABC HBCMP HMEMCMP HGCF HCF254 HCF255 X XF0 XB0 FP0 TLS0 RBY RIMG RWIN SCW SKW RINF SCF SKF ROUT SCO SKO RBC SKBC RFLG RFRM SCFR SKFR).
  (* Route (C): Module ParseFOn's region lemmas, at this Section's variables (arguments read off `About`). *)
  Local Notation srw_frame := (@reac_ctrl_parseF.ParseFOn.srw_frame m f n o S FS fr Rf Rn Ro Lfr).
  Local Notation srw_memset := (@reac_ctrl_parseF.ParseFOn.srw_memset tp m f n o S FS fr Rf Rn Ro RS S16 Lfr X FP0).
  Local Notation srw_memcpy := (@reac_ctrl_parseF.ParseFOn.srw_memcpy tp m f n o S FS fr Rf Rn Ro RS S16 Lfr X FP0).
  Local Notation srw_bcmp := (@reac_ctrl_parseF.ParseFOn.srw_bcmp f n o S FS fr Rf Rn Ro RS Lfr).
  (* Speed: hide_sec turns the Section's implications (and S16's mod) into @id Prop T, which lia does not split on; each stays usable by name and in the Notations above. *)
  Local Ltac hide_h H := let T := type of H in change (@id Prop T) in H.  Local Ltac hide_sec := hide_h HF; hide_h HOK; hide_h AF0; hide_h AO0; hide_h RINF; hide_h SCF; hide_h SKF; hide_h ROUT; hide_h SCO; hide_h SKO; hide_h S16.
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

  (* Wf of reac_ctrl_parseF.v (:1189) without the class-1 hint word: its interval is empty here. *)
  Definition Wf2 (fa j nn : Z) : list ivl :=
    [(S - 8800, S); (fs_hint FS 1, fs_hint FS 1); (fs_flag FS 1 j, fs_flag FS 1 j + nn);
     (fa, fa + 128); (shadow_addr fa, shadow_addr fa + 16)].

  Lemma Wf2_sub : forall fa j nn, sub_fp (Wf2 fa j nn) (Wf fa j nn).
  Proof.
    intros fa j nn x Hx. unfold reac_ctrl_parseF.ParseFOn.Wf in Hx. unfold Wf2. cbn [outside] in Hx |- *.
    destruct Hx as (H1 & H2 & H3 & H4 & H5 & _). repeat split; try assumption; lia.
  Qed.

  (* KB of reac_ctrl_parseF.v (:1395), with the post depending on the frame's kind fv (the frame binder is named
     fra here, as it shadows nothing). *)
  Definition KBx (Q : Z -> machine_state -> Prop) : Prop :=
    forall (fra fv spc j nn : Z) (w120 : word) (mc : word -> option byte)
           (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
      FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> addressable mc (fra + 32) 36 ->
      evtF rsegs RNG (Q fv) (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
                         x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 (Z_to_bv 64 o) (Z_to_bv 64 f)
                         (Z_to_bv 64 n) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
                         (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x8369c) fc None mc (seg_rom rsegs)).

  (* fwords of reac_ctrl_parseF.v (:1434), with KBx *)
  Lemma fwords_x : forall fra fv spc j nn w120 mc
    (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 : word) (Q : Z -> machine_state -> Prop),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> KBx Q ->
    evtF rsegs RNG (Q fv) (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
                       x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 (Z_to_bv 64 o) (Z_to_bv 64 f)
                       (Z_to_bv 64 n) x23 (Z_to_bv 64 fra) (wa ASAN_K) x26 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x8361c) fc None mc (seg_rom rsegs)).
  Proof. hide_sec.
    intros fra fv spc j nn w120 mc rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 Q HK HB HFL K.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (HFSpos & _ & _ & Pfsapp & _) & _ & _ & _ & HFSb & _).
    unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    assert (HHMl : 17594333495296 <= S - 8800) by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    unfold Wf2, shadow_addr in MU.
    (* the writes of this block, for carrying FLG from mc *)
    pose proof (munch_refl [(A + 24, A + 32); (fra, fra + 24); (fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16)] mc) as MUf.
    wst (A + 24) 8%nat ltac:(apply STW0; lia). step. store_done.
    steps_to 0x83644.
    wstb fra 8%nat fra FW. step. store_done.
    wstb (fra + 8) 8%nat fra FW. step. store_done.
    wstb (fra + 16) 8%nat fra FW. step. store_done.
    step. step.
    rewrite (unsigned_lit fra) by lia. rewrite rc_shr3.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
      pose proof (shadow_rw_mono_on _ m mcur SR0 WM RM) as SRmc;
      pose proof (shadow16_stk_on mcur fra (srw_frame fra fv spc j nn w120 mcur HK SRmc) ltac:(lia) FRA
                    ltac:(lia) ltac:(lia)) as STsh
    end.
    pose proof (stk_carve rsegs m1 (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16) 16%nat STsh ltac:(lia))
      as [STsh' [junkS SHC]].
    replace (fra / 8 + ASAN_K + 16 - Z.of_nat 16) with (fra / 8 + ASAN_K) in SHC by lia.
    sstep (fra / 8 + ASAN_K) 0 0%nat SW.
    sstep (fra / 8 + ASAN_K) 1 1%nat SW.
    sstep (fra / 8 + ASAN_K) 2 2%nat SW.
    sstep (fra / 8 + ASAN_K) 3 3%nat SW.
    step.
    sstep (fra / 8 + ASAN_K) 12 12%nat SW.
    sstep (fra / 8 + ASAN_K) 13 13%nat SW.
    sstep (fra / 8 + ASAN_K) 14 14%nat SW.
    sstep (fra / 8 + ASAN_K) 15 15%nat SW.
    sstep (fra / 8 + ASAN_K) 8 8%nat SW.
    sstep (fra / 8 + ASAN_K) 9 9%nat SW.
    sstep (fra / 8 + ASAN_K) 10 10%nat SW.
    sstep (fra / 8 + ASAN_K) 11 11%nat SW.
    sstep (fra / 8 + ASAN_K) 4 4%nat SW.
    sstep (fra / 8 + ASAN_K) 5 5%nat SW.
    sstep (fra / 8 + ASAN_K) 6 6%nat SW.
    sstep (fra / 8 + ASAN_K) 7 7%nat SW.
    destruct SHC as [[_ HB16] _]. cbn [cells_bytes cbytes app] in HB16.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) => assert (FLf : FLG fra nn w120 mf) end.
    { destruct HFL as [(flg & Hfl & Hfln & HflF) Hw].
      assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
      split.
      - exists flg. split; [|split; [exact Hfln | exact HflF]].
        eapply fl_bytes; [exact Hfl | exact MUf |].
        intros x Hx. rewrite Hfln, EFL0 in Hx. change (fs_M 1) with 8192 in Hx.
        assert (Hxa : app_mem x) by (apply Pfsapp; unfold FS_SIZE; clear -Hx HFSpos; lia).
        cbn [outside]. split; [|split; [|split; [|exact I]]].
        + clear -Hx HAlo HFSb RS; lia.
        + clear -Hx FRlo; lia.
        + intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo HFSpos; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia].
      - intros En. eapply fl_bytes; [exact (Hw En) | exact MUf |].
        intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
        assert (Hxa : app_mem x) by (replace x with (fra + (x - fra)) by lia; apply FAP; lia).
        cbn [outside]. split; [|split; [|split; [|exact I]]].
        + clear -Hx FRhi; lia.
        + clear -Hx; lia.
        + intros [HL HR]. apply (acl_app_not_shadow x Hxa).
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo HFSpos; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia]. }
    eapply K.
    - exact HK.
    - unfold reac_ctrl_parseF.ParseFOn.BI, Wf2, shadow_addr. refine (conj MU (conj WM (conj RM (conj MI SV)))).
    - exact FLf.
    - apply frame_shadow_addr.
      + lia.
      + exact FR8.
      + unfold APPMEM_END in *; lia.
      + intros i Hi. replace (fra + 32 + i) with (fra + (32 + i)) by lia. apply FAP; lia.
      + intros g Hg. destruct HB16 as (_ & _ & Hr). exists (Z_to_bv 8 0). split; [|reflexivity].
        assert (Hc : g = 4 \/ g = 5 \/ g = 6 \/ g = 7) by lia.
        destruct Hc as [H|[H|[H|H]]]; rewrite H;
          [ replace (fra / 8 + ASAN_K + 4) with (fra / 8 + ASAN_K + Z.of_nat 4) by lia;
            rewrite (Hr 4%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 5) with (fra / 8 + ASAN_K + Z.of_nat 5) by lia;
            rewrite (Hr 5%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 6) with (fra / 8 + ASAN_K + Z.of_nat 6) by lia;
            rewrite (Hr 6%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 7) with (fra / 8 + ASAN_K + Z.of_nat 7) by lia;
            rewrite (Hr 7%nat ltac:(cbn [length]; lia)) ]; reflexivity.
      + destruct HB16 as (_ & _ & Hr). exists (Z_to_bv 8 4). split; [|reflexivity].
        replace (fra / 8 + ASAN_K + 8) with (fra / 8 + ASAN_K + Z.of_nat 8) by lia.
        rewrite (Hr 8%nat ltac:(cbn [length]; lia)). reflexivity.
  Qed.

  (* The body (0x8369c .. 0x83920) with the exit as a hypothesis. *)
    Variable QE : Z -> machine_state -> Prop.
    Hypothesis HEXIT : forall fra fv spc j nn w120 mc
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
    evtF rsegs RNG (QE fv)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fv) x19 x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K))
               (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83920) fc None mc (seg_rom rsegs)).

    Local Notation P1 := (@reac_ctrl_parseF.ParseFOn.P1 fr).

  (* Every exit of the body reaches 0x83920 in a memory mx that the body produced from mc writing only the box
     and the callee windows, with a0 = the parse's kind and the box holding the parse's bytes: HEXIT's
     premises, assembled once. *)
  Lemma L_join : forall fra fv spc j nn w120 mc ob (mx : word -> option byte)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    munch [(ob, ob + 36); (S - 8800, spc)] mc mx -> wmono rsegs mc mx ->
    mem_inv rsegs mx -> stk rsegs mx (S - 8800) S ->
    rw_cells rsegs mx ob [CB 36 (snd (ctrlparse n fr))] ->
    evtF rsegs RNG (QE fv)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 fv) x19 x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K))
               (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83920) fc None mx (seg_rom rsegs)).
  Proof. hide_sec.
    intros fra fv spc j nn w120 mc ob mx x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x25 x26
      x28 x29 x30 x31 HK HB HFL HO MUb WMb MIx STx RWx.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct HB as (MU & WM & RM & MI & SV).
    pose proof MU as MUw. apply (munch_weaken _ _ _ _ (Wf2_sub fra j nn)) in MU.
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc;
          clear -HAlo HAhi; lia).
    (* the box bytes and the window are readable at mx, so every byte readable at mc still is *)
    assert (RMb : rd_mono mc mx).
    { pose proof RWx as RWbk. destruct RWbk as [[_ Hbx] _]. cbn [cells_bytes cbytes] in Hbx.
      rewrite app_nil_r in Hbx.
      apply (rd_mono_list _ mc mx MUb). constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - intros y Hy. apply (rd_of_bytes _ _ _ Hbx). rewrite ctrlparse_length. clear -Hy; cbn; lia.
      - intros y Hy. apply (rd_of_stk _ _ _ STx). clear -Hy Hspcr RS; lia. }
    assert (EFL0 : fs_flag FS 1 0 = FS + 20480)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384; lia).
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    assert (MUx : munch (Wex fra) m mx).
    { eapply munch_trans;
        [ eapply munch_weaken; [exact (subWf_Wex fra fv spc j nn w120 HK) | exact MU]
        | eapply munch_weaken; [exact (ob_wex fra fv spc j nn w120 ob HK HO) | exact MUb] ]. }
    assert (WMx : wmono rsegs m mx) by (eapply wmono_trans; [exact WM | exact WMb]).
    assert (RMx : rd_mono m mx) by (eapply rd_mono_trans; [exact RM | exact RMb]).
    assert (STfs : stk rsegs mx FS (FS + FS_SIZE)) by (exact (stk_mono m mx _ _ Pfsstk WMx RMx)).
    eapply HEXIT.
    - exact HK.
    - exact MUx.
    - exact WMx.
    - exact RMx.
    - exact MIx.
    - exact (fl_asan_cells (Wex fra) m mx AC0 MUx
               (fun x Hx => aout_rt (Wex fra) x (Wex_subW fra fv spc j nn w120 HK) Hx)).
    - exact (shadow_rw_mono_on _ m mx SR0 WMx RMx).
    - exact STx.
    - apply (rw_cells_transport rsegs _ mc mx (S - 96) SAVES SV MUb WMb).
      cbn [disjoint_from cells_size csize reac_ctrl_parseF.ParseFOn.SAVES fst snd].
      split; [clear -Obsv RS; lia|]. split; [right; clear -Hspcr; lia | exact I].
    - intros Ho. destruct HO as [(Eo & _) | (_ & Eob)]; [exfalso; exact (Ho Eo) | rewrite <- Eob; exact RWx].
    - destruct (rd8_le8 mx (fs_hint FS 1)
                 ltac:(unfold fs_hint; cbn [Z.of_nat]; clear -Pfs0; lia)
                 ltac:(unfold fs_hint; cbn [Z.of_nat]; clear -Pfs0 HFSb RS; lia)
                 ltac:(intros i Hi; apply (rd_of_stk _ _ _ STfs);
                       unfold fs_hint, FS_SIZE; cbn [Z.of_nat]; clear -Hi Pfs0; lia)) as [hh Hhint].
      exists hh. exact Hhint.
    - destruct HFL as [(flg & Hfl & Hfln & HflF) _].
      exists flg. split; [|split; [exact Hfln | exact HflF]].
      eapply fl_bytes; [exact Hfl | exact MUb |].
      intros x Hx. rewrite Hfln, EM1, EFL0 in Hx.
      cbn [outside]. split; [|split; [|exact I]].
      + clear -Hx Obfl EFL0 EM1; rewrite EFL0, EM1 in Obfl; lia.
      + clear -Hx HFSb Pfs0 Hspcr RS; lia.
    - intros Enn. destruct HFL as [_ Hw]. pose proof (Hw Enn) as Hw120.
      assert (Hfrside : fra + 128 <= S - 8800).
      { destruct HK as [(_ & _ & _ & _ & Enn0) | (Hj & Efra & _)]; [clear -Enn Enn0; lia|].
        rewrite EM1 in Hj. rewrite Efra. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
        change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. clear -Hj HFSb Pfs0; lia. }
      eapply fl_bytes; [exact Hw120 | exact MUb |].
      intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
      cbn [outside]. split; [|split; [|exact I]].
      + destruct Obfr as [Eob | Hout]; [clear -Hx Eob; lia | clear -Hx Hout; lia].
      + clear -Hx Hfrside Hspcr RS; lia.
    - (* the class-1 flag array: the frame block wrote only flag j there, the body none of it *)
      intros x Hx Hnj.
      assert (Hxr : FS + 20480 <= x < FS + 28672) by (rewrite EFL0, EM1 in Hx; clear -Hx; lia).
      assert (Hbd : 0 <= x < 2 ^ 64) by (clear -Hxr Pfs0 HFSb RS; lia).
      rewrite (munch_mrd_out _ mc mx x MUb Hbd).
      + exact (munch_mrd_out _ m mc x MU Hbd (flag_out_Wf fra fv spc j nn w120 x HK Hxr Hnj)).
      + cbn [outside]. split; [|split; [|exact I]].
        * clear -Hxr Obfl EFL0 EM1; rewrite EFL0, EM1 in Obfl; lia.
        * clear -Hxr HFSb Pfs0 Hspcr RS; lia.
    - (* the exact writes from m: the frame block's (MUw, Wf2) and the body's (MUb, the box and the window) *)
      exists ob. split; [exact HO|].
      eapply munch_trans.
      + eapply munch_weaken; [|exact MUw]. intros x Hx. unfold Wf2 in *. cbn [app outside] in Hx |- *. clear - Hx; tauto.
      + eapply munch_weaken; [|exact MUb]. intros x Hx. unfold Wf2 in Hx. cbn [app outside] in Hx |- *.
        destruct Hx as (H1 & H2 & H3 & H4 & H5 & H6 & _). split; [exact H6|]. split; [|exact I].
        intros [HL HR]. apply H1. clear -HL HR Hspcr; lia.
  Qed.

  (* The frame bytes [lo, lo + len), read back in the memory the run reached. *)
  Ltac rdb lo len tac :=
    let HIN := fresh "HIN" in
    assert (HIN : forall jx, (jx < len)%nat -> In (lo + jx)%nat (cp_rd n fr)) by tac;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        let R := fresh "RO" in
        assert (R : ro_cells rsegs mcur (f + Z.of_nat lo) (map C1 (map (cp_b fr) (seq lo len))))
          by (eapply ro_mx;
              [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
              | exact HIN | cbn [Nat.add]; lia ]);
        cbn [map seq] in R;
        let z := eval vm_compute in (Z.of_nat lo) in change (Z.of_nat lo) with z in R;
        rewrite ?Z.add_0_r in R
    end;
    clear HIN.

  (* `mv r,s10; beqz s4; mv r,s4` at a join: r holds the box pointer on both paths, continuing at tgt. *)
  Ltac obsel r tgt :=
    lazymatch goal with
    | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm _ ?fcc ?rv ?mm ?ro) =>
        match goal with
        | HOb : OB ?fraq ?obq |- _ =>
            enough (G : forall w : word, w = Z_to_bv 64 obq ->
                          evtF segs rgq Q (MS (bvmap_set r w R) Fm (Z_to_bv 64 tgt) fcc rv mm ro));
            [ step; step; rewrite (rc_eqb_lit o 0) by lia;
              destruct HOb as [(Eo & Eob) | (Eo & Eob)];
              [ rewrite (proj2 (Z.eqb_eq o 0) Eo); cbv iota;
                apply (G (Z_to_bv 64 (fraq + 32)) ltac:(rewrite Eob; reflexivity))
              | rewrite (proj2 (Z.eqb_neq o 0) Eo); cbv iota; step;
                apply (G (Z_to_bv 64 o) ltac:(rewrite Eob; reflexivity)) ]
            | intros w Hw; subst w; simp_regs ]
        end
    end.

  (* the addressable ranges at the memory the run reached *)
  Ltac refresh :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        let A1 := fresh "AFx" in
        assert (A1 : addressable mcur f 50) by (eapply af_mx2; eassumption);
        match goal with
        | HOb : OB _ ?obq |- _ =>
            let A2 := fresh "Aobx" in
            assert (A2 : addressable mcur obq 36) by (eapply ob_mx; eassumption)
        end
    end.

  (* the shadow check of the one-byte load of frame byte i *)
  Ltac chkf i r :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) => try (match goal with HSC : shcov _ f 50 |- _ => move HSC at bottom end);
        let RX := fresh "RX" in let SH := fresh "SH" in
        assert (RX : 0 <= f + i < 2 ^ 64)
          by (match goal with Hb : 0 <= f /\ f + 50 <= 2 ^ 64 |- _ => clear -Hb; lia end);
        pose proof (acl_shadow mcur f 50 i 1 (f + i) ltac:(eassumption) ltac:(clear; lia) ltac:(clear; lia)
                      ltac:(clear; lia)
                      ltac:(let MB := fresh "MB" in
                            pose proof (Z.mod_pos_bound (f + i) 8 ltac:(clear; lia)) as MB; clear -MB; lia)
                      ltac:(clear; lia)) as SH;
        chk_core (f + i) RX r SH pre_sr no_extra
    end.

  (* the shadow check of the four-byte access at the box pointer itself (offset 0: the address register holds ob,
     with no added literal) *)
  Ltac chkb0 r extra :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        match goal with
        | AO : addressable mcur ?obq 36 |- _ => try (match goal with HSC : shcov _ obq 36 |- _ => move HSC at bottom end);
            let RX := fresh "RX" in let SH := fresh "SH" in
            assert (RX : 0 <= obq < 2 ^ 64)
              by (match goal with Hb : 0 <= obq /\ obq + 36 <= 2 ^ 64 |- _ => clear -Hb; lia end);
            pose proof (acl_shadow mcur obq 36 0 4 obq AO ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(apply acl_mod_al0; eassumption) ltac:(clear; lia)) as SH;
            chk_core obq RX r SH pre_sr extra
        end
    end.

  (* the same check where the fast path is the TAKEN branch (`beqz` instead of `bnez`, at 0x83a90) *)
  Ltac chkb0inv r :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        match goal with
        | AO : addressable mcur ?obq 36 |- _ => try (match goal with HSC : shcov _ obq 36 |- _ => move HSC at bottom end);
            let RX := fresh "RX" in let SH := fresh "SH" in
            assert (RX : 0 <= obq < 2 ^ 64)
              by (match goal with Hb : 0 <= obq /\ obq + 36 <= 2 ^ 64 |- _ => clear -Hb; lia end);
            pose proof (acl_shadow mcur obq 36 0 4 obq AO ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(apply acl_mod_al0; eassumption) ltac:(clear; lia)) as SH;
            let kk := fresh "kk" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
            destruct SH as (kk & RK & OK & KR);
            pre_sr obq RX; steps_until_if; clear RK;
            unfold sxb; rewrite (rc_eqb0_signed (bv_signed kk)) by (clear -KR; lia);
            lazymatch goal with
            | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm (if _ then ?B1 else _) ?fcc ?rv ?mm ?ro) =>
                let G := fresh "G" in
                enough (G : forall rr : word, evtF segs rgq Q (MS (bvmap_set r rr R) Fm B1 fcc rv mm ro));
                [ destruct (Z.eqb_spec (bv_signed kk) 0) as [K0|K0]; cbv iota;
                  [ bjoin G r
                  | step; rewrite ?(unsigned_lit obq) by (clear -RX; lia); rewrite rc_land7; add3 obq;
                    step;
                    let MB := fresh "MB" in pose proof (Z.mod_pos_bound obq 8 eq_refl) as MB;
                    rewrite (rc_lts_signed (obq mod 8 + 3) (bv_signed kk)) by (clear -MB KR; lia);
                    replace (obq mod 8 + 3 <? bv_signed kk) with true
                      by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK];
                          [exfalso; exact (K0 OK) | clear -OK; lia]);
                    clear MB; cbv iota; bjoin G r ]
                | intros ?; simp_regs; clear OK KR ]
            end
        end
    end.

  (* `beqz s4; mv r,s4` (0x83c38): r holds the box pointer on both paths *)
  Ltac obsel2 r tgt :=
    lazymatch goal with
    | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm _ ?fcc ?rv ?mm ?ro) =>
        match goal with
        | HOb : OB ?fraq ?obq |- _ =>
            enough (G : forall w : word, w = Z_to_bv 64 obq ->
                          evtF segs rgq Q (MS (bvmap_set r w R) Fm (Z_to_bv 64 tgt) fcc rv mm ro));
            [ step; rewrite (rc_eqb_lit o 0) by lia;
              destruct HOb as [(Eo & Eob) | (Eo & Eob)];
              [ rewrite (proj2 (Z.eqb_eq o 0) Eo); cbv iota;
                apply (G (Z_to_bv 64 (fraq + 32)) ltac:(rewrite Eob; reflexivity))
              | rewrite (proj2 (Z.eqb_neq o 0) Eo); cbv iota; step;
                apply (G (Z_to_bv 64 o) ltac:(rewrite Eob; reflexivity)) ]
            | intros w Hw; subst w; simp_regs ]
        end
    end.

  (* the shadow check of a w-byte access at ob + k *)
  Ltac chkb k w r extra :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        match goal with
        | AO : addressable mcur ?obq 36 |- _ => try (match goal with HSC : shcov _ obq 36 |- _ => move HSC at bottom end);
            let RX := fresh "RX" in let SH := fresh "SH" in
            assert (RX : 0 <= obq + k < 2 ^ 64)
              by (match goal with Hb : 0 <= obq /\ obq + 36 <= 2 ^ 64 |- _ => clear -Hb; lia end);
            pose proof (acl_shadow mcur obq 36 k w (obq + k) AO ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(clear; lia)
                          ltac:(apply (acl_mod_al obq k w); [eassumption | clear; lia | clear; lia])
                          ltac:(clear; lia)) as SH;
            chk_core (obq + k) RX r SH pre_sr extra
        end
    end.

  (* 0x83ac8: the kind is stored into the box (its shadow check was done before the jump), then the exit. *)
  Lemma L_kind : forall fra fv spc j nn w120 mc ob (mx : word -> option byte) k tg amp
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    BJ ob spc mc mx ->
    rw_cells rsegs mx ob [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mx (ob + 4) [CB 24 P1] ->
    rw_cells rsegs mx (ob + 28) [CB 2 tg] -> rw_cells rsegs mx (ob + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG (QE fv)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               (Z_to_bv 64 k) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob)
               x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x83ac8) fc None mx (seg_rom rsegs)).
  Proof. hide_sec.
    intros fra fv spc j nn w120 mc ob mx k tg amp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26
      x28 x29 x30 x31 HK HB HFL HO HBJ HKc HP HTG HAMP Ek Hk EB.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    destruct HBJ as (MUb & WMb & MIx & STx).
    step. step.
    match goal with H : rw_cells rsegs _ ob [C4 _] |- _ => rename H into HKc' end.
    pose proof (rc_rw_join rsegs _ ob (ob + 4) _ _ HKc' ltac:(cbn [cells_size csize app]; lia) HP) as J1.
    pose proof (rc_rw_join rsegs _ ob (ob + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HTG) as J2.
    pose proof (rc_rw_join rsegs _ ob (ob + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HAMP) as J3.
    apply (rc_rw_flat rsegs _ ob _ (snd (ctrlparse n fr))) in J3.
    - rewrite ctrlparse_length in J3. rewrite <- Ek.
      eapply (L_join fra fv spc j nn w120 mc ob);
        [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx
        | exact J3 ].
    - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      rewrite !app_nil_r. cbn [app]. reflexivity.
  Qed.

  (* 0x83ca8: the stored kind is checked, read back, and the run exits. *)
  Lemma L_be0 : forall fra fv spc j nn w120 mc ob (mx : word -> option byte) k tg amp
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    BJ ob spc mc mx -> addressable mc ob 36 ->
    rw_cells rsegs mx ob [C4 (Z_to_bv 64 k)] -> rw_cells rsegs mx (ob + 4) [CB 24 P1] ->
    rw_cells rsegs mx (ob + 28) [CB 2 tg] -> rw_cells rsegs mx (ob + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG (QE fv)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob)
               x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x83ca8) fc None mx (seg_rom rsegs)).
  Proof. hide_sec.
    intros fra fv spc j nn w120 mc ob mx k tg amp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22
      x26 x28 x29 x30 x31 HK HB HFL HO HBJ Aob HKc' HP HTG HAMP Ek Hk EB.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof MU as MUw. apply (munch_weaken _ _ _ _ (Wf2_sub fra j nn)) in MU.
    destruct HBJ as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO) as (Ob0 & Ob64 & Obmod & _).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        assert (Aobx : addressable mcur ob 36) by (eapply ob_mx; eassumption)
    end.
    chkb0 (Z_to_bv 5 11) add3.
    step. rewrite (rcp_sx32 k) by (clear -Hk; lia).
    step.
    pose proof (rc_rw_join rsegs _ ob (ob + 4) _ _ HKc' ltac:(cbn [cells_size csize app]; lia) HP) as J1.
    pose proof (rc_rw_join rsegs _ ob (ob + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HTG) as J2.
    pose proof (rc_rw_join rsegs _ ob (ob + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HAMP) as J3.
    apply (rc_rw_flat rsegs _ ob _ (snd (ctrlparse n fr))) in J3.
    - rewrite ctrlparse_length in J3. rewrite <- Ek.
      eapply (L_join fra fv spc j nn w120 mc ob);
        [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx
        | exact J3 ].
    - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      rewrite !app_nil_r. cbn [app]. reflexivity.
  Qed.

  (* 0x83ca4: the kind is stored into the box, checked, read back, then the exit. *)
  Lemma L_bdc : forall fra fv spc j nn w120 mc ob (mx : word -> option byte) k tg amp
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    BJ ob spc mc mx -> addressable mc ob 36 ->
    rw_cells rsegs mx ob [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mx (ob + 4) [CB 24 P1] ->
    rw_cells rsegs mx (ob + 28) [CB 2 tg] -> rw_cells rsegs mx (ob + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG (QE fv)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               (Z_to_bv 64 k) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob)
               x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x83ca4) fc None mx (seg_rom rsegs)).
  Proof. hide_sec.
    intros fra fv spc j nn w120 mc ob mx k tg amp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26
      x28 x29 x30 x31 HK HB HFL HO HBJ Aob HKc HP HTG HAMP Ek Hk EB.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof MU as MUw. apply (munch_weaken _ _ _ _ (Wf2_sub fra j nn)) in MU.
    pose proof HBJ as HBJ'. destruct HBJ' as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO) as (Ob0 & Ob64 & Obmod & _).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    step.
    match goal with H : rw_cells rsegs _ ob [C4 _] |- _ => rename H into HK4 end.
    eapply (L_be0 fra fv spc j nn w120 mc ob _ k tg amp);
      [ exact HK | exact HB | exact HFL | exact HO
      | refine (conj _ (conj _ (conj _ _))); eassumption
      | exact Aob | exact HK4 | eassumption | eassumption | eassumption
      | exact Ek | exact Hk | exact EB ].
  Qed.

  (* the plain proof's condition normaliser and branch splitter (lib/Prog/reac_ctrl_parse.v) *)
  Ltac cond_norm :=
    rewrite ?rc_lor0;
    rewrite ?rc_eqb_zxb by (clear; lia);
    repeat match goal with
    | |- context [bv_unsigned (cp_b fr ?i)] => change (bv_unsigned (cp_b fr i)) with (cp_v fr i)
    end.

  Ltac br :=
    cond_norm;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if negb (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
    | |- evtF _ _ _ (MS _ _ (if (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
    end.

  (* walk the kind dispatch, stopping at every leaf (each leaf checks the box before it stores the kind) *)
  Ltac drive :=
    repeat (lazymatch goal with
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539172) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539212) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539276) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539316) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539344) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539368) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539744) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539768) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539792) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => br
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
            end).

  (* the kind and the box bytes of a leaf (kfact / bfact of the plain proof) *)
  Ltac kfact :=
    match goal with HE0 : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE0 end; cbn [fst];
    unfold cp_kind, cp_type, cp_amp; zeval; reflexivity.
  Ltac bfact :=
    match goal with HE0 : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE0 end; cbn [snd];
    unfold cp_struct, cp_rec, cp_kind, cp_type, cp_amp, reac_ctrl_parseF.ParseFOn.P1; zeval; zeval; reflexivity.

  Ltac leafk :=
    eapply L_kind;
    first [ eassumption
          | refine (conj _ (conj _ (conj _ _))); eassumption
          | clear; lia
          | match goal with KR0 : 2 <= KL1 ?x <= 13 /\ _ |- _ => clear -KR0; lia end
          | kfact
          | bfact ].
  Ltac leafb :=
    eapply L_bdc;
    first [ eassumption
          | refine (conj _ (conj _ (conj _ _))); eassumption
          | clear; lia
          | match goal with KR0 : 2 <= KL1 ?x <= 13 /\ _ |- _ => clear -KR0; lia end
          | kfact
          | bfact ].

  (* after the two tag bytes are stored, the box's [ob + 28] cell is a C2: flatten it back to the two
     bytes cp_struct names, so that a leaf below the record can still apply L_kind / L_bdc *)
  Ltac flat_tg :=
    match goal with
    | HOb : OB _ ?obq |- _ =>
        match goal with
        | Hq : rw_cells rsegs _ (obq + 28) [C2 _] |- _ =>
            apply (rc_rw_flat rsegs _ (obq + 28) _ [cp_b fr 35; cp_b fr 34]) in Hq;
            [ cbn [length] in Hq
            | first [ cbn [cells_bytes cbytes]; rewrite rc_le2_pack; reflexivity
                    | cbn [cells_bytes cbytes app]; rewrite rc_le2_pack; reflexivity
                    | vm_compute; reflexivity ] ]
        end
    end.

  Ltac leaves :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539172) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafk
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539212) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafk
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539316) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; leafk
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539344) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafb
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539744) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafb
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539768) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; step; leafb
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 539792) _ _ _ _) => refresh; chkb0 (Z_to_bv 5 11) add3; step; leafb
    end.

  (* 0x8370c .. 0x8375c: the two copies into the box, the broadcast comparison and its 4-byte store. *)
  Lemma body_copy : 50 <= n -> cp_hdr n fr = true ->
    forall fra fv spc j nn w120 mc ob (mx : word -> option byte)
      (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    addressable mc ob 36 -> asan_cells mc -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc ->
    BJ ob spc mc mx -> rw_cells rsegs mx ob [CB 36 (repeat cp_z 36)] ->
    evtF rsegs RNG (QE fv)
      (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 ob) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8370c) fc None mx (seg_rom rsegs)).
  Proof. hide_sec.
    intros Hn50 HE fra fv spc j nn w120 mc ob mx rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB HFL HO Aob ACc SRc HBJ RWx.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof (RINF Hn50) as RGINF. pose proof (SCF Hn50) as SCINF. pose proof (SKF Hn50) as SKINF.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof MU as MUw. apply (munch_weaken _ _ _ _ (Wf2_sub fra j nn)) in MU.
    pose proof HBJ as HBJ'. destruct HBJ' as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    destruct (f_facts Hn50 fra fv spc j nn w120 ob HK HO) as (Hf0 & Hf64 & Fapp & AFm & DFf).
    destruct (HF Hn50) as (_ & _ & HfS).
    pose proof (Obf Hn50) as Hobf.
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc; clear -HAlo HAhi; lia).
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -Hspcr RS; lia).
    assert (Rob : 0 <= ob < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rfb : 0 <= f /\ f + 50 <= 2 ^ 64) by (clear -Hf0 Hf64; lia).
    assert (Rob10 : 0 <= ob + 10 < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rob4 : 0 <= ob + 4 < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rf6 : 0 <= f + 6 < 2 ^ 64) by (clear -Hf0 Hf64; lia).
    assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
    assert (STsp : stk rsegs mx (S - 8800) spc)
      by (apply (stk_sub mx (S - 8800) S (S - 8800) spc STx); clear -Hspcr RS; lia).
    destruct (body_rt fra fv spc j nn w120 ob mc mx HK HO Aob ACc SRc MUb WMb) as (ACx & SRx).
    pose proof (ob_mx fra fv spc j nn w120 ob mc mx HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc mx HK HO MU Aob MUb) as AFx.
    rdb 0%nat 23%nat ltac:(intros jx Hjx; apply cp_rd_e; [exact HE | lia]).
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 0 6 RO ltac:(cbn; lia)) as BD0.
    cbn [map seq firstn skipn] in BD0. rewrite Z.add_0_r in BD0.
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 6 6 RO ltac:(cbn; lia)) as BD1.
    cbn [map seq firstn skipn] in BD1. change (Z.of_nat 6) with 6 in BD1.
    clear RO.
    (* the pieces of the box the body writes *)
    destruct (rc_rw_cut_at rsegs _ ob cp_z 36 4 (ob + 4) RWx ltac:(lia) ltac:(lia)) as [HKc HZ1];
      cbn [Nat.sub] in HZ1.
    destruct (rc_rw_cut_at rsegs _ (ob + 4) cp_z 32 6 (ob + 10) HZ1 ltac:(lia) ltac:(lia)) as [HSRC HZ2];
      cbn [Nat.sub] in HZ2.
    destruct (rc_rw_cut_at rsegs _ (ob + 10) cp_z 26 6 (ob + 16) HZ2 ltac:(lia) ltac:(lia)) as [HDST HZ3];
      cbn [Nat.sub] in HZ3.
    destruct (rc_rw_cut_at rsegs _ (ob + 16) cp_z 20 12 (ob + 28) HZ3 ltac:(lia) ltac:(lia)) as [HMID HZ4];
      cbn [Nat.sub] in HZ4.
    destruct (rc_rw_cut_at rsegs _ (ob + 28) cp_z 8 2 (ob + 30) HZ4 ltac:(lia) ltac:(lia)) as [HTG HAMP];
      cbn [Nat.sub] in HAMP.
    clear HZ1 HZ2 HZ3 HZ4 RWx.
    pose proof HMCPY as HMC. unfold asan_memcpy_contract_F_on, ASAN_MEMCPY_K in HMC. cbv zeta in HMC.
    unfold rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HMC.
    (* 0x8370c: __asan_memcpy(ob + 10, f, 6) *)
    do 4 step.
    eapply evtF_cut.
    { eapply HMC with (src := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5])
                      (junk := repeat cp_z 6) (lo := S - 8800);
        rewrite ?(unsigned_lit (ob + 10) Rob10), ?(unsigned_lit f Rf), ?U6, ?(unsigned_lit spc Rspc).
      - exact BD0.
      - reflexivity.
      - change (Z.to_nat 6) with 6%nat. exact HDST.
      - clear -Hobf; lia.
      - clear; lia.
      - apply (acl_addr_sub mx f 50 f 6 AFx); clear; lia.
      - apply (acl_addr_sub mx ob 36 (ob + 10) 6 Aobx); clear; lia.
      - right. apply (acl_app_in mx f 50 6 AFx); clear; lia.
      - right. replace (ob + 10 + 6) with (ob + 16) by lia. apply (acl_app_in mx ob 36 16 Aobx); clear; lia.
      - right. split; [ apply (acl_app_in mx f 50 7 AFx); clear; lia
                      | replace (ob + 10 + 7) with (ob + 17) by lia;
                        apply (acl_app_in mx ob 36 17 Aobx); clear; lia ].
      - clear -Obrt; lia.
      - clear -Obsp; lia.
      - clear -HfS Hspcr RS; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact ACx.
      - apply (srw_memcpy fra fv spc j nn w120 ob mx _ _ _ 10 0 HK HO Hn50);
          [ rewrite ?(unsigned_lit (ob + 10) Rob10), ?(unsigned_lit f Rf), ?U6; lia .. | exact SRx ].
      - exact MIx.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* __asan_memcpy's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the destination bytes in the box *) eapply rng_sub; [exact RGOB | clear; lia | clear; lia].
      - (* the source bytes in the input *) eapply rng_sub; [exact RGINF | clear; lia | clear; lia].
      - (* the destination's aligned shadow word cover *) right. unfold shadow_addr. apply SKOB; clear; lia.
      - (* the source's aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; clear; lia.
      - (* the shadow of __asan_memcpy's window *)
        right. unfold shadow_addr. apply rngF_win_sh8; clear -Hspcr RS; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 &
                       Hms & MU1 & WM1 & MI1 & ST1 & RW1 & BS1 & AC1 & SR1).
    subst ms'.
    pose proof (SR1 _ SRx) as SR1p.
    rewrite (ret_pc_even 538396 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit _ Rob10), U6, (unsigned_lit spc Rspc) in MU1.
    rewrite (unsigned_lit _ Rob10), U6 in RW1.
    rewrite (unsigned_lit _ Rf) in BS1.
    rewrite (unsigned_lit spc Rspc) in ST1.
    unfold ASAN_MEMCPY_K in MU1. change (Z.to_nat 6) with 6%nat in RW1.
    pose proof (bj_call ob spc mc mx m1 (ob + 10) 6 2224 _ HBJ MU1 WM1 MI1 ST1 RW1
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Hspcr RS; lia) ltac:(clear -Hspcr RS; lia)) as HBJ1.
    pose proof (rw_cells_transport rsegs _ mx m1 ob [CB 4 (repeat cp_z 4)] HKc MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HKc1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 4) [CB 6 (repeat cp_z 6)] HSRC MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HSRC1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 16) [CB 12 (repeat cp_z 12)] HMID MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HMID1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 28) [CB 2 (repeat cp_z 2)] HTG MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HTG1.
    pose proof (rw_cells_transport rsegs _ mx m1 (ob + 30) [CB 6 (repeat cp_z 6)] HAMP MU1 WM1
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HAMP1.
    pose proof (bytes_at_transport rsegs _ mx m1 (f + 6) [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9;
                                                          cp_b fr 10; cp_b fr 11] BD1 MU1
                  ltac:(cbn [disjoint_from length]; clear -Hobf Hf0 Hf64 HfS Hspcr RS; lia)) as BD1a.
    clear HKc HSRC HMID HTG HAMP BD0 BD1 MU1 WM1 MI1 ST1 HBJ MUb WMb MIx STx STsp ACx SRx Aobx AFx.
    pose proof HBJ1 as HBJ1'. destruct HBJ1' as (MUb & WMb & MIx & STx).
    assert (STsp : stk rsegs m1 (S - 8800) spc)
      by (apply (stk_sub m1 (S - 8800) S (S - 8800) spc STx); clear -Hspcr RS; lia).
    pose proof (ob_mx fra fv spc j nn w120 ob mc m1 HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc m1 HK HO MU Aob MUb) as AFx.
    (* 0x8371c: __asan_memcpy(ob + 4, f + 6, 6) *)
    do 4 step.
    eapply evtF_cut.
    { eapply HMC with (src := [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11])
                      (junk := repeat cp_z 6) (lo := S - 8800);
        rewrite ?(unsigned_lit (ob + 4) Rob4), ?(unsigned_lit (f + 6) Rf6), ?U6, ?(unsigned_lit spc Rspc).
      - exact BD1a.
      - reflexivity.
      - change (Z.to_nat 6) with 6%nat. exact HSRC1.
      - clear -Hobf; lia.
      - clear; lia.
      - apply (acl_addr_sub m1 f 50 (f + 6) 6 AFx); clear; lia.
      - apply (acl_addr_sub m1 ob 36 (ob + 4) 6 Aobx); clear; lia.
      - right. replace (f + 6 + 6) with (f + 12) by lia. apply (acl_app_in m1 f 50 12 AFx); clear; lia.
      - right. replace (ob + 4 + 6) with (ob + 10) by lia. apply (acl_app_in m1 ob 36 10 Aobx); clear; lia.
      - right. split; [ replace (f + 6 + 7) with (f + 13) by lia; apply (acl_app_in m1 f 50 13 AFx); clear; lia
                      | replace (ob + 4 + 7) with (ob + 11) by lia;
                        apply (acl_app_in m1 ob 36 11 Aobx); clear; lia ].
      - clear -Obrt; lia.
      - clear -Obsp; lia.
      - clear -HfS Hspcr RS; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact AC1.
      - apply (srw_memcpy fra fv spc j nn w120 ob m1 _ _ _ 4 6 HK HO Hn50);
          [ rewrite ?(unsigned_lit (ob + 4) Rob4), ?(unsigned_lit (f + 6) Rf6), ?U6; lia .. | exact SR1p ].
      - exact MIx.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* __asan_memcpy's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the destination bytes in the box *) eapply rng_sub; [exact RGOB | clear; lia | clear; lia].
      - (* the source bytes in the input *) eapply rng_sub; [exact RGINF | clear; lia | clear; lia].
      - (* the destination's aligned shadow word cover *) right. unfold shadow_addr. apply SKOB; clear; lia.
      - (* the source's aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; clear; lia.
      - (* the shadow of __asan_memcpy's window *)
        right. unfold shadow_addr. apply rngF_win_sh8; clear -Hspcr RS; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 &
                       Hms & MU2 & WM2 & MI2 & ST2 & RW2 & BS2 & AC2 & SR2).
    subst ms'.
    pose proof (SR2 _ SR1p) as SR2p.
    rewrite (ret_pc_even 538412 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit _ Rob4), U6, (unsigned_lit spc Rspc) in MU2.
    rewrite (unsigned_lit _ Rob4), U6 in RW2.
    rewrite (unsigned_lit _ Rf6) in BS2.
    rewrite (unsigned_lit spc Rspc) in ST2.
    unfold ASAN_MEMCPY_K in MU2. change (Z.to_nat 6) with 6%nat in RW2.
    pose proof (bj_call ob spc mc m1 m2 (ob + 4) 6 2224 _ HBJ1 MU2 WM2 MI2 ST2 RW2
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Hspcr RS; lia) ltac:(clear -Hspcr RS; lia)) as HBJ2.
    pose proof (rw_cells_transport rsegs _ m1 m2 ob [CB 4 (repeat cp_z 4)] HKc1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HKc2.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 10) [CB 6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3;
                                                                 cp_b fr 4; cp_b fr 5]] RW1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as RW1b.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 16) [CB 12 (repeat cp_z 12)] HMID1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HMID2.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 28) [CB 2 (repeat cp_z 2)] HTG1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HTG2.
    pose proof (rw_cells_transport rsegs _ m1 m2 (ob + 30) [CB 6 (repeat cp_z 6)] HAMP1 MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HAMP2.
    clear HKc1 HSRC1 HMID1 HTG1 HAMP1 RW1 BD1a MU2 WM2 MI2 ST2 HBJ1 MUb WMb MIx STx STsp Aobx AFx
      AC1 SR1 SR1p.
    pose proof HBJ2 as HBJ2'. destruct HBJ2' as (MUb & WMb & MIx & STx).
    assert (STsp : stk rsegs m2 (S - 8800) spc)
      by (apply (stk_sub m2 (S - 8800) S (S - 8800) spc STx); clear -Hspcr RS; lia).
    pose proof (ob_mx fra fv spc j nn w120 ob mc m2 HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc m2 HK HO MU Aob MUb) as AFx.
    (* 0x8372c .. 0x8373c: the bcmp wrapper on the 6 bytes at f and the 6 bytes of .str.4 *)
    destruct (cl_mx2 fra fv spc j nn w120 ob mc m2 HK HO MU MUb) as (CLa & CLb & CLc & CLd & CLe).
    pose proof (abc_mx2 fra fv spc j nn w120 ob mc m2 HK HO MU Aob MUb) as ABCx.
    rdb 0%nat 23%nat ltac:(intros jx Hjx; apply cp_rd_e; [exact HE | lia]).
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 0 6 RO ltac:(cbn; lia)) as BD0c.
    cbn [map seq firstn skipn] in BD0c. rewrite Z.add_0_r in BD0c.
    clear RO.
    destruct (rc_memcmp_ff (cp_b fr 0) (cp_b fr 1) (cp_b fr 2) (cp_b fr 3) (cp_b fr 4) (cp_b fr 5))
      as (v & Hv & Hvr & Hvb).
    pose proof HBCMPW as HBW. unfold bcmp_wrap_contract_F_on, BCMP_WRAP_K in HBW. cbv zeta in HBW.
    assert (UBC : bv_unsigned (Z_to_bv 64 135680) = 135680) by reflexivity.
    do 5 step.
    eapply evtF_cut.
    { eapply HBW with (ls := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5])
                      (rs := repeat (Z_to_bv 8 255) 6) (v := v) (lo := S - 8800);
        rewrite ?(unsigned_lit f Rf), ?U6, ?(unsigned_lit spc Rspc), ?UBC.
      - exact BD0c.
      - apply (rc_ro_in_image rsegs _ _ (repeat (Z_to_bv 8 255) 6)); [exact MIx | vm_compute; reflexivity].
      - exact Hv.
      - exact MIx.
      - clear; lia.
      - apply (acl_addr_sub m2 f 50 f 6 AFx); clear; lia.
      - exact ABCx.
      - right. apply (acl_app_in m2 f 50 6 AFx); clear; lia.
      - right. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; clear; lia.
      - right. apply (acl_app_in m2 f 50 7 AFx); clear; lia.
      - right. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; clear; lia.
      - clear -HfS Hspcr RS; lia.
      - left. pose proof HHM as HH0. unfold HIGHMEM_BEG in HH0. clear -HH0 Hspcr RS; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact AC2.
      - exact (srw_bcmp m2 Hn50 SR2p).
      - exact CLa.
      - exact CLb.
      - exact CLc.
      - exact CLd.
      - exact CLe.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) exact RIMG.
      - (* the bcmp wrapper's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the 6 input bytes *) eapply rng_sub; [exact RGINF | clear; lia | clear; lia].
      - (* their aligned shadow word cover *) right. apply (rcpF_kov8 RNG f 50 _ _ SKINF); clear; lia.
      - (* the 6 bytes at .str.4 *) exact RBC.
      - (* their aligned shadow word cover *)
        right. apply (rcpF_kov8 RNG REAC_CTRL_PARSE_BC 6 _ _ SKBC); unfold REAC_CTRL_PARSE_BC; clear; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 &
                       Hms & MU3 & WM3 & MI3 & ST3 & AC3 & SR3 & BSl & BSr).
    subst ms'.
    rewrite (ret_pc_even 538432 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit spc Rspc) in MU3. rewrite (unsigned_lit spc Rspc) in ST3.
    unfold BCMP_WRAP_K in MU3.
    pose proof (bj_call0 ob spc mc m2 m3 4560 HBJ2 MU3 WM3 MI3 ST3
                  ltac:(clear; lia) ltac:(clear -Hspcr RS; lia) ltac:(clear -Hspcr RS; lia)) as HBJ3.
    pose proof (rw_cells_transport rsegs _ m2 m3 ob [CB 4 (repeat cp_z 4)] HKc2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HKc3.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 4) [CB 6 [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9;
                                                                cp_b fr 10; cp_b fr 11]] RW2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as RW2b.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 10) [CB 6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3;
                                                                 cp_b fr 4; cp_b fr 5]] RW1b MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as RW1c.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 16) [CB 12 (repeat cp_z 12)] HMID2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HMID3.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 28) [CB 2 (repeat cp_z 2)] HTG2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HTG3.
    pose proof (rw_cells_transport rsegs _ m2 m3 (ob + 30) [CB 6 (repeat cp_z 6)] HAMP2 MU3 WM3
                  ltac:(cbn [disjoint_from cells_size csize]; clear -Obsp Ob0 Ob64 Hspcr RS; lia)) as HAMP3.
    clear HKc2 RW2 RW1b HMID2 HTG2 HAMP2 BD0c MU3 WM3 MI3 ST3 HBJ2 MUb WMb MIx STx STsp Aobx AFx
      AC2 SR2 SR2p BSl BSr ABCx CLa CLb CLc CLd CLe.
    pose proof HBJ3 as HBJ3'. destruct HBJ3' as (MUb & WMb & MIx & STx).
    pose proof (ob_mx fra fv spc j nn w120 ob mc m3 HK HO MUb Aob) as Aobx.
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc m3 HK HO MU Aob MUb) as AFx.
    (* 0x83740 .. 0x83758: the 4-byte store of the broadcast flag at ob + 16, checked *)
    step.
    assert (RX16 : 0 <= ob + 16 < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    pose proof (acl_shadow m3 ob 36 16 4 (ob + 16) Aobx ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(clear -Obmod; Z.div_mod_to_equations; lia) ltac:(clear; lia)) as SH16.
    move SCOB at bottom. chk_core (ob + 16) RX16 (Z_to_bv 5 13) SH16 pre_sr add3.
    move HMID3 at bottom. step. step.
    (* 0x8375c .. 0x83900: the frame's fields, each load and each store behind its shadow check *)
    rdb 0%nat 23%nat ltac:(intros jx Hjx; apply cp_rd_e; [exact HE | lia]).
    refresh.
    step.                                      (* 0x8375c addi a0,s5,14 *)
    chkf 14%Z (Z_to_bv 5 12).
    step.                                      (* 0x83770 addi a0,s5,15 *)
    chkf 15%Z (Z_to_bv 5 13).
    obsel (Z_to_bv 5 11) 538516.               (* 0x83788 .. 0x83794: a1 = ob *)
    step.                                      (* 0x83794 addi a1,a1,20 *)
    chkb 20%Z 2%Z (Z_to_bv 5 14) add1.
    do 4 step.                                 (* slli, or, addi a0,s5,18, sh a2,0(a1) *)
    refresh.
    chkf 18%Z (Z_to_bv 5 12).
    obsel (Z_to_bv 5 11) 538584.               (* 0x837cc .. 0x837d8 *)
    step.                                      (* 0x837d8 addi a1,a1,22 *)
    chkb 22%Z 1%Z (Z_to_bv 5 10) no_extra.
    do 2 step.                                 (* sb a2,0(a1), addi a0,s5,19 *)
    refresh.
    chkf 19%Z (Z_to_bv 5 13).
    obsel (Z_to_bv 5 11) 538644.               (* 0x83808 .. 0x83814 *)
    step.                                      (* 0x83814 addi a1,a1,23 *)
    chkb 23%Z 1%Z (Z_to_bv 5 10) no_extra.
    do 2 step.                                 (* sb a3,0(a1), addi a0,s5,20 *)
    refresh.
    chkf 20%Z (Z_to_bv 5 14).
    step.                                      (* 0x83844 addi a0,s5,21 *)
    chkf 21%Z (Z_to_bv 5 15).
    obsel (Z_to_bv 5 11) 538728.               (* 0x8385c .. 0x83868 *)
    step.                                      (* 0x83868 addi a1,a1,24 *)
    chkb 24%Z 2%Z (Z_to_bv 5 16) add1.
    do 4 step.                                 (* slli, or, addi a0,s5,22, sh a4,0(a1) *)
    refresh.
    chkf 22%Z (Z_to_bv 5 14).
    obsel (Z_to_bv 5 11) 538796.               (* 0x838a0 .. 0x838ac *)
    step.                                      (* 0x838ac addi a1,a1,26 *)
    chkb 26%Z 1%Z (Z_to_bv 5 15) no_extra.
    do 2 step.                                 (* sb a0,0(a1), addi a1,s5,16 *)
    refresh.
    chkf 16%Z (Z_to_bv 5 15).
    step.                                      (* 0x838dc addi a1,s5,17 *)
    chkf 17%Z (Z_to_bv 5 16).
    do 3 step.                                 (* lbu a1, zext.b, or a5,a4,a1 *)
    (* 0x83900: (fr[16] | fr[17]) = 0 is the filler, kind 1; else the kind dispatch at 0x83a14 *)
    rewrite ?rc_zextb.
    step.
    rewrite rc_lor0.
    change (bv_unsigned (cp_b fr 16)) with (cp_v fr 16).
    change (bv_unsigned (cp_b fr 17)) with (cp_v fr 17).
    match goal with H : rw_cells rsegs _ (ob + 4) [CB 6 _] |- _ => rename H into HSRCf end.
    match goal with H : rw_cells rsegs _ (ob + 10) [CB 6 _] |- _ => rename H into HDSTf end.
    match goal with H : rw_cells rsegs _ (ob + 16) _ |- _ => rename H into HMIDf end.
    pose proof (rc_rw_join rsegs _ (ob + 4) (ob + 10) _ _ HSRCf
                  ltac:(cbn [cells_size csize app]; lia) HDSTf) as J1.
    pose proof (rc_rw_join rsegs _ (ob + 4) (ob + 16) _ _ J1
                  ltac:(cbn [cells_size csize app]; lia) HMIDf) as J2.
    apply (rc_rw_flat rsegs _ (ob + 4) _ P1) in J2.
    2:{ cbn [app cells_bytes cbytes]. rewrite rc_le4_seqz by lia. rewrite !rc_le2_pack. rewrite Hvb.
        cbn [skipn repeat app]. unfold reac_ctrl_parseF.ParseFOn.P1. reflexivity. }
    change (length P1) with 24%nat in J2.
    destruct ((cp_v fr 16 =? 0) && (cp_v fr 17 =? 0)) eqn:T0; cbn [negb]; cbv iota.
    { idtac "F0".
      (* the filler: 0x83904 the 4-byte check at the box, 0x83914 li a0,1, 0x83918 -> 0x83ac8 *)
    rewrite andb_true_iff, !Z.eqb_eq in T0. destruct T0 as [T0a T0b].
    refresh. idtac "F1".
    chkb0 (Z_to_bv 5 11) add3. idtac "F2".
    step. step. idtac "F3".
    assert (EK1 : cp_kind fr = 1)
      by (unfold cp_kind, cp_type; rewrite T0a, T0b; cbn [Z.eqb andb Pos.eqb]; reflexivity).
    assert (ERC : cp_rec fr = false)
      by (unfold cp_rec, cp_type; rewrite T0a; cbn [Z.eqb andb Pos.eqb]; reflexivity).
    match goal with H : rw_cells rsegs _ ob [CB 4 _] |- _ => rename H into HKf end.
    match goal with H : rw_cells rsegs _ (ob + 28) [CB 2 _] |- _ => rename H into HTGf end.
    match goal with H : rw_cells rsegs _ (ob + 30) [CB 6 _] |- _ => rename H into HAMPf end.
    eapply (L_kind fra fv spc j nn w120 mc ob _ 1 (repeat cp_z 2) (repeat cp_z 6));
      [ exact HK | exact HB | exact HFL | exact HO
      | refine (conj MUb (conj WMb (conj MIx STx)))
      | exact HKf | exact J2 | exact HTGf | exact HAMPf
      | unfold ctrlparse; rewrite HE; cbn [fst]; exact EK1
      | clear; lia
      | unfold ctrlparse; rewrite HE; cbn [snd]; unfold cp_struct; rewrite EK1, ERC;
        cbn [Z.eqb Pos.eqb repeat app]; unfold reac_ctrl_parseF.ParseFOn.P1; reflexivity ]. }
    (* 0x83a14 ..: the kind dispatch *)
    pose proof (cp_v_range fr 16) as R16. pose proof (cp_v_range fr 17) as R17.
    pose proof (cp_v_range fr 18) as R18. pose proof (cp_v_range fr 19) as R19.
    pose proof (cp_v_range fr 22) as R22. pose proof (KL1_range (cp_v fr 22)) as KR.
    assert (KL6 : KL1 (cp_v fr 22) <> 6) by (clear -KR; lia).
    (* the dispatch does no more calls: drop the disjunctive premises, they make every store's
       transport (slia) split the context *)
    clear DFf Fapp Obrt Obsp Obsv Obfr Obcf Obf HfS AFm.
    drive.
    all: try leaves.
    (* goal 2: 0x83a8c, kind_of_link1 *)
    2:{ step.
        eapply evtF_cut; [eapply HKOL | intros ? [? ->]].
        rewrite rc_signed_zxb.
        change (bv_unsigned (cp_b fr 22)) with (cp_v fr 22).
        rewrite (ret_pc_even 539280 ltac:(clear; lia) ltac:(clear; lia)).
        refresh.
        chkb0inv (Z_to_bv 5 12).
        leafb. }
    (* goal 1: 0x83ae8, the record: fr[19] = 3, the two tag bytes, then the amp test *)
    step. step. cond_norm.
    destruct (Z.eqb_spec (cp_v fr 19) 3) as [E19|E19]; cbn [negb]; cbv iota.
    2:{ drive. all: leaves. }
    assert (HRC : cp_rec fr = true) by (unfold cp_rec, cp_type; zeval; reflexivity).
    rdb 34%nat 2%nat ltac:(intros jx Hjx; apply cp_rd_rec; [exact HE | exact HRC | lia]).
    rdb 32%nat 1%nat ltac:(intros jx Hjx; replace (32 + jx)%nat with 32%nat by lia;
                           apply cp_rd_rec; [exact HE | exact HRC | lia]).
    refresh.
    step. chkf 34%Z (Z_to_bv 5 12).
    step. chkf 35%Z (Z_to_bv 5 13).
    obsel (Z_to_bv 5 11) 539432.
    step. chkb 28%Z 2%Z (Z_to_bv 5 14) add1.
    try (match goal with H : rw_cells rsegs _ (ob + 28) _ |- _ => move H at bottom end). do 4 step.
    refresh.
    chkf 32%Z (Z_to_bv 5 13).
    do 3 step. cond_norm.
    destruct (Z.eqb_spec (cp_v fr 32) 18) as [E32|E32]; cbn [negb]; cbv iota.
    2:{ flat_tg. drive. all: leaves. }
    rdb 33%nat 1%nat ltac:(intros jx Hjx; replace (33 + jx)%nat with 33%nat by lia;
                           apply cp_rd_33; [exact HE | exact HRC | exact E32]).
    step. chkf 33%Z (Z_to_bv 5 13).
    do 3 step. cond_norm.
    destruct (Z.eqb_spec (cp_v fr 33) 18) as [E33|E33]; cbn [negb]; cbv iota.
    2:{ flat_tg. drive. all: leaves. }
    do 2 step.
    rewrite rc_pack_eqb by (clear; lia).
    change (bv_unsigned (cp_b fr 34)) with (cp_v fr 34).
    change (bv_unsigned (cp_b fr 35)) with (cp_v fr 35).
    destruct (Z.eqb_spec (cp_v fr 34 * 256 + cp_v fr 35) 257) as [EP|EP]; cbn [negb]; cbv iota.
    2:{ flat_tg.
        destruct (Z.eqb_spec (cp_v fr 34) 1) as [E34a|E34a];
          [ assert (E35a : cp_v fr 35 <> 1)
              by (pose proof (cp_v_range fr 34) as A34; pose proof (cp_v_range fr 35) as A35;
                  clear -A34 A35 EP E34a; lia)
          | ];
          drive; leaves. }
    assert (E34 : cp_v fr 34 = 1)
      by (pose proof (cp_v_range fr 34) as A34; pose proof (cp_v_range fr 35) as A35;
          clear -A34 A35 EP; lia).
    assert (E35 : cp_v fr 35 = 1)
      by (pose proof (cp_v_range fr 34) as A34; pose proof (cp_v_range fr 35) as A35;
          clear -A34 A35 EP; lia).
    refresh. chkb0 (Z_to_bv 5 11) add3.
    try (match goal with H : rw_cells rsegs _ ob _ |- _ => move H at bottom end). do 3 step.
    assert (EK6 : cp_kind fr = 6) by (unfold cp_kind, cp_type, cp_amp; zeval; reflexivity).
    rdb 36%nat 3%nat ltac:(intros jx Hjx; apply cp_rd_amp; [exact HE | exact HRC | exact EK6 | lia]).
    refresh.
    chkf 36%Z (Z_to_bv 5 12).
    obsel (Z_to_bv 5 11) 539596.
    step. chkb 30%Z 1%Z (Z_to_bv 5 13) no_extra.
    do 2 step.
    refresh.
    chkf 37%Z (Z_to_bv 5 12).
    obsel (Z_to_bv 5 11) 539656.
    step. chkb 31%Z 1%Z (Z_to_bv 5 13) no_extra.
    do 2 step.
    refresh.
    chkf 38%Z (Z_to_bv 5 12).
    obsel2 (Z_to_bv 5 26) 539712.
    step. chkb 32%Z 1%Z (Z_to_bv 5 13) no_extra.
    do 2 step.
    flat_tg.
    match goal with
    | HOb : OB ?fraq ?obq |- _ =>
        match goal with Hq : rw_cells rsegs _ (obq + 30) _ |- _ => rename Hq into HAMPr end;
        apply (rc_rw_flat rsegs _ (obq + 30) _
                 ([cp_b fr 36; cp_b fr 37; cp_b fr 38] ++ repeat cp_z 3)) in HAMPr;
        [ cbn [length app repeat] in HAMPr
        | first [ reflexivity
                | cbn [cells_bytes cbytes app repeat skipn firstn]; reflexivity
                | vm_compute; reflexivity ] ];
        eapply (L_be0 fraq _ _ _ _ _ _ obq _ 6 [cp_b fr 35; cp_b fr 34]
                      ([cp_b fr 36; cp_b fr 37; cp_b fr 38] ++ repeat cp_z 3))
    end;
    first [ eassumption
          | refine (conj _ (conj _ (conj _ _))); eassumption
          | clear; lia
          | kfact
          | bfact ].
  Qed.


  (* 0x836c0 .. 0x8370c: the two header bytes (12 = 0x88, 13 = 0x19), each behind its shadow check; a byte that
     differs leaves with the kind 0 and the zeroed box. *)
  Lemma body_tail : 50 <= n -> forall fra fv spc j nn w120 mc ob (mx : word -> option byte)
      (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    addressable mc ob 36 -> asan_cells mc -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc ->
    BJ ob spc mc mx -> rw_cells rsegs mx ob [CB 36 (repeat cp_z 36)] ->
    evtF rsegs RNG (QE fv)
      (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 n) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x836c0) fc None mx (seg_rom rsegs)).
  Proof. hide_sec.
    intros Hn50 fra fv spc j nn w120 mc ob mx rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB HFL HO Aob ACc SRc HBJ RWx.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof (RINF Hn50) as RGINF. pose proof (SCF Hn50) as SCINF. pose proof (SKF Hn50) as SKINF.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MIc & SV).
    pose proof MU as MUw. apply (munch_weaken _ _ _ _ (Wf2_sub fra j nn)) in MU.
    pose proof HBJ as HBJ'. destruct HBJ' as (MUb & WMb & MIx & STx).
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    destruct (f_facts Hn50 fra fv spc j nn w120 ob HK HO) as (Hf0 & Hf64 & Fapp & AFm & DFf).
    assert (Hjnn : 0 <= j < 8192 /\ nn <= 1)
      by (destruct HK as [(_ & _ & _ & Ej & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)];
          [lia | change (fs_M 1) with 8192 in Hjb; lia]).
    pose proof DFf as DFf'. unfold reac_ctrl_parseF.ParseFOn.Wall, reac_ctrl_parseF.ParseFOn.Wf in DFf'. cbn [disjoint_from app fst snd] in DFf'.
    destruct DFf' as (Dwin & Dhint & Dflag & Dfr & Dsh & Dbox & _).
    assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
      by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
    assert (Robb : 0 <= ob /\ ob + 36 <= 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (Rfb : 0 <= f /\ f + 50 <= 2 ^ 64) by (clear -Hf0 Hf64; lia).
    pose proof (af_mx2 Hn50 fra fv spc j nn w120 ob mc mx HK HO MU Aob MUb) as AFx.
    (* 0x836c0: byte 12 of the frame, checked *)
    rdb 12%nat 1%nat ltac:(intros jx Hjx; replace (12 + jx)%nat with 12%nat by lia;
                                     apply cp_rd_12; lia).
    step.
    assert (RX12 : 0 <= f + 12 < 2 ^ 64) by (clear -Hf0 Hf64; lia).
    pose proof (acl_shadow mx f 50 12 1 (f + 12) AFx ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(pose proof (Z.mod_pos_bound (f + 12) 8 ltac:(clear; lia)) as MB; clear -MB; lia)
                  ltac:(clear; lia)) as SH12.
    chk_core (f + 12) RX12 (Z_to_bv 5 12) SH12 pre_sr no_extra.
    do 3 step.
    rewrite (rc_eqb_zxb (cp_b fr 12) 136) by (clear; lia).
    change (bv_unsigned (cp_b fr 12)) with (cp_v fr 12).
    destruct (Z.eqb_spec (cp_v fr 12) 136) as [E12|E12]; cbn [negb]; cbv iota.
    2:{ assert (Hcphdr : cp_hdr n fr = false)
          by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E12), andb_false_r; reflexivity).
        assert (Hcp0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite Hcphdr; reflexivity).
        step.
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite Hcp0; reflexivity).
        eapply L_join;
          [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx | ].
        rewrite (ctrlparse_bytes_none n fr Hcphdr). exact RWx. }
    (* 0x836e0: byte 13 of the frame, checked *)
    rdb 13%nat 1%nat ltac:(intros jx Hjx; replace (13 + jx)%nat with 13%nat by lia;
                                     apply cp_rd_13; lia).
    step.
    assert (RX13 : 0 <= f + 13 < 2 ^ 64) by (clear -Hf0 Hf64; lia).
    pose proof (acl_shadow mx f 50 13 1 (f + 13) AFx ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(pose proof (Z.mod_pos_bound (f + 13) 8 ltac:(clear; lia)) as MB; clear -MB; lia)
                  ltac:(clear; lia)) as SH13.
    chk_core (f + 13) RX13 (Z_to_bv 5 12) SH13 pre_sr no_extra.
    do 3 step.
    rewrite (rc_eqb_zxb (cp_b fr 13) 25) by (clear; lia).
    change (bv_unsigned (cp_b fr 13)) with (cp_v fr 13).
    destruct (Z.eqb_spec (cp_v fr 13) 25) as [E13|E13]; cbn [negb]; cbv iota.
    2:{ assert (Hcphdr : cp_hdr n fr = false)
          by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E13), andb_false_r; reflexivity).
        assert (Hcp0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite Hcphdr; reflexivity).
        step.
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite Hcp0; reflexivity).
        eapply L_join;
          [ exact HK | exact HB | exact HFL | exact HO | exact MUb | exact WMb | exact MIx | exact STx | ].
        rewrite (ctrlparse_bytes_none n fr Hcphdr). exact RWx. }
    assert (HE : cp_hdr n fr = true) by (apply cp_hdr_spec; repeat split; lia).
    (* 0x83700 .. 0x8370c: s6 = the box pointer, on both paths of `beqz s4` *)
    lazymatch goal with
    | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm _ ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w : word, w = Z_to_bv 64 ob ->
                      evtF segs rgq Q (MS (bvmap_set (Z_to_bv 5 22) w R) Fm (Z_to_bv 64 0x8370c) fcc rv mm ro));
        [ step; step; rewrite (rc_eqb_lit o 0) by (clear -Ro; lia);
          destruct HO as [(Eo & Eob) | (Eo & Eob)];
          [ rewrite (proj2 (Z.eqb_eq o 0) Eo); cbv iota;
            apply (G (Z_to_bv 64 (fra + 32)) ltac:(rewrite Eob; reflexivity))
          | rewrite (proj2 (Z.eqb_neq o 0) Eo); cbv iota; step;
            apply (G (Z_to_bv 64 o) ltac:(rewrite Eob; reflexivity)) ]
        | intros w Hw; subst w; simp_regs ]
    end.
    eapply (body_copy Hn50 HE fra fv spc j nn w120 mc ob mx);
      [ exact HK | exact HB | exact HFL | exact HO | exact Aob | exact ACc | exact SRc | exact HBJ | exact RWx ].
  Qed.


  (* 0x836a8 .. : __asan_memset(ob, 0, 36) zeroes the output box, then the header test n < 50. ob is the box the
     run chose at 0x8369c/0x836a0 (the frame's redzone when o = 0, else o). *)
  Lemma body_main : forall fra fv spc j nn w120 mc ob jb
      (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> BI (Wf2 fra j nn) mc -> FLG fra nn w120 mc -> OB fra ob ->
    rw_cells rsegs mc ob [CB 36 jb] -> addressable mc ob 36 -> stk rsegs mc (S - 8800) S ->
    asan_cells mc -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) mc ->
    evtF rsegs RNG (QE fv)
      (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 ob) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 n) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x836a8) fc None mc (seg_rom rsegs)).
  Proof. hide_sec.
    intros fra fv spc j nn w120 mc ob jb rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB HFL HO HOrw Aob STw ACc SRc.
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof (rngF_ob fra fv spc j nn w120 ob HK HO) as RGOB.
    pose proof (rngF_ob_cov fra fv spc j nn w120 ob HK HO) as SCOB.
    pose proof (rngF_ob_kov fra fv spc j nn w120 ob HK HO) as SKOB.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    pose proof MU as MUw. apply (munch_weaken _ _ _ _ (Wf2_sub fra j nn)) in MU.
    destruct (ob_facts fra fv spc j nn w120 ob HK HO)
      as (Ob0 & Ob64 & Obmod & Obapp & Obrt & Obsp & Obsv & Obf & Obfr & Obfl & Obcf).
    assert (Hspcr : S - 288 <= spc /\ spc <= S - 128)
      by (destruct HK as [(_ & _ & Espc & _) | (_ & _ & _ & Espc & _)]; rewrite Espc;
          clear -HAlo HAhi; lia).
    assert (Rspc : 0 <= spc < 2 ^ 64) by (clear -Hspcr RS; lia).
    assert (Rob : 0 <= ob < 2 ^ 64) by (clear -Ob0 Ob64; lia).
    assert (U36 : bv_unsigned (Z_to_bv 64 36) = 36) by reflexivity.
    assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (STsp : stk rsegs mc (S - 8800) spc)
      by (apply (stk_sub mc (S - 8800) S (S - 8800) spc STw); clear -Hspcr RS; lia).
    pose proof HMSET as HM. unfold asan_memset_contract_F_on, ASAN_MEMSET_K in HM. cbv zeta in HM.
    unfold rng_asan.sh_word_rng, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in HM.
    (* 0x836a8 li a2,36; 0x836ac mv a0,s3; 0x836b0 li a1,0; 0x836b4 jal -> 0x524c4 *)
    do 4 step.
    eapply evtF_cut.
    { eapply HM with (junk := jb) (lo := S - 8800);
        rewrite ?(unsigned_lit _ Rob), ?(unsigned_lit spc Rspc), ?U36, ?U0.
      - change (Z.to_nat 36) with 36%nat. exact HOrw.
      - clear; lia.
      - exact Aob.
      - right; exact Obapp.
      - right; apply (acl_app_in mc _ 36 7 Aob); clear; lia.
      - exact Obrt.
      - clear -Obsp; lia.
      - exact STsp.
      - clear -Hspcr RS; lia.
      - exact HHM.
      - clear -Hspcr RS HAE; unfold APPMEM_END in *; lia.
      - exact ACc.
      - apply (srw_memset fra fv spc j nn w120 ob mc _ _ HK HO);
          [ rewrite ?(unsigned_lit _ Rob); reflexivity | first [exact U36 | reflexivity] | exact SRc ].
      - exact MI.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* __asan_memset's window inside this function's window *)
        eapply rng_sub; [exact RWIN | clear -Hspcr RS; lia | clear -Hspcr RS; lia].
      - (* the 36 bytes of the box *) exact RGOB.
      - (* their aligned shadow word cover *) right. unfold shadow_addr. apply SKOB; clear; lia.
      - (* the shadow of __asan_memset's window *)
        right. unfold shadow_addr. apply rngF_win_sh8; clear -Hspcr RS; lia. }
    intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1m & a2m & a3m & a4m & a5m & a6m & a7m & t3' & t4' & t5' & t6' & m' &
                       Hms & MUm & WMm & MIm & STm & RWm & ACm & SRm).
    subst ms'.
    rewrite (ret_pc_even 538296 ltac:(clear; lia) ltac:(clear; lia)).
    rewrite (unsigned_lit _ Rob), U36, (unsigned_lit spc Rspc) in MUm. unfold ASAN_MEMSET_K in MUm.
    rewrite (unsigned_lit _ Rob), U36 in RWm. change (Z.to_nat 36) with 36%nat in RWm.
    rewrite (unsigned_lit spc Rspc) in STm.
    (* the body's running footprint: the box and the callee windows *)
    pose proof RWm as RWbk. destruct RWbk as [[_ Hbox] _]. cbn [cells_bytes cbytes] in Hbox.
    rewrite app_nil_r in Hbox.
    assert (RMc : rd_mono mc m').
    { apply (rd_mono_list _ mc m' MUm). constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - intros y Hy. apply (rd_of_bytes _ _ _ Hbox). rewrite repeat_length. clear -Hy; cbn; lia.
      - intros y Hy. apply (rd_of_stk _ _ _ STm). clear -Hy Hspcr; lia. }
    assert (MUx : munch [(ob, ob + 36); (S - 8800, spc)] mc m').
    { eapply munch_weaken; [| exact MUm].
      intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & _).
      split; [exact H1|]. split; [clear -H2 Hspcr; lia | exact I]. }
    assert (STx : stk rsegs m' (S - 8800) S) by (exact (stk_mono mc m' (S - 8800) S STw WMm RMc)).
    (* 0x836b8: li a0,50; 0x836bc: bltu s6,a0 -> n < 50 exits at 0x8391c *)
    step. step. rewrite (rc_ltu_lit n 50) by lia.
    destruct (Z.ltb_spec n 50) as [Hlt|Hge]; cbv iota.
    - (* n < 50: no header, the box stays zero, a0 = 0 *)
      step.
      assert (Hcphdr : cp_hdr n fr = false)
        by (unfold cp_hdr; rewrite (proj2 (Z.leb_gt 50 n) Hlt); reflexivity).
      assert (Hcp0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite Hcphdr; reflexivity).
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite Hcp0; reflexivity).
      eapply (L_join fra fv spc j nn w120 mc ob m');
        [ exact HK | exact HB | exact HFL | exact HO | exact MUx | exact WMm | exact MIm | exact STx | ].
      rewrite (ctrlparse_bytes_none n fr Hcphdr). exact RWm.
    - (* 50 <= n: the header checks, the copies, the comparison and the kind *)
      eapply (body_tail Hge fra fv spc j nn w120 mc ob m');
        [ exact HK | exact HB | exact HFL | exact HO | exact Aob | exact ACc | exact SRc
        | refine (conj MUx (conj WMm (conj MIm STx))) | ].
      replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with cp_z in RWm
        by (vm_compute; reflexivity).
      exact RWm.
  Qed.

  (* 0x8369c .. 0x836a8: the box pointer s3 = o (or the frame's redzone when o = 0). *)
  Lemma body_holds_x : KBx QE.
  Proof. hide_sec.
    unfold KBx. intros fra fv spc j nn w120 mc rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31
      HK HB HFL HBaddr.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (Pfs0 & Pfs1 & Pfs2 & Pfsapp & Pfsstk) & _ & _ & _
                       & HFSb & _ & HWd & HDd).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    assert (EMt : fs_M 1 = 8192) by reflexivity.
    assert (Hjb0 : 0 <= j < 8192)
      by (destruct HK as [(_ & _ & _ & Ej & _) | (Hjb & _ & _ & _ & _ & _)];
          [lia | rewrite EMt in Hjb; lia]).
    assert (Hnn1 : nn <= 1)
      by (destruct HK as [(_ & _ & _ & _ & Enn) | (_ & _ & _ & _ & _ & Enn & _)]; lia).
    pose proof (stk_mono m mc (S - 8800) S ST0 WM RM) as STw.
    assert (STfr : stk rsegs mc fra (fra + 128)).
    { destruct HK as [(Efv & Efra & _) | (Hj & Efra & _)].
      - apply (stk_sub mc (S - 8800) S fra (fra + 128) STw);
          [ clear -Efra HAlo HAhi RS; rewrite Efra; lia | clear -Efra HAlo HAhi RS; rewrite Efra; lia | lia ].
      - pose proof (stk_mono m mc FS (FS + FS_SIZE) Pfsstk WM RM) as STfs.
        assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
          by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat];
              change (2 ^ 20) with 1048576; change (2 ^ 1) with 2; lia).
        rewrite EMt in Hj.
        apply (stk_sub mc FS (FS + FS_SIZE) fra (fra + 128) STfs);
          [ rewrite Efra, EFRj; clear -Pfs0 Hj; lia
          | rewrite Efra, EFRj; unfold FS_SIZE; clear -Pfs0 HFSb Hj; lia | lia ]. }
    assert (ACc : asan_cells mc).
    { apply (asan_cells_kept (Wf2 fra j nn) m mc AC0 MU).
      unfold Wf2, RT_LO, RT_HI, fs_hint, fs_flag, shadow_addr;
        cbn [disjoint_from fst snd Z.of_nat Pos.of_succ_nat].
      try (change (2 ^ 15) with 32768); try (change (2 ^ (15 - 1)) with 16384).
      repeat split; try exact I; left;
        unfold HIGHMEM_BEG, APPMEM_END in *;
        clear -HHM HAE Pfs2 Hjb0 FRlo SH1; lia. }
    pose proof (shadow_rw_mono_on _ m mc SR0 WM RM) as SRc.
    (* 0x8369c: mv s3,s10; 0x836a0: beqz s4 -> the box pointer *)
    step.
    step. rewrite (rc_eqb_lit o 0) by lia.
    destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbv iota.
    - (* o = 0: the box is the frame's redzone fra + 32, carved from the frame's stack bytes *)
      assert (STbox : stk rsegs mc (fra + 32) (fra + 68))
        by (apply (stk_sub mc fra (fra + 128) (fra + 32) (fra + 68) STfr); lia).
      destruct (stk_carve rsegs mc (fra + 32) (fra + 68) 36%nat STbox ltac:(lia)) as [_ [jb Hrw]].
      replace (fra + 68 - Z.of_nat 36) with (fra + 32) in Hrw by lia.
      eapply (body_main fra fv spc j nn w120 mc (fra + 32) jb);
        [ exact HK | exact HB | exact HFL | left; split; [exact Eo | reflexivity]
        | exact Hrw | exact HBaddr | exact STw | exact ACc | exact SRc ].
    - (* o <> 0: the box is o, transported from the caller's rw_cells *)
      step.
      destruct (HOK Eo) as (Ho4 & Ho36 & HOrw & HoS & Hof).
      assert (HinO : In (o, o + 36) (reac_ctrl_parse_D f n o))
        by (unfold reac_ctrl_parse_D; apply in_or_app; right;
            rewrite (proj2 (Z.eqb_neq o 0) Eo); left; reflexivity).
      assert (Hdjo : forall x, o <= x < o + 36 -> outside (Wf2 fra j nn) x).
      { intros x Hx.
        destruct (AO0 Eo) as (AOa & _ & _).
        assert (Hxapp : app_mem x)
          by (pose proof (acl_app_in m o 36 (x - o) AOa ltac:(lia)) as Ha;
              replace (o + (x - o)) with x in Ha by lia; exact Ha).
        pose proof (dj_pair o (o + 36) _ _ HinO (proj1 (fp_wx_hint_flag_in FS X))) as Hoh.
        pose proof (dj_pair o (o + 36) _ _ HinO (proj2 (fp_wx_hint_flag_in FS X))) as Hofl.
        unfold Wf2. cbn [outside]. split; [| split; [| split; [| split; [| split; [| exact I]]]]].
        - clear -Hx HoS; destruct HoS; lia.
        - intros [HL HR]. clear -Hx HL HR Hoh; lia.
        - intros [HL HR]. destruct HK as [(_ & _ & _ & _ & Enn) | (Hjb & _ & _ & _ & _ & Enn & _)].
          + rewrite Enn in HR. clear -HL HR; lia.
          + rewrite Enn in HR.
            assert (EFL : fs_flag FS 1 j = fs_flag FS 1 0 + j) by (rewrite !fs_flag1; lia).
            rewrite EFL in HL, HR. rewrite EMt in Hjb, Hofl. clear -Hx HL HR Hofl Hjb; lia.
        - intros [HL HR]. destruct HK as [(_ & Efr & _ & _ & _) | (Hjb & Efr & _ & _ & _ & _ & Hfl0)].
          + rewrite Efr in HL, HR. clear -Hx HoS HL HR HAlo HAhi; destruct HoS; lia.
          + destruct (D_apart_frame o (o + 36) j HinO ltac:(clear; lia) Hjb Hfl0) as [Hc|Hc];
              rewrite <- Efr in Hc; clear -Hx HL HR Hc; lia.
        - intros [HL HR]. apply (acl_app_not_shadow x Hxapp). unfold shadow_addr in HL, HR.
          replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
          apply frame_shadow_in; [clear -FRlo Pfs0; lia | exact FRA | clear -SH1; lia | clear -SH2; lia | lia]. }
      assert (Hbox : rw_cells rsegs mc o [CB 36 junk])
        by (eapply acl_rw; [exact HOrw | exact MU | exact WM |
              intros x Hx; apply Hdjo; cbn [cells_size csize] in Hx; lia]).
      assert (Aob : addressable mc o 36).
      { destruct (AO0 Eo) as (AOa & _ & _).
        apply (acl_addr_munch (Wf2 fra j nn) m mc o 36 AOa MU).
        intros i Hi.
        pose proof (acl_app_in m o 36 i AOa Hi) as Hoi.
        pose proof (rt_app_shadow (o + i) Hoi) as Hsh.
        unfold Wf2. cbn [outside]. split; [| split; [| split; [| split; [| split; [| exact I]]]]].
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          unfold app_mem, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *; clear -HL HR HHM HAE; right; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          apply Pfsapp. unfold fs_hint in HL, HR; cbn [Z.of_nat] in HL, HR;
            unfold FS_SIZE; clear -HL HR Pfs0; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          apply Pfsapp. unfold fs_flag in HL, HR; cbn [Z.of_nat Pos.of_succ_nat] in HL, HR;
            change (2 ^ 15) with 32768 in HL, HR; change (2 ^ (15 - 1)) with 16384 in HL, HR;
            unfold FS_SIZE; clear -HL HR Pfs0 Hjb0 Hnn1; lia.
        + intros [HL HR]. apply (acl_app_not_shadow (shadow_addr (o + i))); [| exact Hsh].
          replace (shadow_addr (o + i)) with (fra + (shadow_addr (o + i) - fra)) by lia.
          apply FAP; clear -HL HR; lia.
        + intros HC.
          assert (E16 : shadow_addr fra + 16 = shadow_addr (fra + 128))
            by (unfold shadow_addr; clear -FR8; Z.div_mod_to_equations; lia).
          rewrite E16 in HC.
          apply (acl_win_sh (o + i) fra (fra + 128) FR8); [| exact HC].
          intros [HL HR].
          destruct HK as [(_ & Efr & _ & _ & _) | (Hjb & Efr & _ & _ & _ & _ & Hfl0)].
          * destruct HoS as [Hc|Hc]; rewrite Efr in HL, HR; clear -Hi Hc HL HR HAlo HAhi; lia.
          * destruct (D_apart_frame o (o + 36) j HinO ltac:(clear; lia) Hjb Hfl0) as [Hc|Hc];
              rewrite <- Efr in Hc; clear -Hi HL HR Hc; lia. }
      eapply (body_main fra fv spc j nn w120 mc o junk);
        [ exact HK | exact HB | exact HFL | right; split; [exact Eo | reflexivity]
        | exact Hbox | exact Aob | exact STw | exact ACc | exact SRc ].
  Qed.

End RBodyF.

End RBodyFOn.
