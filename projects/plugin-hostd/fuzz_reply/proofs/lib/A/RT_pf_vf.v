(* The lower half of fuzz_reply.asan's snprintf chain: ___interceptor_vfprintf as musl vsnprintf's `vfprintf`.

   vf_icpt_ok (RT_pf_stmt.v vf_icpt_stmt): musl vsnprintf's `vfprintf` call does not land on musl vfprintf in an
   ASan build - it lands on __wrap_vfprintf 0x421d0 (A_img_vsn's `sym 0x7f000400`), which runs
   ___interceptor_vfprintf 0x4642c: TryAsanInitFromRtl, printf_common (check_printf = 1), then
   REAL(vfprintf) = musl vfprintf 0x92d08 through the cell 0x9f768 (A_img's `sym 0x7f000400`), which is the body
   GXA already closed.  So GXA's guarded vfprintf body at A_img (G_vfprintf_snf_closed.v
   vfprintf_snf_a_guarded_closed, RT_gxa_inst.v fr_vfprintf_guarded) becomes GXA's guarded vfprintf AT THE
   INTERCEPTOR: the same statement at A_img_vsn, for the guard vf_ready_icpt vfb.

   NO FUNCTION IS PROVED HERE.  The pieces are composed, in this order:
     I_vfprintfw1.v:18 vfprintf_walkA1n   0x421d0 -> the printf_common call (frame 48, TryAsanInitFromRtl, the
                                          three runtime cells), R4Printf's relocated Bz walk;
     RT_pf_bz.v:70     pcom_call          printf_common at the floor q - 48 - 2320 (R4's relocated
                                          pcom_genx_spec, rip_stmt discharged);
     I_vfprintfw.v:60  vfprintf_walkA2    -> the REAL(vfprintf) call, pc = 0x92d08;
     the hypothesis VFB                   GXA's guarded body at A_img;
     I_vfprintfw.v:81  vfprintf_walkB     the epilogue, back to the caller.

   THE TWO INSTANCES.  A_img and A_img_vsn (RT_IImgA.v:96, :107) differ in one symbol-map row (0x7f000400).
   Letting Coq CONVERT `img_segs A_img_vsn` against `img_segs A_img` is catastrophic (measured: one `exact` on
   ssp_cells ran 16 minutes).  Every A_img_vsn fact below is first REWRITTEN to `asegs` with RT_pf_kit.v's
   segs_vsn, and every symbol application to its numeral, before it meets an A_img goal; `asegs` against
   `img_segs A_img` is a cheap head-difference, not a record comparison.

   THE TWO TREES.  lib/CJ/Lib and lib/A/Bz/Lib are two copies of one machine library: bytes, stacks, munch and
   wmono cross by RT_pf_kit.v's casts, `msteps` only by cj_bz_evt / bz_cj_evt, and `cell` NOT AT ALL (it is an
   Inductive in each tree).  So a GXA cell fact (snf_file, CK, D, ssp_cells) is transported with CJ's own Frame
   lemmas over a CJ munch, and a Bz walk's cell fact (the interceptor frame, REAL(vfprintf)) with Bz's.

   lia: the statement carries two disjunctive premises (the destination's separation); they are hidden behind
   RT_pf_kit.v's `hid` right after intros and the one consequence the proof needs is derived once as DSEP. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.K Require Import I_vprintfw I_vfprintfw I_vfprintfw1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_pf_Tbl RT_pf_bz.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec.Prelim.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pad.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pop_arg.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_fmt_fp_lib.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_IImgA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_stmt.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Module CJE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Exec.
Module CJF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Module CJC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Cells.
Module CJM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Module CJS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.MState.
Module SPL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec.Prelim.
Module CJR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Module GP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pad.
Module GPA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pop_arg.
Module GFL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_fmt_fp_lib.
Module GIF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.
Module GVF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_vfprintf_snf.
Module VFC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Module RTA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_IImgA.
Module GC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Module PS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_stmt.
Module PK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_kit.

(* ---- the three symbol-map values this file crosses on, each as a NUMBER (RT_pf_Tbl.v) ---- *)

(* the vfprintf entry under each instance: musl vfprintf's body at A_img, the interceptor trampoline at A_img_vsn *)
Lemma sym_vf_img : @CJR.sym RTA.A_img 0x7f000400 = PF_MUSL_VFPRINTF.
Proof. vm_compute. reflexivity. Qed.
Lemma sym_vf_vsn : @CJR.sym RTA.A_img_vsn 0x7f000400 = PF_WRAP_VFPRINTF.
Proof. vm_compute. reflexivity. Qed.

(* the only other symbol the vfprintf statement mentions is sn_write, in the FILE layout - and the two instances
   agree on it, so the FILE cells of one are the FILE cells of the other *)
Lemma sym_snw : @CJR.sym RTA.A_img_vsn GIF.G_printf_iface.K_SN_WRITE
              = @CJR.sym RTA.A_img GIF.G_printf_iface.K_SN_WRITE.
Proof. vm_compute. reflexivity. Qed.

Lemma snf_file_eq : forall bufp CK,
  @GVF.snf_file RTA.A_img_vsn bufp CK = @GVF.snf_file RTA.A_img bufp CK.
Proof. intros bufp CK. unfold GVF.snf_file. rewrite sym_snw. reflexivity. Qed.

(* ---- args_ok depends on the instance only through img_segs, so it crosses by induction - never by conversion ---- *)
Lemma arg_ok_cross : forall (I1 I2 : CJR.RImg), @CJR.img_segs I1 = @CJR.img_segs I2 ->
  forall Fp B BS RC RCS RE RES m lo sp ap w a,
    @GIF.G_printf_iface.arg_ok I1 Fp B BS RC RCS RE RES m lo sp ap w a ->
    @GIF.G_printf_iface.arg_ok I2 Fp B BS RC RCS RE RES m lo sp ap w a.
Proof.
  intros I1 I2 E Fp B BS RC RCS RE RES m lo sp ap w a H.
  destruct a as [s|i|u|d|l]; try exact H.
  destruct H as (slack & BY & REST). exists slack. split; [rewrite <- E; exact BY | exact REST].
Qed.

(* NOTE: args_ok's structural argument is SLOTS, not args (both decrease; Coq takes the first), so the
   induction is on ws - on args the fixpoint stays stuck and even `args_ok .. ws []` is not True. *)
Lemma args_ok_cross : forall (I1 I2 : CJR.RImg), @CJR.img_segs I1 = @CJR.img_segs I2 ->
  forall Fp B BS RC RCS RE RES m lo sp ap ws args,
    @GIF.G_printf_iface.args_ok I1 Fp B BS RC RCS RE RES m lo sp ap ws args ->
    @GIF.G_printf_iface.args_ok I2 Fp B BS RC RCS RE RES m lo sp ap ws args.
Proof.
  intros I1 I2 E Fp B BS RC RCS RE RES m lo sp ap ws args H. revert args H.
  induction ws as [|w ws IH]; intros args H.
  - destruct args as [|a args]; [exact I | destruct H].
  - destruct args as [|a args]; [exact I |].
    destruct H as [H1 H2].
    split; [exact (arg_ok_cross I1 I2 E _ _ _ _ _ _ _ _ _ _ _ _ _ H1) | exact (IH args H2)].
Qed.

Section VF.
Variable vfb : VFC.vf_guard.
Hypothesis VFB : @VFC.vfprintf_guarded_stmt RTA.A_img vfb.

Theorem vf_icpt_ok : @VFC.vfprintf_guarded_stmt RTA.A_img_vsn (PS.vf_ready_icpt vfb).
Proof.
  unfold VFC.vfprintf_guarded_stmt. intros until o. cbv zeta.
  intros -> -> -> FFP FCK FD LJ BY HFb P1 VAA AOK MODEL N0 OM0 HMIN BUFP ST LO GLO QHI SSP MI FRM RDY
    HA HA0 QFP FPCK CKVA CKHI VAHI D0 DHI DD1 DD2.
  set (q := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RQ. unfold bv_modulus in RQ.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in RQ. fold q in RQ.
  (* every A_img_vsn symbol value becomes a numeral, once *)
  rewrite PK.globals_top_val_vsn in GLO, HA, DD2.
  unfold PF_GLOBALS_TOP in GLO, HA, DD2.
  destruct RDY as (RLO & RLOLO & RQHI & RQ16 & RCELLS & RPCOM & RVFB).
  unfold PS.VFI_DEPTH, PF_VF_FRAME, GIF.G_printf_iface.VF_DEPTH in RLO.
  unfold R_m2s.kHighShadowEnd in RLOLO.
  destruct RCELLS as (AI & GCF & CPF & RVF).
  assert (HAz : A + Z.of_nat (length fmt) <= 0x5fb000) by (unfold SPL.zlength in HA; exact HA).
  assert (ZLS : 0 <= SPL.zlength slots) by (unfold SPL.zlength; lia).
  assert (QVA : q <= VA) by lia.
  (* the destination's separation, once; then the two disjunctions leave lia's view *)
  assert (DSEP : forall x y, lo <= x -> y <= q -> D + Z.of_nat dn <= x \/ y <= D)
    by (intros x y Hx Hy; destruct DD1 as [E|E]; [left; lia | right; lia]).
  PK.hide DD1. PK.hide DD2. PK.hide HMIN.
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (q + -48)) = q + -48) by (apply unsigned_lit; lia).
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned).
  (* the statement's GXA facts, rewritten off A_img_vsn *)
  unfold GPA.va_area in VAA.
  rewrite PK.segs_vsn in FFP, FCK, FD, BY, VAA, ST, MI.
  rewrite snf_file_eq in FFP.
  assert (STb : stk asegs m lo q) by exact ST.
  assert (MIb : mem_inv asegs m) by exact (GC.mem_inv_cj_bz m MI).
  assert (SSPi : @GP.ssp_cells RTA.A_img m canary) by exact (PK.ssp_cells_of_vsn m canary SSP).
  unfold GP.ssp_cells in SSPi.
  rewrite PK.got_ssp_val, PK.ssp_guard_val, PK.segs_img in SSPi.
  unfold PF_GOT_SSP, PF_SSP_GUARD in SSPi.
  assert (AOKi : @GIF.G_printf_iface.args_ok RTA.A_img Fp lo 0 CK 16 D (Z.of_nat dn) m lo q lo slots args).
  { apply (args_ok_cross RTA.A_img_vsn RTA.A_img);
      [rewrite PK.segs_vsn, PK.segs_img; reflexivity | exact AOK]. }
  assert (VAb : bytes_at asegs m VA (u64s slots)) by exact VAA.
  (* ---- the interceptor's entry: 0x421d0 ---- *)
  rewrite sym_vf_vsn, PK.segs_vsn, ESP.
  apply GC.bz_cj_evt.
  unfold PF_WRAP_VFPRINTF.
  (* --- the frame, TryAsanInitFromRtl, to the printf_common call --- *)
  eapply BzE.evt_cut.
  { apply (vfprintf_walkA1n q lo ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 VA)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m);
      [ exact STb | lia | lia | lia
      | unfold PF_ASAN_INITED in AI; exact AI
      | unfold PF_GOT_COMMON_FLAGS, PF_COMMON_FLAGS in GCF; exact GCF
      | unfold PF_CHECK_PRINTF in CPF; exact CPF
      | exact MIb ]. }
  intros ms1 H1. unfold vfwA1_post in H1.
  destruct H1 as (m1 & u0 & u1 & u2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & MU1 & WM1 & MI1b & ST1b & FR1).
  assert (VA1 : bytes_at asegs m1 VA (u64s slots)).
  { apply (bytes_at_transport asegs [(q - 64, q)] m m1 VA (u64s slots) VAb MU1).
    cbn [disjoint_from]. split; [right; lia | exact I]. }
  assert (VA1c : @GPA.va_area RTA.A_img m1 VA slots).
  { unfold GPA.va_area. rewrite PK.segs_img. exact VA1. }
  (* --- printf_common, at the floor q - 48 - 2320 --- *)
  eapply BzE.evt_cut.
  { apply (pcom_call A VA lo (Z_to_bv 64 PF_RA_VF_PCOM) (Z_to_bv 64 (q + -48)) gp tp u0 u1 u2
             (Z_to_bv 64 A) (Z_to_bv 64 Fp) (Z_to_bv 64 PF_STR_VFPRINTF) (Z_to_bv 64 A) (Z_to_bv 64 VA)
             b3 b4 b5 b6 b7 (Z_to_bv 64 VA) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1);
      [ reflexivity | reflexivity
      | rewrite EU48; exact ST1b
      | rewrite EU48; lia
      | exact RLOLO
      | rewrite EU48; lia
      | rewrite EU48; Z.div_mod_to_equations; lia
      | rewrite EU48; exact (RPCOM m1 (PK.munch_bz_cj _ m m1 MU1) (PK.wmono_bz_cj m m1 WM1)
                               (GC.mem_inv_bz_cj m1 MI1b) VA1c)
      | exact MI1b ]. }
  intros ms2 H2. unfold pcom_post in H2.
  destruct H2 as (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m2
                  & -> & MU2 & WM2 & MI2b & ST2b).
  rewrite EU48 in MU2, ST2b.
  assert (ERET1 : ret_pc (Z_to_bv 64 PF_RA_VF_PCOM) = Z_to_bv 64 PF_RA_VF_PCOM)
    by (apply ret_pc_even; [unfold PF_RA_VF_PCOM; lia | reflexivity]).
  rewrite ERET1.
  (* the whole front touched only [q - 48 - 2320, q) *)
  assert (MUf : munch [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)] m m2).
  { apply (munch_trans [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)] m m1 m2).
    - apply (munch_weaken [(q - 64, q)]); [| exact MU1].
      unfold sub_fp, PF_VF_FRAME, PF_PCOM_DEPTH. cbn [outside]. intros x (Hx & _). split; [lia | exact I].
    - apply (munch_weaken [(q + -48 - 2320, q + -48)]); [| exact MU2].
      unfold sub_fp, PF_VF_FRAME, PF_PCOM_DEPTH. cbn [outside]. intros x (Hx & _). split; [lia | exact I]. }
  assert (WMf : wmono asegs m m2) by exact (wmono_trans asegs m m1 m2 WM1 WM2).
  pose proof (PK.munch_bz_cj _ m m2 MUf) as MUfc.
  pose proof (PK.wmono_bz_cj m m2 WMf) as WMfc.
  assert (FR2 : rw_cells asegs m2 (q + -48)
            [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_transport asegs [(q + -48 - 2320, q + -48)] m1 m2 _ _ FR1 MU2 WM2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  assert (RVF2 : ro_cells asegs m2 PF_REAL_VFPRINTF [C8 (Z_to_bv 64 PF_MUSL_VFPRINTF)]).
  { apply (ro_cells_transport asegs [(q + -48 - 2320, q + -48)] m1 m2 _ _
             (ro_cells_transport asegs [(q - 64, q)] m m1 _ _ RVF MU1
                ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                      unfold PF_REAL_VFPRINTF; split; [left; lia | exact I]))
             MU2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    unfold PF_REAL_VFPRINTF. split; [left; lia | exact I]. }
  (* --- to the REAL(vfprintf) call --- *)
  eapply BzE.evt_cut.
  { apply (vfprintf_walkA2 q (Z_to_bv 64 VA) (Z_to_bv 64 VA) s2 s1 s0 ra
             (Z_to_bv 64 PF_RA_VF_PCOM) gp tp v0 v1 v2 (Z_to_bv 64 A) (Z_to_bv 64 Fp)
             d0 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 VA) s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F fc m2);
      [ exact FR2 | unfold PF_REAL_VFPRINTF, PF_MUSL_VFPRINTF in RVF2; exact RVF2 | lia | lia | exact MI2b ]. }
  intros ms3 H3. destruct H3 as (a3' & ->).
  (* --- GXA's guarded musl vfprintf, at A_img --- *)
  pose proof sym_vf_img as EVF. unfold PF_MUSL_VFPRINTF in EVF.
  eapply BzE.evt_cut.
  { apply PK.cj_bz_evt. rewrite <- EVF.
    apply (VFB (Z_to_bv 64 PF_RA_VF_REAL) (Z_to_bv 64 (q + -48)) gp tp v0 v1 v2
             (Z_to_bv 64 A) (Z_to_bv 64 Fp) (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 VA)
             a3' d4 d5 d6 d7 (Z_to_bv 64 VA) s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6
             F fc m2 Fp CK D N OM bufp A VA dn junkd fmt slots args lo canary r o).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite PK.segs_img.
      apply (CJF.rw_cells_transport asegs [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)] m m2 _ _ FFP MUfc WMfc).
      cbn [CJF.disjoint_from]. split; [right; lia | exact I].
    - rewrite PK.segs_img.
      apply (CJF.rw_cells_transport asegs [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)] m m2 _ _ FCK MUfc WMfc).
      cbn [CJF.disjoint_from]. split; [right; lia | exact I].
    - rewrite PK.segs_img.
      apply (CJF.rw_cells_transport asegs [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)] m m2 _ _ FD MUfc WMfc).
      cbn [CJF.disjoint_from]. split; [| exact I].
      cbn [CJC.cells_size CJC.csize]. rewrite Nat.add_0_r.
      exact (DSEP (q - (PF_VF_FRAME + PF_PCOM_DEPTH)) q
               ltac:(unfold PF_VF_FRAME, PF_PCOM_DEPTH; lia) ltac:(lia)).
    - exact LJ.
    - rewrite PK.segs_img.
      apply (CJF.bytes_at_transport asegs [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)] m m2 _ _ BY MUfc).
      cbn [CJF.disjoint_from]. unfold GFL.zb. rewrite length_map.
      unfold PF_VF_FRAME, PF_PCOM_DEPTH. split; [left; lia | exact I].
    - exact HFb.
    - exact P1.
    - unfold GPA.va_area. rewrite PK.segs_img.
      apply (CJF.bytes_at_transport asegs [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)] m m2 _ _ VAA MUfc).
      cbn [CJF.disjoint_from]. split; [right; lia | exact I].
    - rewrite EU48.
      eapply GVF.args_ok_rebase;
        [ exact AOKi | | lia | right; reflexivity | right; split; reflexivity
        | right; split; reflexivity | right; reflexivity ].
      apply (CJF.munch_weaken [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)]); [| exact MUfc].
      unfold CJF.sub_fp, PF_VF_FRAME, PF_PCOM_DEPTH. cbn [CJF.outside].
      intros x (Hx & _ & _ & _). split; [lia | exact I].
    - exact MODEL.
    - exact N0.
    - exact OM0.
    - exact HMIN.
    - exact BUFP.
    - rewrite EU48. exact (PK.stk_bz_cj m2 lo (q + -48) ST2b).
    - rewrite EU48. unfold GIF.G_printf_iface.VF_DEPTH. lia.
    - rewrite PK.globals_top_val. unfold PF_GLOBALS_TOP. lia.
    - rewrite EU48. lia.
    - (* the stack-protector cells, inside A_img, by the kit's numerals *)
      unfold GP.ssp_cells. rewrite PK.got_ssp_val, PK.ssp_guard_val, PK.segs_img.
      unfold PF_GOT_SSP, PF_SSP_GUARD. destruct SSPi as [S1 S2]. split.
      + apply (CJF.rw_cells_transport asegs [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)] m m2 _ _ S1 MUfc WMfc).
        cbn [CJF.disjoint_from CJC.cells_size CJC.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
        unfold PF_VF_FRAME, PF_PCOM_DEPTH. split; [left; lia | exact I].
      + apply (CJF.rw_cells_transport asegs [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)] m m2 _ _ S2 MUfc WMfc).
        cbn [CJF.disjoint_from CJC.cells_size CJC.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
        unfold PF_VF_FRAME, PF_PCOM_DEPTH. split; [left; lia | exact I].
    - exact (GC.mem_inv_bz_cj m2 MI2b).
    - exact FRM.
    - rewrite EU48. exact (RVFB m2 MUfc WMfc).
    - rewrite PK.globals_top_val. unfold PF_GLOBALS_TOP. exact HA.
    - exact HA0.
    - rewrite EU48. lia.
    - exact FPCK.
    - exact CKVA.
    - exact CKHI.
    - exact VAHI.
    - exact D0.
    - exact DHI.
    - exact DD1.
    - rewrite PK.globals_top_val. unfold PF_GLOBALS_TOP. exact DD2. }
  cbv beta. intros ms4 H4. unfold GVF.vfprintf_snf_post in H4. rewrite !EU48 in H4.
  destruct H4 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & Ft & fc' & fjunk & m3
                  & -> & MU3 & WM3 & MI3 & FRM' & FOK & ST3 & SSP3 & FD3 & FCK3 & FFP3).
  assert (ERET2 : CJS.ret_pc (Z_to_bv 64 PF_RA_VF_REAL) = Z_to_bv 64 PF_RA_VF_REAL)
    by (apply CJS.ret_pc_even; [unfold PF_RA_VF_REAL; lia | reflexivity]).
  rewrite ERET2.
  assert (MU3b : munch [(lo, q + -48); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m2 m3)
    by exact (PK.munch_cj_bz _ m2 m3 MU3).
  assert (WM3b : wmono asegs m2 m3) by exact (PK.wmono_cj_bz m2 m3 WM3).
  assert (MI3b : mem_inv asegs m3) by exact (GC.mem_inv_cj_bz m3 MI3).
  assert (FR3 : rw_cells asegs m3 (q + -48)
            [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_transport asegs [(lo, q + -48); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)]
             m2 m3 _ _ FR2 MU3b WM3b).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    split; [lia | split; [lia | split; [lia | split; [| exact I]]]].
    destruct (DSEP (q + -48) q ltac:(lia) ltac:(lia)) as [E|E]; [right; lia | left; lia]. }
  (* --- the epilogue --- *)
  eapply BzE.evt_cut.
  { apply (vfprintf_walkB q lo (Z_to_bv 64 VA) (Z_to_bv 64 VA)
             (Z_to_bv 64 PF_RA_VF_REAL) ra gp tp w0 w1 w2 s0 s1 s2
             (Z_to_bv 64 A) (Z_to_bv 64 Fp) (Z_to_bv 64 VA)
             (Z_to_bv 64 r) e1 e2 e3 e4 e5 e6 e7 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 Ft fc' m3);
      [ exact (PK.stk_cj_bz m3 lo (q + -48) ST3) | lia | lia | exact FR3 | exact MI3b ]. }
  cbv beta. intros ms5 H5.
  destruct H5 as ((y0 & y1 & y2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & y3 & y4 & y5 & y6 & ->) & ST4).
  apply BzE.evt_done.
  unfold GVF.vfprintf_snf_post. rewrite PK.segs_vsn.
  exists y0, y1, y2, g1, g2, g3, g4, g5, g6, g7, y3, y4, y5, y6, Ft, fc', fjunk, m3.
  rewrite EUq.
  split; [reflexivity|].
  split.
  { apply (PK.munch_bz_cj [(lo, q); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m m3).
    apply (munch_trans [(lo, q); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m m2 m3).
    - apply (munch_weaken [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)]); [| exact MUf].
      unfold sub_fp, PF_VF_FRAME, PF_PCOM_DEPTH. cbn [outside]. intros x (Hx & _). split; [lia | exact I].
    - apply (munch_weaken [(lo, q + -48); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)]); [| exact MU3b].
      unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & H4 & _).
      split; [lia | split; [exact H2 | split; [exact H3 | split; [exact H4 | exact I]]]]. }
  split; [exact (PK.wmono_bz_cj m m3 (wmono_trans asegs m m2 m3 WMf WM3b))|].
  split; [exact MI3|].
  split; [exact FRM'|].
  split; [exact FOK|].
  split; [exact (PK.stk_bz_cj m3 lo q ST4)|].
  split; [exact (PK.ssp_cells_to_vsn m3 canary SSP3)|].
  split; [exact FD3|].
  split; [exact FCK3 | exact FFP3].
Qed.

End VF.

(* the frozen statement, met *)
Theorem vf_icpt_stmt_ok : PS.vf_icpt_stmt.
Proof. exact vf_icpt_ok. Qed.

(* ---- the chain at fuzz_reply's record ----
   PfChain owns this section.  It is kept verbatim, as a comment, because the two files it calls do not exist /
   do not compile yet in this lane: PV.vsnprintf_icpt_ok_body (RT_pf_vsn.v:328 puts it in RT_pf_vsn_body.v) and
   PN.snprintf_icpt_ok (RT_pf_snf.v).  Uncomment, with the matching Requires and the PN / PV / SC / GVS aliases,
   once those land.

Section Chain.
Variable set_ready : mem -> Z -> Z -> Z -> Prop.
Variable vfb : VFC.vf_guard.
(* GXA's vsnprintf_x_proof at the second instance with its image facts filled - a Theorem Labs lane's fm_vsnprintf_x_proof shape;
   ours is RT_gxa_inst.v fr_vsnprintf_x *)
Hypothesis GXA_VSN : forall vf_ready : VFC.vf_guard,
  @SC.memset_stack_contract RTA.A_img_vsn set_ready -> @VFC.vfprintf_guarded_stmt RTA.A_img_vsn vf_ready ->
  @GVS.vsnprintf_x_stmt RTA.A_img_vsn set_ready vf_ready.
Hypothesis SPEC_memset : @SC.memset_stack_contract RTA.A_img_vsn set_ready.
(* GXA's guarded musl vfprintf body at A_img (RT_gxa_inst.v fr_vfprintf_guarded) *)
Hypothesis VFB : @VFC.vfprintf_guarded_stmt RTA.A_img vfb.

Theorem snprintf_chain_ok : PS.snprintf_icpt_stmt set_ready (PS.vf_ready_icpt vfb).
Proof.
  apply (PN.snprintf_icpt_ok set_ready (PS.vf_ready_icpt vfb)).
  apply (PV.vsnprintf_icpt_ok_body set_ready (PS.vf_ready_icpt vfb)).
  apply (GXA_VSN (PS.vf_ready_icpt vfb) SPEC_memset).
  exact (vf_icpt_ok vfb VFB).
Qed.

End Chain.
*)
