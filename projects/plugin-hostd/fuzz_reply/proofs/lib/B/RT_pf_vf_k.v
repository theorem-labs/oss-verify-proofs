(* Image B twin of lib/A/RT_pf_vf_k.v at 2c1f180a413 (sha256 2a13b35e8fe6; internal record): module paths lib.A -> lib.B; 2 image numerals moved to fuzz_reply.asan-ubsan by symbol + offset, each checked against that image (CHAINKB-numerals.tsv sha256 86a76b0550d0; internal record). *) (* KEEP-FX copy of RT_pf_vf.v: ___interceptor_vfprintf as musl vsnprintf's `vfprintf`, from the keep-FP twin's guarded
   musl vfprintf body (lib/CJ/RL/GXAK, provenance/keepfx/README.md).
   Copy of lib/A/RT_pf_vf.v:33-83 and :128-362 at d49bd1db505 (sha256 0022c9da30b0; internal record), retargeted to GXAK; the helper
   lemmas at RT_pf_vf.v:84-126 are not copied but used in place, qualified by the alias PF.

   vf_icpt_ok_k: the twin's guarded vfprintf body at A_img (GXAK/G_vfprintf_snf_closed.v
   vfprintf_snf_a_guarded_closed, RT_gxa_inst_k.v fr_vfprintf_guarded_k) becomes the twin's guarded vfprintf AT THE
   INTERCEPTOR: the same statement at A_img_vsn, for the guard RT_pf_stmt.v vf_ready_icpt vfb.  The twin's statement
   has no `frm0 fc` premise, and its post (GXK/G_vfprintf_snf.v vfprintf_snf_post) holds `Ft = F /\ fc' = fc` where
   the released one holds `frm0 fc'` and "every f-register except f10 kept".

   The proof is RT_pf_vf.v's vf_icpt_ok with three differences and no new step:
   - no frm0 premise to introduce or to pass on;
   - the post's two FP conjuncts are equalities, carried through unchanged (the Bz walks keep Ft and fc');
   - the twin's copies of released names (snf_file, va_area, args_ok, GLOBALS_TOP, VF_DEPTH) are rewritten to the
     released ones with RT_gxak_eq.v where they meet RT_pf_vf.v's cross-instance lemmas and RT_pf_kit.v's numerals.
   The composition is RT_pf_vf.v's: I_vfprintfw1.v vfprintf_walkA1n, RT_pf_bz.v pcom_call, I_vfprintfw.v
   vfprintf_walkA2, the hypothesis VFB (the twin's guarded body at A_img), I_vfprintfw.v vfprintf_walkB.

   The traps of RT_pf_vf.v's header hold here unchanged: every A_img_vsn fact is rewritten to `asegs` (RT_pf_kit.v
   segs_vsn) before it meets an A_img goal, cell facts stay in their own tree, and the destination's disjunctions are
   hidden from lia behind RT_pf_kit.v's `hid`. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.K Require Import I_vprintfw I_vfprintfw I_vfprintfw1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_pf_Tbl RT_pf_bz.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
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
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_IImgA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_stmt.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GK.G_pop_arg.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.VfprintfCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxak_eq.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_vf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
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
Module RTA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_IImgA.
Module GC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls.
Module PS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_stmt.
Module PK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_kit.
Module GPAK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GK.G_pop_arg.
Module GIFK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_printf_core_common.G_printf_iface.
Module GVFK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXK.G_vfprintf_snf.
Module VFCK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.VfprintfCall.
Module EQ := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxak_eq.
Module PF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_vf.

(* the symbol-map numerals (sym_vf_img, sym_vf_vsn), the FILE-layout crossing (snf_file_eq) and the args_ok crossing
   (args_ok_cross) are RT_pf_vf.v's, used qualified by the alias PF *)
Section VF.
Variable vfb : VFC.vf_guard.
Hypothesis VFB : @VFCK.vfprintf_guarded_stmt RTA.A_img vfb.

Theorem vf_icpt_ok_k : @VFCK.vfprintf_guarded_stmt RTA.A_img_vsn (PS.vf_ready_icpt vfb).
Proof.
  unfold VFCK.vfprintf_guarded_stmt. intros until o. cbv zeta.
  intros -> -> -> FFP FCK FD LJ BY HFb P1 VAA AOK MODEL N0 OM0 HMIN BUFP ST LO GLO QHI SSP MI RDY
    HA HA0 QFP FPCK CKVA CKHI VAHI D0 DHI DD1 DD2.
  (* the twin's copies of released names, rewritten to the released ones (RT_gxak_eq.v) *)
  rewrite EQ.snf_file_eq in FFP. rewrite EQ.va_area_eq in VAA. rewrite EQ.args_ok_eq in AOK.
  rewrite EQ.GLOBALS_TOP_eq in GLO, HA, DD2.
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
  assert (HAz : A + Z.of_nat (length fmt) <= 0x5fc000) by (unfold SPL.zlength in HA; exact HA).
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
  rewrite PF.snf_file_eq in FFP.
  assert (STb : stk asegs m lo q) by exact ST.
  assert (MIb : mem_inv asegs m) by exact (GC.mem_inv_cj_bz m MI).
  assert (SSPi : @GP.ssp_cells RTA.A_img m canary) by exact (PK.ssp_cells_of_vsn m canary SSP).
  unfold GP.ssp_cells in SSPi.
  rewrite PK.got_ssp_val, PK.ssp_guard_val, PK.segs_img in SSPi.
  unfold PF_GOT_SSP, PF_SSP_GUARD in SSPi.
  assert (AOKi : @GIF.G_printf_iface.args_ok RTA.A_img Fp lo 0 CK 16 D (Z.of_nat dn) m lo q lo slots args).
  { apply (PF.args_ok_cross RTA.A_img_vsn RTA.A_img);
      [rewrite PK.segs_vsn, PK.segs_img; reflexivity | exact AOK]. }
  assert (VAb : bytes_at asegs m VA (u64s slots)) by exact VAA.
  (* ---- the interceptor's entry: 0x42228 ---- *)
  rewrite PF.sym_vf_vsn, PK.segs_vsn, ESP.
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
  pose proof PF.sym_vf_img as EVF. unfold PF_MUSL_VFPRINTF in EVF.
  eapply BzE.evt_cut.
  { apply PK.cj_bz_evt. rewrite <- EVF.
    apply (VFB (Z_to_bv 64 PF_RA_VF_REAL) (Z_to_bv 64 (q + -48)) gp tp v0 v1 v2
             (Z_to_bv 64 A) (Z_to_bv 64 Fp) (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 VA)
             a3' d4 d5 d6 d7 (Z_to_bv 64 VA) s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6
             F fc m2 Fp CK D N OM bufp A VA dn junkd fmt slots args lo canary r o).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite EQ.snf_file_eq, PK.segs_img.
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
    - rewrite EQ.va_area_eq. unfold GPA.va_area. rewrite PK.segs_img.
      apply (CJF.bytes_at_transport asegs [(q - (PF_VF_FRAME + PF_PCOM_DEPTH), q)] m m2 _ _ VAA MUfc).
      cbn [CJF.disjoint_from]. split; [right; lia | exact I].
    - rewrite EU48, EQ.args_ok_eq.
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
    - rewrite EU48. unfold GIFK.VF_DEPTH. lia.
    - rewrite EQ.GLOBALS_TOP_eq, PK.globals_top_val. unfold PF_GLOBALS_TOP. lia.
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
    - rewrite EU48. exact (RVFB m2 MUfc WMfc).
    - rewrite EQ.GLOBALS_TOP_eq, PK.globals_top_val. unfold PF_GLOBALS_TOP. exact HA.
    - exact HA0.
    - rewrite EU48. lia.
    - exact FPCK.
    - exact CKVA.
    - exact CKHI.
    - exact VAHI.
    - exact D0.
    - exact DHI.
    - exact DD1.
    - rewrite EQ.GLOBALS_TOP_eq, PK.globals_top_val. unfold PF_GLOBALS_TOP. exact DD2. }
  cbv beta. intros ms4 H4. unfold GVFK.vfprintf_snf_post in H4. rewrite !EU48 in H4.
  (* the twin's post: the FP conjuncts are Ft = F and fc' = fc *)
  destruct H4 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & Ft & fc' & fjunk & m3
                  & -> & MU3 & WM3 & MI3 & EFt & Efc & ST3 & SSP3 & FD3 & FCK3 & FFP3).
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
  unfold GVFK.vfprintf_snf_post. rewrite PK.segs_vsn.
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
  split; [exact EFt|].
  split; [exact Efc|].
  split; [exact (PK.stk_bz_cj m3 lo q ST4)|].
  split; [exact (PK.ssp_cells_to_vsn m3 canary SSP3)|].
  split; [exact FD3|].
  split; [exact FCK3 | exact FFP3].
Qed.

End VF.
