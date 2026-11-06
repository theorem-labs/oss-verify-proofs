(* Image B twin of lib/A/RT_pf_vsn.v at d49bd1db505: module paths lib.A -> lib.B; 11 image numerals moved to fuzz_reply.asan-ubsan by symbol + offset, each checked against that image (CHAINB-numerals.tsv sha256 3cedf5e564f7; internal record). *) (* SNP-ROUTE SCRATCH: THIS COPY COMPILES (rc=0). Four
   changes against a working branch 9067b7156f9, all in the back half or at its seam, none to a statement:
   (1) premise 23 (`65536 <= A`, from HA0) gets its original lia bullet back in place of the `fail`;
   (2) GXA's post facts MI2 ST2 WM2 DST2 are crossed from A_img_vsn to A_img by rewriting (PK.segs_vsn, then
       <- PK.segs_img) right after the destruct: without it line 244's `exact (GC.mem_inv_cj_bz m2 MI2)` makes Coq
       compare the two RImg records and does not terminate (the hang UnionRehearse measured);
   (3) ERET is stated at CJ's ret_pc (lib/CJ/Lib/MState.v:167), not Bz's (lib/A/Bz/Lib/MState.v:153): the post
       GXA returns names CJ's, so `rewrite ERET` found no subterm;
   (4) the two Bz rw_cells_transport side conditions (FRt2, FRb2) take DSEP's disjunction by destruct: Bz's
       disjoint_from puts the two sides in the other order, so `exact (DSEP ..)` did not type-check.
   The header below is the pf-chain's and is out of date where it says the file does not compile. *)
(* STATE, 15:2xZ 2026-10-29: THIS FILE DOES NOT COMPILE, AND IT FAILS FAST ON PURPOSE: a `fail` replaces the premise-23
   bullet of the GXA application, because with premises 23-29 and the back half in place the file did not terminate
   (UnionRehearse: 6816 s and 6452 s in two union builds) and hung every union build.  The part left is NAMED here.
   WHAT IS MEASURED CLEAN, each by cutting the proof at that point and building (rc=0):
     - the front: the trampoline, the frame, TryAsanInitFromRtl, printf_common through RT_pf_bz.v pcom_call, and
       all the premise transports, including the stack-protector crossing   11-18 s
     - GXA's vsnprintf_x applied, with every premise admitted                24 s
     - the same with all 29 premises really proved                          ~24 s (the bullets below)
   WHAT IS LEFT: everything after `cbv beta. intros ms2 H2.` - destructuring GXA's post, the Bz walk of the output
   check (vsnprintf_walkCm) and the final assembly - has NEVER been exercised, and with the bullets passing the
   build no longer terminates.  It is the same disease the front already cured three times, and the cure is known:
     1. every segs that reaches a Bz lemma must be the CONSTANT `asegs`, never `img_segs A_img(_vsn)` - two
        projections of different records with one head are what Coq cannot decide (see RT_pf_kit.v's header);
     2. cross instances only with RT_pf_kit.v's explicit lemmas (ssp_cells_of_vsn, args_ok_cross, cj_bz_evt_segs);
     3. never let `lia` see the destination's separation disjunctions - they are hidden behind `hid`, and
        `unfold .. in *` UNHIDES them (measured: 24 s -> over 520 s).
   The post built at the end is at A_img while GXA's post is at A_img_vsn: build it component by component, each
   component crossed explicitly, and never by `exact` on the whole post.
   The three Qed pieces of this chain - RT_pf_snf.v snprintf_icpt_ok, RT_pf_vf.v vf_icpt_ok, RT_pf_vsn_body.v
   vsnprintf_icpt_ok_body - do NOT depend on this file, and neither does RT_pf_stmt.v or RT_pf_kit.v. *)

(* ___interceptor_vsnprintf at fuzz_reply.asan-ubsan: RT_pf_stmt.v vsnprintf_icpt_stmt, assembled from pieces that are
   already proved - no function is walked here:
   - R4Printf's RELOCATED Bz walks (a working branch 5247aa4d0b9, lib/A/Bz/K/I_vsnprintfw.v): vsnprintf_walkAc
     (the trampoline 0x4222c, the frame, TryAsanInitFromRtl, printf_common, to the REAL(vsnprintf) call) and
     vsnprintf_walkCm (the output's write check after it, and the return);
   - RT_pf_bz.v pcom_call, printf_common from R4's relocated pcom_genx_spec;
   - GXA's vsnprintf_x at the second instance A_img_vsn, as the REAL(vsnprintf) call (the Section hypothesis VSNX);
   - the Bz <-> CJ vocabulary bridge RT_gxa_calls.v (R4Printf; a Theorem Labs lane relocated exactly these lemmas as
     FMgxa_bzcj.v, a working branch 534b701a600, whose own header names this file as their source), with
     the CJ -> Bz direction of msteps added below because neither copy had it.

   PERFORMANCE, measured here the hard way (one compile ran 40 min and was killed): `lia` with a DISJUNCTIVE
   hypothesis in context splits on it, and this statement carries two (the destination's separation premises), so
   every arithmetic side condition of a `rewrite ... by lia` paid for the split.  The two are hidden behind `hid`
   right after intros, and the one consequence the proof needs is derived once as DSEP; the unsigned-literal
   equations are proved once (EUq, EU2160) and used as rewrites with no side condition. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require Import R_isPoisoned.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.K Require Import I_vprintfw I_vfprintfw I_vsnprintfw I_snprintfw.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_pf_Tbl RT_pf_bz.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pad.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vsnprintf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_IImgA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_stmt.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec.Prelim.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.MState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
Module CJE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Exec.
Module CJR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Module GP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pad.
Module GIF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.
Module GVF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_vfprintf_snf.
Module VFC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Module GVS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vsnprintf.
Module RTA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_IImgA.
Module GC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls.
Module PS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_stmt.
Module PK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_kit.
Module SPL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec.Prelim.
Module CJF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Module CJS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.
Module CJM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
(* the instance crossings and the value lemmas are used qualified, as PK.* *)
Ltac hide H := PK.hide H.
Ltac show H := PK.show H.
Notation cj_bz_evt := PK.cj_bz_evt (only parsing).
Notation pf_evt_fwd := PK.pf_evt_fwd (only parsing).
(* the instance crossings and the value lemmas are used qualified, as PK.* *)


Section Icpt.
Variable set_ready : mem -> Z -> Z -> Z -> Prop.
Variable vf_ready : VFC.vf_guard.
Hypothesis VSNX : @GVS.vsnprintf_x_stmt RTA.A_img_vsn set_ready vf_ready.

Theorem vsnprintf_icpt_ok : PS.vsnprintf_icpt_stmt set_ready vf_ready PF_WRAP_VSNPRINTF.
Proof.
  unfold PS.vsnprintf_icpt_stmt. intros until o. cbv zeta.
  intros -> -> -> -> DST HDN BY HF P1 VAA AOK MODEL R0 R31 Hn ST LO GLO LOLO QHI Q16 SSP MI FRM HA HA0 QVA VAHI
    D0 DHI DMH DD1 DD2 CELLS PCOM READY NE.
  pose proof PK.globals_top_val as EGT.
  set (q := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RQ. unfold bv_modulus in RQ.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in RQ. fold q in RQ.
  unfold PS.VSNI_DEPTH, PF_VSN_FRAME, PF_TRYINIT, GVS.VSN_DEPTH in *.
  rewrite EGT in GLO, HA, DD2.
  unfold R_m2s.kHighShadowEnd in LOLO.
  pose proof (u64s_length slots) as LU. unfold SPL.zlength in *.
  (* the destination's separation, once; then the two disjunctions leave lia's view *)
  assert (DSEP : forall x y, lo <= x -> y <= q -> D + Z.of_nat dn <= x \/ y <= D)
    by (intros x y Hx Hy; destruct DD1 as [E|E]; [left; lia | right; lia]).
  hide DD1. hide DD2.
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (q + -2160)) = q - 2160) by (rewrite unsigned_lit by lia; lia).
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (sni_cells_walk m CELLS) as (VSNPF & VSNC).
  assert (MIb : mem_inv asegs m) by exact (GC.mem_inv_cj_bz m MI).
  assert (STb : stk asegs m lo q) by exact ST.
  rewrite ESP. unfold PF_WRAP_VSNPRINTF.
  apply GC.bz_cj_evt.
  (* --- the interceptor's front, through printf_common, to the REAL(vsnprintf) call --- *)
  eapply BzE.evt_cut.
  { apply (vsnprintf_walkAc q lo); [exact STb | lia | lia | lia | exact VSNPF | exact VSNC | exact MIb |].
    intros m1 u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MU1 WM1 MI1b ST1b.
    pose proof (GC.mem_inv_bz_cj m1 MI1b) as MI1.
    assert (VAA1 : bytes_at asegs m1 VA (u64s slots)).
    { apply (bytes_at_transport asegs [(q - 2176, q)] m m1 VA (u64s slots) (PK.bya_cj_bz _ _ _ VAA) MU1).
      cbn [disjoint_from]. rewrite LU. split; [lia | exact I]. }
    apply (pcom_call A VA lo (Z_to_bv 64 0x465b0) (Z_to_bv 64 (q + -2160)) gp tp u0 u1 u2 (Z_to_bv 64 q)
             (Z_to_bv 64 A) (Z_to_bv 64 0x17944) (Z_to_bv 64 A) (Z_to_bv 64 VA) b3 b4 b5 b6 b7
             (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 0x138168) s5 s6 s7 s8 s9 s10 s11
             u3 u4 u5 u6 F fc m1);
      [ reflexivity | reflexivity | rewrite EU2160; exact ST1b | rewrite EU2160; lia
      | unfold R_m2s.kHighShadowEnd; lia | rewrite EU2160; lia
      | rewrite EU2160; Z.div_mod_to_equations; lia
      | rewrite EU2160; replace (q + -2160) with (q - 2160) by lia;
        exact (PCOM m1 (PK.munch_bz_cj _ _ _ MU1) (PK.wmono_bz_cj _ _ WM1) MI1 (PK.bya_bz_cj _ _ _ VAA1))
      | exact MI1b ]. }
  intros ms1 H1. unfold vsnprintf_at_call in H1.
  destruct H1 as (m1 & u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & j8 & junk & -> & MU1 & WM1 & MI1b
                  & ST1b & FRt1 & FRb1).
  pose proof (GC.mem_inv_bz_cj m1 MI1b) as MI1.
  assert (MUwb : munch [(lo, q); (D, D + Z.of_nat dn)] m m1).
  { apply (munch_weaken [(q - 4480, q)]); [| exact MU1].
    unfold sub_fp. cbn [outside]. intros x (Hx & _). split; [lia | exact I]. }
  pose proof (PK.munch_bz_cj _ _ _ MUwb) as MUw.
  pose proof DST as DST1.
  eapply CJF.rw_cells_transport in DST1;
    [ | exact (PK.munch_bz_cj _ _ _ MU1) | exact (PK.wmono_bz_cj _ _ WM1) | ].
  2:{ cbn. rewrite ?Nat.add_0_r. split; [| exact I]. exact (DSEP (q - 4480) q ltac:(lia) ltac:(lia)). }
  assert (BY1 : bytes_at asegs m1 A (G_fmt_fp_lib.zb fmt)).
  { apply (bytes_at_transport asegs [(q - 4480, q)] m m1 A _ (PK.bya_cj_bz _ _ _ BY) MU1).
    cbn [disjoint_from]. unfold G_fmt_fp_lib.zb. rewrite length_map. split; [lia | exact I]. }
  assert (VAA1 : bytes_at asegs m1 VA (u64s slots)).
  { apply (bytes_at_transport asegs [(q - 4480, q)] m m1 VA (u64s slots) (PK.bya_cj_bz _ _ _ VAA) MU1).
    cbn [disjoint_from]. rewrite LU. split; [lia | exact I]. }
  assert (AOK1 : @GIF.G_printf_iface.args_ok RTA.A_img lo lo 0 lo 0 D (Z.of_nat dn) m1 lo (q + -2160) lo slots args).
  { eapply GVF.args_ok_rebase; [exact AOK | | lia | right; reflexivity | right; split; reflexivity
                               | right; split; reflexivity | right; reflexivity].
    apply PK.munch_bz_cj. apply (munch_weaken [(q - 4480, q)]); [| exact MU1].
    unfold sub_fp. cbn [outside]. intros x (Hx & _ & _ & _). split; [lia | exact I]. }
  (* the stack-protector cells, crossed to A_img_vsn by RT_pf_kit.v's rewriting form, never by conversion *)
  assert (SSP1 : @GP.ssp_cells RTA.A_img_vsn m1 canary).
  { apply PK.ssp_cells_to_vsn. destruct SSP as [S1 S2].
    rewrite PK.got_ssp_val, PK.ssp_guard_val, PK.segs_img in S1.
    rewrite PK.ssp_guard_val, PK.segs_img in S2.
    unfold GP.ssp_cells. rewrite PK.got_ssp_val, PK.ssp_guard_val, PK.segs_img.
    unfold PF_GOT_SSP, PF_SSP_GUARD in S1, S2 |- *.
    split.
    - eapply CJF.rw_cells_transport;
        [ exact S1 | exact (PK.munch_bz_cj _ _ _ MU1) | exact (PK.wmono_bz_cj _ _ WM1) | ].
      cbn. split; [lia | exact I].
    - eapply CJF.rw_cells_transport;
        [ exact S2 | exact (PK.munch_bz_cj _ _ _ MU1) | exact (PK.wmono_bz_cj _ _ WM1) | ].
      cbn. split; [lia | exact I]. }
  assert (WM1' : CJF.wmono (@CJR.img_segs RTA.A_img) m m1) by exact (PK.wmono_bz_cj _ _ WM1).
  destruct (READY m1 MUw WM1') as (RDY1 & _ & _).
  (* --- GXA's vsnprintf_x: the REAL(vsnprintf) call ---
     MEASURED: a `first [ ... ]` over these premises does NOT terminate in 25 min.  Each failing alternative makes
     Coq try to unify a term at A_img with the goal's at A_img_vsn, and those two records are not convertible (the
     symbol maps differ at 0x7f000400), so every attempt walks the maps.  One `exact` per premise, in order, is
     directed and cheap. *)
  assert (ESYM : @CJR.sym RTA.A_img_vsn 0x7f000200 = PF_MUSL_VSNPRINTF) by (vm_compute; reflexivity).
  assert (EGTV : @GIF.G_printf_iface.GLOBALS_TOP RTA.A_img_vsn = PF_GLOBALS_TOP) by (vm_compute; reflexivity).
  show DD2.
  (* MEASURED: every premise below that carries a segment list must be handed over with its segs written as the
     Bz tree's constant `asegs`, never as `img_segs A_img`: against the goal's `img_segs A_img_vsn` the shared head
     makes Coq unify the two RECORDS, and the 29 premises then do not finish in 500 s while the bare apply takes
     24 s.  Normalise them once, here. *)
  rewrite PK.segs_img in DST1, MI1.
  assert (BY1c : CJM.bytes_at asegs m1 A (G_fmt_fp_lib.zb fmt))
    by (pose proof (PK.bya_bz_cj _ _ _ BY1) as H'; rewrite PK.segs_img in H'; exact H').
  assert (VAA1c : CJM.bytes_at asegs m1 VA (u64s slots))
    by (pose proof (PK.bya_bz_cj _ _ _ VAA1) as H'; rewrite PK.segs_img in H'; exact H').
  assert (ST1cj : CJF.stk asegs m1 lo (q - 2160)).
  { pose proof (PK.stk_bz_cj _ _ _ ST1b) as H'. rewrite PK.segs_img in H'.
    replace (q - 2160) with (q + -2160) by lia. exact H'. }
  assert (SSP1c : @GP.ssp_cells RTA.A_img_vsn m1 canary) by exact SSP1.
  eapply BzE.evt_cut.
  { (* MEASURED: crossing to CJ at A_img here makes the apply below compare the two RECORDS and it does not
       finish in 400 s even with every premise admitted.  Cross at `asegs` instead - a constant, so the
       comparison with A_img_vsn's projection is one reduction. *)
    apply (PK.cj_bz_evt_segs asegs). unfold PF_MUSL_VSNPRINTF in ESYM. rewrite <- ESYM.
    apply (VSNX (Z_to_bv 64 0x465cc) (Z_to_bv 64 (q + -2160)) gp tp u0 u1 u2 (Z_to_bv 64 q) (Z_to_bv 64 A)
             (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 VA) b4 b5 b6 b7
             (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 0x138168) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
             F fc m1 D n A VA dn junkd fmt slots args lo canary r o).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact DST1.
    - exact HDN.
    - exact BY1c.
    - exact HF.
    - exact P1.
    - exact VAA1c.
    - rewrite EU2160. replace (q - 2160) with (q + -2160) by lia.
      exact (PK.args_ok_cross _ _ PK.segs_img_vsn _ _ _ _ _ _ _ _ _ _ _ _ _ AOK1).
    - exact MODEL.
    - clear - RQ LO LOLO QHI Q16 QVA VAHI D0 DHI DMH Hn R0 R31 HDN LU HA HA0 GLO; unfold SPL.zlength; cbn [length]; lia.
    - rewrite EU2160. exact ST1cj.
    - rewrite EU2160. unfold GVS.VSN_DEPTH. lia.
    - exact GLO.
    - rewrite EU2160. clear - RQ LO LOLO QHI Q16 QVA VAHI D0 DHI DMH Hn R0 R31 HDN LU HA HA0 GLO; unfold SPL.zlength; cbn [length]; lia.
    - exact SSP1.
    - exact MI1.
    - exact FRM.
    - rewrite EU2160. exact RDY1.
    - rewrite EGTV. unfold SPL.zlength. exact HA.
    - clear - RQ LO LOLO QHI Q16 QVA VAHI D0 DHI DMH Hn R0 R31 HDN LU HA HA0 GLO; unfold SPL.zlength; cbn [length]; lia.
    - rewrite EU2160. clear - RQ LO LOLO QHI Q16 QVA VAHI D0 DHI DMH Hn R0 R31 HDN LU HA HA0 GLO; unfold SPL.zlength; cbn [length]; lia.
    - clear - RQ LO LOLO QHI Q16 QVA VAHI D0 DHI DMH Hn R0 R31 HDN LU HA HA0 GLO; unfold SPL.zlength; cbn [length]; lia.
    - clear - RQ LO LOLO QHI Q16 QVA VAHI D0 DHI DMH Hn R0 R31 HDN LU HA HA0 GLO; unfold SPL.zlength; cbn [length]; lia.
    - clear - RQ LO LOLO QHI Q16 QVA VAHI D0 DHI DMH Hn R0 R31 HDN LU HA HA0 GLO; unfold SPL.zlength; cbn [length]; lia.
    - exact DD1.
    - rewrite EGTV. unfold PF_GLOBALS_TOP. exact DD2. }
  hide DD2.
  cbv beta. intros ms2 H2. unfold GVS.vsnprintf_x_post in H2. rewrite !EU2160 in H2.
  destruct H2 as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & Ft & fc' & m2
                  & -> & MU2 & WM2 & MI2 & FRM' & FOK & ST2 & SSP2 & DST2).
  (* SNP-ROUTE experiment: cross GXA's post from A_img_vsn to A_img by rewriting, never by conversion *)
  rewrite PK.segs_vsn in MI2, ST2, WM2, DST2.
  rewrite <- PK.segs_img in MI2, ST2, WM2, DST2.
  assert (MI2b : mem_inv asegs m2) by exact (GC.mem_inv_cj_bz m2 MI2).
  assert (ERET : OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.MState.ret_pc (Z_to_bv 64 0x465cc) = Z_to_bv 64 0x465cc)
    by (apply OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.MState.ret_pc_even; [lia | reflexivity]).
  rewrite ERET.
  assert (FRt2 : rw_cells asegs m2 (q + -96)
            [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1;
             C8 s0; C8 ra]).
  { apply (rw_cells_transport asegs [(lo, q + -2160); (D, D + Z.of_nat dn)] m1 m2 _ _ FRt1
             (PK.munch_cj_bz _ _ _ MU2) (PK.wmono_cj_bz _ _ WM2)).
    cbn [disjoint_from cells_size csize Nat.add]. split; [lia | split; [| exact I]].
    destruct (DSEP (q + -96) q ltac:(lia) ltac:(lia)) as [EDS|EDS]; [right | left]; lia. }
  assert (FRb2 : rw_cells asegs m2 (q + -2160) [CB 2064 junk]).
  { apply (rw_cells_transport asegs [(lo, q + -2160); (D, D + Z.of_nat dn)] m1 m2 _ _ FRb1
             (PK.munch_cj_bz _ _ _ MU2) (PK.wmono_cj_bz _ _ WM2)).
    cbn [disjoint_from cells_size csize Nat.add]. split; [lia | split; [| exact I]].
    destruct (DSEP (q + -2160) q ltac:(lia) ltac:(lia)) as [EDS|EDS]; [right | left]; lia. }
  assert (MU02 : CJF.munch [(lo, q); (D, D + Z.of_nat dn)] m m2).
  { apply PK.munch_bz_cj. apply (munch_trans [(lo, q); (D, D + Z.of_nat dn)] m m1 m2); [exact MUwb|].
    apply (munch_weaken [(lo, q + -2160); (D, D + Z.of_nat dn)]); [| exact (PK.munch_cj_bz _ _ _ MU2)].
    unfold sub_fp. cbn [outside]. intros x (Hx & Hy & _). split; [lia | split; [lia | exact I]]. }
  destruct (READY m2 MU02 (CJF.wmono_trans (@CJR.img_segs RTA.A_img) m m1 m2 WM1' WM2))
    as (_ & M2S2 & CHK2).
  (* --- the write check and the return --- *)
  eapply BzE.evt_cut.
  { apply (vsnprintf_walkCm rip_proof q D n r lo j8 junk (Z_to_bv 64 0x465cc) ra gp tp v0 v1 v2 s0 s1
             (Z_to_bv 64 A) s2 s3 s4 s5 s6 s7 (Z_to_bv 64 0x138168) s5 s6 s7 s8 s9 s10 s11 c1 c2 c3 c4 c5 c6 c7
             v3 v4 v5 v6 (Z_to_bv 64 VA) Ft fc' m2);
      [ exact (PK.stk_cj_bz _ _ _ ST2) | lia | unfold R_m2s.kHighShadowEnd; lia | lia | exact FRt2 | exact FRb2
      | lia | lia | lia | lia | lia | exact CHK2 | exact M2S2 | exact MI2b ]. }
  cbv beta. intros ms3 H3. unfold vsnprintf_ret in H3.
  destruct H3 as (m3 & w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6
                  & -> & MU3 & WM3 & MI3b & ST3).
  apply BzE.evt_done.
  unfold GVS.vsnprintf_x_post.
  exists w0, w1, w2, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, Ft, fc', m3.
  rewrite EUq.
  split; [reflexivity|].
  split.
  { apply (CJF.munch_trans [(lo, q); (D, D + Z.of_nat dn)] m m2 m3).
    - apply (CJF.munch_trans [(lo, q); (D, D + Z.of_nat dn)] m m1 m2); [exact MUw|].
      apply (CJF.munch_weaken [(lo, q + -2160); (D, D + Z.of_nat dn)]); [| exact MU2].
      unfold CJF.sub_fp. cbn [CJF.outside]. intros x (Hx & Hy & _). split; [lia | split; [lia | exact I]].
    - apply PK.munch_bz_cj. apply (munch_weaken [(q - 2240, q)]); [| exact MU3].
      unfold sub_fp. cbn [outside]. intros x (Hx & _). split; [lia | exact I]. }
  split; [exact (CJF.wmono_trans _ m m2 m3 (CJF.wmono_trans _ m m1 m2 (PK.wmono_bz_cj _ _ WM1) WM2)
                   (PK.wmono_bz_cj _ _ WM3))|].
  split; [exact (GC.mem_inv_bz_cj m3 MI3b)|].
  split; [exact FRM'|].
  split; [exact FOK|].
  split; [exact (PK.stk_bz_cj _ _ _ ST3)|].
  split.
  { apply PK.ssp_cells_of_vsn. destruct SSP2 as [S1 S2].
    rewrite PK.got_ssp_val_vsn, PK.ssp_guard_val_vsn, PK.segs_vsn in S1.
    rewrite PK.ssp_guard_val_vsn, PK.segs_vsn in S2.
    unfold GP.ssp_cells. rewrite PK.got_ssp_val_vsn, PK.ssp_guard_val_vsn, PK.segs_vsn.
    unfold PF_GOT_SSP, PF_SSP_GUARD in S1, S2 |- *.
    split.
    - eapply CJF.rw_cells_transport;
        [ exact S1 | exact (PK.munch_bz_cj _ _ _ MU3) | exact (PK.wmono_bz_cj _ _ WM3) | ].
      cbn. split; [lia | exact I].
    - eapply CJF.rw_cells_transport;
        [ exact S2 | exact (PK.munch_bz_cj _ _ _ MU3) | exact (PK.wmono_bz_cj _ _ WM3) | ].
      cbn. split; [lia | exact I]. }
  eapply CJF.rw_cells_transport;
    [ exact DST2 | exact (PK.munch_bz_cj _ _ _ MU3) | exact (PK.wmono_bz_cj _ _ WM3) | ].
  cbn. rewrite ?Nat.add_0_r. split; [| exact I].
  exact (DSEP (q - 2240) q ltac:(lia) ltac:(lia)).
Qed.

(* The same statement entered at the BODY 0x46538 - where ___interceptor_snprintf calls it, jumping past the
   trampoline - is one step forward from here (RT_pf_kit.v pf_evt_fwd with I_snprintfw.v:81 vsn_tramp_mstep, turning
   on the statement's premise `ret_pc ra <> __wrap_vsnprintf`).  It is a Theorem Labs lane's, in lib/B/RT_pf_vsn_body.v. *)

End Icpt.

