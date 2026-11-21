(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the stack floor rt_sp0 - STACK_SPAN, the span the start state guarantees writable, in TCTX, TRET, TCTX_agree and TCTX_agree_nw; the recorded proofs of TCTX_agree and TCTX_agree_nw replaced by plain proofs after leptonica/bilateral_fuzzer's text for the same driver). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx D_rlkit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_D_trdefs () := "C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_assocC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib5Lists7ListDef6repeatK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes7nat_indC69OSSVerify5KrLib2K54Spec5Canon9zeros_outC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatI47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K69OSSVerify5KrLib2K54Spec5Stdio9stdout_st01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238D_trdefs>zeros_out_snocC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib2K54Spec5Stdio8so_firstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio6so_bufC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8so_linesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface:emit0_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes4bool00I69OSSVerify5KrLib2K54Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib2K53B238D_trdefs8tr_frameC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K53B235D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K53B235D_kit9agree_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit>rw_cells_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53B235D_kitArw_cells_agree_nwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface3rtsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238D_trdefs4TCTXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs3CLXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs:main_frameC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53B238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K53B238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238D_trdefs7tr_liveC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53B238RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C69OSSVerify5KrLib2K53B237D_rlkit@main_frame_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238D_trdefs>tr_frame_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit>bytes_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs8TR_EMPTYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib2K53B237D_rlkitCmain_frame_agree_nwC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238D_trdefsAtr_frame_agree_nwC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9in_rangesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K53B235D_clxIoutside_of_not_in_ranges'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs8drv_cellC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib2K53B235D_clxCclient_static_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib2K53B235D_clxHnot_in_ranges_of_outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit>agree_of_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_clx7LIB_imgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_clx?drv_cell_staticC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2or00C69OSSVerify5KrLib2K53B235D_kit>ro_cells_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit9stk_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53B237D_iface9SSP_GUARDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs7ERRNO_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236Layout<g_read_stageC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53B23:D_libiface6LIB_FPC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Definition e_target_run : Z := 0xf9de4.
Definition e_emit : Z := 0xf9f70.
(* [comment removed for export] *)
Definition TR_M2 : Z := -2.   (* [comment removed for export] *)
Definition TR_M1 : Z := -1.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition tr_calls (L : Z) (c0 : byte) : Z := if L =? 0 then 1 else Z.land (bv_unsigned c0) 3 + 1.

(* [comment removed for export] *)
Definition tr_frame (m : word -> option byte) (sp : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 : word) : Prop :=
  exists junk, rw_cells asegs m (sp - 80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition tr_latch_hyp (XENV : mem -> Prop) (XENV_FP : list (Z * Z)) : Prop :=
  forall (tsp lo : Z) (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  XENV m -> ro_cells asegs m GOT_LLVMINIT [C8 (Z_to_bv 64 0)] ->
  stk asegs m lo tsp -> lo <= tsp - 48 -> SEGTOP_A <= lo -> tsp < 2^47 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (ra' a0' a1' a2' a3' : word) (m' : mem) (Wx : list (Z * Z)),
    ms' = MS (mkR ra' (Z_to_bv 64 tsp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 a0 (Z_to_bv 64 TR_INIT)
                  s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xf9e2c) fc None m' (seg_rom asegs)
    /\ XENV m' /\ (forall x, in_ranges Wx x -> in_ranges XENV_FP x)
    /\ munch ((tsp - 48, tsp) :: Wx) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo tsp)
    (MS (mkR ra (Z_to_bv 64 tsp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 TR_INIT)
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xf9e20) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition tr_incb_hyp (XENV : mem -> Prop) (XENV_FP : list (Z * Z)) : Prop :=
  (forall m, XENV m -> rw_cells asegs m TR_INCB [C1 (Z_to_bv 8 0)])
  /\ (forall m m', XENV m -> (forall a : word, in_ranges XENV_FP (bv_unsigned a) -> ~ (TR_INCB <= bv_unsigned a < TR_INCB + 1) -> m' a = m a) ->
                   rw_cells asegs m' TR_INCB [C1 (Z_to_bv 8 0)] -> XENV m')
  /\ (forall x, TR_INCB <= x < TR_INCB + 1 -> in_ranges XENV_FP x).

(* [comment removed for export] *)
Definition tr_live (plen owned buf cap : Z) : list (Z * Z) := (if plen =? 0 then [] else [(owned, plen)]) ++ [(buf, cap)].

Lemma zeros_out_snoc : forall k, zeros_out k ++ [48; 10] = zeros_out (S k).
Proof.
ltac2:(KReplay.run1 (kr_t_D_trdefs ()) [] "h01kh11lh22IHp;1p;3p;2p;6p;4p-1g0000R0p4p710p8g000MR1p4p710g000kR2p4p710p8g001Gj1BTg001gj1:Tg002Lj13Tg0031j18Tg003Oj1ATg003oj37Tg004Oj32Tg004nj14Tg005Mj35Tg005gj26Tg006Aj6;TP1j4@TP2j6?Tg006_j4=Tg007@j19Tg008<j2<TP0j3>Tg008WR0f0R2'<p=1f1R1=>02p=0g0095R3%B0R4g009TR5#:#3#3#3#3#8%35#:#3#8%A0570570R5=242#1/05%42R69245#135R7X03g00:9#49245#1,64P4A2451#1R8/05R9,05f2#49245#1,05R:9542X14P4%419245#1R11052=54:X141051,64P9P2E;1058/05P0P5P8P5C@E?X27X03P2C=%92/05%96554eW0o"). Qed.

Lemma emit0_next_lines : forall j, emit0_next (so_lines j) = so_lines (S j).
Proof.
ltac2:(KReplay.run1 (kr_t_D_trdefs ()) [] "h01jp;1p;3p;2p;8p;4g007@j14Tg001gj1;Tg002Lj10Tg0031j15Tg003Oj1GTg003oj31Tg0000j39Tg00:Xj3:j28j1=j4ATg001Gj1@Tg004Oj3?Tg008<j2>Tg005gj2<Tg00;Vj1FTg00<Yj83Tg00=6j1ETg00>1j1DTg004nj1CTg005Mj37Tg00>jj16Tg00?gj1BTg00@fR0f0R1g00AFR2P2CAp=2g0095g00AfR3g00BFR4g008WR5%41R6g009TR7#;#0#0#0#0#5R8%07#;#0#5R7%G5515515R939R:=:02%@5R;??91,>591579158R8=:02P2P2P3P4\3R7180:1808P2P2P;P7\3R7%=0R0P0P:P8P7\;/<0%F1G31<32R2G3P2G3P3P4%26R6#Eg00:9#4#2%D6=959#2n0100000020000%C1R9#4#2574e%61#B%69574eW0o"). Qed.

Lemma emit0_out_lines : forall j, emit0_out (so_lines j) = [].
Proof.
ltac2:(KReplay.run1 (kr_t_D_trdefs ()) [] "h01jp;1p;2g001Gj12Tg003Oj11Tg005gj20Tg0095g008WR0#2%10'0W0o"). Qed.

Section TrDefs.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIB : mem -> Prop.
Variable fs : Fs.

(* [comment removed for export] *)
Definition TCTX (Σ : rts RT) (so : stdout_st) (usp buf cap plen d owned : Z) (payload : list byte)
    (c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 : word) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ CLX OUT_rep ERR_rep XENV LIB so m
  /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7 /\ tr_frame m (usp - 80) (Z_to_bv 64 0xf9c84) x0 x1 x2 x3 x4 x5 x6 x7
  /\ stk asegs m (rt_sp0 RT Σ - STACK_SPAN) (usp - 160)
  /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_SPAN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
  /\ rt_live RT Σ = tr_live plen owned buf cap /\ rt_frames RT Σ = []
  /\ plen = Z.of_nat (length payload) /\ plen < 2^26 /\ bytes_at asegs m d payload
  /\ (plen = 0 -> d = TR_EMPTY /\ owned = 0) /\ (0 < plen -> d = owned) /\ 0 < cap <= 67108864 (* [comment removed for export] *) /\ usp + 16 <= USTACK_TOP.

(* [comment removed for export] *)
Definition TLOOP (k : Z) (so : stdout_st) (usp buf cap : Z) (x0 x1 x2 x3 x4 x5 x6 x7 : word) (c : config) : Prop :=
  exists (Σ : rts RT) (plen d owned : Z) (payload : list byte)
         (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (entry_st ra (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 d)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_INIT) (Z_to_bv 64 k) (Z_to_bv 64 0) (Z_to_bv 64 TR_M2)
             s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xf9ea0 m)) c
    /\ TCTX Σ so usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m
    /\ 1 <= k <= 4 /\ k * FUZZ_COST <= rt_credit RT Σ.

(* [comment removed for export] *)
Definition TFREE (so : stdout_st) (usp buf cap : Z) (x0 x1 x2 x3 x4 x5 x6 x7 : word) (c : config) : Prop :=
  exists (Σ : rts RT) (plen d owned : Z) (payload : list byte)
         (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (entry_st (Z_to_bv 64 0xf9ee0) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 d)
             (Z_to_bv 64 owned) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_INIT) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 TR_M2)
             s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m)) c
    /\ TCTX Σ so usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m.

(* [comment removed for export] *)
Definition TRET (so : stdout_st) (usp buf cap : Z) (x0 x1 x2 x3 x4 x5 : word) (c : config) : Prop :=
  exists (Σ : rts RT) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (MS (mkR (Z_to_bv 64 0xf9c84) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1 (Z_to_bv 64 0)
                   a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0xf9c84) fc None m (seg_rom asegs))) c
    /\ ART RT Σ m /\ mem_inv asegs m /\ CLX OUT_rep ERR_rep XENV LIB so m
    /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7 /\ stk asegs m (rt_sp0 RT Σ - STACK_SPAN) (usp - 80)
    /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_SPAN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
    /\ rt_live RT Σ = [(buf, cap)] /\ rt_frames RT Σ = [] /\ usp + 16 <= USTACK_TOP.

End TrDefs.

Section TrTransport.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIB : mem -> Prop.
Hypothesis AF : art_facts RT.

Lemma tr_frame_agree : forall m m' sp ra x0 x1 x2 x3 x4 x5 x6 x7, tr_frame m sp ra x0 x1 x2 x3 x4 x5 x6 x7 ->
  agree_on (fun x => sp - 80 <= x < sp) m m' -> wmono asegs m m' -> tr_frame m' sp ra x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
ltac2:(KReplay.run1 (kr_t_D_trdefs ()) ["TrTransport"] "p'0h01xi001xh14junkh24__x1h34__x2h41mh52AGh62FRh71Hh82Hxh93Hx0h:2WMh;7__arithh<4__ffh=8__varmaph>5__with?2m'h@1nhA2rahB2sphC2x0hD2x1hE2x2hF2x3hG2x4hH2x5hI2x6hJ2x7hK1yp;1p;;p;2p;4p;3p;<p;6p;8p;Bp;7g002Lj12Tg00CDj1NTg00Cbj1FTg00DEj1XTg00Dgl;LTg001Gj1JTg001gj1_Tg0031j1[Tg00Edj23Tg00FAj2<Tg00G9j11Tg003Oj1CTg00H1j4=Tg00Hjj27Tg00IFj3ITg00J@j3GTg00K7j1\Tg00L3R0j1>Tg00LSR1j28Tg00M0R2j2:Tg00MLj2ETg00Mgj1HTg005gj29Tg00NEj4ZTg00Nhl<VTg00OMj6UTg00P6j4RTg00P]j2QTg00Q;j1PTg00QYj4OTg00R7j1STg00RUj1TTg00S@j2MTg00Scj2nTg00TFj3mTg00Tij4ATg00UTj3lTg00V7j1kTg00VYj8jTg00W=j2gTg00W_j2fTg005Mj3eTg00XKj3cTg00Xjj4bTg00Y\j6aTg00ZWj8`Tg00[Wj4dTg004nj10Tg003oj36Tg00\1l<^Tg00\VlBhTg00]<j7]Tg00]`j7iTf0R3#0#0#0#0#0#0#0#0p=Dg00^DR4f2R5f1R6=64336p=Bf4R7f3R8A64639645564564p=41:63,E5p=5A6463p=?%03#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=;g0095R9g008WR:P:P:P0P0f5R0P7P8P5P6P3M<^p=YP:P:P:P:P:P:P1P3P6P5P1P8P7P0f6R1f7R;f8R<f9R=MBhp=WP6g00_<R>g00_[R?P?g00`;R@P3g00`[F]p=@P5P>P?P?P@P6P3Fip=Kg009TRA#2RB#2#2RC#2#2#2#N#FRD%NC#FRC#X[REf;RFP=P<P;P1P0P7P8P5P6P3M;Lg00a;%JCRCg00aURGf=RH%_B#2#2#2#2#[RI,3Fg00:9#DRJ/<3RK%15%18%17RL%10RM%11RN%1;RO%1<RP%1=RQf:RR#1RS%C4R43BD4D4C=X1Cf<RT/3I/73?53TX0:?IHTf>RU=GGHPUPHPTPFPRP=P<P;P1P0P7M;L[[P3PGf?R013HIPKPLPMPNPOPPPQPS%1FRF%1TRT;B4D4D4C=130I/73?530X0:f@RN;I0fARM=GGNPCPGfBRL13MIR1PPPQPSPFPT%1HRH%1URU%10R0%1N/?4D4D4R;,?KC=X1CP8PGPLPM13NI1<J8POPPPQPSPFPTPHABU04D4D4P51713R0?53MX0:1<J7/?;#\#>,819503R0X0:PLPMP613LIRL/76RM%DJ#;#;#;#;RJ#>R1,8LR;,:6R7'E18LI95M6RUPMP7PMP3X0:R7PIO1R4,8LRH,:6%HMP:P:P2P7P21:63#HXK:X0:P6P619:6P;PHP7P7P7P:P:g00bM1863CZ,9:X4:X@:PLPL19:LP1P4P7P7%>3,9:X09PJPI19:IEYM:WM<VEUP3CRPUg00c1RU#C%JUP:1Q:5P6%P:CO%S:%T:RUP>P?P?P@P:1M:ARA1n:IR>5m:RJg00c]1M:BRBCA,@UR9P:PBg00dDR7Al:J>CA,@U5KU%k?P:PBP7PACA,@U9KU9Gj1gU@P3P5g00AfRUg00@fR@'91f35=eU@dg00dk=c:6Cbb<b=b>X2:X3:133IR@/7618@I756136I/75?556[^2:^3:P3P8fDP6O3b;b9fCR8/3I/73?538X0:P6O1eX80X0:EaP3G`CdW:W5W6X1CP6P3O2n2001000000121100000W7XJDXIDXHDXGDXFDXEDXDDXCDXADXB:X?EW4o"). Qed.

Lemma tr_frame_agree_nw : forall m m' sp ra x0 x1 x2 x3 x4 x5 x6 x7, tr_frame m sp ra x0 x1 x2 x3 x4 x5 x6 x7 ->
  agree_on (fun x => sp - 80 <= x < sp) m m' -> tr_frame m' sp ra x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
ltac2:(KReplay.run1 (kr_t_D_trdefs ()) ["TrTransport"] "p'0h01xi001xh14junkh24__x1h34__x2h41mh52AGh62FRh71Hh82Hxh93Hx0h:7__arithh;4__ffh<8__varmaph=5__with>2m'h?1nh@2rahA2sphB2x0hC2x1hD2x2hE2x3hF2x4hG2x5hH2x6hI2x7hJ1yp;1p;;p;2p;4p;3p;<p;6p;8p;7p;Bg002Lj12Tg00CDj1MTg00Cbj1GTg00DEj1VTg00Dgl;LTg001Gj1ITg001gj1]Tg0031j1ZTg00Edj23Tg00FAj2=Tg00G9j11Tg003Oj1CTg00H1j4@Tg00Hjj27Tg00IFj3KTg00K7j1[Tg00L3R0j1<Tg00LSR1j28Tg00M0R2j2;Tg00MLj2FTg00Mgj1HTg005gj29Tg00NEj4YTg00Nhl<UTg00OMj6TTg00P6j4STg00P]j2OTg00Q;j1PTg00QYj4QTg00R7j1NTg00RUj1RTg00S@j2DTg00Scj2mTg00TFj3lTg00Tij4BTg00UTj3kTg00V7j1jTg00VYj8iTg00W=j2eTg00W_j2dTg005Mj3cTg00XKj3bTg00Xjj4_Tg00Y\j6`Tg00eIj7aTg00[Wj4^Tg004nj10Tg003oj36Tg00\1l<\Tg00\VlBfTg00]<j7gTg00]`j7hTf0R3#0#0#0#0#0#0#0#0p=Eg00^DR4f2R5f1R6=64336p=>f4R7f3R8A64639645564564p=41;63,F5p=5A6463p=?%03#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=:g0095R9g008WR:P:P:P0P0f5R0P7P8P5P6P3M<\p=XP:P:P:P:P:P:P1P3P6P5P1P8P7P0f6R1f7R;f8R<f9R=MBfp=WP6g00_<R>g00_[R?P?g00`;R@P3g00`[Fgp=AP5P>P?P?P@P6P3Fhp=Jg009TRA#2RB#2#2RC#2#2#2#M#GRD%MC#GRC#V[REf;RFP=P<P;P1P0P7P8P5P6P3M;Lg00a;%ICRCg00aURGf=RH%]B#2#2#2#2#ZRI,3Fg00:9#ERJ/=3RK%15%18%17RL%10RM%11RN%1;RO%1<RP%1=RQf:RR#1RS%C4R43>D4D4C@X1Cf<RT/3I/73?53TX0:?KHTPHPTPFPRP=P<P;P1P0P7P8M;L[P3PGf?R713HIPKPLPMPNPOPPPQPS%1FRF%1TRT;>4D4D4C@137IRM/73?537X0:f@RL;K7PCPGfAR013LIR1POPPPQPSPFPT%1HRHf>#1R;%17/?4D4D4R7,?KC@X1CP5PGP0PLPM1=J5PNPOPPPQPSPFPTA>H;4D4D4P61713R;?53LX0:1=J8/?7#[#<,8195;3R;X0:P0PLP3130IR0/76RL%EJ#:#:#:#:RJ#<R1,80R7,;6RH'F180I95L6R4PLPHPLP3X0:RHPIO1RT,80RF,;6%HLP:P:P2PHP21;63#HXJ:X0:P6P619:6P7PFPHPHPHP:P:g00bM1863CY,9:X4:X?:P0P019:0P1PTPHPH%<3,9:X09PJPI19:IEXM:WM<UETP3CSP4g00c1R4#C%I4P:1O:5P6%P:CQ%N:%R:R4P>P?P?P@P:1D:ARA1m:IR>5l:RJg00c]1D:BRBCB,A4R9P:PBg00dDRHAk:J>CB,A45J4%j?P:PBPHPACB,A49J49Gi1e4@P3P5g00AfR4g00@fR@'91d35=c4@dg00dk=b:6C_b;b<b=X2:X3:133IR@/7618@I756136I/75?556[^2:^3:P3P8fCP6O3b:b9fBR8/3I/73?538X0:P6O1eX8;X0:E`FaC^W5W6X1CP6P3O2n2001000000121100000W7XIDXHDXGDXFDXEDXDDXCDXBDX@DXA:X>EW4o"). Qed.

(* [comment removed for export] *)
Lemma TCTX_agree : forall Σ Σ' so so' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m m',
  TCTX RT OUT_rep ERR_rep XENV LIB Σ so usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m ->
  ART RT Σ' m' -> mem_inv asegs m' -> wmono asegs m m' -> stk asegs m' (rt_sp0 RT Σ - STACK_SPAN) (usp - 160) ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = [] ->
  CLX OUT_rep ERR_rep XENV LIB so' m' ->
  agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m' ->
  agree_on (fun x => d <= x < d + plen) m m' ->
  TCTX RT OUT_rep ERR_rep XENV LIB Σ' so' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m'.
Proof using AF.
  intros Σ Σ' so so' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m m'
    (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0)
    ART1 MI1 WM ST1 ESP ELV EFR CLX1 AGS AGD.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
  split; [apply (main_frame_agree m m' usp _ _ _ _ _ _ _ _ FR0); [eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia| exact WM]|].
  split; [apply (tr_frame_agree m m' _ _ _ _ _ _ _ _ _ _ TF0); [eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia| exact WM]|].
  rewrite ESP, ELV, EFR. split; [exact ST1|].
  split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|]. split; [exact LV|]. split; [reflexivity|].
  split; [exact PL|]. split; [exact PB|].
  split; [apply (bytes_at_agree asegs m m' _ _ BD); rewrite <- PL; exact AGD|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Lemma TCTX_agree_nw : forall Σ Σ' so so' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m m',
  TCTX RT OUT_rep ERR_rep XENV LIB Σ so usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m ->
  ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' (rt_sp0 RT Σ - STACK_SPAN) (usp - 160) ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = [] ->
  CLX OUT_rep ERR_rep XENV LIB so' m' ->
  agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m' ->
  agree_on (fun x => d <= x < d + plen) m m' ->
  TCTX RT OUT_rep ERR_rep XENV LIB Σ' so' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m'.
Proof using AF.
  intros Σ Σ' so so' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m m'
    (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0)
    ART1 MI1 ST1 ESP ELV EFR CLX1 AGS AGD.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
  split; [apply (main_frame_agree_nw m m' usp _ _ _ _ _ _ _ _ FR0); eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia|].
  split; [apply (tr_frame_agree_nw m m' _ _ _ _ _ _ _ _ _ _ TF0); eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia|].
  rewrite ESP, ELV, EFR. split; [exact ST1|].
  split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|]. split; [exact LV|]. split; [reflexivity|].
  split; [exact PL|]. split; [exact PB|].
  split; [apply (bytes_at_agree asegs m m' _ _ BD); rewrite <- PL; exact AGD|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

End TrTransport.

Section TrXenv.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

(* [comment removed for export] *)
Lemma CLX_xenv_update : forall so m m' (flo fhi : Z) (Wx : list (Z * Z)),
  CLX OUT_rep ERR_rep XENV LIB so m -> munch ((flo, fhi) :: Wx) m m' -> wmono asegs m m' ->
  SEGTOP_A <= flo -> (forall x, in_ranges Wx x -> in_ranges XENV_FP x) -> XENV m' ->
  CLX OUT_rep ERR_rep XENV LIB so m'.
Proof using OUT_loc ERR_loc LIB_loc IO_img XENV_img.
ltac2:(KReplay.run1 (kr_t_D_trdefs ()) ["TrXenv"] "p'0h01xi001xh11vh21gh34__x1h44__x2h51Hh64__p1h74__p2h87__arithh94__ffh:8__varmaph;5__with<2Hxh=3Hx2h>1nh?2H0h@2HahA4__x3hB1ahC2lohD1mhE3AGDhF3AGIhG3AGLhH2ERhI3FLOhJ2H1hK2H2hL2H3hM2H4hN2HWhO2HdhP3HinhQ2HnhR2MUhS4OUTWhT2RShU2SGhV2WMhW2WxhX3XE'hY3fhihZ3floh[2m'h\2soh]1yp&0p;1p;2p;6p;3p;4p;7p;8p;<p;Bg002Lj1ITg00CDj1nTg00Cbj1wTg00DEk10NTg00lIk20HTg001Gj1sTg00i5j6=Tg00G9j1ZTg003Oj1hTg00a;R0j25Tg01E4j1fTg0031j1eTg00LSR1j26Tg01Elj22Tg01Fjj1LTg01GCj2MTg004nj1@Tg015@j2[Tg015ij3lTg016Rk203Tg003oj3UTg00P]j2cTg00Q;j1}Tg00QYj4OTg00R7j1zTg00RUj1yTg00S@j2QTg00V7k10MTg01H<k60LTg00W=k20KTg005gj2BTg00W_k20GTg005Mk30FTg00XKk30CTg00Xjk40ATg00Hjj24Tg00M0R2j28Tg01H`k30@Tg01:Ej4ETg01Ikj1rTg01Jmj1qTg00MLR3j20Tg01Khj3`k40<Tg01LCj2^Tg01MHj3dTg01Mcj4pTg01Nmj6]Tg00IFj3_Tg01Omk20>Tg01Pfk20=Tg01Qgk20;Tg00K7j1RTg00L3R4j1DTg00Mgj1\Tg00NEk408Tg00OMj6gTg00P6j4iTg001gk106Tg00Scj2bTg00UTj3STg01RQj2CTg01Rkk705Tg00[Wj4mTg00ZWk809Tg00Y\k60:Tg01Skk802Tg01Tfk401Tg00H1k40?Tg01<Oj4uTg01U_j4tTg01V?k300Tg00J@j3~Tg01W6k60BTg00Tij4vTg00]<j7|Tg00]`k70DTg00VYk80ETg00\1l<{Tg00\VlBxTg00Nhm<0ITg01WZk70JTf0R5#I#Ip=Hg00^DR6f1R7;U5p=Kg00aUR8P7g01X>R9P5H01p=3P8P7g01Y;R:P5H0?p=1f3R;f2R<'5P8P7g01Z5R=P5Cu'0p=71075,0<p=Af5R>g008WR?P?f4R@P;Ct;U<@0075p=;A~875p=<g01@<RA/45p=:15<7/05p=VP8P7P=P5Cup=X14;<1875'0p=9P7g00_<RBg00_[RCPCg00`;RDP5J0Bp=YP?P7g00dDP5Cvp=PP7PBPCPCPDP5g00`[F|p=>P<PBPCPCPDP7P5K0Dp=GP?P7g00c]P5Cvp=WP;PBPCPCPDP<P7P5L0Ep=J1875,0<p=F14<7/05p=aP?P?P<P7Ct=U;5p=T1675,8<p=og0095REP?P?P?P4P4P>P@P;P<P7P5M<{p=kP?P?P?P?P?P?P1f7R4f6RFP>P1P@P9P9P;P<P7P5MBxp>07P?P?P2P4P2PFP>P@P;P<P7P5N<0Ip=jP<PBPCPCPDP7P5K0Jp=N1675,8<,0;p=?P?P?P?P?P?P?P1P4PFP>P1P@P:P:P;P<P7P5MBxp>04g00BFg009TR1#IR2#IRG#IRH#I#HRI#nRJ#wRK%nH#w$0N[RL20H??RM#sp,7OUT_repRNp,7ERR_repROp,4XENVRPp,3LIBRQP>P@E=P3PNPFP>O2POP>O1PPP>O1PQP>O1%Z5%h6R6'KRR,3FX2K,5KPK%f5/K6RS,1FX1KP>%HI#H#H#H#H#eRI,6=RTC73A3APMP@P;P<PFP>E;1<4F%:F12F5p,7XENV_FP/27RU[^0?PPf9RVO1RWPNPOPPPQf<RXf:RYE=[[[[[P5PNf8RZP4O2POPZO1PPPZO1PQPZO113VRX2K,5KPK11VSX1KPZPTC73A3AP3POPVO1PQPVO113YRX2KPK11YSX1KPVPTC75VK5AWPMPZP4PFPYPVE;f;RZ/<Y%:Y12Y5PU[^0?PPf=RWO1R[PNPOPPPQf@R\f>R]E=[[[[[P5POPZO1PPPXO1PQPXO113WRX2KPK11WSX1KPXPTC75VK3AP3P[PQPWO113]RX2K,5KPK11]SX1KPWPTC73APMPXPZPYP]PWE;f?RW/<]%:]12]5PU[^0?PPfAR[O1PNPOPPPQfDR^fBR_E=[[[[[P5PPPWO1PQP\O113[RX2K,5KPK11[SX1KP\PTC73AP3PQP[O113_RX2KPK11_SX1KP[PTC75VKPMP\PWP]P_P[E;fCR[/<_%:_12_5PU[^0?PPfER]O1PNPOPPPQfHRWfFR\E=[[[[[P5PQP[O113]RX2KPK11]SX1KP^PTC75VKP313\RX2K,5KPK11\SX1KP]PTC7PMP^P[P_P\P]E;fGR]/<\%:\12\5PU[^0?PPfIR`O1PNPOPPPQfLRafJRbE=[[[[[P513WRX2K,5KP0PK13`RX2KPK11bSX1KP`PTC7PMPWP]P\PbP`E;fKR`/<b%:b12b5PU[^0?PPfMR\O1PNPOPPPQfPR]fNRWE=[[[[[[P513`RPK11\SX1KPaPTC7P311WSX1K,5K1X\TPMPaP`PbPWP\E;fOR\/<W%:W12W5PU[^0?PPfQR`O1PNPOPPPQfTRafRR3E=[[[[[P511]SX1K,5KP0PK11`SX1K1X`TPMP]P\PWP3P`E;fSRW/<3%:31235PU[^0?PPfUR\O1PNPOPPPQfXR]fVR0E=[[[[[[P511WS1XaTPMPWP3P`P\PaE;1<0\%:\12\5PU[^0?PPP]O1PIP5P5PAC9R\%LURaf[R`P<P<fZRWC9#LfYRc/M<p-0Rdg00c1Reg00:9Rf#@Rg#@Rh,[?1[?g1[?f5l?5l?g01B;+03%heRf3U%seReP?P?1c?;P<%}?RgCOP7PgCO%z?Ri%y?Rj1Yj>Rk1Q?2R21Q?GRl'P,>j5Gj&0MCRmPj1Q?1Rn,Wl,>jPmPjPBPCPCPD1Wn2,>jRC1YjF5GjJ0LCJCJ20KjDRDP5P<g00AfRBg00@fRo'B20G5<>0FBodg00dk>0C?7H0ARob9b:b;X3?X4?XA?X6dW7AF;7<14;7Aa<;Fg01[4[[[^3?^4?^A?^6d^7dP518;`14I;PAP;f\RAP<PFO7b812c<RBP7P>P;P5O2O1WP%LBe:0@c<CEPMP`PWPcCT/M<RBeWQW<X0?PB\a\\^0?PMPcP]fWCTP`PWp,5IO_FPR\/25RBX0?RpP>P<P7%r7R>%q7Rq#LRrg01[QRs/M7'0p,6IO_imgP7P5O23`,^7P\P<1M\<Rt1Ms<Ru%q<#LRv10tuRw%r<10vwp,8XENV_imgP<P5O23dRx3dRy3`P7CpX=UPaeO3X<BX0?E]A_p`WPMPWPcP]CTPAP`12s5R]X0?RcPFP;P720>759`>r,^7PsP<AdtuyP7CpX=UPaeO3X<]X0?E]A_cA`Ao5<79a<5Pq[^0?RqPMf^RMf]RcPACTf`RAf_R`Ao5;<9a;5R]X0?RyPYP4P7P<P7P5O2-0=7,^7PvPwPxP;P<P7O2H0<X=UPaeO3X<]X0?E]WOX>?XC?A_yA`\q^>?^C?PNP`PcO2POPcO1ROPPPcO1RPPQPcO1RQ13MRX2KRR,5KRN11MSX1KRS,5KRq1XcTRy'0RA'0R]'0Ra'0RU'0p,7OUT_locP`PMPcP020;J5RJ,2\P@P7P5O2W@XBKR\O5POPUp,7ERR_locPMPcP3P\O4PPPaP@PQP]p,7LIB_locPMPcPb12sJP;P7P5O2W@XBKO4PNPAPKPRP[P8PMPcP9%Z[/K6R[P_P5P9%R[#D1495R[%@h#@Rh#@#@#@#@R_#DRR,69RA7F51497RN187ARJ'0%eHRH,69Rs9FN7RbPNPJPNP5X0?RJPHO1R],69RQ,87%\NPJ1875#\X]?X0?RNP7P71B?7RaPAPQPJPJPJP?P?g00bM1675H08,B?XD?X>?RQ1B?9PRP]PJPJ%D5,B?X0EREP_PH1B?HEkL07GjEgP5CiPbPfPeP?1c?7P<1c?<R_COPiPj&061,Q?R1/W2,>j1b?H9S?1,P2,>j5GjR1Pm1Yj@R]ANj1k5NjCJPDPob9b:b;X3?X4?X6dX7d1475R1P5P7PHC?14<7RRP7P<PHC?/C@,C;[^3?^4?^6d^7dP5P=P;P;PTC9RHP:P;P;%eGRG,6:RAC9P9P;P7O5b8b?UX0?P[P5P9%Z^/K6#R#DC?14:7R^?F7AR[P=P7P7PTC9,Cb'CRb[^0?eO3K05CmPqPyPKPSPZP8PMPcP:%fZ/K6RZPYP5P:%RZ#D14:5RZ%DhRY,6:RS7F5187SRy,0^P[P^PyP^PJPGO1Ry,6:Rq,87%\^PJPNP7P7PaPSPqPJPJPJPQ1B?:PYPyPJPJPEPhPG1B?GEkL04GjEgP5CiP[PfPeP?P_P7PgCOR_PiPj1b?G9S?n,P2,>j9GjCR[PmANj[]CJPDPob9b:b;X3?X4?X6d1457R[P7P5PGC?147<RhP<P7PGC?/C;[^3?^4?^6dP5P9P;P;PsC9/CHP;P:P7O4b8b?UX0?PZP5P:%fX/K6#R#DC?Pb[^0?eO3P4L09CmP8PMPcP=PTPVP=P5P5PTC9RTX0?RVPVPMPcP5P=PIPfPeP?P_P<PgCOPiPj1Wl2,>j1b?IRg9S?l,P2,>j5GjRlPmANjkl9Nj]CJPDPob9b:b;X3?X4?X6dX7d167IR]9F15PRP7P<PIC?,C@,C;[^3?^4?^6d^7dP5P9P<P<PsC9P:P<P<PAC9P=P<P7O5b8VTX0?O3PfPeP_PiPjAS?ng,P2,>j9GjCRCPmPCCJPDPob9b:b;X3?X4?P[P7P5PIC?AFh<][^3?^4?P5P<P=P7O3b8VTX0?PVP7O1\T^0?eJ0:P4L02CECECECECECEbEbGbFbSWXWNWIWVWRWTWHX1KP7P5O2n2001000000121100000W5P7P5O2n2001000000121000000W5WUX2KP7P5O2n2001000000121100000W5P7P5O2n2001000000121000000W5WMP7P5O2n2001000000121000000W5WLP7P5O2n2001000000121000000W5WKP7P5O2n2001000000121000000W5WJP7P5O2n2001000000121000000W5WWXY?XZ?X[LWDW\o"). Qed.

End TrXenv.
