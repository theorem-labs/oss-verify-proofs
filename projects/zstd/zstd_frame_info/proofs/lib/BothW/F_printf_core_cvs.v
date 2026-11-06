(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import Stdio_kit Stdio_kitI F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import Printf_zfacts F_printf_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import F_printf_core_common.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".  (* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Local Ltac acc_hint ::= lazymatch goal with |- acc_in _ (wa ?e, ?n) => change (wa e) with (Z_to_bv 64 e : word); solve_acc1 end.
  Local Ltac acc_enrich ::=
    repeat match goal with
    | H : nth_error ?l ?k = Some ?x |- _ =>
        lazymatch goal with _ : (k < length l)%nat |- _ => fail | _ => pose proof (nth_error_some_bound l k x H) end
    end;
    rewrite ?u32s_length, ?u64s_length, ?length_app, ?repeat_length, ?zb_length in *; cbn [length] in *; unfold zlength in *.
  Context {St : Type}.
  Variables (Fp B BS : Z) (RB : region) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS RB SINK TOPOK OUT.
  Hypothesis HSTRN : strnlen_a_stmt.
  Variables (RNG : footprint) (rstk rfmt : region).
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q < 2^47)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.
  (* [comment removed for export] *)
  Hypothesis HA : (A + zlength fmt <= 622592)%Z.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_F : ((634528 <= Fp /\ Fp + 232 <= 659512) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((6242328 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.
  Hypothesis KH : (KHIGH <= lo)%Z.
  Hypothesis RSK : (r_lo rstk <= lo /\ q <= r_hi rstk)%Z.
  Hypothesis RFM : inreg rfmt A (zlength fmt).
  Hypothesis RPF : inreg rfmt 68436 9.
  Hypothesis RBI : inreg RB B BS.
  Hypothesis RG_stk : rng RNG lo (q - lo).
  Hypothesis RG_img : rng_aimg RNG.
  Hypothesis RG_ap : rng RNG AP 8.
  Hypothesis RG_va : rng RNG VA (8 * zlength slots).
  Hypothesis RG_F : rng RNG Fp 232.
  Hypothesis RG_B : rng RNG B BS.
  Hypothesis RG_fmt : rng RNG A (zlength fmt).
  Hypothesis RR_stk : rrng RNG rstk.
  Hypothesis RR_fmt : rrng RNG rfmt.
  Hypothesis RR_B : rrng RNG RB.
  Hypothesis ENV0 : ashenv m0.
  Hypothesis RC_stk : rclean m0 rstk.
  Hypothesis RC_fmt : rclean m0 rfmt.
  Hypothesis RC_B : rclean m0 RB.

  (* [comment removed for export] *)
  Local Notation ctx_all := (F_printf_core_common.ctx_all RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
  Local Notation appW_W := (F_printf_core_common.appW_W Fp B BS RB q m0 lo AP VA LO SEP_F HAP KH RBI RC_B).
  Local Notation ashsafe_W := (F_printf_core_common.ashsafe_W Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP KH).
  Local Notation env_now := (F_printf_core_common.env_now Fp B BS q m0 lo AP VA LO GLO SEP_F SEP_B HAP KH ENV0).
  Local Notation rc_now := (F_printf_core_common.rc_now Fp B BS RB q m0 lo AP VA LO SEP_F HAP KH RBI RC_B).
  Local Notation arg_ok_s_W := (F_printf_core_common.arg_ok_s_W Fp B BS RNG q lo fmt AP slots).
  Local Notation Fok := (F_printf_core_common.Fok F).
  Local Notation Fok_refl := (F_printf_core_common.Fok_refl F).
  Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
  Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
  Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
  Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
  Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
  Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
  (* [comment removed for export] *)
  Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
  Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
  Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS RB RNG q m0 lo fmt AP VA slots LO SEP_F HAP KH RBI RC_B).
  Local Notation args_ok_W := (F_printf_core_common.args_ok_W Fp B BS RB RNG q m0 lo fmt AP VA slots LO SEP_F HAP KH RBI RC_B).
  Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
  Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
  Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
  Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq RNG q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA RG_stk RG_img RG_ap RG_va).
  Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq Fp B BS RB HSTRN RNG q gp tp m0 lo AP VA LO GLO QHI SEP_F SEP_B HAP KH RBI RG_stk RG_img ENV0 RC_B).
  Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS RB SINK TOPOK OUT TOK HOUT RNG q gp tp m0 lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
  Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
  Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS RB SINK TOPOK OUTFP TOK RNG q gp tp m0 lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
  Local Notation S_EXIT := (F_printf_core_common.S_EXIT (St:=St) Fp B BS RB SINK RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PLOOP := (F_printf_core_common.S_PLOOP Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS RB SINK RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
  Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
  Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS RB SINK TOPOK OUTFP RNG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T6 := (F_printf_core_common.S_T6 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T5 := (F_printf_core_common.S_T5 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T4 := (F_printf_core_common.S_T4 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T3 := (F_printf_core_common.S_T3 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC2 := (F_printf_core_common.S_INTC2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_INTC := (F_printf_core_common.S_INTC (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
  Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation xloop_post := (F_printf_core_common.xloop_post q gp tp).
  Local Notation S_XLOOP := (F_printf_core_common.S_XLOOP RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation POST1 := (F_printf_core_common.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
  Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
  Local Notation S_PRO := (F_printf_core_common.S_PRO Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

  (* [comment removed for export] *)
  Notation sfx := (sfx fmt).
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).
  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.
  (* [comment removed for export] *)
  Ltac len_norm := unfold zlength, zrepeat; rewrite ?repeat_length, ?zb_length, ?length_map, ?length_firstn, ?length_skipn, ?length_app; cbn [length]; try rewrite !Z2Nat.id by lia.
  Ltac inreg_side := solve [ unfold inreg in *; len_norm; unfold zlength in *; lia ].
  Ltac rng_side :=
    lazymatch goal with |- rng ?RNG0 ?lo' ?len' =>
      first [ assumption
            | match goal with H : rng RNG0 ?lo ?len |- _ => apply (rng_sub' RNG0 lo len lo' len' H); solve [len_norm; unfold zlength in *; lia] end ]
    end.
  Ltac body_reg_stk := exists rstk; split; [ exact RC_stk | split; [ inreg_side | exact RR_stk ] ].
  Ltac hypMU := match goal with H : munch _ m0 _ |- _ => exact H end.
  Ltac hypWM := match goal with H : wmono _ m0 _ |- _ => exact H end.
  (* [comment removed for export] *)
  Ltac memset_pad PADa :=
    eapply (memset_callZ RNG (r_lo rstk) (r_hi rstk) (r_rlo rstk) (r_rhi rstk));
    [ exact PADa | match goal with H : mem_inv _ _ |- _ => exact H end | lia | lia | lia | lia
    | match goal with H : stk _ _ _ _ |- _ => exact H end | lia | exact KH
    | eapply env_now; [ hypMU | hypWM ]
    | apply rclean_shclean; eapply rc_now; [ exact RC_stk | hypMU | hypWM ]
    | lia | lia | lia | lia | exact RG_img | rng_side | rng_side | exact RR_stk ].
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
    unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
    try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
         lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
    try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
         lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
    unfold zlength in *; hush.
  Ltac hyp :=
    lazymatch goal with
    | |- rw_cells _ ?m ?A ?cs =>
        match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
    | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
    end.
  Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
  Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
  Ltac rd_fmt idx :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
        (* [comment removed for export] *)
        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.
  Ltac the_mi k := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
  Tactic Notation "jump" tactic3(tac) := eapply evtF_eq; [ | tac ]; [ mseq | .. ].
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
    eapply implAM_eq_ms; [ | tac ]; [ mseq | .. ].
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  (* [comment removed for export] *)
  Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
    end.
  Local Ltac transport_call_extra segs W m m' MU WM ::=
    repeat match goal with
    | H : SINK m ?st |- _ =>
        first [ eapply (sink_call W m m' st) in H;
                [ | exact MU | exact WM
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    end.
  Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
  Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
  Local Ltac mem_after_store ::= mem_after_store_fast.
  Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
  Local Ltac lia ::= lia3.
  Ltac out_call_with r :=
    ileave; eapply implAM_bind;
    [ eapply (out_callq r);
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 629952 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 6242320 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | |
      | hypMU | hypWM
      | first [ assumption | idtac ]
      | first [ inreg_side | idtac ]
      | first [ rng_side | idtac ]
      | first [ assumption | idtac ] ]
    | cbv beta ].
  Tactic Notation "out_call" constr(r) := out_call_with r.
  Tactic Notation "out_call" := out_call_with rfmt.
  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call bsegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := cbv delta [bsegs bsegs] in *; fold bsegs in *.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    let rb := fresh "rb" in let RCb := fresh "RCb" in let IRb := fresh "IRb" in let RRb := fresh "RRb" in let RGb := fresh "RGb" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & (rb & RCb & IRb & RRb) & RGb & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & PFlo & PFhi & Hi4 & Hfl & HnI & Hnp & Hplp);
    pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
    pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
    let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
  Ltac mk_tinv :=
    lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      unfold tinv, body_loc;
      split; [mk_finv|];
      split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
      split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
      split; [match goal with H : SINK m _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
      split; [lia|];
      split; [assumption|];
      split; [assumption|];
      split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
      split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [first [assumption | reflexivity | lia | zl] |];
      split; [match goal with H : rclean m0 ?r, H2 : inreg ?r _ _, H3 : rrng _ ?r |- _ => exists r; split; [exact H| split; [exact H2| exact H3]] end |];
      split; [assumption|];
      repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
    end.

  Hypothesis HS_TAIL : S_TAIL.

  (* [comment removed for export] *)
  #[using="SFR HSTRN LO GLO QHI HA SEP_F SEP_B HAP HVA BS0 KH RBI RG_stk RG_img ENV0 RC_B HS_TAIL"] Lemma L_CV_S : S_CV_S.
  Proof.
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p fl10 xp P s slack pfx s2s za pl plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP STR SRNG SPAD P0 SD1 SD2 SD3 SD5 RGS REGS E10.
    destruct REGS as (rs & RCS & IRS & RRS).
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app, zb_length in SB. cbn [length] in SB.
    Local Ltac2 Set LiaHints.tbl := fun () => "0330?1163624459.192 11666457166.17211668961905.17411668962290.17411820177899.19311822584175.19212524393443.19212526607207.19312551536654.19112551536654.1931328334446.202 1328334446.206 13563969523.19113563969523.19314341690004.19216248664866.17216250358557.17416252485563.16916886332493.19318761041880.18919042827563.19919042827563.20219059271977.19019059271977.19221483424549.19221485634465.19322638612785.19323077509607.20123077509607.2052307889141.193 23086586795.19223089025839.19323089080730.1742309513073.192 23099167141.17223145753735.20023145753735.20323191472327.19323193845827.19223417445761.1932583290783.193 26131081623.19326575679118.19126575679118.19327164055491.19227474226815.19327475879675.19227647207830.18827647207830.19028908644622.17228922925361.17429258395259.18830101911539.19330351702510.20230351702510.20631070687724.20231070687724.20631165778545.17431165778672.19132410872973.19333263823594.20233263823594.20633928676191.19933928676191.20334292888555.17434305264110.20234305264110.20634954965222.19134954965222.19335827935646.20035827935646.20336194455448.20036194455448.20336831100915.19136831100915.19337057194968.19337058782044.19237631032481.19937631032481.20339047133539.20239047133539.2063942199251.197 3942199251.200 40345170492.19340347482808.19240457137823.16940825907496.1884105703320.200 4105703320.203 41107722880.1934113535205.174 4113535334.173 41602360616.19141602360616.19341860256368.19343100747103.19343638561891.193445078394.200  445078394.203  46135357670.19146135357670.19346271681008.18446898303580.19446898303580.19547200734390.17247202972809.17447203077692.19347204927160.19247917741756.20247917741756.20648881857403.19248883710975.19349376477044.19349378949104.19249549723667.17449551700012.17250111462772.17451184819047.19351192955883.19351194710895.19251678946857.19351680767661.19251721469139.19851721469139.20151792577165.19251794659849.19352268114131.17252270078188.17453199507948.19254121776830.20254121776830.20654429404910.18855223871902.20055223871902.20355537228055.20055537228055.20255537228055.20355537228055.20656368271429.19256369895617.19356867836477.19256869624505.19357283210687.19257285780795.19357897851615.20057897851615.20458665690269.19758665690269.20058963326956.16659308628179.17459308628433.19159650130105.17459652110470.17259959107129.17059976791280.20259976791292.19860111391000.20060111391000.20360300497348.20461756489387.19361993915987.19262438234458.20062438234458.20363053735762.19263767058543.19263769661675.19364656456728.20064656456728.20365227213690.20065227213690.20366201836243.18566388384015.17466402672944.17266829496233.19366831968045.19267281204924.20267281204924.20668360121726.19268362135034.19368500806127.17368500806127.19468585761514.20268585761514.2067320613356.202 7320613356.206 7355949818.200 7355949818.203 7357714442.190 7357714442.192 9220934353.191 9220934353.193 9852913522.199 9852913534.196 990943913.191  990943913.193  00000E00[01101K01^02102202302F02Y02h03703N03e04:04I04X04g04h05705J05]06^07_08108C08D08W08j0:=0:Q0:`0:o0<<0<K0=L0>M0>N0>O0>P0>e0>f0?90?L0?`0?a0?b0@10@@0@O0@^0A30AH0AW0Af0B<0BR0Bd0C60C70CP0Ci0D80DG0D[0Dj0E90EL0E_0F60FM0GN0HO0He0I;0IJ0IY0Ih0J70K80L90LH0LW0Lf0M50MH0MW0Mj0N=0NL0N^0O00O?0ON0Oc0P60PN0P]0Pl0Qm0Rn0S@0SO0S^0Sm0T<0TK0TZ0U[0V\0V]0V^0V_0V`0W40WH0WZ0W[0W\0W]0X40XK0X]0Xo0YA0YS0Yb0Z10ZD0[E0\F0\U0\n0]G0]Y0]k0^=0^O0^b0_50_G0_Y0_h0`70`I0`[0`j0a90aD0aY0an0bo0d00dC0dU0dg0e=0eS0eb0f40fC0gD0hE0iH0iW0if0j<0jR0ja0k00k?0kS0kg0kh0ki0l<0lO0l^0lm0m>0mO0mf0n=0nS0ni0o80oG10D11A11B11C11U11g11h11iS3LZB2LU2SB3LZS5SMALLS2P03SD53LZB2LU2SB3LZSS2P03SD53LZB2LU2SB3LZSS2P03SD53LZB2LU2SB3LSB3LZSS3Hi43LZB2LU2SB3LZSS3Hi43LZB2LU2SB3LZSFFS3GLO3LZB2LU2SB3LZSS3GLO3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3HAP3HVA3LZB2LU2SB3LZSS3HAP3HVA3LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZS2K1S3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSFS3LZB2LU2SB3LZSS3QHI3LZB2LU2SB3LZSS3QHI3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2Hw3LZB2LU2SB3LZSS2Hw3LZB2LU2SB3LZSFS3QHI3LZB2LU2SB3LZSS3QHI3LZB2LU2SB3LZSS2LO3GLO3QHI5SEP_F5SEP_B3HAP3BS02Hp4SPAD2P03SD13SD23SD33SD53LZB2LU2SB3LSB3LZS2K02K1S4SPAD3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2LO3GLO3QHI5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33SD53LZB2LU2SB3LSB3LZS2K0S3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0FFFS3LZB2LU2SB3LZS2K12HpFS3GLO3LZB2LU2SB3LZSS3GLO3LZB2LU2SB3LZSS4SPAD3LZB2LU2SB3LZSFFS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZS5SMALLS2Hp3LZB2LU2SB3LZS2K1S3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZSFS2LO3GLO2HA3LZB2LU2SB3LZSS2LO3GLO2HA3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS4SPAD3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3HAP3LZB2LU2SB3LZSS3HAP3LZB2LU2SB3LZSS3HAP3HVA3LZB2LU2SB3LZSS3HAP3HVA3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S3GLO2HA3LZB2LU2SB3LZSS3GLO2HA3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3Hfl3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3HAP3LZB2LU2SB3LZSS3HAP3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZS2K1S3SD53LZB2LU2SB3LZSS2Hp3LZB2LU2SB3LZS2K12LFS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0FFFFS4SPAD3LZB2LU2SB3LZSS4SPAD3LZB2LU2SB3LZSS3LZB2LU2SB3LZS2K1FFFS3Hfl3LZB2LU2SB3LZS3FLBS3Hfl3LZB2LU2SB3LZS3FLBS3LZB2LU2SB3LZS2HBS3LZB2LU2SB3LZS2HBS2Hk3LZB2LU2SB3LZSS2Hk3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3SD53LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S3LZB2LU2SB3LZSS2LO3GLO2HA3LZB2LU2SB3LZSS2LO3GLO2HA3LZB2LU2SB3LZSS2LO3LZB2LU2SB3LZSS2LO3LZB2LU2SB3LZSS2LO3LZB2LU2SB3LZSS2LO3LZB2LU2SB3LZSS3E103LZB2LU2SB3LZSS3E103LZB2LU2SB3LZSS2Hc3LZB2LU2SB3LZSS2Hc3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZS2HBS3LZB2LU2SB3LZS2HBS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SBS2P03LZB2LU2SB3LZS2K0S2Hp3LZB2LU2SB3LZS2K2S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S3Hfl3LZB2LU2SB3LZSS2LO3LZB2LU2SB3LZSS2LO3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZS2LFS3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K0S2LO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23SD33LZB2LU2SB3LZS2K05SMALLS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS4SPAD3LZB2LU2SB3LZSS4SPAD3LZB2LU2SB3LZSFFS3HAP3LZB2LU2SB3LZSS3HAP3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZS1HS3LZB2LU2SB3LZS1HS3HAP3HVA3LZB2LU2SB3LZSS3HAP3HVA3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS2LO3GLO3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS3LZB2LU2SB3LZSS2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23LZB2LU2SB3LZS2K0S2LO3GLO5SEP_F5SEP_B3HAP3BS04SPAD2P03SD13SD23LZB2LU2SB3LZS2K0FFS2LO3LZB2LU2SB3LZSS2LO3LZB2LU2SB3LZSFF".
assert (LSB : Z.of_nat (length (zb s ++ Z_to_bv 8 0 :: slack)) = (Z.of_nat (length s) + 1 + Z.of_nat (length slack))%Z)
      by (rewrite length_app, zb_length; cbn [length]; lia).
    pose proof (zb_nonul s SRNG) as NONUL. pose proof (zb_length s) as LZS.
    pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq fl) in FLB by lia.
    assert (BRNG : forall n, Forall (fun c0 => 0 <= c0 < 256)%Z (firstn n s)).
    { intros n. rewrite <- (skipn_O s). apply Forall_sub. eapply Forall_impl; [|exact SRNG]. cbv beta. intros. lia. }
    stmt (HS_TAIL fuel HH) as NX.
    set (len := Z.of_nat (length s)) in *.
    unfold ZERO_PAD.
    ienter.
    zs. zs. brf K0; [|exfalso; lia].
    destruct XP as [[-> ->] | [-> Hp]].
    - (* [comment removed for export] *)
      cbn [Z.b2z]. change ((-1) <? 0)%Z with true. cbn [andb].
      destruct (Z.leb_spec0 2147483647 len) as [BIG|SMALL]; [ileave; apply implAM_unr_l|].
      rewrite ?ift, ?iff.
      zs. zs. if_lit. zs. zs. zs.
      callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack) (n := 2147483647%Z) (r := rs);
        [ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
        | rewrite length_app, zb_length; cbn [length]; unfold zlength in *; lia | lia | lia
        | hypMU | hypWM | exact RCS
        | rewrite (strnlen_rl_cstr _ (zb s) slack NONUL) by lia; rewrite zb_length; eapply inreg_sub; [exact IRS | lia | unfold zlength in *; lia]
        | rewrite (strnlen_rl_cstr _ (zb s) slack NONUL) by lia; rewrite zb_length; unfold zlength in *; lia
        | rewrite length_app, zb_length; cbn [length]; eapply rng_sub'; [exact RGS | unfold zlength in *; lia] | exact RRS ]).
      rewrite (strnlen_res_cstr 0) by exact NONUL. rewrite zb_length. fold len. replace (Z.min len 2147483647) with len by lia.
      match goal with H : bytes_at _ ?mm P _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR1 end.
      zs. zs. if_lit.
      assert (NTH : nth_error (zb s ++ Z_to_bv 8 0 :: slack) (Z.to_nat len) = Some (Z_to_bv 8 0)).
      { rewrite nth_error_app2 by (rewrite zb_length; lia). rewrite zb_length. replace (Z.to_nat len - length s)%nat with 0%nat by lia. reflexivity. }
      pose proof (u8ro_read bsegs _ P (zb s ++ Z_to_bv 8 0 :: slack) len (Z_to_bv 8 0) _ STR1 NTH ltac:(lia) eq_refl) as RD.
      zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. zs. if_lit. zs. zs. zs. zs. zs. zs. zs.
      match goal with H : bytes_at _ ?mm P _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
      lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at bsegs mm P (zb s)) end.
      { pose proof STR2 as STR3. apply bytes_at_app in STR3. exact (proj1 STR3). }
      rewrite (@firstn_all2 Z (Z.to_nat len) s) by (unfold len; lia).
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := len) (prefix := []) (body := s) (BA := P) (PFXA := 68436%Z));
        [ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | exact SUB | eapply Forall_impl; [|exact SRNG]; cbv beta; intros; lia
        | unfold body_loc; zl | zl | unfold INT_MAX; zl
        | exists rs; split; [exact RCS | split; [eapply inreg_sub; [exact IRS | lia | unfold zlength in *; lia] | exact RRS]]
        | eapply rng_sub'; [exact RGS | unfold zlength in *; lia]
        | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | lia | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
      match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
    - (* [comment removed for export] *)
      replace (p <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb Z.b2z]. rewrite ?ift, ?iff.
      zs. zs. brf K1; [ | zs ].
      (* [comment removed for export] *)
      all: zs; zs.
      all: callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack) (r := rs);
        [ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
        | rewrite length_app, zb_length; cbn [length]; unfold zlength in *; lia | lia | lia
        | hypMU | hypWM | exact RCS
        | rewrite (strnlen_rl_cstr _ (zb s) slack NONUL) by lia; rewrite zb_length; eapply inreg_sub; [exact IRS | lia | unfold zlength in *; lia]
        | rewrite (strnlen_rl_cstr _ (zb s) slack NONUL) by lia; rewrite zb_length; unfold zlength in *; lia
        | rewrite length_app, zb_length; cbn [length]; eapply rng_sub'; [exact RGS | unfold zlength in *; lia] | exact RRS ]).
      all: rewrite (strnlen_res_cstr 0) by exact NONUL; rewrite zb_length; fold len.
      all: zs; zs; br K2; zs; zs; zs; zs; zs; zs; zs.
      all: match goal with H : bytes_at _ ?mm ?PP (zb _ ++ _) |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
      all: lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at bsegs mm P (zb (firstn (Z.to_nat (Z.min len p)) s)))
        by (pose proof STR2 as STR3; rewrite <- (firstn_skipn (Z.to_nat (Z.min len p)) s) in STR3; rewrite zb_app, <- app_assoc in STR3; apply bytes_at_app in STR3; exact (proj1 STR3)) end.
      all: assert (LF : zlength (firstn (Z.to_nat (Z.min len p)) s) = Z.min len p) by (unfold zlength; rewrite length_firstn; lia).
      all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := Z.min len p) (prefix := []) (body := firstn (Z.to_nat (Z.min len p)) s) (BA := P) (PFXA := 68436%Z));
        [ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | exact SUB | apply BRNG
        | unfold body_loc; rewrite LF; lia | rewrite LF; lia | rewrite LF; unfold INT_MAX; lia
        | exists rs; split; [exact RCS | split; [rewrite LF; eapply inreg_sub; [exact IRS | lia | unfold zlength in *; lia] | exact RRS]]
        | rewrite LF; eapply rng_sub'; [exact RGS | unfold zlength in *; lia]
        | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | lia | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
      all: match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PrintfCore.
End CANSEC1.
