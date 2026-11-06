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

  Hypothesis HS_INTC : S_INTC.
  Hypothesis HS_XLOOP : S_XLOOP.

  (* [comment removed for export] *)
  #[using="SFR LO GLO QHI HA SEP_F SEP_B HAP HVA RG_stk HS_INTC HS_XLOOP"] Lemma L_CV_X : S_CV_X.
  Proof.
    intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u t pfx s2s za pl plp ahi j128 digs pad _
           FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu Ht.
    pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
    pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
    stmt (HS_INTC fuel HH) as NX.
    unfold ALT_FORM.
    assert (Hl : (Z.land t 32 = 0 \/ Z.land t 32 = 32)%Z) by (destruct Ht as [-> | ->]; [right | left]; reflexivity).
    pose proof (hex_digits_length (Z.land t 32) u) as LH.
    assert (HRNG : Forall (fun c0 => 0 <= c0 < 256)%Z (hex_digits (Z.land t 32) u)).
    { eapply Forall_impl; [|apply hex_digits_range; exact Hl]. cbv beta. intros. Local Ltac2 Set LiaHints.tbl := fun () => "02]0?11801586693.16511801586693.16611822273140.15911822273140.16311822273140.1651328334446.169 1328334446.175 1328334446.176 15003208587.16316131571847.16317462492999.15919042827563.16719042827563.17319042827563.17420767975323.16320767975323.16521483538494.15921483538494.16321483538494.16521542523261.16521700301309.16522536103943.16323077509607.16823077509607.17423077509607.17523145753735.16823145753735.17423145753735.1752394497527.163 2688827190.158 2688893194.159 2691026847.159 2691026847.163 2691026847.165 27060081109.16627829487411.17527829487411.17630092641543.16530351702510.16930351702510.17530351702510.17631070687724.16931070687724.17531070687724.17632762049119.17432762049119.17533263823594.16933263823594.17533263823594.17633928676191.16633928676191.17233928676191.17334305264110.16934305264110.17534305264110.17634886392720.17835827935646.16835827935646.17435827935646.17536012197272.16436062510379.15936626036698.16836626036699.17437059289159.15937059289159.16537424966173.15937631032481.16637631032481.17237631032481.17339047133539.16939047133539.17539047133539.1763942199251.165 3942199251.171 3942199251.172 40347269539.15940347269539.1654105703320.168 4105703320.174 4105703320.175 41747852803.16344284318572.16644484923210.165445078394.168  445078394.174  445078394.175  4606055276.166 46271681008.16846898303580.16146898303580.16747760654131.16348098010007.16351386121459.16351721469139.16651721469139.17251721469139.17351792560534.15951792560534.16351792560534.16554121776830.16954121776830.17554121776830.17654465910932.16555223871902.16855223871902.17455223871902.1755531535850.159 55353115226.16655456739088.16355537228055.16855537228055.16955537228055.17455537228055.17555537228055.17656003042083.16356867524902.15956867524902.16356867524902.16557283686052.15957283686052.16557897851615.16757897851615.17357897851615.1745806267475.163 58665690269.16558665690269.17158665690269.17258708115388.16559110412935.16359959005346.15959959005346.16359959005346.16559976791292.16559976791292.17259976791295.17160111391000.16860111391000.17460111391000.17562438234458.16862438234458.17462438234458.17563767567220.15963767567220.16564286212051.16364656456728.16864656456728.17464656456728.17565227213690.16865227213690.17465227213690.17566201836243.16967281204924.16967281204924.17567281204924.17668360040037.15968360040037.16568500806127.15868585761514.16968585761514.17568585761514.1766948088766.159 6948088766.163 6948088766.165 7320613356.169 7320613356.175 7320613356.176 7355949818.168 7355949818.174 7355949818.175 8605673009.165 9852913534.164 9852913534.170 9852913535.171 00000?00N00a01401G01V01e02402C02R02l03?03R03e04404C04U04g05905O05e06406G06Z06m07I07k08M08\08n09C09U09g0:90:L0:`0;40;V0;e0<40<C0<Y0<o0=E0=Y0=m0>F0>_0?80?G0?V0?e0@40@C0@R0@e0A<0AS0Aj0B90BH0B`0C80CG0CV0Ce0D40DC0DR0Dn0EP0F20FA0FP0F_0Fn0G=0GP0Gc0H60HE0H^0Hm0I<0IK0IZ0J10JC0JR0Ja0K00K?0KN0K`0L20LD0LV0Lh0M:0MZ0N@0Nf0O50ON0Og0P@0PO0PP0P_0Q10QC0QU0Qg0R90RH0RZ0Rl0S>0SM0S\0Sn0T@0TR0Ta0U00U?0UN0V40VC0VV0Vi0W<0WN0W`0X20XH0X^0Y40YT0Z:0Z`0Zo0[>0[M0[c0\90\O0\^0\m0]<0]K0]^0^10^D0^S0^b0_30_J0_a0`80`G0`[0`o0aE0a[0b10b@0bO0b^0bm0c?0cQ0ccS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3Hi43LZB2LU3LDS2LHS3Hi43LZB2LU3LDS2LHS3Hi43LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS2LO3GLO3QHI3LZB2LU3LDS2LHS3QHI3LZB2LU3LDS2LHS3QHI3LZB2LU3LDS2LHS3QHI3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS2Hw3LZB2LU3LDS2LHS2Hw3LZB2LU3LDS2LHS2Hw3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3QHI3LZB2LU3LDS2LHS3QHI3LZB2LU3LDS2LHS3QHI3LZB2LU3LDS2LHS2LO5SEP_B3HAP3LZB2LU3LDS2LHS2LO5SEP_B3HAP2Hu3LZB2LU3LDS2LH2K0S2LO5SEP_B3HAP2Hu3LZB2LU3LDS2LH2K0S3LZB2LU3LDS2LHS2Hu3LZB2LU3LDS2LHS2Hu3LZB2LU3LDS2LH2K0S2Hu3LZB2LU3LDS2LHS2Hu3LZB2LU3LDS2LHS2Hu3LZB2LU3LDS2LHS3HAP3LZB2LU3LDS2LHS3LZB2LU3LDS2LH4POSTS3LZB2LU3LDS2LH4POSTS2LO5SEP_B3HAP2Hu3LZB2LU3LDS2LH2K0S3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS3LZB2LU3LDS2LH4POSTS3LZB2LU3LDS2LH4POSTS2LO3GLO2HA3LZB2LU3LDS2LHS2LO3GLO2HA3LZB2LU3LDS2LHS2LO3GLO2HA3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3Hfl3LZB2LU3LDS2LHS3HAP3HVA3LZB2LU3LDS2LHS3HAP3HVA3LZB2LU3LDS2LHS3HAP3HVA3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS2Hu2Ht3LZB2LU3LDS2LH2K0S2Hu2Ht3LZB2LU3LDS2LH2K0S3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS2LO5SEP_B3HAP3LZB2LU3LDS2LHS2LO5SEP_B3HAP2Hu3LZB2LU3LDS2LH2K0S2LO5SEP_B3HAP2Hu3LZB2LU3LDS2LH2K0S3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3HAP3LZB2LU3LDS2LHS3HAP3LZB2LU3LDS2LHS3HAP3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS2LO3GLO2HA3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3HAP3HVA3LZB2LU3LDS2LHS2LO3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LH2HBS3LZB2LU3LDS2LH2HBS3LZB2LU3LDS2LH2HBS2Hk3LZB2LU3LDS2LHS2Hk3LZB2LU3LDS2LHS2Hk3LZB2LU3LDS2LHS2LO3GLO5SEP_F3HAP3LZB2LU3LDS2LHS2LO3GLO5SEP_F3HAP2Hu3LZB2LU3LDS2LH2K0S2LO3GLO5SEP_F3HAP2Hu3LZB2LU3LDS2LH2K0S3LZB2LU3LDS2LHS2LO3GLO2HA3LZB2LU3LDS2LHS2LO3GLO2HA3LZB2LU3LDS2LHS2LO3GLO2HA3LZB2LU3LDS2LHS3LZB2LU3LDS2LHFS3LZB2LU3LDS2LHS2LO3LZB2LU3LDS2LHS2LO3LZB2LU3LDS2LHS2LO3LZB2LU3LDS2LHS2LO3LZB2LU3LDS2LHS2LO3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS2Hc3LZB2LU3LDS2LHS2Hc3LZB2LU3LDS2LHS2Hc3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LH2HBS3LZB2LU3LDS2LH2HBS3LZB2LU3LDS2LH2HBS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS2LO3GLO5SEP_F3HAP2Hu3LZB2LU3LDS2LH2K0S3LZB2LU3LDS2LHS3Hfl3LZB2LU3LDS2LHS3Hfl3LZB2LU3LDS2LHS3Hfl3LZB2LU3LDS2LHS2LO3LZB2LU3LDS2LHS2LO3LZB2LU3LDS2LHS2LO3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS2LO3GLO5SEP_F3HAP3LZB2LU3LDS2LHS2LO3GLO5SEP_F3HAP2Hu3LZB2LU3LDS2LH2K0S2LO3GLO5SEP_F3HAP2Hu3LZB2LU3LDS2LH2K0S3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3HAP3LZB2LU3LDS2LHS3HAP3LZB2LU3LDS2LHS3HAP3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LH1HS3HAP3HVA3LZB2LU3LDS2LHS3HAP3HVA3LZB2LU3LDS2LHS3HAP3HVA3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LH4POSTS3LZB2LU3LDS2LH4POSTS2LO3GLO3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS2LO3GLO3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS3LZB2LU3LDS2LHS2LO3LZB2LU3LDS2LHS2LO3LZB2LU3LDS2LHS2LO3LZB2LU3LDS2LH".
lia. }
    ienter.
    zs. zs. zs. zs. brf K0.
    - (* [comment removed for export] *)
      replace (u =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K0). cbn [negb andb].
      zs. zs. zs. zs.
      jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := []) (BA := (q + -368)%Z) (PFXA := 68436%Z));
        [ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
        | rewrite K0, hex_digits_0; apply bytes_at_nil; lia | exact HRNG | rewrite K0, hex_digits_0; zl | zl
        | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | lia | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
    - replace (u =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K0). cbn [negb andb].
      zs. zs.
      replace (Z.land t 32) with (Z.land t 32) by reflexivity.
      stmt HS_XLOOP as NL.
      callx (eapply NL with (l := Z.land t 32) (x := u) (j := 24%Z) (ds := digs);
             [ exact MI | exact DIG | lia | exact Hl | unfold zlength; lia | f_equal; lia ]).
      destruct_ands POST. cbv zeta in *.
      match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ =>
        rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
      pose proof (rw_cells_bytes_at' _ _ _ _ DIG') as BODY. cbn [cells_bytes cbytes app] in BODY. rewrite app_nil_r in BODY.
      apply bytes_at_app in BODY. destruct BODY as [_ BODY]. rewrite length_firstn, LDS in BODY.
      replace (Z.of_nat (Nat.min (Z.to_nat (24 - zlength (hex_digits (Z.land t 32) u))) 24)) with (24 - zlength (hex_digits (Z.land t 32) u))%Z in BODY by (unfold zlength in *; lia).
      zs. zs. brf K1.
      + (* [comment removed for export] *)
        replace (Z.land fl 8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K1). cbn [negb andb].
        zs. zs. zs. zs. zs. zs. zs. zs.
        destruct Ht as [-> | ->]; cbn [Z.eqb Pos.eqb].
        * jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 120]%Z)
                                 (BA := (q + -392 + (24 - zlength (hex_digits (Z.land 120 32) u)))%Z) (PFXA := 68443%Z));
            [ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | exact BODY | exact HRNG | unfold zlength in *; lia | zl
            | intros mq MIq; exact (pfx_sub mq 7 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | lia | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
          match goal with H : SINK _ _ |- _ => exact H end.
        * jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 88]%Z)
                                 (BA := (q + -392 + (24 - zlength (hex_digits (Z.land 88 32) u)))%Z) (PFXA := 68441%Z));
            [ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
            | exact BODY | exact HRNG | unfold zlength in *; lia | zl
            | intros mq MIq; exact (pfx_sub mq 5 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | lia | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
          match goal with H : SINK _ _ |- _ => exact H end.
      + (* [comment removed for export] *)
        replace (Z.land fl 8 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K1). cbn [negb andb].
        zs. zs. zs.
        jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [])
                               (BA := (q + -392 + (24 - zlength (hex_digits (Z.land t 32) u)))%Z) (PFXA := 68436%Z));
          [ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
          | exact BODY | exact HRNG | unfold zlength in *; lia | zl
          | intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | lia | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
        match goal with H : SINK _ _ |- _ => exact H end.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PrintfCore.
End CANSEC1.
