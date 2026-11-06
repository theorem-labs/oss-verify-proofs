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


  (* [comment removed for export] *)
  #[using="LO GLO QHI HA HAP HVA RG_stk RG_img"] Lemma L_PRO : S_PRO.
  Proof.
    intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f Q _ ST0 MI0 BY0 VAA0 SSP0 Hf CONT.
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO. unfold zlength in *.
    destruct SSP0 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. fix_rsegs.
    pose proof (zb_length fmt) as LZB. pose proof (u64s_length slots) as LU. unfold va_area in VAA0.
    pose proof (munch_refl [(q + -544, q)]%Z m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
    pose proof ST0 as ST.
    Local Ltac2 Set LiaHints.tbl := fun () => "03M0?10272362876.11411201005823.11311508118739.11411752073758.11711957068056.11712155184024.11712382228435.11512595585491.11613420688383.11313597299870.11713600341715.11613667971741.11413680293528.11713897906899.11914917775615.11315586823123.12015689378334.11716093407827.11416524822296.12216553225630.11717405756062.11718233711256.12118577971102.11818615078739.11518847311384.11720135743403.1202091822494.117 21100895787.11721334325971.11721480739864.12221612632403.11821680855704.11722127343571.11522143612115.11422700267513.11423178748056.11624036004348.11524036004348.11624036004348.11724036004348.11824036004348.12024036004348.12124036004348.12224295764126.11824640625875.11325139515390.11225840440989.1172592859293.112 26080215251.11726254586835.1142663245080.118 26719358360.117268530974.121  27188222878.11827212391576.1162725810462.117 27324848595.11027498241560.11727503144222.12027648403155.116278684627.119  28072922155.12128146828627.11528372451870.11728486540958.12229119334483.11229238396318.11530139634259.11830157702271.1133026317523.113 30425733022.11830466574750.11530568039070.11731161366443.11931188841880.11731257565214.1163145767960.115 31935008925.11532103981611.11632377758494.11632789514963.11832861791901.11833245239326.11633325503646.11733691640562.11633733759.113   34146947795.1163464842776.118 34770702291.11434972189341.11435115442845.11435215434392.12035245701631.1133565375699.113 35938450643.11436158635987.12036344913816.1203687877790.117 37075292184.11737335211388.11437376304920.11837856796317.11338266762648.11638573664880.11838717616285.11439385456414.11739576479384.11739638303531.11739659001331.11739791549024.11239895554200.12040120534558.11740166465619.1154019199787.117 40208238251.11640334639006.11840396364156.11441133846827.11641713439999.11342194730282.10442741387947.11642917525912.11743002532126.11743121191467.11643666971947.11443747137432.12043790126035.11543858822558.11543930011632.11844220693675.11544534409240.12244632013470.12245003250643.11945628037918.1224592356504.122 45983645651.11246202211795.11546436265939.11247276489374.12247353912944.1184772068376.117 47790018456.11647966531614.12048753977240.12149432976664.11749438652465.11049769706782.1214997082269.112 50279408152.11850483928734.12250664164139.11750686062066.1165072571819.121 51030502686.12051234361003.11651604857624.12251771777451.11652151318827.11452219370323.11452571404445.11953236108203.11653385592787.11553828067997.11453839360895.11354076858136.11854214273107.11555238157483.11955545848606.11656032817310.11856665434835.11457249640403.11557525976221.11457604283549.11557908368029.11358222110931.1155888109310.112 59457942168.11759595594526.12259777015582.11759789064349.11460063104926.11860103006232.1156014957611.121 60231693779.11560481712158.12060576894110.11760641463965.11460914404217.11161122271955.11461510633629.11962766187947.11563577150621.11563654713624.11763692058667.11664240569043.1136561911891.115 65850876883.11466141418776.11566267431763.1206637974685.115 67188671006.11767320211736.11567523405694.11167549937309.11767723773464.11868504659008.1067282666904.122 7435684254.115 7502478104.117 7581339987.119 786424600.118  7936367518.118 7986827800.118 858367615.113  8714569246.117 8832905373.114 8841584792.117 8985252819.114 9042327676.114 9371665053.119 945828248.117  00000;00F00N00^00m01<01D01O01Z01j02502=02L02T02_02j03<03G03V03h04:04I04[04f05505A05Q05]05e06406?06N06Y06a07207A07I07Q07Y07a07i08108908K08V08a08i09109909A09P09_0:10:C0:R0:b0:j0;90;K0;V0;^0;j0<50<G0<Y0<a0=30=>0=I0=Q0=a0>30>C0>O0>^0>n0?=0?E0?Q0?c0?k0@30@E0@W0@b0@m0A80AG0AO0AW0A_0An0B90BD0BL0BW0Bf0C60CE0CP0C_0Cg0D60DA0DI0D[0Dj0E60EA0EI0EX0Ej0F50FA0FM0F]0Fh0G40G?0GJ0GV0Ge0H70HC0HO0H^0Hf0I60IA0IM0I\0In0J60JF0JU0J]0Jh0K00K@0KK0KZ0Ki0L90LH0LW0L_0Lo0M70MF0MV0Mb0Mm0N90NI0NU0Nd0O00O<0OG0OO0O[0Oc0Ok0P60PE0PP0P\0Pl0Q<0QD0QL0QT0Q\0Qd0Qo0R:0RI0R[0Rk0S30SE0ST0S`0Sk0T=0TO0TW0Tb0Tj0U20U>0UF0UU0Ua0Ui0V40V<0VK0VV0V^0Vn0W=0WH0WP0W_0Wg0X60XF0XU0X`0Xo0Y?0YN0YY0Yi0Z10Z@0ZH0ZS0Z[0ZjS2LO3LZB2LUS2LO3LZB2LUS3LZB2LUS3HAP3HVA3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LU2HBS2LO3LZB2LUS3HAP3HVA3LZB2LUS3LZB2LU2HBS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS2LO3LZB2LUS3LZB2LU2HBS2LO3GLO2HA3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LUS3QHI3LZB2LUS3HAP3HVA3LZB2LUS3QHI3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LUS3LZB2LU2HBS3LZB2LUS2LO3HAP3LZB2LU1HS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS2LO3GLO2HA3LZB2LUS3LZB2LU2HBS2LO3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS3HAP3HVA3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS3LZB2LU2HBS3LZB2LUS3QHI3LZB2LUS3LZB2LU2HBS2LO3GLO2HA3LZB2LUS2LO3GLO2HA3LZB2LUS3LZB2LUS2LO3GLO2HA3LZB2LUS3LZB2LU2HBS2LO3LZB2LUS3LZB2LUS3HAP3HVA3LZB2LUS2LO3GLO2HA3LZB2LUS3HAP3HVA3LZB2LUS3QHI3LZB2LUS2LO3GLO3LZB2LUS3HAP3HVA3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3QHI3LZB2LUS2LO3GLO2HA3LZB2LUS3LZB2LUS3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3LZB2LUS2LO3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS2LO3LZB2LUS3LZB2LU2HBS3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LUS3HAP3HVA3LZB2LUS2LO3GLO3LZB2LUS2LO3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS2LO3LZB2LUS3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS3QHI3LZB2LUS2LO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS3LZB2LU2HBS3QHI3LZB2LUS3QHI3LZB2LUS3HAP3HVA3LZB2LUS2LO3LZB2LUS3QHI3LZB2LUS2LO3LZB2LUS2LO3LZB2LUS3QHI3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS3QHI3LZB2LUS3QHI3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3HAP3HVA3LZB2LUS2LO3LZB2LUS3QHI3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS3LZB2LUS3HAP3HVA3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3LZB2LU2HBS3LZB2LUS3HAP3HVA3LZB2LUS2LO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS3HAP3HVA3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS3HAP3HVA3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS3HAP3HVA3LZB2LUS3QHI3LZB2LUS2LO3LZB2LUS3QHI3LZB2LUS3HAP3HVA3LZB2LUS3QHI3LZB2LUS2LO3GLO3LZB2LUS3QHI3LZB2LUS3QHI3LZB2LUS3LZB2LU2HBS3LZB2LUS3QHI3LZB2LUS3LZB2LUS3LZB2LUS2LO3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU2HBS3QHI3LZB2LUS3HAP3HVA3LZB2LUS3HAP3HVA3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LU2HBS2LO3LZB2LUS2LO3GLO3LZB2LUS2LO3GLO2HA3LZB2LUS3HAP3HVA3LZB2LUS3LZB2LUS2LO3GLO2HA3LZB2LUS2LO3GLO3LZB2LUS3QHI3LZB2LUS3LZB2LU2HBS2LO3GLO2HA3LZB2LUS2LO3GLO2HA3LZB2LUS3LZB2LUS2LO3LZB2LUS3LZB2LUS3LZB2LUS3QHI3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS3QHI3LZB2LUS3LZB2LUS3LZB2LU2HBS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU2HBS3LZB2LUS3HAP3HVA3LZB2LUS2LO3GLO3LZB2LUS2LO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS3HAP3HVA3LZB2LUS2LO3GLO3LZB2LUS3LZB2LU2HBS2LO3GLO3LZB2LUS3HAP3HVA3LZB2LUS2LO3GLO3LZB2LUS2LO3LZB2LUS3HAP3HVA3LZB2LUS3LZB2LUS2LO3GLO3LZB2LUS3LZB2LUS2LO3LZB2LUS3LZB2LUS2LO3GLO3LZB2LU".
carve_frame 544%nat ST.
    do 43 zs.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (CB 40 ?ja :: _) => set (jA := ja) in FR; clearbody jA end.
    lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 320 ?jb :: _) => set (jB := jb) in FR; clearbody jB end.
    apply (proj1 (rw_cells_app bsegs _ _ [_;_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [LOWa FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    replace (q + -544 + Z.of_nat 432)%Z with (q + -112)%Z in FRhi by lia.
    apply (rw_cells_split_CB bsegs _ _ [_;_;_;_;_;_;_;_;_;_] 320 _ [] [16; 24; 24; 256]%nat) in LOWa; [ | cbn; lia ].
    cbn [mk_CB_cells app] in LOWa.
    apply (rw_cells_split_CB bsegs _ _ [] 40 _ _ [8; 8; 8; 8; 8]%nat) in LOWa; [ | cbn; lia ].
    cbn [mk_CB_cells app] in LOWa.
    apply (rw_cells_split_CB bsegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] 16 _ _ [8; 8]%nat) in LOWa; [ | cbn; lia ].
    cbn [mk_CB_cells app] in LOWa.
    do 7 c8ify LOWa.
    apply (proj1 (rw_cells_app bsegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in LOWa. destruct LOWa as [LOW DP]. cbn [cells_size csize Nat.add app] in DP.
    apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in DP. destruct DP as [DIG PAD]. cbn [cells_size csize Nat.add app] in PAD.
    replace (q + -544 + Z.of_nat 152)%Z with (q + -392)%Z in DIG by lia.
    replace (q + -544 + Z.of_nat 152 + Z.of_nat 24)%Z with (q + -368)%Z in PAD by lia.
    eapply CONT; [ | exact MU | exact LOW | exact DIG | exact PAD ].
    unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area.
    split; [assumption|]. split; [eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|].
    split; [exact FRhi|]. split; [exact ST|]. split; [exact BY0|]. split; [exact VAA0|]. split; [exact SSP1|exact SSP2].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PrintfCore.
End CANSEC1.
