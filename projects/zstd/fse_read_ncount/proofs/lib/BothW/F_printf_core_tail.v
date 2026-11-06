(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import Stdio_kit Stdio_kitI F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import Printf_zfacts F_printf_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import F_printf_core_common.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".
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
Hypothesis HA : (A + zlength fmt <= 626688)%Z.
Hypothesis SEP_F : ((636800 <= Fp /\ Fp + 232 <= 664888) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((6247704 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.
Hypothesis KH : (KHIGH <= lo)%Z.
Hypothesis RSK : (r_lo rstk <= lo /\ q <= r_hi rstk)%Z.
Hypothesis RFM : inreg rfmt A (zlength fmt).
Hypothesis RPF : inreg rfmt 68452 9.
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
Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS RB SINK TOPOK OUT TOK HOUT RNG q gp tp m0 lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS RB SINK TOPOK OUTFP RNG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Ltac hush := idtac.
Ltac len_norm := unfold zlength, zrepeat; rewrite ?repeat_length, ?zb_length, ?length_map, ?length_firstn, ?length_skipn, ?length_app; cbn [length]; try rewrite !Z2Nat.id by lia.
Ltac inreg_side := solve [ unfold inreg in *; len_norm; unfold zlength in *; lia ].
Ltac rng_side :=
lazymatch goal with |- rng ?RNG0 ?lo' ?len' =>
first [ assumption
| match goal with H : rng RNG0 ?lo ?len |- _ => apply (rng_sub' RNG0 lo len lo' len' H); solve [len_norm; unfold zlength in *; lia] end ]
end.
Ltac hypMU := match goal with H : munch _ m0 _ |- _ => exact H end.
Ltac hypWM := match goal with H : wmono _ m0 _ |- _ => exact H end.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
Tactic Notation "jump" tactic3(tac) := eapply evtF_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
eapply implAM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
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
[ match goal with H : rw_cells _ _ 632224 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 6247696 _ |- _ => exact H end ]
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
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
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
Hypothesis HS_T1 : S_T1.
Hypothesis HS_T2 : S_T2.
#[using="Type"] Lemma conv_tail_k : forall (a1 a2 a3 a4 a5 a6 : M St unit) (v : Z) (k : Z -> M St Z) s Q ms,
implAM RNG (a1 ;;; a2 ;;; a3 ;;; a4 ;;; a5 ;;; a6 ;;; k v) s Q ms ->
implAM RNG (x <- (a1 ;;; a2 ;;; a3 ;;; a4 ;;; a5 ;;; a6 ;;; mret v) ;; k x) s Q ms.
Proof.
clear. intros a1 a2 a3 a4 a5 a6 v k s Q ms H.
eapply implAM_teq; [| exact H]. apply mteq_sym.
repeat (eapply mteq_trans; [apply mteq_assoc|]; apply mteq_cong; intros _).
apply mteq_ret_l.
Qed.
#[using="SFR LO GLO QHI HA SEP_F SEP_B HAP HVA BS0 RG_stk HS_T1 HS_T2"] Lemma L_TAIL : S_TAIL.
Proof.
intros fuel HH x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p prefix body BA PFXA s2s za plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BLOC BHI BIM REGB RGb HPFX PRNG PF0 PF1 PL2 PFlo PFhi Hi4 Hfl Hw Hp Hc.
destruct REGB as (rb & RCb & IRb & RRb).
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW. unfold body_loc in BLOC.
pose proof (bytes_at_bound _ _ _ _ BODY) as BB. pose proof (zb_length body) as LB. rewrite LB in BB.
set (n := Z.of_nat (length body)) in *. set (pl := Z.of_nat (length prefix)) in *.
unfold conv_tail. unfold zlength. fold n. fold pl. cbv zeta.
ienter.
Local Ltac2 Set LiaHints.tbl := fun () => "01X0?10013579028.17810013579029.17810726434877.17510726435004.17611931241720.17811931241721.17812918402330.17813982842684.17813982842685.17818725221342.17320038834899.17820093761198.17320631100810.17820631100811.17822640680452.17822640680453.17822699178698.17822699178699.17823193536498.17823193536499.17823568626820.17823568626821.17824437507741.18125384949884.1832572271933.178 27165442373.17527165442500.17627476353354.17827476353355.17828968518718.17828968518719.17830751000210.17830751000211.17831158168052.18131158168057.18231158168058.18432412935096.17832412935097.17834605986108.17834861672711.17334861672838.17434884295579.18536540390392.17836540390393.17836617377956.17836617377957.17837025140364.17837025140365.17837274455756.17837274455757.1783780080445.175 3780080572.176 38623111670.17339227494304.1763942199251.180 3942199251.181 43293545490.17843293545491.17844629354747.1784701196031.180 4701196031.181 4729360541.184 48881644746.17848881644747.17849738257407.17749799750301.17851186947154.17851186947155.17852193505174.1785313000423.174 54005891398.17854005891399.17856342124696.17856342124697.1785660671580.178 5660671581.178 57179046150.17857179046151.17857704787810.17857704787811.17858487675802.18358487675802.18459576980277.17760373108790.18160833911574.17860833911575.17861809962126.17861809962127.17861937685140.18161937685146.18462699989938.17862699989939.17863696756947.18163696756947.18265887914963.18467117997754.17467763243807.1748634224974.181 9387742206.178 9387742207.178 9852913535.179 9852913535.180 9865609510.174 9865609639.173 00000A00R00`00n00o01001101201301B01M01[01\01]01^01_01m02;02<02=02Z03703B03P03Q03e04904:04;04<04=04K04Y04j04k05<05=05>05?05N05c06206G06\06]06^06l07:07H07V07g08;08P08^08i09409E09V09W09e0:30:>0:?0:@0:N0:Y0:Z0:[0:i0;=0;>0;?0;@0;A0;B0;C0;D0;E0;F0;G0;V0;e0<00<B0<C0<D0<E0<F0<[0=00=A0=R0=]0=h0>30>B0>S0>e0>f0>g0?50?C0?Q0?_S3LZB2LU2LB2K12K3S3LZB2LU2LB2K12K3S2Hw3LZB2LU2LBS2Hw3LZB2LU2LBFFFFFS3PL23LZB2LU2LBS3LZB2LU2LBS2Hp3LZB2LU2LBFFFFS3LZB2LU2LB2K1S3LZB2LU2LB2K1FFS2Hw3LZB2LU2LB2K12K32Hc2K22K4S2Hw3LZB2LU2LB2K12K32Hc2K22K4S3LZB2LU2LBS2LO3LZB2LU2LBFS2Hp3LZB2LU2LB2K12K2S2Hw3LZB2LU2LB2K22K3FFFFS3LZB2LU2LB2K1S3LZB2LU2LB2K1S2Hp3LZB2LU2LB2K1FS2Hp3LZB2LU2LB2K1FFFS3BIM3LZB2LU2LBS3BIM2Hp3LZB2LU2LB2K1S3Hfl3LZB2LU2LBS3BIM2Hp3LZB2LU2LB2K1S3BIM2Hp3LZB2LU2LB2K1FFS3LZB2LU2LB2K1S3LZB2LU2LB2K1S3LZB2LU2LB2K1S3LZB2LU2LB2K1S3LZB2LU2LB2K12K2S2Hw3LZB2LU2LB2K22K3S3BIM2Hp3LZB2LU2LB2K1S2Hc3LZB2LU2LBS3LZB2LU2LBS3LZB2LU2LBS3LZB2LU2LB2K12K3S3LZB2LU2LB2K12K3FS2LO3LZB2LU2LBS2LO3LZB2LU2LBS3LZB2LU2LBFFS2LO3LZB2LU2LBS3LZB2LU2LBFFS3LZB2LU2LB2K5S2Hp3LZB2LU2LB2K12K2FFFFFFFFFFS3PL23LZB2LU2LBS3PL23LZB2LU2LBS3LZB2LU2LBS3BHI3LZB2LU2BB2LBFFFFS3BIM2Hp3LZB2LU2LB2K1S3BIM2Hp3LZB2LU2LB2K1S3LZB2LU2LB2K12K3S3LZB2LU2LB2K12K3S3LZB2LU2LBS3LZB2LU2LBS3LZB2LU2LBS3PL23LZB2LU2LBS3LZB2LU2LB2K12K2S3BHI3LZB2LU2BB2LBFFS2LO3LZB2LU2LBS2LO3LZB2LU2LBS2Hp3LZB2LU2LBS2Hp3LZB2LU2LB".
zs. rewrite (sextw_small p) by lia. zs. replace (BA + n - BA)%Z with n by lia. zs. zs. zs.
brf K1; [ | zs ].
all: zs; try rewrite (sextw_small p) by lia; fixr; zs; zs; fixr; zs; brf K2;
[ replace (INT_MAX - pl <? Z.max p n)%Z with true by (symmetry; apply Z.ltb_lt; unfold INT_MAX; lia); ileave; apply implAM_unr_l
| replace (INT_MAX - pl <? Z.max p n)%Z with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia) ].
all: zs; zs; zs; fixr; zs; zs; zs; brf K3; [ | zs ].
all: zs; brf K4;
[ replace (INT_MAX - c <? Z.max w (pl + Z.max p n))%Z with true by (symmetry; apply Z.ltb_lt; unfold INT_MAX; lia); ileave; apply implAM_unr_l
| replace (INT_MAX - c <? Z.max w (pl + Z.max p n))%Z with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia) ].
all: zs; zs; zs; zs; brf K5.
all: ileave; apply conv_tail_k.
all: match goal with
| K : Z.land ?flv 73728 <> 0%Z |- _ =>
unfold mpad at 1; change (Z.lor LEFT_ADJ ZERO_PAD) with 73728%Z; rewrite (proj2 (Z.eqb_neq _ 0) K); cbn [negb orb]; apply implAM_ret_l;
stmt (HS_T2 fuel HH) as NX2;
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := Z.max w (pl + Z.max p n)) (pq := Z.max p n) (args := args)
(PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ]
| K : Z.land ?flv 73728 = 0%Z |- _ =>
stmt (HS_T1 fuel HH) as NX1;
jumpM (eapply NX1 with (k := k) (i4 := i4) (c := c) (w := w) (wq := Z.max w (pl + Z.max p n)) (pq := Z.max p n) (args := args)
(PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia | exact K ]
end.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PrintfCore.
End CANSEC1.
