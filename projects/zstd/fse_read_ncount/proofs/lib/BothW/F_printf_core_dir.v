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
Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS RB SINK TOPOK OUT TOK HOUT RNG q gp tp m0 lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Notation sfx := (sfx fmt).
Notation SPv := (Z_to_bv 64 (q + -544)).
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
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
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
Hypothesis HS_FLAGS : S_FLAGS.
Hypothesis HS_WIDTH : S_WIDTH.
Hypothesis HS_PREC : S_PREC.
Hypothesis HS_STATE : S_STATE.
#[using="HF LO RG_stk RG_fmt HS_FLAGS HS_WIDTH HS_PREC HS_STATE"] Lemma L_DIR : S_DIR.
Proof.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q i d rest pfx s2s za pl plp alo ahi j128 _
FI LOW Hi Hi1 PD HK.
pose proof FI as FI'. dest_finv FI. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
pose proof (parse_dir_shape _ _ _ PD) as (POSN & SH).
destruct (parse_flags (sfx (i + 1)) 0) as [fl s1] eqn:PF.
destruct SH as (Efl & c1' & s1b & Es1 & N42 & s2 & G & c2 & s2b & Es2 & PX).
destruct (parse_flags_suffix _ _ _ _ PF) as (n1 & Hs1 & Hn1). rewrite sfx_skipn in Hs1 by lia. set (k1 := (i + 1 + Z.of_nat n1)%Z) in Hs1.
rewrite Hs1 in Es1. destruct (sfx_cons_inv fmt k1 c1' s1b ltac:(lia) Es1) as (Hk1 & Ec1' & Es1b).
destruct (getint_suffix _ _ _ _ G) as (n2 & Hs2 & Hn2). rewrite Hs1, sfx_skipn in Hs2 by lia. set (k2 := (k1 + Z.of_nat n2)%Z) in Hs2.
rewrite Hs2 in Es2. destruct (sfx_cons_inv fmt k2 c2 s2b ltac:(lia) Es2) as (Hk2 & Ec2 & Es2b).
Local Ltac2 Set LiaHints.tbl := fun () => "01Z0?11483605265.19112507726676.20512507726676.22012523110867.20512523110867.22012526625365.18412526625492.18213075202069.21313075202069.21713897906899.18513897906899.18914310072823.20514310072823.22014795172235.17614939502105.19015364638931.21315751230903.18016078154741.19216078154741.19516080219135.17816867068942.19416944440073.20516944440073.22018235932694.18418235932823.18220043567762.20520631100863.18522462746212.18222462746341.18422561301476.19322563500808.20322638503939.18422638504066.18222640680497.18522642330501.20522642330501.22022939927385.17023191368052.18223191368181.18423193536455.18523196242547.20523196242547.22025429519210.18225429519339.18425775293992.18225775294121.18426296115031.21327470345419.20527470345419.22027474171725.18427474171852.18227476353407.18527504392570.18227504392699.18428571384179.18428571384306.18230384227778.2203317811226.196 3430228316.171 3432423143.179 3432997638.175 3434357062.179 3434357191.180 34774493576.2183542557139.185 35932142342.18235932142471.18436211075190.18539286293099.20543048805490.18443048805619.18243048806389.18143142334568.1804377213522.205 4377213522.220 43930011645.18443930011645.18846975609589.18548410040606.18448410040735.18248879984971.20548879984971.22048883810892.18248883811021.18449985790935.20549985790935.22049990336593.18449990336720.18251184902741.18451184902868.18253349346893.20553349346893.22055978527891.18557154485530.19457486141545.17859308628304.18159976203207.17862773180056.20562773180056.22064913144385.18264913144512.18465627129575.2207184070965.192 7191124532.178 7995767509.212 7995767509.216 00000G00H00I00J00K00L00M00j01G01W01g01h01i01j01k02C02S02n03E03\04004104204304404D04E04F04G04^05505605705805905:05N05O05P05Q05R05S05g06;06<06=06V06W06X06Y06Z06[06\06]06^06_07307J07b08:08R08i09A09^09n0:B0:V0:k0;?0;R0;e0<90<:0<N0<f0=90=L0=M0=N0=O0=P0=Q0=R0=S0=T0=U0=V0=W0=X0=Y0=Z0=[0=\0>40>L0>d0?;0?<0?=0?R0?g0@?0@U0@V0A10ALS2Hi3LZB2LU3Hn13Hn23Hi2FFFFFFS3LZB2LU3Hn13Hn23Hn34Hk303Hk3S3LZB2LU3Hn13Hn23Hn34Hk303Hk3S3LZB2LU3Hn13Hn2S3LZB2LU3Hn13Hn2FFFFS3LZB2LU3Hn13Hn23Hn33Hk3S3LZB2LU3Hn13Hn2S2Hi3LZB2LU3Hn13Hk13Hn23Hk'S2Hi3LZB2LU3Hn13Hk13Hn2S2Hi3LZB2LU3Hn13Hk13Hn2S3LZB2LU3Hn13Hn23RGkFFFFS3LZB2LU3Hn13Hn2FFFS2Hi3LZB2LU3Hn13Hn23Hk2S2Hi3LZB2LU3Hn13Hn23Hk2FFFFFS3LZB2LU3Hn13Hk13Hn2FFFFFS3LZB2LU3Hn13Hn23Ek1S3LZB2LU3Hn13Hn23Ek1FFS3LZB2LU3Hn13Hn24Hk213Hn3FFFFFFFFFS3LZB2LU3Hn13Hn23Hn3S2Hi3LZB2LU3Hn13Hn23Hk'S2Hi3LZB2LU3Hn13Hn24Hi1'S2Hi3LZB2LU3Hn13Hn24Hi1'S2Hi3LZB2LU3Hn13Hn24Hi1'S2Hi3Hi13LZB2LU3Hn13Hn2S2Hi3LZB2LU3Hn13Hn24Hi1'S3LZB2LU3Hn13Hn23Hn34Hk303Hk3S3LZB2LU3Hn13Hn2S3LZB2LU3Hn13Hn23Ek1S3LZB2LU3Hn13Hn23Ek1S3LZB2LU3Hn13Hn24Hi1'S3LZB2LU3Hn13Hn23Hk2S3LZB2LU3Hn13Hn22RGS3LZB2LU3Hn13Hn22RGS3LZB2LU3Hn13Hn23RG0FS3LZB2LU3Efl3Hn13Hn2S3LZB2LU3Efl3Hn13Hn23Hn3S2LO3LZB2LU3Hn13Hn2S2LO3LZB2LU3Hn13Hn2FFFFFFFFFFFFFFFFS2Hi3LZB2LU3Hn13Hn24Hk2'S2Hi3LZB2LU3Hn13Hn24Hi1'S3LZB2LU4POSN3Hn13Hn22K1S2Hi3LZB2LU3Hn13Hn23Hi2FFS3LZB2LU3Hn13Hn24Efl0S3LZB2LU3Hn13Hn24Efl0S3LZB2LU3Hn13Hn23Hn33Hk3S3LZB2LU3Hn13Hn22RG2HcFS2Hi3LZB2LU3Hn13Hn23Hk23Hn3S2Hi3LZB2LU3Hn13Hn23Hk23Hn3".
assert (Hi1' : (i + 1 < zlength fmt)%Z) by zl.
rewrite (sfx_cons fmt (i + 1)) in POSN, PF by zl.
assert (POSTFLAGS : forall (t0 t1 a3 a4 a5 a6 a7 : word),
evtF bsegs RNG Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) a3 a4 a5 a6 a7
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x8f858) fc None m (seg_rom bsegs))).
{ intros t0 t1 a3 a4 a5 a6 a7.
pose proof (parse_flags_range (sfx (i + 1)) 0 ltac:(lia)) as FLR. rewrite (sfx_cons fmt (i + 1)), PF in FLR by zl. cbn [fst] in FLR.
stmt HS_WIDTH as NXW. jump (eapply NXW with (k1 := k1) (w := d_w d) (s2 := s2); [exact FI' | exact LOW' | lia | rewrite <- Hs1; exact G | rewrite Hs2, Es2; discriminate | ]).
intros k2' t0' t1' a1' a3' a4' a5' a6' a7' Hk2' Hs2' Hnd Hw.
assert (k2' = k2).
{ pose proof (sfx_length fmt k2 ltac:(zl)) as L1. pose proof (sfx_length fmt k2' ltac:(zl)) as L2. rewrite <- Hs2', Hs2 in L2. lia. }
subst k2'.
stmt HS_PREC as NXP. jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := (if d_xp d then k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 else k2)%Z);
[exact FI' | exact LOW' | lia | | ]).
{ destruct PX as [(N46 & Hp & Hxp & Ht & Hrest & CT) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & Es3 & CT)].
- left. rewrite <- Ec2, Hxp. repeat split; try assumption; reflexivity.
- right. rewrite Hxp. rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
rewrite Hs3 in Es3.
assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
destruct (sfx_cons_inv fmt (k2 + 1 + Z.of_nat n3) (d_t d) rest Hk30 Es3) as (Hk3 & Et & Erest).
assert (EK : (k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 = k2 + 1 + Z.of_nat n3)%Z).
{ rewrite Es2b, Erest. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)). pose proof (sfx_length fmt (k2 + 1 + Z.of_nat n3 + 1) ltac:(zl)). unfold zlength in *. lia. }
rewrite EK. split; [congruence|]. split; [reflexivity|]. split; [zl|]. split; [rewrite <- Ec3; exact N42q|].
split; [rewrite <- Es2b, <- Hs3; exact G2 | zl]. }
intros a1q a3q a4q Hp.
destruct PX as [(N46 & Hpq & Hxp & Ht & Hrest & CT) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & Es3 & CT)].
- rewrite Hxp. cbn [Z.b2z].
stmt HS_STATE as NXS. jump (eapply NXS with (k3 := k2) (ty := d_ty d); [exact FI' | zl | rewrite <- Ec2; exact CT | ]).
intros a2q a3q2. rewrite Hxp in HK. cbn [Z.b2z] in HK.
jump (apply (HK (k2 + 1)%Z); [zl | rewrite Hrest, Es2b; reflexivity | replace (k2 + 1 - 1)%Z with k2 by lia; rewrite <- Ec2, Ht; reflexivity | lia | lia | lia]).
- rewrite Hxp. cbn [Z.b2z]. rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
rewrite Hs3 in Es3.
assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
destruct (sfx_cons_inv fmt (k2 + 1 + Z.of_nat n3) (d_t d) rest Hk30 Es3) as (Hk3 & Et & Erest).
assert (EK : (k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 = k2 + 1 + Z.of_nat n3)%Z).
{ rewrite Es2b, Erest. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)). pose proof (sfx_length fmt (k2 + 1 + Z.of_nat n3 + 1) ltac:(zl)). unfold zlength in *. lia. }
rewrite EK.
stmt HS_STATE as NXS. jump (eapply NXS with (k3 := (k2 + 1 + Z.of_nat n3)%Z) (ty := d_ty d); [exact FI' | zl | rewrite <- Et; exact CT | ]).
intros a2q a3q2. rewrite Hxp in HK. cbn [Z.b2z] in HK.
jump (apply (HK (k2 + 1 + Z.of_nat n3 + 1)%Z); [zl | exact Erest | replace (k2 + 1 + Z.of_nat n3 + 1 - 1)%Z with (k2 + 1 + Z.of_nat n3)%Z by lia; symmetry; exact Et | lia | lia | lia]). }
assert (FL34 : forall (a3 a4 a5 : word), evtF bsegs RNG Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt (i + 1))) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 (Z_to_bv 64 1) x17
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x8f7c8) fc None m (seg_rom bsegs))).
{ intros a3q a4q a5q. pose proof (fmt_rng (i + 1) ltac:(zl)) as RG.
assert (NOFLAG : flag_bit (znth fmt (i + 1)) = None -> fl = 0%Z /\ k1 = (i + 1)%Z).
{ intros NF. rewrite (parse_flags_cons_none _ _ _ NF) in PF. injection PF as Efl0 Es1q. split; [congruence|].
pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt (i + 1) ltac:(zl)) as L2.
rewrite (sfx_cons fmt (i + 1)) in L2 by zl. rewrite Es1q, Hs1 in L2. lia. }
zs. zs. zs. brf K2.
-
assert (NF : flag_bit (znth fmt (i + 1)) = None).
{ destruct (flag_bit (znth fmt (i + 1))) eqn:E; [|reflexivity]. exfalso.
pose proof (flag_bit_range (znth fmt (i + 1)) ltac:(congruence)) as R. rewrite land_M64_id in K2 by lia. lia. }
destruct (NOFLAG NF) as [Efl0 Ek1].
zs. zs. zs. brf K3. { exfalso. apply N42. rewrite Ec1', Ek1. exact K3. }
jump (apply POSTFLAGS).
- assert (Hc : (32 <= znth fmt (i + 1) < 64)%Z) by (apply (proj1 (sp_test _ RG)); lia).
rewrite (land_M64_id (znth fmt (i + 1) + -32)) in * by lia.
zs. zs. zs. zs. zs. brf K3.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
assert (NF : flag_bit (znth fmt (i + 1)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
destruct (NOFLAG NF) as [Efl0 Ek1].
zs. zs. brf K4; [ jump (apply POSTFLAGS) | exfalso; apply N42; rewrite Ec1', Ek1; exact K4 ].
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
destruct (flag_bit (znth fmt (i + 1))) as [b|] eqn:E.
2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
pose proof (flag_some _ _ Hc E) as [Hfw Hb].
rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
zs.
stmt HS_FLAGS as NXF. jump (eapply NXF with (p := (i + 1)%Z) (k := 1%Z) (fl := 0%Z) (b := b) (FL := fl) (s1 := s1);
[exact FI' | lia | lia | zl | rewrite unsigned_lit_land; exact Hfw | lia | lia | rewrite Z.lor_0_l; exact PF | rewrite Hs1, Es1; discriminate | ]).
intros k' c' a3' a4' a5' Hk' Hs1' Hc' HN HFL.
assert (Ek1 : k' = k1).
{ pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt k' ltac:(zl)) as L2. rewrite <- Hs1', Hs1 in L2. lia. }
subst k'. subst c'. pose proof (fmt_rng k1 ltac:(zl)) as RGk.
zs. zs. brf K4; [ | exfalso; apply N42; rewrite Ec1'; exact K4 ].
jump (apply POSTFLAGS). }
rd_fmt (i + 1)%Z. zs. fix_u8 (i + 1)%Z. zs. zs. zs. zs. zs. brf K.
- zs. zs. apply FL34.
- assert (DG : is_digit (znth fmt (i + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
assert (Hi2 : (i + 2 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (i + 2) (zlength fmt)); [assumption|]. exfalso.
rewrite (sfx_nil fmt (i + 1 + 1)) in POSN by lia. rewrite DG in POSN. discriminate. }
replace (i + 1 + 1)%Z with (i + 2)%Z in POSN by lia.
rewrite (sfx_cons fmt (i + 2)) in POSN by zl. rewrite DG in POSN. cbn [andb] in POSN. apply Z.eqb_neq in POSN.
rd_fmt (i + 2)%Z. zs. fix_u8 (i + 2)%Z. zs. zs. zs. zs. br K1. apply FL34.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PrintfCore.
End CANSEC1.
