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
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import Stdio_kit Stdio_kitI F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import Printf_zfacts F_printf_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import F_printf_core_common.
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
Hypothesis SEP_F : ((636400 <= Fp /\ Fp + 232 <= 664696) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((6247512 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
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
Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS RB SINK TOPOK OUT TOK HOUT RNG q gp tp m0 lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (F_printf_core_common.S_END (St:=St) Fp B BS RB SINK RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (F_printf_core_common.S_HEAD (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Notation sfx := (sfx fmt).
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
[ match goal with H : rw_cells _ _ 631824 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 6247504 _ |- _ => exact H end ]
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
Hypothesis HS_SCAN : S_SCAN.
Hypothesis HS_DIR : S_DIR.
Hypothesis HS_CONV : S_CONV.
Hypothesis HS_END : S_END.
#[using="SFL TOK HOUT HF LO GLO QHI TQ HA SEP_F SEP_B HAP HVA A0 VAHI BS0 KH RFM RBI RG_stk RG_img RG_F RG_B RG_fmt RR_fmt RR_B ENV0 RC_fmt RC_B HS_SCAN HS_DIR HS_CONV HS_END"] Lemma L_HEAD : forall fuel, S_HEAD fuel.
Proof.
induction fuel as [|fuel IH]; intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 Ft fc m st i cnt l k args pfx s2s za pl plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi Hcnt Hl Hcl.
{ cbn [printf_loop]. apply implAM_unr. }
rewrite printf_loop_S. rewrite fp_calls_S in FPC.
destruct (sfx i) as [|c s'] eqn:Es. { apply implAM_unr. }
destruct (sfx_cons_inv fmt i c s' Hi Es) as (Hilt & Ec & Es').
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
Local Ltac2 Set LiaHints.tbl := fun () => "01\0?11383290000.19811383290000.20311409396336.16211409396336.18011409396336.18513755488006.18916888394563.20917509446421.16217509446421.18017509446421.18518510977946.17118510977946.17418510977946.18918510977946.19218510977946.19418510977946.19719512137968.15922520717061.18322520717061.18822520769325.16522638504455.18322638504455.18822638583343.16522640680511.20922934309245.19422946084415.21423409711806.18924356466096.19024356466096.19524471108001.18325216032964.19425309805616.20925774904127.18827025541745.18627025541745.19127382584830.20927474171209.18327474171209.18827474256225.16527476353393.20927671308048.19428086201690.18928310633487.18932410837907.16532410916795.18332410916795.18832412935043.20933628201112.19434713230823.1893823480469.162 3823480469.180 3823480469.185 39818012962.18339818012962.18839818091786.16540448778119.19441344150998.16741344150998.18541344150998.19041344151002.17441344151002.19241344151002.19742432537837.18948881644785.20948883741921.16548883810505.18348883810505.18851184850041.16551184902225.18351184902225.1885258704946.165 52851042612.16452851042612.18252851042612.18752853254960.16252853254960.18052853254960.18553704195668.18953704195668.19455345847750.18355345847750.18856344221874.16556344308890.18356344308890.18856781706523.19956781706523.20458678682808.17658678682808.19458678682808.19959308628179.18359308628179.18859308628304.18659308628304.19159308628433.19059308628433.19559308628566.20859308628566.21359314923118.16259314923118.18059314923118.18560588841125.18360588841125.18861265214881.20961929812503.20863971019882.20966350173012.16466350173012.18266350173012.18700000800@00T00m01F01`01a02502N02g03;03M03f04=04V04m05=05>05?05@05A05B05C05D05T05a06906A06I06U07607707D07g08J08R08S08T08U08V08j09O09h09i09j09k09l0:B0:V0:j0;C0;\0;d0;l0<40<U0<i0=B0=[0=m0>D0>[0?@0?A0?B0?C0?D0?E0?F0?G0?H0?Z0@10@H0@\0A50AN0A^0An0BA0BU0BV0BW0BX0B`0Bh0C80CH0CX0Ck0DB0Dc0ED0F10Fe0G50G@0GN0G\0Gj0Gk0Gl0Gm0HL0HM0Ha0I:0ISS3LZB2LUS3LZB2LUS4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS2HA2A02Hi4Hilt3LZB2LU3HinFS4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3LZB2LU1KS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl4Hilt3LZB2LU1KS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl4Hilt3LZB2LU1KS2Hi4Hilt3LZB2LUFFFFFFFS2HA4Hilt3LZB2LUS4Hilt3LZB2LUS3GLO2HA4Hilt3LZB2LU3HinS3LZB2LUS3LZB2LUS3LZB2LU3HinS2LO3GLO2HA5SEP_F3HAP4Hilt3LZB2LUFS4Hilt3LZB2LUS2LO3GLO5SEP_F3HAP4VAHI4Hilt3LZB2LUS2LO3GLO5SEP_F3HAP4VAHI4Hilt3LZB2LUS3LZB2LUFFFFS3GLO2HA4Hilt3LZB2LUS2LO3GLO2HA5SEP_F3HAP4Hilt3LZB2LU3HinS4Npos2Hi4Hilt3LZB2LU3HinFFFFS2HA2A02Hi4Hilt3LZB2LUS2HA4Hilt3LZB2LU3HinS4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS2LO3GLO2HA5SEP_B3HAP4Hilt3LZB2LUS4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3LZB2LU1KS4Hcnt2Hl4Hilt3LZB2LU1KS4Hcnt2Hl4Hilt3LZB2LU1KS2LO3GLO2HA5SEP_B3HAP4Hilt3LZB2LU3HinFFFFFFFFS4Hcnt2Hl3LZB2LU1KS4Hcnt2Hl4Hilt3LZB2LU1KS4Hcnt2Hl4Hilt3LZB2LU1KS4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS2HA4Hilt3LZB2LUS2HA4Hilt3LZB2LUS4Hilt2Ec3LZB2LU2RGS4Hilt2Ec3LZB2LU3C37FFFS3LZB2LUS3LZB2LUS2Hi4Hilt3LZB2LUS2Hi4Hilt3LZB2LUS2Hi4Hilt3LZB2LUS4Hilt3LZB2LU2C02K0S4Hilt2Ec3LZB2LU3C372K0S2LO3GLO5SEP_F3HAP4Hilt3LZB2LU2K1S2LO3GLO5SEP_F3HAP4Hilt3LZB2LU2K1S2LO3GLO5SEP_F3HAP4Hilt3LZB2LU2C02K02K12FB2K2S2LO3GLO5SEP_F3HAP4Hilt2Ec3LZB2LU2C03C372K02K12FB2K2S4Npos3LZB2LU2K3S3LZB2LU2K3S3Hcl3LZB2LU1KS3Hcl3LZB2LU1KS3Hcl3LZB2LU1KFFFS2HA2A04Npos2Hi4Hilt3LZB2LU3HinFS4Hcnt2Hl3Hcl3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LUS4Hcnt2Hl3Hcl4Hilt3LZB2LU".
pose proof (fmt_rng i ltac:(zl)) as RGi.
destruct (Z.eqb_spec c 0) as [C0|C0].
{
apply implAM_ret.
zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. rewrite <- Ec, C0. zs. fixr. zs. if_lit.
stmt HS_END as NX. jump (eapply NX; [exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | unfold INT_MAX; lia]). }
rewrite <- Es in *. cbv zeta. cbv zeta in FPC.
pose proof (lit_run_sfx fmt i Hi) as (Hn & Hs1 & LIT & Hlit). cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
set (lit := lit_run (sfx i)) in *. set (n := Z.of_nat (length lit)) in *.
rewrite Hs1. rewrite Hs1 in FPC.
assert (Hn0 : (0 <= n)%Z) by (unfold n; lia).
destruct (sfx (i + n)) as [|c1 s2] eqn:Es1. { apply implAM_unr. }
destruct (sfx_cons_inv fmt (i + n) c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
match goal with |- context [if ?b then munr else _] => destruct b eqn:PCT; [apply implAM_unr|] end.
assert (TERM : (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z).
{ pose proof (lit_run_stop (sfx i) c1 s2 Hs1) as ST12. rewrite <- Ec1.
destruct ST12 as [E0|E37]; [left; exact E0 | right]. split; [exact E37|].
rewrite E37, Z.eqb_refl in PCT. cbn [andb] in PCT. destruct s2 as [|c2 s2q]; [discriminate|].
destruct (sfx_cons_inv fmt (i + n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
split; [exact Hin1|]. rewrite <- Ec2. apply Z.eqb_neq. exact PCT. }
stmt HS_SCAN as NXS.
destruct (0 <? n) eqn:En; try rewrite En in FPC; [apply Z.ltb_lt in En; rename En into Npos | apply Z.ltb_ge in En; rename En into Nz].
-
destruct (Z.ltb_spec0 (2147483647 - (cnt + l)) n) as [|Hncl]; [apply implAM_unr|].
ienter.
zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
jump (eapply NXS with (i := i) (n := n) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | exact LIT | exact TERM | left; exact Npos | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2.
zs. br K1.
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K2. clear FLC.
zs. zs. zs. zs.
ileave. eapply implAM_bind.
{ eapply (out_callq rfmt); try exact HS; try exact ST; try exact MI;
try match goal with |- munch _ m0 _ => hypMU | |- wmono _ m0 _ => hypWM | |- rclean _ _ => assumption | |- rrng _ _ => assumption end.
- rewrite Hlit, zb_firstn. unfold sfx. rewrite zb_skipn. replace (A + i)%Z with (A + Z.of_nat (Z.to_nat i))%Z by lia. apply bytes_at_sub; [exact BY | zl].
- rewrite Hlit. unfold sfx. apply Forall_sub. exact HF.
- unfold n, zlength. reflexivity.
- unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
- lia. - zl. - zl. - zl. - zl. - unfold INT_MAX in *; zl. - zl. - inreg_side. - rng_side. }
cbv beta. intros [] st'. post_call asegs m. rename MI0 into MI.
ienter. replace (ret_pc (Z_to_bv 64 587240)) with (Z_to_bv 64 587240) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
zs. zs. br K3.
rewrite <- Es1. rewrite <- Es1 in FPC.
stmt IH as NXH.
jumpM (eapply NXH with (i := (i + n)%Z) (cnt := (cnt + l)%Z) (l := n) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
-
assert (En0 : n = 0%Z) by lia. rewrite En0 in *.
assert (C37 : znth fmt i = 37%Z).
{ destruct TERM as [E0 | [E37 _]]; rewrite Z.add_0_r in *; [|exact E37]. exfalso. apply C0. rewrite Ec. exact E0. }
replace (i + 0 + 1)%Z with (i + 1)%Z in Es2 by lia.
destruct (parse_dir s2) as [[d s3]|] eqn:PD; [|apply implAM_unr].
destruct args as [|a args']; [apply implAM_unr|].
ienter.
zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
jump (eapply NXS with (i := i) (n := 0%Z) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | intros j Hj; lia | rewrite !Z.add_0_r in TERM |- *; exact TERM | right; exact C37 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2.
zs. br K1.
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K2. clear FLC.
zs. zs. zs. zs.
ileave. eapply implAM_bind.
{ eapply (out_callq rfmt); try exact HS; try exact ST; try exact MI;
try match goal with |- munch _ m0 _ => hypMU | |- wmono _ m0 _ => hypWM | |- rclean _ _ => assumption | |- rrng _ _ => assumption end.
- apply bytes_at_nil; zl.
- constructor.
- reflexivity.
- unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
- lia. - zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; lia.
- change (zlength (@nil Z)) with 0%Z; zl.
- change (zlength (@nil Z)) with 0%Z. inreg_side. - change (zlength (@nil Z)) with 0%Z. rng_side. }
cbv beta. intros [] st'. post_call asegs m. rename MI0 into MI.
ienter. replace (ret_pc (Z_to_bv 64 587240)) with (Z_to_bv 64 587240) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
zs. zs. br K3.
stmt HS_DIR as NXD.
jump (eapply NXD with (i := i) (d := d) (rest := s3)); [mk_finv | unfold lo_cells, ssp_guard; exact LOW | lia | zl | rewrite <- Es2; exact PD | ].
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp. subst s3.
stmt (HS_CONV fuel IH) as NXC.
jumpM (eapply NXC with (i4 := k4) (k := k) (c := (cnt + l)%Z) (d := d) (a := a) (args := args'));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK
| | | exact FRM | exact FOK | lia | exact Ht | | lia | exact Hw | exact Hp | exact (parse_dir_xp _ _ _ PD) | unfold INT_MAX; lia ].
+ destruct a; try exact I. exact (Forall_inv FPC).
+ destruct a; try exact FPC. exact (Forall_inv_tail FPC).
+ exact (parse_dir_conv_type _ _ _ PD).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PrintfCore.
End CANSEC1.
