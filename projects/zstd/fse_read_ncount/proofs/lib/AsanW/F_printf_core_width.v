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
Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS RB SINK TOPOK OUT TOK HOUT RNG q gp tp m0 lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
Local Notation S_WLOOP := (F_printf_core_common.S_WLOOP Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS RB RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
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
#[using="HF LO RG_stk RG_fmt"] Lemma L_WLOOP : S_WLOOP.
Proof.
intros x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc w s2 pfx s2s za pl plp alo ahi j128 _
FI LOW Hpos Hacc DG G NE HK.
remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
revert pos acc x5 x6 x12 x14 x15 x16 x17 Hpos Hacc DG G HK Hkk.
induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
pose proof (proj1 (digit_range _) DG) as DGR.
rewrite (sfx_cons fmt pos) in G by (unfold zlength in *; lia). rewrite (getint_cons_digit _ _ _ DG) in G.
destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.
assert (Hnx : (pos + 1 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
Local Ltac2 Set LiaHints.tbl := fun () => "00]0?12504114132.14912504162387.15112526625492.15114055715129.15114310470722.15914782281014.15914784378173.15614793070003.15114793070132.14815341631903.15121485664786.15122638504066.15122638750469.14923191368052.15123191614195.14927474089035.14927474171852.151278684627.150  30971616991.1493181307914.151 32410736313.14932410916158.15132510381208.14932510496543.15134695944544.14947353912958.14948883565003.14948883810892.15149990583127.14951845487163.15151851082430.15952935585048.14957474309287.16257486141538.15758429306979.15159308628566.15159314923118.14563366081968.15164856713608.14966136220539.14566151350208.15366325220836.1498937270825.158 8991141871.149 8991157352.151 00000100200300400R00b01201B01C01D01d01e01f01g01h01i01j02602702K02L02M02Y02e03:03I03J03K03L03j04H04I04Y04n05>05Q05c05d06>06S06h07407R07g08<FFFFS4Hpos4Hacc3OV23Hkk3LZB2LU3DGRS3Hkk3LZB2LU3DGRS3Hkk3LZB2LU3DGRS3Hkk3LZB2LU3DGRFFS4Hpos4Hacc2Ew3Hkk3LZB2LU3DGR2K3FFFFFFS3Hkk3LZB2LUFS4Hpos2Ew3Hkk3LZB2LUFFS3Hkk3LZB2LUS3Hkk3LZB2LUS4Hpos3Hkk3LZB2LU3HnxS2LO3Hkk3LZB2LUFFFS4Hpos4Hacc3OV23Hkk3LZB2LU3DGRS4Hpos4Hacc3OV23Hkk3LZB2LU3DGRFS3Hkk3LZB2LU3Hk2S4Hpos3Hkk3LZB2LU3HnxS3Hkk3LZB2LU3HnxS3OV23Hkk3LZB2LU2K3S3OV13Hkk3LZB2LU1KFS4Hpos4Hacc3Hkk3LZB2LU3DGRS4Hacc3OV13Hkk3LZB2LUS4Hacc3OV13Hkk3LZB2LUS3Hkk3LZB2LUS4Hpos4Hacc3OV23Hkk3LZB2LU3DGRS4Hpos3Hkk3LZB2LU3HnxS4Hpos3Hkk3LZB2LU3Hnx".
zs. zs. br K.
zs. zs. try rewrite (swrap32_small (acc * 10)) by lia.
zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z.
zs. try rewrite (lxor_imax (acc * 10)) by lia.
zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
zs. zs. zs. try rewrite Z.lor_0_l. zs. zs. brf K2.
-
assert (ND : is_digit (znth fmt (pos + 1)) = false).
{ destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
rewrite (sfx_cons fmt (pos + 1)) in G by (unfold zlength in *; lia). rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ew Es2.
zs. br K3.
jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
-
assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HF"] Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
Proof.
intros HWL x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k1 w s2 pfx s2s za pl plp alo ahi j128 _
FI LOW Hk1 G NE HK.
pose proof FI as FI'. dest_finv FI.
Local Ltac2 Set LiaHints.tbl := fun () => "0070?12121194833.15314795172235.13816078120181.14016080184174.13616080218877.13816080218877.13955581874680.13800000<00=00I00U00a00m019S3LZB2LU3Hk2FS3Hk13LZB2LUS3Hk13LZB2LUS3Hk13LZB2LUS3Hk13LZB2LUS3Hk13LZB2LU".
pose proof (fmt_rng k1 ltac:(zl)) as RG1.
zs. zs. zs. zs. brf K.
-
assert (ND : is_digit (znth fmt k1) = false).
{ destruct (is_digit (znth fmt k1)) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG1)) in E. lia. }
rewrite (sfx_cons fmt k1) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G. injection G as Ew Es2.
subst w. jump (apply (HK k1); [zl | | exact ND | unfold INT_MAX; lia]).
rewrite (sfx_cons fmt k1) by zl. symmetry. exact Es2.
- assert (DG : is_digit (znth fmt k1) = true) by (apply (proj1 (digit_test _ RG1)); lia).
zs. zs.
stmt HWL as NXL. jump (eapply NXL with (pos := k1) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact DG | exact G | exact NE | ]).
intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PrintfCore.
End CANSEC1.
