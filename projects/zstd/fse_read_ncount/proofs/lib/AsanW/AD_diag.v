(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode Bytes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FmtFp Printf_model Printf_mlib Printf_pieces Printf_fmts F_fmt_fp_lib DrvAgree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow ITreeA SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells Stdio_kit Stdio_kit2 F_syscalls StdioFiles MonadF MonadF2 Strnlen_iface
F_printf_iface F_fwritex_stderr F_stdio_flush F_vfprintf F_vfprintf_stderr Printf_bridge Stdio_iface F_fwrite
I_printf_formats I_printf_icpt I_fwrite AProto ABase ADriver_iface.
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
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Section CANSEC1. Context {rc : runConstT}.
Definition AFPRINTF : Z := 0x429ac.
Definition AFWRITE : Z := 0x42994.
Definition AFWRITE_DEPTH : Z := 2368.
Definition AFPRINTF_DEPTH : Z := 5664.
Section Fwrite.
Context {St : Type}.
Definition afwrite_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (canary : word) (m : amem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ stderr_wfile0 m'
/\ ssp_cells m' canary
/\ st' = st.
Definition afwrite_diag_stmt : Prop :=
forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (st : St) (lo : Z) (canary : word) (A : Z) (s : list Z),
stderr_wfile0 m ->
bytes_at asegs m A (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
0x10000 + 64 <= A -> A + zlength s + 64 <= 0x20dc0 ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - AFWRITE_DEPTH) -> (KHIGH <= lo) -> (bv_unsigned sp < 2^47) ->
ssp_cells m canary -> mem_inv asegs m ->
ashenv m -> rodata_sh0 m ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rrng RNG RFMT ->
implAM RNG (stderr_fwrite s : M St unit) st
(afwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFWRITE) fc None m (seg_rom asegs)).
#[using="Type"] Theorem afwrite_diag_proof : afwrite_diag_stmt.
Proof.
unfold afwrite_diag_stmt. intros until s. intros SF BY HF LEN -> -> -> -> ALO AHI ST LO KH SPHI SSP MI ENV ROD RGstk RGimg RRF.
unfold AFWRITE_DEPTH in *. pose proof KH as KH'. unfold KHIGH in KH'.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof ENV as (Hgot & Hric & Hshb & Hini & Hlay & Hrmem & Hrpf & Hrwcs & Hrread & Hrfw & _).
pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB. unfold zlength in *.
unfold AFWRITE. ienterF.
zs.
eapply evtF_cut.
{ Local Ltac2 Set LiaHints.tbl := fun () => "00g0?10350943620.92 10927566174.92 13793839360.68 16293186103.92 16293186103.94 16293186103.97 16450591840.92 17841768607.12818475783232.68 18728421362.12821747447203.12022115424366.12022700267513.11922700267513.15122706553362.15022706553362.90 23815817401.92 25362686761.92 27110084175.92 28818133820.12828818364989.92 32017990067.12832494599134.12832782317950.68 34167131939.12034361039384.12834474458044.92 39051815024.12839236893995.11739631860434.15239631860434.15739636579653.12840221322032.11341993220.92    41994766937.68 42152887364.92 43640583054.12843879737620.92 48046414148.12848148475188.1194859321984.113 4859321985.92  51359718895.68 51363913183.12854464761885.12854547585536.68 56185111960.92 57622410744.11957628696595.11658356741644.12858806926368.1165989704831.128 6767037005.92  9304456310.120 9543206896.119 00000900>00?00N00Y00d00e00j00n01301401801B01L01S01W01\01e01k02802E02F02G02H02I02J02O02S02\02d02l02m02n03203303803903:03?03C03P03]03a03e03f03g03h03k04604?04G04L04M04N04OS3ALO3AHIS3AHIFS3AHI2LO3KH'2HaS2LO3KH'2HaS2LO3KH'2HaFS3LENS2LOS3AHIFS2KHS2LO3KH'1HS2LO3KH'1HS2LO2HaS2HaS3LENS3AHI3KH'S4SPHIS3LEN3ALO3AHIS3LEN3ALO3AHISFFSSS3AHIS2LOS4SPHI2HaS3KH'2HaS3KH'2HaFSS2LOFS3KH'SFS3LENS2KHS2LO4SPHI3KH'S2LO4SPHI3KH'S2KHS2KHFFSS1HS2LO3KH'2HaS3ALO3AHIS2LO3KH'S3ALOFSS".
eapply (fwrite_i_pre RNG); first [exact MI | exact ST | lia | exact KH | exact Hini | exact Hrfw | exact RGimg | exact RGstk]. }
cbv beta. intros ms1 MID.
destruct MID as (u0 & u1 & u2 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & STM1 & FR1 & INI1).
apply evtF_done.
pose proof (magree_of_munch asegs _ _ _ MU1 WM1) as AG1.
assert (OUT1 : forall a, a < bv_unsigned sp - 2144 -> outside [(bv_unsigned sp - 2144, bv_unsigned sp)] a) by (intros a Ha; cbn; lia).
assert (SF1 : stderr_wfile0 m1).
{ destruct SF as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
eapply rw_cells_magree; [exact AG1 | exact Hc | intros a Ha; apply OUT1; cbn in Ha; lia]. }
assert (BY1 : bytes_at asegs m1 A (zb s)).
{ eapply bytes_at_magree; [exact AG1 | exact BY | intros a Ha; apply OUT1; rewrite zb_length in Ha; lia]. }
assert (SSP1 : ssp_cells m1 canary).
{ destruct SSP as [G1 G2]. split; (eapply rw_cells_magree; [exact AG1 | eassumption | intros a Ha; apply OUT1; unfold got_ssp, ssp_guard in Ha; cbn in Ha; lia]). }
eapply implAM_post_evt.
{ eapply (fwrite_diag_proof (St:=St) RNG) with (lo := lo) (s := s); first
[ exact towrite_proof | exact SF1 | exact BY1 | exact HF | reflexivity | exact ST1 | exact SSP1 | exact MI1 | exact RGimg | idtac ];
rewrite ?unsigned_lit by lia; unfold zlength, FWRITE_DEPTH, GLOBALS_TOP;
first [ exact BY1 | exact ST1 | reflexivity | lia | eapply rng_sub'; [exact RGstk | lia] | eapply rng_sub'; [exact RGimg | lia] ]. }
cbv beta. intros [] st' ms' PO.
destruct PO as (v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & SF2 & SSP2 & ->).
rewrite ?unsigned_lit in MU2, ST2 by lia. fix_ret.
pose proof (magree_of_munch asegs _ _ _ MU2 WM2) as AG2.
assert (OUT2 : forall a, (bv_unsigned sp - 2128 <= a /\ a < 2^47) \/ (a < 0x5f7000 /\ ~ (RSTDERR <= a < RSTDERR + 232)) ->
outside [(lo, bv_unsigned sp - 2128); (RSTDERR, RSTDERR + 232)] a) by (intros a Ha; cbn; lia).
assert (FR2 : rw_cells asegs m2 (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_magree; [exact AG2 | exact FR1 | intros a Ha; apply OUT2; cbn in Ha; lia]. }
assert (STM2 : stk asegs m2 (bv_unsigned sp - 2128) (bv_unsigned sp - 56)).
{ eapply stk_transport_disjoint; [exact STM1 | exact MU2 | exact WM2 | cbn; lia]. }
assert (MU02 : munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m2).
{ apply (munch_trans _ m m1 m2).
- eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
- eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM02.
assert (AW : appW [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]) by solve_appW.
xport_env ENV MU02 WM02 as ENV2. pose proof (rodata_sh0_frame _ _ _ ROD MU02 WM02 AW) as ROD2.
pose proof ENV2 as (Hgot2 & _ & Hshb2 & _ & Hlay2 & _).
pose proof (rodata_sh0_rclean _ ROD2) as RCF2. destruct (rclean_shclean _ _ RCF2) as (UNP2 & _ & _ & APB2). cbn [r_lo r_hi r_rlo r_rhi RFMT] in UNP2, APB2.
destruct ROD2 as [_ WRF2].
eapply evtF_cut.
{ eapply (fwrite_i_post RNG) with (lo := lo) (res := 1) (size := Z.of_nat (length s)) (N := Z.of_nat (length s)) (RLO := 0x10000) (RHI := 0x20dc0);
rewrite ?unsigned_lit by lia;
first [ exact MI2 | exact ST2 | exact STM2 | exact FR2 | exact Hgot2 | exact Hshb2 | exact Hlay2 | exact WRF2 | exact RGimg | exact RGstk
| reflexivity | idtac ].
all: first [ lia | exact KH | unfold KEND; lia
| eapply app_blk_sub; [exact APB2 | lia | lia | lia]
| eapply unpoisoned_sub; [exact UNP2 | lia | lia]
| unfold rrng, RFMT in RRF; cbn [r_rlo r_rhi] in RRF; exact RRF
| (eapply wr_at_sub; [exact WRF2| rewrite !shad_div; lia| rewrite !shad_div; lia| rewrite !shad_div; lia])
| (eapply wr_at_sub; [exact WRF2| rewrite !shad_div; lia| rewrite !shad_div; lia]) ]. }
cbv beta. intros ms3 PO3.
destruct PO3 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
rewrite ?unsigned_lit in MU3 by lia.
pose proof (magree_of_munch asegs _ _ _ MU3 WM3) as AG3.
assert (OUT3 : forall a, (bv_unsigned sp - 2128 <= a \/ a < lo) -> outside [(bv_unsigned sp - 2208, bv_unsigned sp - 2128)] a) by (intros a Ha; cbn; lia).
apply evtF_done. unfold afwrite_diag_post.
do 15 eexists. exists m3. split; [reflexivity|].
split. { apply (munch_trans _ m m2 m3); [exact MU02|]. eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [eapply wmono_trans; [exact WM02 | exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
split. { destruct SF2 as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
eapply rw_cells_magree; [exact AG3 | exact Hc | intros a Ha; apply OUT3; cbn in Ha; lia]. }
split; [| reflexivity].
destruct SSP2 as [G1 G2]. split; (eapply rw_cells_magree; [exact AG3 | eassumption | intros a Ha; apply OUT3; unfold got_ssp, ssp_guard in Ha; cbn in Ha; lia]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Fwrite.
#[using="Type"] Lemma forall_range_b : forall l, forallb (fun c => (0 <=? c) && (c <? 256))%bool l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
intros l H. rewrite forallb_forall in H. apply Forall_forall. intros c Hc. specialize (H c Hc).
apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. Local Ltac2 Set LiaHints.tbl := fun () => "0010<3748619754.6000007S2H12H2".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Fprintf.
Context {St : Type}.
Hypothesis HSTRN : strnlen_a_stmt.
Definition afprintf_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : amem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : amem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stderr_wfile m'
/\ ssp_cells m' canary
/\ st' = st.
#[using="HSTRN"] Lemma afprintf_core : forall RNG (rstk : region)
(ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x13 x14 x15 x16 x17 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m m1 : amem) (st : St) (A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z)
(lo : Z) (canary : word) (j32 : list byte),
let q := bv_unsigned sp - 112 in
munch [(bv_unsigned sp - 2432, bv_unsigned sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo q ->
rw_cells asegs m1 q [CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A ->
stderr_wfile m1 -> ssp_cells m1 canary -> frm0 fc ->
0x10000 + 64 <= A -> A + zlength fmt + 64 <= 0x20dc0 ->
bytes_at asegs m1 A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
args_ok RSTDERR (q - 352) 80 RNG m1 lo q (q - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
(lo <= bv_unsigned sp - AFPRINTF_DEPTH) -> (KHIGH <= lo) -> (bv_unsigned sp < 2^47) ->
ashenv m1 -> rclean m1 rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> rodata_sh0 m1 ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG -> rrng RNG rstk -> rrng RNG RFMT ->
implAM RNG (stderr_fprintf ps) st (afprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR (Z_to_bv 64 0x46190) (Z_to_bv 64 q) gp tp t0 t1 t2 a1 a0 a0 a1 (Z_to_bv 64 (bv_unsigned sp - 48)) x13 x14 x15 x16 x17
(Z_to_bv 64 (bv_unsigned sp - 48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8f2f0) fc None m1 (seg_rom asegs)).
Proof.
intros until j32. cbv zeta.
intros MU1 WM1 MI1 ST1 FR1 -> -> SF1 SSP1 FRM ALO AHI BYF HFF P1 AOK PP FPC LO KH SPHI ENV1 RCS1 RSlo RShi ROD1 RGstk RGimg RG0 RRS RRF.
unfold AFPRINTF_DEPTH in *. pose proof KH as KH'. unfold KHIGH in KH'.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (bytes_at_bound _ _ _ _ BYF) as AB. rewrite zb_length in AB. unfold zlength in *.
unfold stderr_fprintf.
apply (implAM_mono RNG _ st (fun _ st' ms' => afprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms'));
[| intros [] st' ms' H; exact H].
apply (stderr_bridgeA RNG ps [] st (fun st' ms' => afprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms')).
pose proof (vfprintf_stderr_proof (St:=St) fwritex_stderr_proof stdio_write_flush_proof HSTRN) as VF.
unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
pose proof FR1 as FR1'.
apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_] _)) in FR1'. destruct FR1' as [FRlo VAC]. cbn [cells_size csize Nat.add app] in VAC.
Local Ltac2 Set LiaHints.tbl := fun () => "00`0?1345575729.87  1345835911.116 1349669538.91  13531833732.1161731794684.87  17821834965.87 18308028340.87 19011890464.87 1965672311.115 20895495679.87 21046391515.11621954436510.87 22700267513.1172393973379.87  29454010563.87 29726287862.87 30056349857.87 32780564991.87 33483641252.87 34317161955.87 35883875021.87 36127226691.87 36246866875.87 38341551499.87 41939266045.87 42150874612.87 42682729169.87 42967139908.87 47615370909.87 4949871407.87  50096010103.11651361537390.87 52151141559.11554451966315.87 56170482728.87 5714065249.87  57622410744.11758817723687.11559579107419.87 59821527829.87 6004565198.87  61397091028.87 62292229408.87 62300128021.87 65900216381.87 66169959927.87 67029314521.87 8590032195.87  00000=00J00W00X00Y00Z00^00_00`00f00j00k01501601<01=01>01?01@01A01B01G01H01I01J01O01P01Q01R01S01W01[01\01]01^01d01g01o02002102602702802A02B02F02G02MS2LO4SPHI3KH'S2LO4SPHI3KH'S2LO4SPHI3KH'SFFS2LOFSS4SPHIS2LOFS2LO3KH'1HSS4RSloFFFFFFS3AHIFFFS3KH'FFSSS2LOS2KHSFSS4RShiS1HS2LO3KH'FFS3ALOFFS3ALO3AHIFS2LOFS4SPHI".
replace (bv_unsigned sp - 112 + Z.of_nat 64)%Z with (bv_unsigned sp - 48)%Z in VAC by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.
eapply implAM_post_evt with
(Q := fun _ bs ms' => vfprintf_stderr_post (Z_to_bv 64 0x46190) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 RSTDERR) (Z_to_bv 64 (bv_unsigned sp - 48))
s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m1 (snd bs) ms' /\ snd bs = st).
{ apply implAM_fold. eapply implF_mono.
- eapply (implF_tforall asegs (at_nodeA asegs) fstepS RNG (fun rr => match rr with Ok qq => snd (snd qq) = st | Unr => True end));
[apply outsk_flush_leaves|].
apply implAM_unfold.
eapply VF with (A := A) (VA := (bv_unsigned sp - 48)%Z) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args)
(r := r) (lo := lo) (canary := canary) (rstk := rstk) (rfmt := RFMT);
clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
all: try reflexivity. all: try lia.
all: try assumption.
all: first [ exact VAA
| apply rodata_sh0_rclean; exact ROD1
| unfold inreg, RFMT; cbn; lia
| eapply rng_sub'; [exact RGstk | cbn; lia] ].
- intros [|[[] [b st']]] RNG' ms'; cbn; intros [X EST]; [exact I | destruct X as [E P]; exact (conj E (conj P EST))]. }
cbv beta. intros [] [buf st'] ms' [P EST]. cbn [snd] in P, EST. subst st'.
unfold vfprintf_stderr_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MU3 & WM3 & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
fix_ret.
assert (FR3 : rw_cells asegs m3 (bv_unsigned sp - 112) [CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]).
{ eapply rw_cells_transport; [exact FR1 | exact MU3 | exact WM3 | cbn; lia]. }
eapply evtF_cut.
{ eapply (fprintf_i_post RNG); rewrite ?unsigned_lit by lia; [exact MI3 | exact FR3 | reflexivity | eapply rng_sub'; [exact RGstk | lia]]. }
cbv beta. intros ms' ->. rewrite !unsigned_lit by lia.
replace (bv_unsigned sp - 112 + 112)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
release_frame FR3 ST3 (bv_unsigned sp).
apply evtF_done. unfold afprintf_diag_post. cbn [fst snd].
do 17 eexists. exists m3. split; [reflexivity|].
split. { apply (munch_trans _ m m1 m3).
- eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
- eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [eapply wmono_trans; [exact WM1 | exact WM3]|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [assumption|]. split; [exact SF3|]. split; [exact SSP3| reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition adiag_args (RNG : footprint) (d : diag_msg) (m : amem) (fmtp argw : word) (lo sp : Z) : Prop :=
match d with
| DUsage s | DCannotOpen s | DReadError s =>
fmtp = Z_to_bv 64 (match d with DUsage _ => FMT_USAGE | DCannotOpen _ => FMT_CANTOPEN | _ => FMT_READERR end)
/\ exists (slack : list byte) (r : region),
bytes_at asegs m (bv_unsigned argw) (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned argw + zlength s + 1)) mod 8 <= zlength slack)
/\ (zlength s < INT_MAX - 256)
/\ (bv_unsigned argw + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned argw)
/\ (bv_unsigned argw + zlength s + 1 <= 2^47)
/\ (GLOBALS_TOP <= bv_unsigned argw)
/\ rclean m r /\ inreg r (bv_unsigned argw) (zlength s + 1 + zlength slack)
/\ rng RNG (bv_unsigned argw) (zlength s + 1 + zlength slack) /\ rrng RNG r
| DTooBig => fmtp = Z_to_bv 64 FMT_TOOBIG /\ bv_unsigned argw mod 2^32 = 67108864
| _ => False
end.
Definition afprintf_diag_stmt : Prop :=
forall RNG (rstk : region) (d : diag_msg)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (st : St) (lo : Z) (canary : word),
stderr_wfile m ->
a0 = Z_to_bv 64 RSTDERR -> adiag_args RNG d m a1 a2 lo (bv_unsigned sp) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - AFPRINTF_DEPTH) -> (KHIGH <= lo) -> (bv_unsigned sp < 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
ashenv m -> rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> rodata_sh0 m ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG -> rrng RNG rstk -> rrng RNG RFMT ->
implAM RNG (s_diag d) st
(afprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFPRINTF) fc None m (seg_rom asegs)).
#[using="HSTRN"] Lemma afprintf_s : forall (A n : Z) (fmt : list Z) (PIECES : list Z -> list (list Z)) (nf : Z),
fprintf_i_pre_s_stmt A n ->
0x10000 + 64 <= A -> A + zlength fmt + 64 <= 0x20dc0 -> zlength fmt = n + 1 -> 0 <= n ->
ro_bytes_b asegs A (zb fmt) = true -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
(forall sarg, zlength sarg < INT_MAX - 256 -> printf_pieces fmt [PA_s sarg] = Some (PIECES sarg, nf + zlength sarg)) ->
(forall sarg, fp_calls (length fmt) fmt [PA_s sarg] = []) ->
forall RNG (rstk : region) (sarg : list Z)
(ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (st : St) (lo : Z) (canary : word),
stderr_wfile m ->
(exists (slack : list byte) (r : region),
bytes_at asegs m (bv_unsigned a2) (zb sarg ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) sarg
/\ ((- (bv_unsigned a2 + zlength sarg + 1)) mod 8 <= zlength slack)
/\ (zlength sarg < INT_MAX - 256)
/\ (bv_unsigned a2 + zlength sarg + 1 + zlength slack <= lo \/ bv_unsigned sp <= bv_unsigned a2)
/\ (bv_unsigned a2 + zlength sarg + 1 <= 2^47)
/\ (GLOBALS_TOP <= bv_unsigned a2)
/\ rclean m r /\ inreg r (bv_unsigned a2) (zlength sarg + 1 + zlength slack)
/\ rng RNG (bv_unsigned a2) (zlength sarg + 1 + zlength slack) /\ rrng RNG r) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - AFPRINTF_DEPTH) -> (KHIGH <= lo) -> (bv_unsigned sp < 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
ashenv m -> rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> rodata_sh0 m ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG -> rrng RNG rstk -> rrng RNG RFMT ->
evtF asegs RNG (fun ms' => implAM RNG (stderr_fprintf (PIECES sarg)) st
(afprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 RSTDERR) (Z_to_bv 64 A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x460d0) fc None m (seg_rom asegs)).
Proof.
intros A n fmt PIECES nf PRE ALO AHI NLEN N0 ROB HFF P1 PP FPC.
intros RNG rstk sarg. intros until canary.
intros SF DA ST LO KH SPHI SSP MI FRM ENV RCS RSlo RShi ROD RGstk RGimg RG0 RRS RRF.
unfold AFPRINTF_DEPTH in *. pose proof KH as KH'. unfold KHIGH in KH'.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof ENV as (Hgot & Hric & Hshb & Hini & Hlay & Hrmem & Hrpf & Hrwcs & Hrread & Hrfw & Hrsl & Hrmc & Hckp & Hisl).
Local Ltac2 Set LiaHints.tbl := fun () => "00[0?10427370913.11510960921459.14112551987063.1411324541964.141 13466127566.14113766864029.14114018181193.14314018181193.14414018181193.1491421651544.115 15458583837.14116208836192.13716510758680.11422706553362.13822922197269.1152427397472.111 24944293306.14125175913006.11525951848349.14127585989457.11529296780442.91 29296833861.13829297210565.13931059105597.11234319324755.14138928203971.11542631412581.11543141496116.11744268145047.11544729452080.11548039318239.11748773972215.14149849032372.14151312033520.11154449803995.14157562056574.11559589528555.14160922589298.14162266698453.11165903665757.1418212626088.141 9111178423.115 9124086686.141 00000<00G00a00m01901:01[01f02102<02=02Q02Y03:03;03F03R03S03^03f03n04P05205Y05Z06506S06_06j07607B07\07]07i07j08E08F08Q09509609709B09MS3LZF2AB3SL0S2IR3LZF2ABS2DJ2IR2LO3KH'3LZF4HULr2ABS3AHI3LZF2ABS3LEN3LZF2ABFS2DJ2IR2LO3KH'3LZF4HULr2AB3SL02HaS3LZF2AB2HaS3LZF2AB2HaS2LO3LZF2ABFS2LO3KH'3LZF4HULr2ABS3LZF2ABS2GA2IR2LO3KH'3LZF4HULr2AB3SL02HaFS2N03LZF2ABS3ALO3LZF2ABFS2DJ3LZF2ABS3LZF2ABS2LO3KH'S3SLK2GA2IR2LO3KH'3LZF4HULr2AB3SL0S3SLK2GA2IR2LO3KH'3LZF4HULr2AB3SL0S3ALO3AHI4NLEN2N02GA2IR3LZF4HULr2AB3SL0FS3SLK2GA2IR3LZF4HULr2AB3SL0S2DJ2IR2LO3KH'3LZF4HULr2AB3SL0S3LZF2AB3Hc'S2IR3LZF2ABS3LEN3LZF2ABS3LZF2AB3Hc'S2DJ2IR2LO3KH'3LZF4HULr2ABFS3ALO3LZF2ABFS3SLK2GA2IR3LZF4HULr2AB3SL0FS2GA3LZF2ABS3AHI4NLEN3SLK2GA2IR3LZF4HULr2AB3SL0FFS2GA3LZF2ABS2GA3LZF2AB".
assert (AW1 : appW [(bv_unsigned sp - 2432, bv_unsigned sp)]) by solve_appW.
pose proof (zb_length fmt) as LZF. unfold zlength in *.
destruct DA as (slack & r & BY & HF & SLK & LEN & DJ & T47 & GA & RC & IR & RGs & RRr).
pose proof (rclean_shclean _ _ RC) as (UNPr & HULr & WRr & APBr). unfold hull64 in HULr. unfold inreg in IR.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite length_app, zb_length in AB. cbn [length] in AB.
pose proof (zlength_nonneg' slack) as SL0. unfold GLOBALS_TOP in GA. unfold zlength in *.
assert (FZ : shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0)) by (apply (rodata_sh0_fmt _ A n ROD); lia).
assert (RSHF : rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64))).
{ unfold rrng, RFMT in RRF. cbn [r_rlo r_rhi] in RRF. eapply rng_sub'; [exact RRF|]. rewrite !shad_div. unfold ASHOFF. lia. }
assert (BY0 : bytes_at asegs m (bv_unsigned a2) (zb sarg ++ [Z_to_bv 8 0])).
{ pose proof BY as BY'. rewrite <- (firstn_skipn (length (zb sarg) + 1) (zb sarg ++ Z_to_bv 8 0 :: slack)) in BY'.
apply bytes_at_app in BY'. destruct BY' as [BY' _].
rewrite firstn_app, firstn_all2, Nat.add_comm, Nat.add_sub in BY' by lia. cbn [firstn Nat.add] in BY'. exact BY'. }
assert (NZ : Forall (fun b : byte => bv_unsigned b <> 0) (zb sarg)).
{ unfold zb. apply Forall_forall. intros b Hb. apply in_map_iff in Hb. destruct Hb as (c & <- & Hc).
pose proof (proj1 (Forall_forall _ _) HF c Hc) as Hc'. cbv beta in Hc'.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_small by (unfold bv_modulus; cbn; lia). lia. }
eapply evtF_cut.
{ eapply (PRE RNG) with (lo := lo) (sstr := zb sarg) (RLO := r_rlo r) (RHI := r_rhi r);
rewrite ?length_app, ?zb_length; cbn [length];
first [ exact MI | exact ST | exact KH | exact FZ | exact BY0 | exact NZ | exact WRr | exact RGimg | exact RGstk | exact RSHF | exact RRr
| reflexivity | idtac ].
all: first [ assumption
| lia
| unfold INT_MAX in *; lia
| eapply app_blk_sub; [exact APBr | lia | lia | lia]
| eapply unpoisoned_sub; [exact UNPr | lia | lia]
| unfold KEND in *; lia
| eapply rng_sub'; [exact RGs | lia] ]. }
cbv beta. intros ms1 MID.
destruct MID as (u0 & u1 & u2 & x13 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & j32 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & INI1).
apply evtF_done.
pose proof (magree_of_munch asegs _ _ _ MU1 WM1) as AG1.
assert (OUT1 : forall a, (a < lo \/ bv_unsigned sp <= a \/ a < 0x5f7000) -> outside [(bv_unsigned sp - 2432, bv_unsigned sp)] a) by (intros a Ha; cbn; lia).
xport_env ENV MU1 WM1 as ENV1. xport_reg RCS MU1 WM1 as RCS1. xport_reg RC MU1 WM1 as RC1.
pose proof (rodata_sh0_frame _ _ _ ROD MU1 WM1 AW1) as ROD1.
eapply (afprintf_core RNG rstk) with (m := m) (m1 := m1) (A := A) (fmt := fmt) (args := [PA_s sarg]) (ps := PIECES sarg)
(r := nf + Z.of_nat (length sarg)) (lo := lo) (canary := canary) (j32 := j32);
first [ exact MU1 | exact WM1 | exact MI1 | exact ST1 | exact FR1 | reflexivity | exact FRM | exact ENV1 | exact RCS1 | exact ROD1 | exact HFF | exact P1
| idtac ].
all: try assumption.
all: try (unfold zlength, AFPRINTF_DEPTH in *; lia).
- destruct SF as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
eapply rw_cells_magree; [exact AG1 | exact Hc | intros a Ha; apply OUT1; cbn in Ha; lia].
- destruct SSP as [G1 G2]. split; (eapply rw_cells_magree; [exact AG1 | eassumption | intros a Ha; apply OUT1; unfold got_ssp, ssp_guard in Ha; cbn in Ha; lia]).
- apply fmt_bytes_at; [exact MI1 | exact ROB | lia | unfold zlength; lia].
- cbn [args_ok arg_ok]. split; [|exact I]. exists slack. unfold zlength. rewrite ?unsigned_lit by lia. unfold VF_FRAME.
repeat match goal with |- _ /\ _ => split end;
first [ assumption | lia
| eapply bytes_at_magree; [exact AG1 | exact BY | intros a Ha; apply OUT1; rewrite length_app, zb_length in Ha; cbn [length] in Ha; lia]
| exists r; split; [exact RC1|]; split; [unfold inreg; lia| exact RRr] ].
- unfold zlength in PP. apply PP. lia.
- apply FPC.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HSTRN"] Theorem afprintf_diag_proof : afprintf_diag_stmt.
Proof.
intros RNG rstk d. intros until canary. intros SF -> DA ST LO KH SPHI SSP MI FRM ENV RCS RSlo RShi ROD RGstk RGimg RG0 RRS RRF.
unfold AFPRINTF. ienterF. zs.
destruct d as [argv0 | path | path | | | |]; cbn [adiag_args] in DA; try contradiction; unfold s_diag.
-
destruct DA as [-> DA].
Local Ltac2 Set LiaHints.tbl := fun () => "00T0?1323343225.60  14018181193.10614018181193.1111417389892.78  15029528643.10316149407881.60 16208836192.10019342056920.60 21972317293.10322706553362.10122921142957.76 2310049737.103 2449294360.60  29296780442.75 29296833861.10131059105597.77 33496708520.60 34319324755.10336737493321.60 372942824.60   42482367928.60 44017149229.76 50620306781.10350937879326.10353508056215.10353514350498.60 53908168024.60 57425789704.60 5756994900.60  59589528555.10361728853404.76 61735387932.10362258837346.60 63168078216.60 65499904920.60 66700086449.10300000100500900=00>00?00G00H00I00T00U00V00W00_00g00h00i00j00k00l00m00n00o01001101201301401501601701801901:01;01<SS2HaS2HaS2LOSSS2LO3KH'SSS2LO3KH'2HaSFSS2LO3KH'S2LO3KH'SFFSFSSSFFFFSFFSSFSSS".
eapply (afprintf_s FMT_USAGE 16 FMT_usage pieces_usage 14 fprintf_i_pre_usage); try eassumption; try reflexivity;
first [ unfold FMT_USAGE; lia | lia | replace (zlength FMT_usage) with 17 by reflexivity; unfold FMT_USAGE; lia
| apply forall_range_b; vm_compute; reflexivity | intros; apply printf_pieces_usage; assumption ].
-
destruct DA as [-> DA].
eapply (afprintf_s FMT_CANTOPEN 20 FMT_cannot_open pieces_cannot_open 18 fprintf_i_pre_cantopen); try eassumption; try reflexivity;
first [ unfold FMT_CANTOPEN; lia | lia | replace (zlength FMT_cannot_open) with 21 by reflexivity; unfold FMT_CANTOPEN; lia
| apply forall_range_b; vm_compute; reflexivity | intros; apply printf_pieces_cannot_open; assumption ].
-
destruct DA as [-> DA].
eapply (afprintf_s FMT_READERR 22 FMT_read_error pieces_read_error 20 fprintf_i_pre_readerr); try eassumption; try reflexivity;
first [ unfold FMT_READERR; lia | lia | replace (zlength FMT_read_error) with 23 by reflexivity; unfold FMT_READERR; lia
| apply forall_range_b; vm_compute; reflexivity | intros; apply printf_pieces_read_error; assumption ].
-
destruct DA as [-> Hu].
unfold AFPRINTF_DEPTH in *. pose proof KH as KH'. unfold KHIGH in KH'.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof ENV as (Hgot & Hric & Hshb & Hini & Hlay & Hrmem & Hrpf & Hrwcs & Hrread & Hrfw & Hrsl & Hrmc & Hckp & Hisl).
assert (AW1 : appW [(bv_unsigned sp - 2432, bv_unsigned sp)]) by solve_appW.
assert (FZ : shadow_bytes m (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64)) (fun _ => 0)) by (apply (rodata_sh0_fmt _ FMT_TOOBIG 32 ROD); unfold FMT_TOOBIG; lia).
assert (RSHF : rng RNG (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64) - shad (FMT_TOOBIG - 64))).
{ unfold rrng, RFMT in RRF. cbn [r_rlo r_rhi] in RRF. eapply rng_sub'; [exact RRF|]. rewrite !shad_div. unfold ASHOFF, FMT_TOOBIG. lia. }
eapply evtF_cut.
{ eapply (fprintf_i_pre_toobig RNG) with (lo := lo);
first [ exact MI | exact ST | exact KH | exact FZ | exact RGimg | exact RGstk | exact RSHF | reflexivity | assumption | lia ]. }
cbv beta. intros ms1 MID.
destruct MID as (u0 & u1 & u2 & x13 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & j32 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & INI1).
apply evtF_done.
pose proof (magree_of_munch asegs _ _ _ MU1 WM1) as AG1.
assert (OUT1 : forall a, (a < lo \/ bv_unsigned sp <= a \/ a < 0x5f7000) -> outside [(bv_unsigned sp - 2432, bv_unsigned sp)] a) by (intros a Ha; cbn; lia).
xport_env ENV MU1 WM1 as ENV1. xport_reg RCS MU1 WM1 as RCS1.
pose proof (rodata_sh0_frame _ _ _ ROD MU1 WM1 AW1) as ROD1.
eapply (afprintf_core RNG rstk) with (m := m) (m1 := m1) (A := FMT_TOOBIG) (fmt := FMT_too_big) (args := [PA_u 67108864]) (ps := pieces_too_big)
(r := 38) (lo := lo) (canary := canary) (j32 := j32);
first [ exact MU1 | exact WM1 | exact MI1 | exact ST1 | exact FR1 | reflexivity | exact FRM | exact ENV1 | exact RCS1 | exact ROD1
| exact printf_pieces_too_big | idtac ].
all: try assumption.
all: try (replace (zlength FMT_too_big) with 33 by reflexivity; unfold FMT_TOOBIG, AFPRINTF_DEPTH in *; lia).
+ destruct SF as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
eapply rw_cells_magree; [exact AG1 | exact Hc | intros a Ha; apply OUT1; cbn in Ha; lia].
+ destruct SSP as [G1 G2]. split; (eapply rw_cells_magree; [exact AG1 | eassumption | intros a Ha; apply OUT1; unfold got_ssp, ssp_guard in Ha; cbn in Ha; lia]).
+ apply fmt_bytes_at; [exact MI1 | vm_compute; reflexivity | unfold FMT_TOOBIG; lia | replace (zlength FMT_too_big) with 33 by reflexivity; unfold FMT_TOOBIG; lia].
+ apply forall_range_b. vm_compute. reflexivity.
+ cbn [args_ok arg_ok]. split; [|exact I]. split; [lia | exact Hu].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Fprintf.
End CANSEC1.
