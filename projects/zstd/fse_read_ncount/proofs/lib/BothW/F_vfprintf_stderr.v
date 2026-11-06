(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Stdio Driver.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import Stdio_kit F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface Printf_outsA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import F_printf_iface F_printf_core F_vfprintf.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_pieces Printf_fmts.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ITreeA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import F_vfprintf_stdout Printf_bridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg Stdio_kit2.
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
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := ienterF.
Ltac ileave := ileaveF.
Ltac hide_low :=
repeat match goal with H : rw_cells bsegs _ ?A _ |- _ =>
lazymatch A with Zpos _ => idtac | _ => fail end;
lazymatch eval vm_compute in (A <? 0x1ffdc0)%Z with true => idtac | false => fail end;
lazymatch type of H with ?T => change T with (sf_hide T) in H end
end.
Ltac zs_canary := hide_low; zs; sf_unhide.
Section CANSEC1. Context {rc : runConstT}.
Section StderrSinkProofs.
Context {St : Type}.
Variable B : Z.
Let SINK := SINK_stderr (St:=St) B.
Lemma stderr_sink_frame : sink_frame_stmt RSTDERR B 80 SINK.
Proof using .
unfold sink_frame_stmt. intros W m m' [buf st] (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BLO) MU WM D1 D2.
exists flags, mode, tail, rest.
split; [|split; [exact FL32 | split; [exact FL8 | split; [| split; [exact LEN | split; [exact BHI | exact BLO]]]]]].
- eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
- eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
Qed.
Lemma stderr_sink_flags : sink_flags_stmt RSTDERR SINK.
Proof using B.
unfold sink_flags_stmt. intros m [buf st] (flags & mode & tail & rest & FC & FL32 & _).
exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
rewrite <- land_mod_low by lia. exact FL32.
Qed.
End StderrSinkProofs.
#[using="Type"] Lemma flags40_8 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
#[using="Type"] Lemma flags40_32 : forall f, Z.land f 40 = 0 -> Z.land f 32 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
#[using="Type"] Lemma sflags_noerr_8 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 ->
Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_8. exact H.
Qed.
#[using="Type"] Lemma sflags_noerr_32 : forall (flags : word),
Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 32 = 0.
Proof.
intros flags. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 32) with 0. apply Z.land_0_r.
Qed.
#[using="Type"] Lemma sflags_olderr0 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 -> Z.land (bv_unsigned (sx32 flags)) 32 = 0.
Proof. intros flags H. rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_32. exact H. Qed.
#[using="Type"] Lemma sflags_final_40 : forall (flags2 : word), Z.land (bv_unsigned flags2) 32 = 0 -> Z.land (bv_unsigned flags2) 8 = 0 ->
Z.land (Z.lor (bv_unsigned (sx32 flags2)) 0) 40 = 0.
Proof.
intros flags2 H32 H8. rewrite Z.lor_0_r. rewrite land_low7, sx32_mod128, <- land_low7 by lia.
replace 40 with (Z.lor 32 8) by reflexivity. rewrite Z.land_lor_distr_r, H32, H8. reflexivity.
Qed.
Section Stderr.
Context {St : Type}.
Hypothesis FWE : fwritex_stderr_stmt.
Hypothesis FLS : stdio_write_flush_stmt.
Hypothesis HSTRN : strnlen_a_stmt.
Definition vfprintf_stderr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk bsegs m' lo (bv_unsigned sp)
/\ stderr_wfile m'
/\ ssp_cells m' canary.
Definition vfprintf_stderr_stmt : Prop :=
forall RNG (rstk rfmt : region) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
(lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
stderr_wfile m ->
bytes_at bsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> args_ok RSTDERR (q - 352) 80 RNG m lo q (q - VF_FRAME) slots args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
stk bsegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->
ssp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
(KHIGH <= lo) -> ashenv m ->
rclean m rstk -> r_lo rstk <= lo -> q <= r_hi rstk ->
rclean m rfmt -> inreg rfmt A (zlength fmt) -> inreg rfmt 68452 9 ->
rng RNG lo (q - lo) -> rng_aimg RNG -> rng RNG VA (8 * zlength slots) -> rng0 RNG ->
rrng RNG rstk -> rrng RNG rfmt ->
implAM RNG (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
(fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8f480) fc None m (seg_rom bsegs)).
Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
Proof using FLS FWE HSTRN.
unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI
KH ENV RCS RSlo RShi RCF RFM RPF RGstk RGimg RGva RG0 RRS RRF.
unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
assert (RGfmt : rng RNG A (Z.of_nat (length fmt))) by (eapply rng_sub'; [exact RGimg | unfold zlength in *; lia]).
assert (RGF : rng RNG RSTDERR 232) by (eapply rng_sub'; [exact RGimg | lia]).
assert (AW : appW [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z) by solve_appW.
assert (AS : ashsafe [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z) by solve_ashsafe.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.
apply (printf_model_outsA OUT_stderr (OUTFP_stderr (St:=St)) RNG fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
match goal with |- implAM _ _ _ ?Q _ => set (QQ := Q) end.
ienter.
Local Ltac2 Set LiaHints.tbl := fun () => "0180?1162083373.109 13824580263.11314785984131.21514937404946.21516280164007.11216290529959.11017776320428.21017776320431.11118902133379.11020137662083.11221220757366.18622369299843.21123718643375.11124350674608.21724559885229.10925878270241.21325878270255.11127408782893.10927838173863.11028913119922.21531665601155.1133207549315.217 33890036525.10934917819932.201350813315.110  36115622433.21336115622446.11236128138371.21436132821563.20038180606771.11240091925677.10941209313411.21541298247043.11242621589892.21142716202543.11143059367082.10143779114627.21443987951392.21443987951406.11244514548391.11047296502915.11048281866919.11348664870567.11049009098115.11249189320359.11250378712294.10350703773351.1125081553575.110 50965962115.11051678667183.11151680764331.21652660366723.21753510313876.21153767577775.11153769674920.2165610800515.112 58052939139.1125905824131.213 59872667303.11060026416259.11361917199022.21261917199023.11162262045351.11262309080743.11262406045455.11263235321888.21463235321900.10963638282919.11264335387779.11265465916547.11067217347971.1108938098606.215 00000;00C00O00P00X00`00o01:01B01J01V01b01m02902D02S02^02i03103=03E03Q03\03o04704F04Q04]04m05505@05L05T05l06706B06N06]06h07007807@07H07P07X07`07h08008808C08R08^08j09509D09L09T09`09h0:00:?0:J0:R0:Z0:b0;10;<0;D0;L0;T0;\0;]S2LO3LZB2LUS3LZB2LUS3LZB2LU3LJBFS3LZB2LUS3LZB2LUS2LO3LZB2LU3LJBS2LO3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LU3LJBS2LO3LZB2LUS3LZB2LU3LJBS2LO3LZB2LUS2LO3LZB2LU3LJBS2LO3LZB2LUS2LO3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LU3LJBS2LO3LZB2LUS2LO3LZB2LU3LJB3LB4S3LZB2LUS2LO3LZB2LU3LJBS2LO3LZB2LUS3LZB2LU3LJBS3LZB2LU3LJB3LB4S3LZB2LUS2LO3LZB2LUS3LZB2LU3LJBS3LZB2LUS2LO3GLO3LZB2LU3LJB4BHI3S2LO3LZB2LUS2LO3LZB2LUS3LZB2LU3LJBS2LO3LZB2LU3LJBS2LO3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS2LO3LZB2LUS2LO3LZB2LU3LJBS3LZB2LU3LJBS3LZB2LU3LJBS2LO3LZB2LUS2LO3LZB2LU3LJBS3LZB2LUS3LZB2LUS3LZB2LU3LJBS3LZB2LUS3LZB2LUS2LO3LZB2LU3LJBS2LO3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS2LO3LZB2LU3LJBS2LO3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUS3LZB2LUF".
carve_frame 368%nat ST.
do 12 zs. do 14 zs.
pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
pose proof (ashenv_transport _ _ _ ENV MU WM AS) as ENV1.
pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS1. pose proof (rclean_transport _ _ _ _ RCF MU WM AW) as RCF1.
eapply evtF_cut.
{ eapply (PC1 RNG rstk rfmt); rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
[ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
| unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia
| exact KH | exact ENV1 | exact RCS1 | lia | lia | exact RCF1 | exact RFM | exact RPF
| eapply rng_sub'; [exact RGstk | lia] | exact RGimg | exact RGfmt | eapply rng_sub'; [exact RGstk | lia] | exact RRS | exact RRF ]. }
clear ENV1 RCS1 RCF1.
cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
rewrite !unsigned_lit in MUc, STc by lia.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.
clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit.
do 10 zs.
pose proof towrite_proof as TW. unfold towrite_stmt in TW.
eapply evtF_cut.
{ eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption | exact RGF ].
rewrite unsigned_lit; [apply sflags_noerr_8; exact FL40|].
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
cbv beta. intros ms' P. clear TW.
destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
fix_ret.
zs. if_lit. do 6 zs.
set (B := bv_unsigned sp + -352) in *.
match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
apply (rw_cells_split_CB bsegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by lia.
replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
ileave.
pose proof (printf_core_proof (list Z * St) RSTDERR B 80 rstk (SINK_stderr B) TOPOK_none OUT_stderr (OUTFP_stderr (St:=St))
(stderr_sink_frame B) (stderr_sink_flags B) (topok_none) (FWE St B rstk) HSTRN) as PC2.
pose proof (ashenv_transport _ _ _ ENV MU WM AS) as ENV2.
pose proof (rclean_transport _ _ _ _ RCS MU WM AW) as RCS2. pose proof (rclean_transport _ _ _ _ RCF MU WM AW) as RCF2.
assert (RBI : inreg rstk B 80) by (unfold inreg; subst B; lia).
unfold printf_core_stmt in PC2.
assert (FR3 : 0 <= Z.land (bv_unsigned (sx32 flags)) 18446744073709551583 < 2^64).
{ pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
eapply implAM_bind.
{ eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt) (RNG := RNG) (rstk := rstk) (rfmt := rfmt);
clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
all: try lia. all: try exact I.
all: try first [ exact ENV2 | exact RCS2 | exact RCF2 | exact RFM | exact RPF | exact RBI | exact RGimg | exact RGva | exact RGF | exact RGfmt
| exact RRS | exact RRF
| lazymatch goal with |- rng _ _ _ => eapply rng_sub'; [exact RGstk | lia] end ].
- unfold SINK_stderr. cbn [fst].
exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, jb.
change (zlength (@nil Z)) with 0. rewrite Z.add_0_r. cbn [zb map app].
split; [exact FCt|]. rewrite unsigned_lit by lia.
split; [apply sflags_noerr_32|]. split; [apply sflags_noerr_8; exact FL40|]. split; [exact BUFc|].
unfold zlength. rewrite LJB. unfold GLOBALS_TOP. subst B. lia.
- exact BY.
- exact HF.
- reflexivity.
- exact APC.
- exact VAA.
- cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1 | exact WM | exact AW].
- rewrite FPC. apply Forall_nil.
- exact STc.
- split; [exact SSP1 | exact SSP2].
- assumption.
- exact FRM. }
cbv beta. intros r' [buf3 st3] ms' P. clear PC2 MU1 ENV2 RCS2 RCF2.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m3 MUc WMc; clear MUc WMc end.
ienter. fix_ret.
pose proof SNK3 as SNK3'. destruct SNK3' as (flags2 & mode2 & tail2 & rest2 & FC3 & FL32 & FL8 & BUF3 & LEN3 & BHI3 & BLO3). cbn [fst] in FC3, BUF3, LEN3.
unfold file_cells in FC3.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
zs. zs. zs. if_lit.
zs. zs. zs. zs. zs.
ileave. unfold FLUSH_stderr, implAM. cbv beta iota.
pose proof (FLS St B) as FL. unfold stdio_write_flush_stmt in FL.
match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 2368) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
eapply implF_ebind.
{ unfold implAM in FL.
eapply FL with (lo := bv_unsigned sp + -368 - 2368) (canary := canary) (RNG := RNG); clear FL; rewrite ?unsigned_lit by lia; unfold OUT_DEPTH, GLOBALS_TOP.
all: try lia.
all: try first [ exact RGimg | exact RG0 | lazymatch goal with |- rng _ _ _ => eapply rng_sub'; [exact RGstk | lia] end ].
- exact SNK3.
- reflexivity.
- reflexivity.
- reflexivity.
- exact ST4b.
- split; [exact SSP1 | exact SSP2].
- assumption. }
cbv beta. intros [[] st4] RNG' ms' [ERNG P]. subst RNG'.
unfold stdio_write_flush_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (z5 & z6 & z7 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4b' & SNK4 & SSP4).
lazymatch type of MUc with munch _ ?mm _ => transport_after_call bsegs mm m4 MUc WMc; clear MUc WMc end.
apply implAM_retF. cbn [fst snd]. fix_ret.
cbn [fst snd] in SNK4 |- *. clear SNK3 FL.
destruct SNK4 as (flags4 & mode4 & tail4 & rest4 & FC4 & FL32' & FL8' & BUF4 & LEN4 & _ & _). cbn [fst snd] in FC4, BUF4, LEN4.
unfold file_cells in FC4. change (zlength (@nil Z)) with 0 in FC4. rewrite Z.add_0_r in FC4.
clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
do 9 zs.
zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
zs_canary. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 9 zs.
match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 2368)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 2368)%Z _ |- _ =>
pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
pose proof (rw_CB_length _ _ _ _ BUF4) as LB4.
lazymatch goal with A1 : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, A2 : rw_cells _ ?mm (bv_unsigned sp + -360)%Z _,
BU : rw_cells _ ?mm B [CB 80 ?bb], FR : rw_cells _ ?mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
assert (FALL : rw_cells bsegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
[ apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [exact A1|];
apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
| clear A1 A2 BU FR ] end.
cbn [app] in FALL.
release_frame FALL ST5 (bv_unsigned sp).
apply evtF_done. subst QQ. cbn [epost fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST5|].
split.
{ exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags4)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode4, 0, 0, tail4.
split; [unfold file_cells; exact FC4|].
rewrite (sflags_olderr0 flags FL40). rewrite unsigned_lit; [apply sflags_final_40; [exact FL32' | exact FL8']|].
rewrite Z.lor_0_r. pose proof (bv_unsigned_in_range 64 (sx32 flags4)) as R4. unfold bv_modulus in R4. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R4. lia. }
split; [exact SSP1 | exact SSP2].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Stderr.
End CANSEC1.
