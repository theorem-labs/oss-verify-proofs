(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib DrvAgree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg F_syscalls MonadF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
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

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac sort_lits :=
repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
then fail
else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
Ltac hyp_by_addr :=
lazymatch goal with
| |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
| |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
| |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
| |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
end.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).
Definition APATEXIT : Z := 0x89314.
Definition APATX_CALLFN : Z := 0x893d8.
Definition APNEED_LOCKS : Z := 0x5f5763.
Definition ACOV_HOOK : Z := 0x702e0.
Definition ACOV_FLAG : Z := 0x1343e0.
Definition APEXIT_GUARD : Z := 0x80ca8.
Definition APAEF_INCB : Z := 0x5d4b94.
Definition atx_cellsA (slot f1 a1 : Z) (m : mem) : Prop :=
rw_cells bsegs m 0x5f5520 [C1 (Z_to_bv 8 0)]
/\ rw_cells bsegs m 0x5f5524 [C4 (Z_to_bv 64 0)]
/\ rw_cells bsegs m 0x5f5528 [C4 (Z_to_bv 64 slot)]
/\ rw_cells bsegs m 0x5f5530 [C8 (Z_to_bv 64 0x5f5538)]
/\ rw_cells bsegs m 0x5f5538 [C8 (Z_to_bv 64 0)]
/\ rw_cells bsegs m 0x5f5540 [C8 (Z_to_bv 64 APATX_CALLFN)]
/\ rw_cells bsegs m 0x5f5640 [C8 (Z_to_bv 64 ACOV_HOOK)]
/\ rw_cells bsegs m 0x5f5548 [C8 (Z_to_bv 64 f1)]
/\ rw_cells bsegs m 0x5f5648 [C8 (Z_to_bv 64 a1)].
Definition atx_stateA (reg : bool) (m : mem) : Prop :=
atx_cellsA (if reg then 2 else 1) (if reg then APATX_CALLFN else 0) (if reg then APEXIT_GUARD else 0) m
/\ rw_cells bsegs m APAEF_INCB [C1 (Z_to_bv 8 0)]
/\ rw_cells bsegs m ACOV_FLAG [C1 (Z_to_bv 8 0)].
Definition atx_addrA (a : Z) : Prop :=
(0x5f5520 <= a < 0x5f5521)%Z \/ (0x5f5524 <= a < 0x5f552c)%Z \/ (0x5f5530 <= a < 0x5f5550)%Z \/ (0x5f5640 <= a < 0x5f5650)%Z.
Definition atx_state_addrA (a : Z) : Prop := atx_addrA a \/ (0x5d4b94 <= a < 0x5d4b95)%Z \/ (0x1343e0 <= a < 0x1343e1)%Z.
Lemma atx_cellsA_agree : forall (P : Z -> Prop) m m' slot f1 a1,
magree bsegs P m m' -> (forall a, atx_addrA a -> P a) -> atx_cellsA slot f1 a1 m -> atx_cellsA slot f1 a1 m'.
Proof.
intros P m m' slot f1 a1 AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). unfold atx_cellsA.
Ltac agx AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold atx_addrA in *; cbn in Ha; lia].
Local Ltac2 Set LiaHints.tbl := fun () => "0010<139459780.19000004S2Ha".
split; [agx AG HP A1|]. split; [agx AG HP A2|]. split; [agx AG HP A3|]. split; [agx AG HP A4|].
split; [agx AG HP A5|]. split; [agx AG HP A6|]. split; [agx AG HP A7|]. split; [agx AG HP A8| agx AG HP A9].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma atx_stateA_agree : forall (P : Z -> Prop) m m' reg,
magree bsegs P m m' -> (forall a, atx_state_addrA a -> P a) -> atx_stateA reg m -> atx_stateA reg m'.
Proof.
intros P m m' reg AG HP (AX & CB & CF). split; [| split].
- eapply atx_cellsA_agree; [exact AG| intros a Ha; apply HP; left; exact Ha| exact AX].
- Local Ltac2 Set LiaHints.tbl := fun () => "0020>23394620064.1159654290208.11000004008S2HaS2Ha".
eapply rw_cells_magree; [exact AG| exact CB| intros a Ha; apply HP; right; left; unfold APAEF_INCB in *; cbn in Ha; lia].
- eapply rw_cells_magree; [exact AG| exact CF| intros a Ha; apply HP; right; right; unfold ACOV_FLAG in *; cbn in Ha; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section CANSEC1. Context {rc : runConstT}.
Definition patexit_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo g : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f5528, 0x5f552c); (0x5f5548, 0x5f5550); (0x5f5648, 0x5f5650)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ atx_cellsA 2 APATX_CALLFN g m'.
#[using="Type"] Lemma patexit_specA : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo g : Z),
stk bsegs m lo (bv_unsigned sp) ->
atx_cellsA 1 0 0 m ->
rw_cells bsegs m APNEED_LOCKS [C1 (Z_to_bv 8 0)] ->
mem_inv bsegs m ->
a0 = Z_to_bv 64 g -> (0 <= g < 2^64)%Z ->
(lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
evtF bsegs RNG (patexit_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo g m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APATEXIT) fc None m (seg_rom bsegs)).
Proof.
intros until g. intros ST (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) NL MI -> Hg LO KH RSTK RIMG.
unfold APNEED_LOCKS, APATEXIT, APATX_CALLFN, ACOV_HOOK in *. pose proof KH as KH'. unfold KHIGH in KH'.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f5528, 0x5f552c); (0x5f5548, 0x5f5550); (0x5f5648, 0x5f5650)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "01n0>10136806254.6911514987578.741171576688.72 13768071406.7014159447534.6914328636398.6915135021626.7415204751930.741586831214.67 16394845038.6916733534830.6917510092090.7217776320431.681800609155.69 1931560046.69 22389541692.6722793452142.6923498667066.7223570233326.6723742962798.6924638473347.6924638473347.702590035514.74 27907070492.612793184826.72 28417259964.6929950340078.6930958998586.6931068521070.6931356015674.7231378308326.6031423754298.6931662557237.6932531853370.6932595612014.6933510318702.6933680001082.7034170545134.6934430152252.7034454534638.6734650439630.6935045894714.7236115622446.6936115622447.6836901426061.7437111680570.7437359508794.7437364793838.6737380448590.6937917614158.7038926605882.7239476301370.7439482238446.6940457739452.6940531229166.6740583097326.6940584289006.704068500334.69 40830108557.7241589340654.6743059266230.5843350164538.7443941322990.7043987951406.6943988483203.6743988483203.684454318318.70 44804625134.7045221239098.694541777776.74 45745840622.6745848756903.6746058767598.6946396466030.6946468661564.6947794612789.7448165869806.704829287792.69 4903099834.72 49649769127.7051011570510.6751711223320.6051890444685.6952105090727.6952567164907.6752567164907.6952567164907.7052567164907.7252567164907.7452970898030.6953767577775.6854083902005.7254243526019.6954289615862.6754394415470.6954893195322.6955201985594.69563227834.69  57745675194.695808028474.69 59176389614.6959303010234.6959823140282.746062692974.69 60858483367.6962891835758.6963046200890.6963235321900.6663235321900.6763305555623.6963894255854.7064019761722.7264101751662.6964893713978.7264997134979.7066161370682.6966766799342.6767105489134.706736605166.67 68205640558.6968303650510.696950140022.67 8163491438.70 8264524782.69 8583720762.67 9939242478.69 00000800900:00B00J00R00S00T00\00d00l00m01101201:01>01F01G01O01W01X01Y01Z01^01_01c01k01l02402502602702?02@02H02P02U02]02a02i03103203603:03;03<03=03E03M03U03V03W03_03c03k04304;04C04D04L04P04Q04Y04]04^04_04g04o05405505=05>05F05N05R05Z05b05c05d05e05m05n05o06006106206306406506=06A06I06J06K06S06T06U06Z06_06`06h06i06j07207307;07<07@07D07E07M07N07V07W07X07Y07a07i08108908A08B08J08R08W08_S2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'SS2LOSS2LO3KH'S2HBS2LO3KH'SS2LO3KH'S2LO3KH'SSSS2LOSS2HBS2LO3KH'SS2LO3KH'SSSS2LO3KH'SS2LO3KH'S2LO3KH'S3RSPS2LO3KH'S2HBS2LO3KH'S2LO3KH'SS2LOS2LOSSSS2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'S2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LOSS2LO3KH'S2LOSSS2LO3KH'S2LO3KH'S3RSPSS2LO3KH'SS2LO3KH'S2LO3KH'S2HBS2LO3KH'S2LO3KH'SSSS2LO3KH'SSSSSSSSS2LO3KH'S2LOS2LO3KH'SSS2LO3KH'SSS3RSPS3RSPSS2LO3KH'SSS2LO3KH'SS2LO3KH'SS2LOS2LOSS2LO3KH'SS2LO3KH'SSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S3RSPS2LO3KH'".
carve_frame 48%nat ST.
steps_to 0x93510%Z.
hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
steps_to 0x89344%Z.
hstep. hstep. hstep. if_false.
hstep. hstep. if_true.
hstep. try replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
hstep. hstep. if_true.
steps_to 0x93798%Z.
hstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
hstep. if_false. hstep.
steps_to 0x893d0%Z.
release_frame FR ST (bv_unsigned sp). astep. astep.
unfold patexit_postA, atx_cellsA, APATX_CALLFN, ACOV_HOOK. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
