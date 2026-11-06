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
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg F_syscalls MonadF.
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
repeat (match goal with H : rw_cells asegs _ (Zpos ?p) _ |- _ =>
tryif (match goal with H' : rw_cells asegs _ (Zpos ?p') _ |- _ =>
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
Definition APATEXIT : Z := 0x89184.
Definition APATX_CALLFN : Z := 0x89248.
Definition APNEED_LOCKS : Z := 0x5f56a3.
Definition ACOV_HOOK : Z := 0x703f4.
Definition ACOV_FLAG : Z := 0x134320.
Definition APEXIT_GUARD : Z := 0x80dbc.
Definition APAEF_INCB : Z := 0x5d4ad4.
Definition atx_cellsA (slot f1 a1 : Z) (m : mem) : Prop :=
rw_cells asegs m 0x5f5460 [C1 (Z_to_bv 8 0)]
/\ rw_cells asegs m 0x5f5464 [C4 (Z_to_bv 64 0)]
/\ rw_cells asegs m 0x5f5468 [C4 (Z_to_bv 64 slot)]
/\ rw_cells asegs m 0x5f5470 [C8 (Z_to_bv 64 0x5f5478)]
/\ rw_cells asegs m 0x5f5478 [C8 (Z_to_bv 64 0)]
/\ rw_cells asegs m 0x5f5480 [C8 (Z_to_bv 64 APATX_CALLFN)]
/\ rw_cells asegs m 0x5f5580 [C8 (Z_to_bv 64 ACOV_HOOK)]
/\ rw_cells asegs m 0x5f5488 [C8 (Z_to_bv 64 f1)]
/\ rw_cells asegs m 0x5f5588 [C8 (Z_to_bv 64 a1)].
Definition atx_stateA (reg : bool) (m : mem) : Prop :=
atx_cellsA (if reg then 2 else 1) (if reg then APATX_CALLFN else 0) (if reg then APEXIT_GUARD else 0) m
/\ rw_cells asegs m APAEF_INCB [C1 (Z_to_bv 8 0)]
/\ rw_cells asegs m ACOV_FLAG [C1 (Z_to_bv 8 0)].
Definition atx_addrA (a : Z) : Prop :=
(0x5f5460 <= a < 0x5f5461)%Z \/ (0x5f5464 <= a < 0x5f546c)%Z \/ (0x5f5470 <= a < 0x5f5490)%Z \/ (0x5f5580 <= a < 0x5f5590)%Z.
Definition atx_state_addrA (a : Z) : Prop := atx_addrA a \/ (0x5d4ad4 <= a < 0x5d4ad5)%Z \/ (0x134320 <= a < 0x134321)%Z.
Lemma atx_cellsA_agree : forall (P : Z -> Prop) m m' slot f1 a1,
magree asegs P m m' -> (forall a, atx_addrA a -> P a) -> atx_cellsA slot f1 a1 m -> atx_cellsA slot f1 a1 m'.
Proof.
intros P m m' slot f1 a1 AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). unfold atx_cellsA.
Ltac agx AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold atx_addrA in *; cbn in Ha; lia].
Local Ltac2 Set LiaHints.tbl := fun () => "0010>41908313284.19000004S2Ha".
split; [agx AG HP A1|]. split; [agx AG HP A2|]. split; [agx AG HP A3|]. split; [agx AG HP A4|].
split; [agx AG HP A5|]. split; [agx AG HP A6|]. split; [agx AG HP A7|]. split; [agx AG HP A8| agx AG HP A9].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma atx_stateA_agree : forall (P : Z -> Prop) m m' reg,
magree asegs P m m' -> (forall a, atx_state_addrA a -> P a) -> atx_stateA reg m -> atx_stateA reg m'.
Proof.
intros P m m' reg AG HP (AX & CB & CF). split; [| split].
- eapply atx_cellsA_agree; [exact AG| intros a Ha; apply HP; left; exact Ha| exact AX].
- Local Ltac2 Set LiaHints.tbl := fun () => "0020>17389544096.1154664153888.11000004008S2HaS2Ha".
eapply rw_cells_magree; [exact AG| exact CB| intros a Ha; apply HP; right; left; unfold APAEF_INCB in *; cbn in Ha; lia].
- eapply rw_cells_magree; [exact AG| exact CF| intros a Ha; apply HP; right; right; unfold ACOV_FLAG in *; cbn in Ha; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section CANSEC1. Context {rc : runConstT}.
Definition patexit_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo g : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f5468, 0x5f546c); (0x5f5488, 0x5f5490); (0x5f5588, 0x5f5590)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ atx_cellsA 2 APATX_CALLFN g m'.
#[using="Type"] Lemma patexit_specA : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo g : Z),
stk asegs m lo (bv_unsigned sp) ->
atx_cellsA 1 0 0 m ->
rw_cells asegs m APNEED_LOCKS [C1 (Z_to_bv 8 0)] ->
mem_inv asegs m ->
a0 = Z_to_bv 64 g -> (0 <= g < 2^64)%Z ->
(lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
evtF asegs RNG (patexit_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo g m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APATEXIT) fc None m (seg_rom asegs)).
Proof.
intros until g. intros ST (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) NL MI -> Hg LO KH RSTK RIMG.
unfold APNEED_LOCKS, APATEXIT, APATX_CALLFN, ACOV_HOOK in *. pose proof KH as KH'. unfold KHIGH in KH'.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f5468, 0x5f546c); (0x5f5488, 0x5f5490); (0x5f5588, 0x5f5590)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "01n0>10279686709.7210345787758.691042885690.72 11613074542.6911624100237.6912389690253.7412898343994.7414965928558.6915239826254.6715399724986.6915401314670.6916592417338.7217440010734.6717776320431.681800609155.69 18472172602.6918694006766.6719603176506.7419622476014.7019715914222.671994914414.69 20358894318.7022389541692.6722641828174.6923806169710.6923847006446.7024336903790.7024638473347.6924638473347.7025792608750.6726585609786.7227717157230.6927907070492.6128417259964.6929013669434.7229181207093.7429193796462.6929218357326.7029531591534.6929870281326.6930740307312.6930876851182.6931378308326.6032307613550.6732716547054.6933680001082.7034430152252.7036115622446.6936115622447.683622303802.69 36936768494.6937813712954.6939485255630.6939806217206.6740457739452.6940597249904.7240647629038.7040653749742.6942434819642.7242923401786.7443059266230.5843299019630.6943864983022.6943967450992.7443987951406.6943988483203.6743988483203.6844590757434.6945221239098.6945848756903.6746063881934.6946134254574.6946468661564.694745347642.74 47974685754.6948217190970.7248712801850.694890470458.69 49305458106.7449649769127.7050263849454.6750317564526.6951004059630.6751711223320.6052105090727.6952567164907.6752567164907.6952567164907.7052567164907.7252567164907.7453767577775.6853923769402.7254243526019.6954722921710.6956072045370.69563227834.69  56375174714.74563780493.72  56573624373.6956757832430.7056840378606.7057400943598.6957745675194.6958501866938.7259415204078.705953130734.70 60280114806.6760858483367.6962245250030.6962492919098.7262569894766.6962704248302.6963235321900.6663235321900.6763305555623.6963338612282.7464997134979.7065097823086.6967773994298.7468008320110.6968096078318.677720336238.69 8054831726.69 8583720762.67 8967238126.67 9164252730.74 00000800@00A00I00J00K00L00T00\00]00e00f00n01201301401<01=01E01M01U01]01a01i02102902A02B02C02K02L02T02X02\02]02e02m03503=03E03F03N03O03W03_03d03h03l04004104904:04B04C04G04H04P04X04Y04Z04^04f04n04o05305405505605;05<05D05L05P05Q05R05S05T05U05V05W05_05g05o06006106206306406506606:06;06<06D06E06J06K06L06T06\06d06l07107207:07B07C07D07L07M07U07]07a07e07f07g07h08008108908A08I08Q08V08^08_S2LO3KH'S2LO3KH'SS2LO3KH'SSSS2LO3KH'S2LO3KH'SS2LO3KH'SS2LO3KH'S2LOSSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2HBS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SSS2LO3KH'SS2LO3KH'S2LOS2HBSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'SS2LO3KH'S2LO3KH'S3RSPS2HBS2LOS2LOSS2LO3KH'SS2LO3KH'SS2HBSS2LO3KH'S2LO3KH'SSS2LOS2LO3KH'S2LO3KH'SS2LOSSSS3RSPSS2LO3KH'S2LO3KH'S2HBSSSSSSSS2LO3KH'S2LO3KH'S2LO3KH'SSSSSSSS2LOSSS2LO3KH'SS3RSPSSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S3RSPSS2LO3KH'S2LO3KH'SSS2LO3KH'SS2LO3KH'S2LO3KH'S2LOS2LOSSSS2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S3RSPS2LO3KH'S".
carve_frame 48%nat ST.
steps_to 0x93380%Z.
hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
steps_to 0x891b4%Z.
hstep. hstep. hstep. if_false.
hstep. hstep. if_true.
hstep. try replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
hstep. hstep. if_true.
steps_to 0x93608%Z.
hstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
hstep. if_false. hstep.
steps_to 0x89240%Z.
release_frame FR ST (bv_unsigned sp). astep. astep.
unfold patexit_postA, atx_cellsA, APATX_CALLFN, ACOV_HOOK. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
