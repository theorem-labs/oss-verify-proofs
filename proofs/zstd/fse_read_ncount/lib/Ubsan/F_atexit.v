(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun STRW_tac Startup_kit DrvAgree.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Definition PATEXIT : Z := 0x14e98.
Definition PATX : Z := 0x4ef78.
Definition PATX_CALLFN : Z := 0x14f5c.
Definition PNEED_LOCKS : Z := 0x4f1c3.
Definition PEXIT_GUARD : Z := 0x134b0.
Definition PAEF_INCB : Z := 0x2ee34.
Definition atx_cells (head slot f0 a0 : Z) (m : word -> option byte) : Prop :=
rw_cells usegs m 0x4ef78 [C1 (Z_to_bv 8 0)]
/\ rw_cells usegs m (0x4ef7c) [C4 (Z_to_bv 64 0)]
/\ rw_cells usegs m (0x4ef80) [C4 (Z_to_bv 64 slot)]
/\ rw_cells usegs m (0x4ef88) [C8 (Z_to_bv 64 head)]
/\ rw_cells usegs m (0x4ef90) [C8 (Z_to_bv 64 0)]
/\ rw_cells usegs m (0x4ef98) [C8 (Z_to_bv 64 f0)]
/\ rw_cells usegs m (0x4f098) [C8 (Z_to_bv 64 a0)].
Definition atx_state (reg : bool) (m : word -> option byte) : Prop :=
atx_cells (if reg then 0x4ef90 else 0) (if reg then 1 else 0) (if reg then PATX_CALLFN else 0) (if reg then PEXIT_GUARD else 0) m
/\ rw_cells usegs m PAEF_INCB [C1 (Z_to_bv 8 0)].
Definition atx_addr (a : Z) : Prop :=
(0x4ef78 <= a < 0x4ef79)%Z \/ (0x4ef7c <= a < 0x4ef84)%Z \/ (0x4ef88 <= a < 0x4efa0)%Z \/ (0x4f098 <= a < 0x4f0a0)%Z.
Definition atx_state_addr (a : Z) : Prop := atx_addr a \/ (PAEF_INCB <= a < PAEF_INCB + 1)%Z.
Lemma atx_cells_agree : forall (P : Z -> Prop) m m' head slot f0 a0,
magree usegs P m m' -> (forall a, atx_addr a -> P a) -> atx_cells head slot f0 a0 m -> atx_cells head slot f0 a0 m'.
Proof.
intros P m m' head slot f0 a0 AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold atx_cells.
Ltac agx AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold atx_addr, PATX in *; cbn in Ha; lia].
Local Ltac2 Set LiaHints.tbl := fun () => "0010>56698129348.18000004S2Ha".
split; [agx AG HP A1|]. split; [agx AG HP A2|]. split; [agx AG HP A3|]. split; [agx AG HP A4|].
split; [agx AG HP A5|]. split; [agx AG HP A6| agx AG HP A7].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma atx_state_agree : forall (P : Z -> Prop) m m' reg,
magree usegs P m m' -> (forall a, atx_state_addr a -> P a) -> atx_state reg m -> atx_state reg m'.
Proof.
intros P m m' reg AG HP [AX CB]. split.
- eapply atx_cells_agree; [exact AG| intros a Ha; apply HP; left; exact Ha| exact AX].
- Local Ltac2 Set LiaHints.tbl := fun () => "0010>34721881033.10000004S2Ha".
eapply rw_cells_magree; [exact AG| exact CB| intros a Ha; apply HP; right; unfold PAEF_INCB in *; cbn in Ha; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition patexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo g : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x4ef80, 0x4ef84); (0x4ef88, 0x4ef90); (0x4ef98, 0x4efa0); (0x4f098, 0x4f0a0)]%Z m m'
/\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ atx_cells (0x4ef90) 1 PATX_CALLFN g m'.
Lemma patexit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo g : Z),
stk usegs m lo (bv_unsigned sp) ->
atx_cells 0 0 0 0 m ->
rw_cells usegs m PNEED_LOCKS [C1 (Z_to_bv 8 0)] ->
mem_inv usegs m ->
a0 = Z_to_bv 64 g -> (0 <= g < 2^64)%Z ->
(lo <= bv_unsigned sp - 48)%Z -> (0x50000 <= lo)%Z ->
evt usegs (patexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo g m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PATEXIT) fc None m (seg_rom usegs)).
Proof.
intros until g. intros ST (X1 & X2 & X3 & X4 & X5 & X6 & X7) NL MI -> Hg LO LOLO.
unfold PATX, PNEED_LOCKS, PATEXIT in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x4ef80, 0x4ef84); (0x4ef88, 0x4ef90); (0x4ef98, 0x4efa0); (0x4f098, 0x4f0a0)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "01b0>10136806254.6211010703157.6512608870894.6212637488570.6213768071406.6314025007930.6614328636398.6216933491898.651718456973.67 1723618286.60 17635863152.6517708578106.671800609155.62 18589389294.6218842811194.6519916546158.6221014469232.6722053546702.6222389541692.6022398960058.622269937006.62 22793452142.6224130231354.6724459566414.6224638473347.6224638473347.6324657695214.6225449023214.6326030471949.6226407234618.6627487025262.6227906909861.5427922131438.6228232470254.6328417259964.6229292004410.662937793594.66 29903703861.6730180773870.6030675329978.6231068521070.6231378308326.5331798771054.6232359787248.6233680001082.6334430152252.6334613502574.6036901426061.6637111680570.6638050789454.6338467863406.6340057062766.6240457739452.6240531229166.6041128860986.6741161757422.6342309955386.6542732709998.6243059266230.5143988483203.6043988483203.614454318318.63 45221239098.624541777776.66 45745840622.6045848756903.6046420405562.6546468661564.6246690875510.6047794612789.6647962693050.6248797830094.6249245040366.6349649769127.6351711223320.5352105090727.6252136437230.6252429080398.6052567164907.6052567164907.6252567164907.6352567164907.6552567164907.6652567164907.6752644002798.6053431880694.6053919796282.6554243526019.6254488852794.6756023003502.62563227834.62  56640701754.6557745675194.6258240445498.6658612007565.6559176389614.6260858483367.6260870302650.6261127261166.6062150983482.6763305555623.6264101751662.6264997134979.6365803551930.6767003974766.626734544186.62 67615064174.627004130106.67 7626864058.66 7683670709.62 8583720762.60 8745729466.62 8773384430.62 9234291002.65 00000900B00K00L00U00V00_00`00a00j00k00l00m01601701@01A01J01N01O01X01a01b01k01l01m02602?02@02A02J02N02W02`02d02e02f02o03803903B03C03L03M03R03V03_03`03a03j04304<04@04I04J04S04T04]04a04b04c04l05105205;05<05=05A05B05K05L05U05^05_05`05a05j06306406506606706806906B06C06D06E06F06O06T06U06Z06[06\06e06f06g07007107207;07<07=07F07G07P07Q07R07[07`07a07j07kS2LO4LOLOS2LO4LOLOS2LO4LOLOSS2LO4LOLOSS2LO4LOLOSSS2LO4LOLOSSSS2LO4LOLOSS2LO4LOLOSS2LO4LOLOS2HBSS2LO4LOLOS2LO4LOLOSS2LO4LOLOSSS2LO4LOLOS2LO4LOLOSSS2LO4LOLOS2LOS2LO4LOLOS2LO4LOLOS2HBSSS2LO4LOLOS2LO4LOLOSS2LO4LOLOSS2LO4LOLOSS3RSPS2HBS2LO4LOLOSSS2LO4LOLOS2LO4LOLOS2LO4LOLOS2HBS2LO4LOLOSS2LO4LOLOSS2LO4LOLOS2LOSSS2LO4LOLOS3RSPSS2LO4LOLOSSS2HBSS2LO4LOLOSS2LO4LOLOS2LO4LOLOSSSS2LO4LOLOS2LO4LOLOSSSSSSS2LO4LOLOSSSSS2LO4LOLOS3RSPSS3RSPSSS2LO4LOLOSSS2LO4LOLOSSS2LO4LOLOSSS2LO4LOLOSS2LO4LOLOSSS2LO4LOLOS3RSPSS2LO4LOLOS".
carve_frame 48%nat ST.
steps_to 0x1c73c%Z.
lstep. lstep. lstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. lstep.
steps_to 0x14ec8%Z.
lstep. lstep. lstep. if_false.
lstep. lstep. if_false. lstep. lstep.
lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
lstep. lstep. if_true.
steps_to 0x1c9c4%Z.
lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
lstep. if_false. lstep.
steps_to 0x14f54%Z.
release_frame FR ST (bv_unsigned sp). astep. astep.
unfold patexit_post, atx_cells, PATX, PATX_CALLFN. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
