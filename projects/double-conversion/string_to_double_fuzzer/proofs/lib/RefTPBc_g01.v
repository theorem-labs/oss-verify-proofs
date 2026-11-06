(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymPlan RefTargetEntry_defs RefTargetEntryK_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.
(* [comment removed for export] *)
Local Abbreviation Qd1 := (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) (only parsing).
Definition XC : expr := Qd1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Abbreviation Qd2 := (PCall SumFreePro [] (PMunmap PExitCall)) (only parsing).
Definition p_k0_317_396_cnt1 : plan := Qd2.
Local Abbreviation Qdt3 Qdp1 Qdp2 Qdp3 Qdp4 := (PSplit (EVar Qdp1) Qdp2 Qdp3 Qdp4) (only parsing).
Local Abbreviation Qdt4 Qdp1 Qdp2 Qdp3 Qdp4 := (PResume (Qdt3 Qdp1 Qdp2 Qdp3 Qdp4)) (only parsing).
Definition p_k0_317_396_oom2 : plan := Qdt4 7 127 p_k0_317_396_cnt1 p_k0_317_396_cnt1.
Local Abbreviation Qd5 := (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] Qd2))) (only parsing).
Local Abbreviation Qd6 := (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume Qd5))))))))))))) (only parsing).
Local Abbreviation Qd7 := (PCall SumEnframe [] Qd6) (only parsing).
Local Abbreviation Qd8 := (PCall SumEnframe [] Qd7) (only parsing).
Definition p_k0_317_396_cfg0_3 : plan := PMmap p_k0_317_396_oom2 Qd8.
Definition p_k0_317_396_exit3_4 : plan := Qd5.
Local Abbreviation Qd9 := (PCall SumLib [] (PCall SumPrintf [] (PResume Qd5))) (only parsing).
Local Abbreviation Qdt10 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 := (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit Qdp1 Qdp2 Qdp3 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp4 Qdp5 Qdp6 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp7 Qdp8 Qdp9 Qd9)))))))))))))))))))))) (only parsing).
Local Abbreviation Qdt11 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 := (PCall SumEnframe [] (Qdt10 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9)) (only parsing).
Local Abbreviation Qdt12 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10 := (PMmap Qdp1 (PCall SumEnframe [] (Qdt11 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10))) (only parsing).
Definition p_k0_317_396_cfgpos_5 : plan := Qdt12 p_k0_317_396_oom2 XC 0 p_k0_317_396_exit3_4 XC 1 p_k0_317_396_exit3_4 XC 2 p_k0_317_396_exit3_4.
Definition p_k0_317_396 : plan := Qdt3 5 0 p_k0_317_396_cfg0_3 p_k0_317_396_cfgpos_5.

Local Abbreviation Qd13 := (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (only parsing).
Local Abbreviation Qdc2_14 Qde1 Qde2 Qd0 := (Qde1 :: Qde2 :: Qd0) (only parsing).
Local Abbreviation Qd15 := (SEmit 1 (Qdc2_14 48 10 []) (SExit 0)) (only parsing).
Local Abbreviation Qdc4_16 Qde1 Qde2 Qde3 Qde4 Qd0 := (Qde1 :: Qde2 :: Qde3 :: Qde4 :: Qd0) (only parsing).
Local Abbreviation Qd17 := (SAlt2 Qd13 (SEmit 1 (Qdc2_14 48 10 []) (SCase Qd1 0 (SExit 0) (SCase Qd1 1 Qd15 (SCase Qd1 2 (SEmit 1 (Qdc4_16 48 10 48 10 []) (SExit 0)) (SEmit 1 (Qdc4_16 48 10 48 10 (Qdc2_14 48 10 [])) (SExit 0))))))) (only parsing).
Local Abbreviation Qd18 := (SCase (EVar 5) 0 (SAlt2 Qd13 Qd15) Qd17) (only parsing).
Definition s_k0_317_396 : shape := Qd18.

Lemma chk_k0_317_396 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 317 396) p_k0_317_396 = COk s_k0_317_396.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_317_396)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_397_492_cnt1 : plan := Qd2.
Definition p_k0_397_492_oom2 : plan := Qdt4 7 127 p_k0_397_492_cnt1 p_k0_397_492_cnt1.
Definition p_k0_397_492_cfg0_3 : plan := PMmap p_k0_397_492_oom2 Qd8.
Definition p_k0_397_492_exit3_4 : plan := Qd5.
Definition p_k0_397_492_cfgpos_5 : plan := Qdt12 p_k0_397_492_oom2 XC 0 p_k0_397_492_exit3_4 XC 1 p_k0_397_492_exit3_4 XC 2 p_k0_397_492_exit3_4.
Definition p_k0_397_492 : plan := Qdt3 5 0 p_k0_397_492_cfg0_3 p_k0_397_492_cfgpos_5.

Definition s_k0_397_492 : shape := Qd18.

Lemma chk_k0_397_492 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 397 492) p_k0_397_492 = COk s_k0_397_492.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_397_492)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_493_572_cnt1 : plan := Qd2.
Definition p_k0_493_572_oom2 : plan := Qdt4 7 127 p_k0_493_572_cnt1 p_k0_493_572_cnt1.
Definition p_k0_493_572_cfg0_3 : plan := PMmap p_k0_493_572_oom2 Qd7.
Definition p_k0_493_572_exit3_4 : plan := Qd5.
Local Abbreviation Qdt19 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10 := (PMmap Qdp1 (Qdt11 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10)) (only parsing).
Definition p_k0_493_572_cfgpos_5 : plan := Qdt19 p_k0_493_572_oom2 XC 0 p_k0_493_572_exit3_4 XC 1 p_k0_493_572_exit3_4 XC 2 p_k0_493_572_exit3_4.
Definition p_k0_493_572 : plan := Qdt3 5 0 p_k0_493_572_cfg0_3 p_k0_493_572_cfgpos_5.

Definition s_k0_493_572 : shape := Qd18.

Lemma chk_k0_493_572 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 493 572) p_k0_493_572 = COk s_k0_493_572.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_493_572)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_573_668_cnt1 : plan := Qd2.
Definition p_k0_573_668_oom2 : plan := Qdt4 7 127 p_k0_573_668_cnt1 p_k0_573_668_cnt1.
Definition p_k0_573_668_cfg0_3 : plan := PMmap p_k0_573_668_oom2 Qd7.
Definition p_k0_573_668_exit3_4 : plan := Qd5.
Definition p_k0_573_668_cfgpos_5 : plan := Qdt19 p_k0_573_668_oom2 XC 0 p_k0_573_668_exit3_4 XC 1 p_k0_573_668_exit3_4 XC 2 p_k0_573_668_exit3_4.
Definition p_k0_573_668 : plan := Qdt3 5 0 p_k0_573_668_cfg0_3 p_k0_573_668_cfgpos_5.

Definition s_k0_573_668 : shape := Qd18.

Lemma chk_k0_573_668 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 573 668) p_k0_573_668 = COk s_k0_573_668.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_573_668)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_5437_6540_cnt1 : plan := Qd2.
Definition p_k0_5437_6540_oom2 : plan := Qdt4 7 127 p_k0_5437_6540_cnt1 p_k0_5437_6540_cnt1.
Local Abbreviation Qdt20 Qdp1 := (PMmap Qdp1 Qd6) (only parsing).
Definition p_k0_5437_6540_cfg0_3 : plan := Qdt20 p_k0_5437_6540_oom2.
Definition p_k0_5437_6540_exit3_4 : plan := Qd5.
Local Abbreviation Qdt21 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10 := (PMmap Qdp1 (Qdt10 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10)) (only parsing).
Definition p_k0_5437_6540_cfgpos_5 : plan := Qdt21 p_k0_5437_6540_oom2 XC 0 p_k0_5437_6540_exit3_4 XC 1 p_k0_5437_6540_exit3_4 XC 2 p_k0_5437_6540_exit3_4.
Definition p_k0_5437_6540 : plan := Qdt3 5 0 p_k0_5437_6540_cfg0_3 p_k0_5437_6540_cfgpos_5.

Definition s_k0_5437_6540 : shape := Qd18.

Lemma chk_k0_5437_6540 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 5437 6540) p_k0_5437_6540 = COk s_k0_5437_6540.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_5437_6540)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_6541_8172_cnt1 : plan := Qd2.
Definition p_k0_6541_8172_oom2 : plan := Qdt4 7 127 p_k0_6541_8172_cnt1 p_k0_6541_8172_cnt1.
Definition p_k0_6541_8172_cfg0_3 : plan := Qdt20 p_k0_6541_8172_oom2.
Definition p_k0_6541_8172_exit3_4 : plan := Qd5.
Definition p_k0_6541_8172_cfgpos_5 : plan := Qdt21 p_k0_6541_8172_oom2 XC 0 p_k0_6541_8172_exit3_4 XC 1 p_k0_6541_8172_exit3_4 XC 2 p_k0_6541_8172_exit3_4.
Definition p_k0_6541_8172 : plan := Qdt3 5 0 p_k0_6541_8172_cfg0_3 p_k0_6541_8172_cfgpos_5.

Definition s_k0_6541_8172 : shape := Qd18.

Lemma chk_k0_6541_8172 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 6541 8172) p_k0_6541_8172 = COk s_k0_6541_8172.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_6541_8172)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_8173_9340_cnt1 : plan := Qd2.
Definition p_k0_8173_9340_oom2 : plan := Qdt4 7 127 p_k0_8173_9340_cnt1 p_k0_8173_9340_cnt1.
Definition p_k0_8173_9340_cfg0_3 : plan := Qdt20 p_k0_8173_9340_oom2.
Definition p_k0_8173_9340_exit3_4 : plan := Qd5.
Definition p_k0_8173_9340_cfgpos_5 : plan := Qdt21 p_k0_8173_9340_oom2 XC 0 p_k0_8173_9340_exit3_4 XC 1 p_k0_8173_9340_exit3_4 XC 2 p_k0_8173_9340_exit3_4.
Definition p_k0_8173_9340 : plan := Qdt3 5 0 p_k0_8173_9340_cfg0_3 p_k0_8173_9340_cfgpos_5.

Definition s_k0_8173_9340 : shape := Qd18.

Lemma chk_k0_8173_9340 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 8173 9340) p_k0_8173_9340 = COk s_k0_8173_9340.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_8173_9340)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_9341_10908_cnt1 : plan := Qd2.
Definition p_k0_9341_10908_oom2 : plan := Qdt4 7 127 p_k0_9341_10908_cnt1 p_k0_9341_10908_cnt1.
Definition p_k0_9341_10908_cfg0_3 : plan := Qdt20 p_k0_9341_10908_oom2.
Definition p_k0_9341_10908_exit3_4 : plan := Qd5.
Definition p_k0_9341_10908_cfgpos_5 : plan := Qdt21 p_k0_9341_10908_oom2 XC 0 p_k0_9341_10908_exit3_4 XC 1 p_k0_9341_10908_exit3_4 XC 2 p_k0_9341_10908_exit3_4.
Definition p_k0_9341_10908 : plan := Qdt3 5 0 p_k0_9341_10908_cfg0_3 p_k0_9341_10908_cfgpos_5.

Definition s_k0_9341_10908 : shape := Qd18.

Lemma chk_k0_9341_10908 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 9341 10908) p_k0_9341_10908 = COk s_k0_9341_10908.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_9341_10908)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_10909_12268_cnt1 : plan := Qd2.
Definition p_k0_10909_12268_oom2 : plan := Qdt4 7 127 p_k0_10909_12268_cnt1 p_k0_10909_12268_cnt1.
Definition p_k0_10909_12268_cfg0_3 : plan := Qdt20 p_k0_10909_12268_oom2.
Definition p_k0_10909_12268_exit3_4 : plan := Qd5.
Definition p_k0_10909_12268_cfgpos_5 : plan := Qdt21 p_k0_10909_12268_oom2 XC 0 p_k0_10909_12268_exit3_4 XC 1 p_k0_10909_12268_exit3_4 XC 2 p_k0_10909_12268_exit3_4.
Definition p_k0_10909_12268 : plan := Qdt3 5 0 p_k0_10909_12268_cfg0_3 p_k0_10909_12268_cfgpos_5.

Definition s_k0_10909_12268 : shape := Qd18.

Lemma chk_k0_10909_12268 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 10909 12268) p_k0_10909_12268 = COk s_k0_10909_12268.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_10909_12268)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_18701_20460_cnt1 : plan := Qd2.
Definition p_k0_18701_20460_oom2 : plan := Qdt4 7 127 p_k0_18701_20460_cnt1 p_k0_18701_20460_cnt1.
Definition p_k0_18701_20460_cfg0_3 : plan := Qdt20 p_k0_18701_20460_oom2.
Definition p_k0_18701_20460_exit3_4 : plan := Qd5.
Definition p_k0_18701_20460_cfgpos_5 : plan := Qdt21 p_k0_18701_20460_oom2 XC 0 p_k0_18701_20460_exit3_4 XC 1 p_k0_18701_20460_exit3_4 XC 2 p_k0_18701_20460_exit3_4.
Definition p_k0_18701_20460 : plan := Qdt3 5 0 p_k0_18701_20460_cfg0_3 p_k0_18701_20460_cfgpos_5.

Definition s_k0_18701_20460 : shape := Qd18.

Lemma chk_k0_18701_20460 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 18701 20460) p_k0_18701_20460 = COk s_k0_18701_20460.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_18701_20460)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_20461_21820_cnt1 : plan := Qd2.
Definition p_k0_20461_21820_oom2 : plan := Qdt4 7 127 p_k0_20461_21820_cnt1 p_k0_20461_21820_cnt1.
Definition p_k0_20461_21820_cfg0_3 : plan := Qdt20 p_k0_20461_21820_oom2.
Definition p_k0_20461_21820_exit3_4 : plan := Qd5.
Definition p_k0_20461_21820_cfgpos_5 : plan := Qdt21 p_k0_20461_21820_oom2 XC 0 p_k0_20461_21820_exit3_4 XC 1 p_k0_20461_21820_exit3_4 XC 2 p_k0_20461_21820_exit3_4.
Definition p_k0_20461_21820 : plan := Qdt3 5 0 p_k0_20461_21820_cfg0_3 p_k0_20461_21820_cfgpos_5.

Definition s_k0_20461_21820 : shape := Qd18.

Lemma chk_k0_20461_21820 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 20461 21820) p_k0_20461_21820 = COk s_k0_20461_21820.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_20461_21820)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_24557_26188_cnt1 : plan := Qd2.
Definition p_k0_24557_26188_oom2 : plan := Qdt4 7 127 p_k0_24557_26188_cnt1 p_k0_24557_26188_cnt1.
Definition p_k0_24557_26188_cfg0_3 : plan := Qdt20 p_k0_24557_26188_oom2.
Definition p_k0_24557_26188_exit3_4 : plan := Qd5.
Definition p_k0_24557_26188_cfgpos_5 : plan := Qdt21 p_k0_24557_26188_oom2 XC 0 p_k0_24557_26188_exit3_4 XC 1 p_k0_24557_26188_exit3_4 XC 2 p_k0_24557_26188_exit3_4.
Definition p_k0_24557_26188 : plan := Qdt3 5 0 p_k0_24557_26188_cfg0_3 p_k0_24557_26188_cfgpos_5.

Definition s_k0_24557_26188 : shape := Qd18.

Lemma chk_k0_24557_26188 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 24557 26188) p_k0_24557_26188 = COk s_k0_24557_26188.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_24557_26188)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_43677_45036_cnt1 : plan := Qd2.
Definition p_k0_43677_45036_oom2 : plan := Qdt4 7 127 p_k0_43677_45036_cnt1 p_k0_43677_45036_cnt1.
Definition p_k0_43677_45036_cfg0_3 : plan := Qdt20 p_k0_43677_45036_oom2.
Definition p_k0_43677_45036_exit3_4 : plan := Qd5.
Definition p_k0_43677_45036_cfgpos_5 : plan := Qdt21 p_k0_43677_45036_oom2 XC 0 p_k0_43677_45036_exit3_4 XC 1 p_k0_43677_45036_exit3_4 XC 2 p_k0_43677_45036_exit3_4.
Definition p_k0_43677_45036 : plan := Qdt3 5 0 p_k0_43677_45036_cfg0_3 p_k0_43677_45036_cfgpos_5.

Definition s_k0_43677_45036 : shape := Qd18.

Lemma chk_k0_43677_45036 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 43677 45036) p_k0_43677_45036 = COk s_k0_43677_45036.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_43677_45036)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_32763_36844_cnt1 : plan := Qd2.
Definition p_k1_32763_36844_exit3_2 : plan := Qd5.
Definition p_k1_32763_36844_oom3 : plan := Qdt4 7 127 p_k1_32763_36844_cnt1 p_k1_32763_36844_cnt1.
Definition p_k1_32763_36844_cfgpos_4 : plan := Qdt21 p_k1_32763_36844_oom3 XC 0 p_k1_32763_36844_exit3_2 XC 1 p_k1_32763_36844_exit3_2 XC 2 p_k1_32763_36844_exit3_2.
Definition p_k1_32763_36844 : plan := PSplit (EVar 5) 0 PContra p_k1_32763_36844_cfgpos_4.

Definition s_k1_32763_36844 : shape := SCase (EVar 5) 0 SNil Qd17.

Lemma chk_k1_32763_36844 : check ImgP.M.loaded_segments ITAB P0 NX0k 20000%nat 400%nat (cs_Tk 1 32763 36844) p_k1_32763_36844 = COk s_k1_32763_36844.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_32763_36844)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_73709_74876_cnt1 : plan := Qd2.
Definition p_k1_73709_74876_oom2 : plan := Qdt4 7 127 p_k1_73709_74876_cnt1 p_k1_73709_74876_cnt1.
Definition p_k1_73709_74876_cfg0_3 : plan := Qdt20 p_k1_73709_74876_oom2.
Definition p_k1_73709_74876_exit3_4 : plan := Qd5.
Definition p_k1_73709_74876_cfgpos_5 : plan := Qdt21 p_k1_73709_74876_oom2 XC 0 p_k1_73709_74876_exit3_4 XC 1 p_k1_73709_74876_exit3_4 XC 2 p_k1_73709_74876_exit3_4.
Definition p_k1_73709_74876 : plan := Qdt3 5 0 p_k1_73709_74876_cfg0_3 p_k1_73709_74876_cfgpos_5.

Definition s_k1_73709_74876 : shape := Qd18.

Lemma chk_k1_73709_74876 : check ImgP.M.loaded_segments ITAB P0 NX0k 20000%nat 400%nat (cs_Tk 1 73709 74876) p_k1_73709_74876 = COk s_k1_73709_74876.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_73709_74876)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_85997_87356_cnt1 : plan := Qd2.
Definition p_k1_85997_87356_oom2 : plan := Qdt4 7 127 p_k1_85997_87356_cnt1 p_k1_85997_87356_cnt1.
Definition p_k1_85997_87356_cfg0_3 : plan := Qdt20 p_k1_85997_87356_oom2.
Definition p_k1_85997_87356_exit3_4 : plan := Qd5.
Definition p_k1_85997_87356_cfgpos_5 : plan := Qdt21 p_k1_85997_87356_oom2 XC 0 p_k1_85997_87356_exit3_4 XC 1 p_k1_85997_87356_exit3_4 XC 2 p_k1_85997_87356_exit3_4.
Definition p_k1_85997_87356 : plan := Qdt3 5 0 p_k1_85997_87356_cfg0_3 p_k1_85997_87356_cfgpos_5.

Definition s_k1_85997_87356 : shape := Qd18.

Lemma chk_k1_85997_87356 : check ImgP.M.loaded_segments ITAB P0 NX0k 20000%nat 400%nat (cs_Tk 1 85997 87356) p_k1_85997_87356 = COk s_k1_85997_87356.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_85997_87356)). Qed.

