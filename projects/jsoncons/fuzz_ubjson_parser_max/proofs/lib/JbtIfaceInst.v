(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA ArtMem ArtRuns ArtBridge JbtInv JbtFsInv JbtFsInvLaws
JbtWrapMallocAll JbtWrapAligned16 JbtIfaceLaws JbtInvFrame JbtIfaceFrame JbtIfaceRelease JbtHandoffRi JbtWrapMemI JbtWrapHnr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx ShadowRLaws StrictOfJ.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtIfaceInst () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtIfaceInst."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StrictOfJ."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0BASE"; "0BUDGET"; "1list"; "1option"; "1prod"; "2and"; "2or"; "3Z"; "0G"; "0LB"; "0M"; "0MAPS0"; "0NOACC0"; "0RESV0"; "4cell"; "5BIGSHADOW_LO"]; ["5aaligned16_spec"; "5ahandle_no_return_spec"; "5amalloc_spec"; "5amemcpy_spec"; "5amemmove_spec"; "5amemset_spec"; "5asan_iface_ok"; "5hl_img_hi"; "5hl_rt_ro"; "5hl_rt_static"; "5rt_release_frame"; "6asan_iface_okR"; "6rt_frame_ctr"; "6strict_of"; "7art_fsg"; "7art_fsinv"]; ["8art_C"; "8art_L"; "9art_alloc_rep"; "9art_gs"; "9art_iface"; "9art_zone_statics"; "9rn_ar"; "9rn_key"; "9rn_loff"; "9rn_tp"; "9rn_tsd"; ":rt_flag_in_fs"; ";loaded_segments"; "<add"; "<le"; "<lt"]; ["<mul"; "<sub"; "0a"; "0rn"; "0scfg"; "=bv"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Definition art_static (a : Z) : Prop :=
0x136000 <= a < 0x138ac0 \/ 0x139380 <= a < 0x65f090 \/ 0x670a68 <= a < 0x670a70 \/ 0x670ab8 <= a < 0x670ad0 \/ 0x670ad0 <= a < 0x670ad4
\/ 0x670ae8 <= a < 0x670af0 \/ 0x691f78 <= a < 0x691f80.
Definition art_ro (a : Z) : Prop := 0x10000 <= a < 0x136000.
Definition art_L : asan_layout :=
AL ASEGS 0x79190 0x7918c 0x79198 (fun k => if k =? 0 then 0x5d4fc else if k =? 1 then 0x5d670 else if k =? 2 then 0x5d800 else if k =? 3 then 0x5d99c else 0x5db48) 0x80b60 0x77aa8 0x7760c 0x77ce8
0x670ac0 0x10000 0x693000 art_static art_ro 4096 4096 4096 512 4160 2560 8 3 (2 ^ 21) 8192 (2 ^ 34).
Definition art_C : asan_statics_cells := art_statics_cells.
Lemma art_L_statics : ltac2:(TCodec.tc2 tcn__JbtIfaceInst ":'7&Q5r1%211&I&Q1r2%3221p051pS691").
Proof. intros a Z. cbn [art_L hl_rt_static]. unfold art_static, art_zone_statics in *. lia. Qed.
Lemma art_L_ro : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "@'7'5&Q>+RPP0r1%3221&Q?+QVhP0%2241%8241&H&Q1r2%3221p051pS6?1").
Proof. intros a Z. exact Z. Qed.
Section Inst.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis Htp : rn_tp rn = 0x670ac0.
Hypothesis Hkey0 : rn_key rn = 0.
Hypothesis Htsd : rn_tsd rn = 0x691f78.
Hypothesis Hloff : rn_loff rn = 0x10.
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[using="Htp Hkey0 Htsd Hloff"] Lemma art_L_tls : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "QO'7'6'5&Q>&QA&Q9vQC%211+RH%5221r1%8221&Q?+R@%:271%3251%>251&Q=&Q:%11=&Q@+8&Q7%11A%4231%8261%G21@%:226%@2B1%K231+V^ReH%L21E+V^Rf0%E2G1%Q0231+V^Rg8%Q121J+V^Rg@%J2L1%Q5231%Q52Q1N%H2Q2D%N2Q01%Q9231&Q8%11Q7%M2Q71%Q<21Q5+4%Q0231%Q62Q81%QA241%QC291%QD2>1%QE2D1%QF2J1%QG2Q81&I&Q1r2%3221p051pS6QN1").
Proof. intros a Z. rewrite Htp, Hkey0, Htsd, Hloff in Z. cbn [art_L hl_rt_static]. unfold art_static. lia. Qed.
#[using="Htp"] Lemma art_L_cs : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "Q3'7'6'5&Q>+QVh]Hr1%3221&Q?+QVh^0%2241%8241+QVhd0%9217+QVhdH%7291%=231&Q=&Q9vQC%211+8%5221%C21A+@%8251%B2D1%H241%J2<1%K2B1&I&Q1r2%3221p051pS6Q21").
Proof. intros a Z. rewrite Htp in Z. cbn [art_L hl_rt_static]. unfold art_static. lia. Qed.
Hypothesis FREE : afree_spec art_L (rn_ar rn) scfg HI.
Hypothesis SMALLOC : forall k, In k [0; 1; 2; 3; 4] -> astack_malloc_spec art_L (rn_ar rn) scfg HI k.
#[using="Type"] Lemma art_L_static_img0 : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "@'7&I&Q1r1%3221'5&Q>+RPP0r2%3221&Q?+Vb\P0%2241%8241p0:1pS6?1").
Proof. intros a S. cbn [art_L hl_rt_static] in S. unfold art_static in S. lia. Qed.
#[using="Type"] Lemma art_L_ro_img0 : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "@'7&H&Q1r1%3221'5&Q>+RPP0r2%3221&Q?+Vb\P0%2241%8241p0:1pS6?1").
Proof. intros a S. cbn [art_L hl_rt_ro] in S. unfold art_ro in S. lia. Qed.
#[using="Hwx Htp"] Theorem art_inst_no_return : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "@&A&Q1&Q6vQC%211vQD&Q4'Nv;v=v<v0v1&O%887654321;%?4>;:1").
Proof. apply (art_ahnr MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L); try reflexivity. symmetry. exact Htp. Qed.
#[using="Hwx Htp Hkey0 Htsd Hloff"] Theorem art_inst_memset : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "@&E&Q1&Q6vQC%211vQD&Q4'Nv;v=v<v0v1&O%887654321;%?4>;:1").
Proof. exact (art_amemset MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics art_L_tls art_L_ro art_L_cs). Qed.
#[using="Hwx Htp Hkey0 Htsd Hloff"] Theorem art_inst_memcpy : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "@&C&Q1&Q6vQC%211vQD&Q4'Nv;v=v<v0v1&O%887654321;%?4>;:1").
Proof. exact (art_amemcpy MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics art_L_tls art_L_ro art_L_cs). Qed.
#[using="Hwx Htp Hkey0 Htsd Hloff"] Theorem art_inst_memmove : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "@&D&Q1&Q6vQC%211vQD&Q4'Nv;v=v<v0v1&O%887654321;%?4>;:1").
Proof. exact (art_amemmove MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics art_L_tls art_L_ro art_L_cs). Qed.
#[using="Halloc Hwx STATIC Htp"] Theorem art_inst_malloc : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "@&B&Q1&Q6vQC%211vQD&Q4'Nv;v=v<v0v1&O%887654321;%?4>;:1").
Proof.
apply (art_wrap_malloc art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg art_L Halloc Hwx STATIC); try reflexivity.
- symmetry. exact Htp.
- exact art_L_statics.
- cbn. lia.
- cbn. lia.
- cbn. lia.
- exact art_fsinv_frame_law_proved.
- intros gfs FF LK M FS. exact (art_fsinv_in_proved rn gfs FF LK M FS).
Qed.
Section SE.
Local Abbreviation SEC_T_art_r1_1046 := (ltac2:(TCodec.tc2 tcn__JbtIfaceInst "Q0'Q3'N%211'2'4'7%2211%411'QEyR0%211'3y8%511%311p051&Q2vQCr3r2r1%55D4321&>&Q<+RQTHu1+4%5548321p071pF>1pDG1pBM1")) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_r1_1046) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_art_r1_1046) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_r1_1046) 2%nat 0%nat).
Lemma art_r1_1046 : ltac:(sec_stmt2 constr:(SEC_T_art_r1_1046) 3%nat 0%nat).
Proof using Type G LB M.
intros (_ & ST & _).
unfold art_rt_statics in ST. decompose [and] ST. assumption. Qed.
End SE.
#[using="Halloc Hwx STATIC Htp"] Theorem art_inst_aligned : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "@&@&Q1&Q6vQC%211vQD&Q4'Nv;v=v<v0v1&O%887654321;%?4>;:1").
Proof.
apply (art_wrap_aligned16 art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg art_L Halloc Hwx STATIC); try reflexivity.
- exact art_r1_1046.
- symmetry. exact Htp.
- exact art_L_statics.
- cbn. lia.
- cbn. lia.
- cbn. lia.
- exact art_fsinv_frame_law_proved.
- intros gfs FF LK M FS. exact (art_fsinv_in_proved rn gfs FF LK M FS).
Qed.
#[using="Htp Hkey0 Htsd Hloff"] Theorem art_inst_release : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "?&J&Q1&Q6vQC%211&Q4'Nv;v=v<v0v1&O%887654321:%>3=:1").
Proof. exact (art_law_release_frame MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl eq_refl eq_refl art_L_statics art_L_tls art_L_ro art_L_cs ltac:(intros a Z; cbn in Z; unfold art_ro in Z; lia)). Qed.
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff FREE SMALLOC"] Theorem art_inst_ok : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "A'K&Q1&Q6vQC%211&Q0vQD&Q4'Nv;v=v<v0v1&O%887654321<%@5?<;:1").
Proof.
constructor.
- exact art_inst_malloc.
- exact art_inst_aligned.
- exact FREE.
- exact SMALLOC.
- exact art_inst_release.
- exact (art_law_leak_frames MAPS0 RESV0 NOACC0 BASE BUDGET rn).
- exact art_inst_no_return.
- exact art_inst_memset.
- exact art_inst_memcpy.
- exact art_inst_memmove.
- exact (art_law_frame MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl eq_refl art_L_statics art_L_tls art_L_ro art_L_cs).
- exact (art_law_wf MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl eq_refl).
- exact (art_law_lazy MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl).
- exact (art_law_perm MAPS0 RESV0 NOACC0 BASE BUDGET rn).
- exact (art_law_statics MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl Htp Hkey0 Htsd Hloff).
- exact (art_law_flagptr MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl).
- exact (art_law_small_high MAPS0 RESV0 NOACC0 BASE BUDGET rn).
Qed.
#[using="Type"] Lemma art_L_img_low : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "6&Q>&G&Q1%211&?%5221").
Proof. cbn [art_L hl_img_hi]. unfold BIGSHADOW_LO. lia. Qed.
#[using="Type"] Lemma art_inst_flag_in_fs : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "?&Q;&Q1&Q6vQC%211&Q4'Nv;v=v<v0v1&O%887654321:%>3=:1").
Proof.
intros LB FF LK cr A M V F k rs fl (G & _ & FS & _) Hin CF Hfl.
destruct FS as (GEO & _ & _ & _ & _ & _ & _ & _ & FR & _).
destruct (FR (F, k, rs) ltac:(apply in_or_app; left; exact Hin)) as (K1 & (i & (Hi & A1) & C1) & _).
unfold ff_class, ff_addr in *. cbn [fst snd] in *.
pose proof (fs_flag_below_frames (ar_fs (rn_ar rn)) k i ltac:(lia) Hi) as B.
destruct GEO as (G1 & G2 & G3 & _ & (AM0 & _ & AM2) & _).
assert (W : word_to_le_bytes 8 (Z_to_bv 64 fl) = word_to_le_bytes 8 (Z_to_bv 64 (fs_flag (ar_fs (rn_ar rn)) k i))).
{ unfold cell_is in CF. unfold cell in C1. cbn [art_L hl_segs] in CF. rewrite CF in C1. congruence. }
assert (E : bv_unsigned (Z_to_bv 64 fl) mod 2 ^ (8 * Z.of_nat 8) = bv_unsigned (Z_to_bv 64 (fs_flag (ar_fs (rn_ar rn)) k i)) mod 2 ^ (8 * Z.of_nat 8)).
{ rewrite <- !bytes_le_N. rewrite W. reflexivity. }
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in E.
rewrite !art_u_lit in E by (unfold FS_BYTES in *; lia). rewrite !Z.mod_small in E by (unfold FS_BYTES in *; lia).
unfold FS_BYTES in *. lia.
Qed.
#[using="Htp Hkey0 Htsd Hloff"] Theorem art_inst_frame_ctr : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "?&L&Q1&Q6vQC%211&Q4'Nv;v=v<v0v1&O%887654321:%>3=:1").
Proof. exact (art_law_frame_ctr MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl eq_refl eq_refl art_L_statics art_L_tls art_L_ro art_L_cs Htp Hloff Htsd Hkey0 eq_refl). Qed.
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff FREE SMALLOC"] Theorem art_inst_strict_ok : ltac2:(TCodec.tc2 tcn__JbtIfaceInst "C'F&Q1&Q6vQC%211&Q0vQD&M&Q4'Nv;v=v<v0v1&O%887654321=%:11%B5A>=<1").
Proof. exact (strict_ok art_L (rn_ar rn) art_C scfg HI art_L_img_low art_inst_flag_in_fs art_inst_ok). Qed.
End Inst.
