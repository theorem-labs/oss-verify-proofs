(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare MemSplit AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
RefNodes RefMemcpyLib HeapIface HeapIfaceA IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ja0DrvEntry Ja0Drv_defs Ja0DrvLib
Ja0RegionPoisoned Ja0AsanMemcpy Ja0ReadIcpt Ja0DrvHIcpt Ja0DrvRead.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DrvHRead () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvHRead."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvRead."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1O"; "1Some"; "1app"; "1bool"; "1length"; "1list"; "1nat"; "1option"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2not"; "3add"]; ["4le"; "4lt"; "5map"; "6Z"; "0E"; "0E'"; "0HI"; "0K"; "0L"; "0LB"; "0LK"; "7Fs"; "8mkCfg"; "9FdDir"; "9FdEntry"; "9Model"]; ["9fd_lookup"; "9m_fds"; "9m_fs"; ":bvmap"; "0M"; "0M'"; "0M0"; "0R"; "0R'"; ";mrestrict"; "<find_nz"; "=credit"; ">ahid"; ">fframe"; "?ERRNO_A"; "?TP_A"]; ["?keep_readEA"; "@dinv"; "@has_window"; "@sub_blockA"; "ASTAGE"; "Bc_kept"; "Cgetr"; "Cmkst"; "Cseg_rom"; "DTSet"; "Esrealizes"; "Fwseg_ok"; "Gjunk_vals"; "Gsr_after_call_j"; "HEnv"; "Henv"]; ["Hexpr"; "Hkentry"; "Hridx"; "Iknow_ok"; "Iregs_ok"; "Jkn_vars_lt"; "Jsr_vars_lt"; "Jvals_ev"; "Kloaded_segments"; "Ladd"; "Lle"; "Llt"; "Lmodulo"; "Lopp"; "Lpow"; "Lsub"]; ["0a"; "0ar"; "0b"; "0bls"; "0cnt"; "0cr"; "0ebs"; "0fx"; "0i"; "0kn"; "0model"; "0model'"; "0nb"; "0ra"; "0scfg"; "0so"]; ["0sp0"; "0sr"; "MBV"; "MZ_to_bv"; "Mbv"; "Mbv_unsigned"; "0v"; "0vals"; "0vals'"; "0vbnd"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition TP_A : Z := 0x66ed80.
Definition ERRNO_A : Z := 0x66ecdc.
Definition IMG_NOERRNO : list (Z * Z) :=
[(0x10000, 0x134000); (0x136d58, 0x137640); (0x65d350, 0x66ecdc); (0x66ece0, 0x66ed28); (0x66ed30, 0x66ed78); (0x66ed94, 0x66eda8); (0x66edb0, 0x690238);
(0x690240, 0x691000)].
Definition keep_readEA (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
kn_keep 0 so 2200 bls vbnd [] IMG_NOERRNO IMG_RW_A kn.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvReadDir.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis DL : drv_layoutA L ar IL sp0.
Hypothesis Hcells : incl RD_CELLS (asc_cells C).
Variable M0 : word -> option byte.
#[local] Abbreviation dinvA := (dinv ar HI sp0 M0).
Lemma wseg_errno : ltac2:(TCodec.tc2 tcn__Ja0DrvHRead "<'='4&QK&R8&S3yR0+V]kVL%3221u4%73621(:%;3:21").
Proof. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_aread_dir_site := (ltac2:(TCodec.tc2 tcn__Ja0DrvHRead "[9'6'S4yR0%211%411'7y8%611%811p041'R0%;11'R1%=11&Q3y5%221='8%11;p0@1'O'9'C%2211%H11&Q=%J11&Q;%72G6%M11&QI'QO(QN&R7rA%211r@%5221&R4r1r>%33251&R3&R8r2&Q9&Q<r9r=%3221%521:%94871?'='4&R6&5rD%22QF1rB%5221(:%93821&R5rE%92QM1%3217%>3=16'@u1rF%?2R31%4231rG(1%Q9221vS0%H3R921&QB%11?%K3J1C&QF(S2+2(;%33R521%52F1&S3&R9&S5%12RG>%321Q:%52RI1%Q83RI71'<&R:&R=&R>+F%22@1%411%621QLz%82QN1%:231&R<r?+@%3221%QH3RF17rH+4%N3S01L%Q0231&Q?%L2S@1%QO3S@31rI+:%Q53S71Q3%Q7231+3%Q32SG1%R63SG31rJ+;%Q<3S>1Q:%Q>231&QD%Q:2SN1%R=3SN31rK+<%QC3SE1QA%QE231%Q@2T4R>%RC3T421+1%Q;21R:+RPP0%Q=2R<1%Q?231rM%QM3SO6QK%QO221%QJ2T>RF%RM3T>21rC%QE2Q>1&R;+R0%QF2R41%3251%QK251%QA2S1R7%S63T41QE'QAvRAvFvQ6rLrOrN%7:65RG4E3Q0Q721'N%TC11&Q0&Q1%117%321Q?(2(M%2281%SH3841%TL1TG&Q:%12T3Q=%72TJT9%SM3421&Ar3rQ9%SN2UB1%4231&QCvHrQ2%TI267%S32UI1%554Q031T@%S0271p0=1pUJU91pUBUK1rQ:%T;2UO1%A2@1%U323A%S=2V31%S821TJ%S:241p0G1pU6UC1pV>V51&3rQ;&QL%11K%43V<31%U?1U9%UA215%TK2V?U6&?rQ=%TN2VB1uQ0%4221%U43VC61rQ>%U32VG1u:%9221%UL2Q:1+_oooooooooooO%T92VM1%U<3VM31&QM&B%W21VD&R2&QE%443W121rQ?%UA2W51%83E31r7%V53QH21r4rQ6r6%V1221%V3216&Q@rQ4rQ3%3421QKQ0%V;4V:951rQ8rQ7r8%RN:RMRLU>RKQHR5321?%W52WGRG%WK11%RF14rQ<%RH11%V;3431&K&Q2%11VC%21Q?%V@3421%U72U0VN%SB2VOS@%U:221&>&R?%UC2UAR9+RTH%3221%U?21W1%SJ2W24%UB221%811&Q>%UD21RO%UL22U5%T02S11%UH231%>11%V12XEQ;%U?11rQC%113%W73X931p061p0=1p0G1pU2X91'QJvRN(L&QGvRG%V?2Y3QHr<&QH%11WM%655WI431r;%9221rQ5%=4X2<21p0?1p0Q;1p0QA1p0QH1p0QM1p0R81p0RD1p0RM1tQ<XGS51tVBYCS81pUHY41pR<Y61pRBY:1+\ZaH%W62YJ1%J5IA1R;E%L21R;%O4XDN1V;p061p0SG1p0T21p0TG1p0U21p0U;1p0U>1p0UF1p0UL1p0V21p0V91p0VA1p0VI1p0W11p0W71p0WC1p0X11p0X51p0X;1p0XA1p0XG1p0Y21p0Y=1tQ:YHYB1pQ@YJ1pULZ31pVDYM1pU8YN1pV0Z61pU:Z71p2Z61pU<Z41pQFZ61pQDZ91pUFZ>1pR:Z@1pR@ZD1pUDZH1pV4ZK1pU>ZN1pV@[41")) (only parsing).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 0%nat 0%nat).
Variable ebs : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 1%nat 0%nat).
Variable sr : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 2%nat 0%nat).
Variable kn : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 3%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 5%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 6%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 7%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 8%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 9%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 10%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 11%nat 0%nat).
Variable so : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 12%nat 0%nat).
Variable bls : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 13%nat 0%nat).
Variable vbnd : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 14%nat 0%nat).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 15%nat 0%nat).
Variable K : ltac:(sec_ty2 constr:(SEC_T_aread_dir_site) 16%nat 0%nat).
Lemma aread_dir_site : ltac:(sec_stmt2 constr:(SEC_T_aread_dir_site) 17%nat 0%nat).
Proof.
intros E HR HK Hsv Hkv HL1 P0 Hiw
R2 Hso Hsoal R4 R10 R11 R12 Hcnt R1 Hra Hra2 DI Hfd Hbl Hvb CONT.
pose proof Hsp as Hsp'. unfold STAGE, TP_A, ERRNO_A in *.
set (s := bv_unsigned sp0 + so) in *. set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
destruct (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ DI) as (HOFF & HLC & HAWF & _ & _). fold H in HOFF, HLC.
assert (Hs : 0x1000000 <= s - 2200 /\ s < 2 ^ 64) by (unfold s; lia).
assert (WOK : store_ok ASEGS MV (Z_to_bv 64 (s - 2200)) 2200 = true).
{ replace (s - 2200) with (bv_unsigned sp0 + (so - 2200)) by (unfold s; ring).
apply (window_store_ok sp0 vals ebs MV kn (so - 2200) 2200 HK Hiw P0); lia. }
assert (VIS : forall a, 0 <= a < 2 ^ 64 -> (a < 0x691000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LB a) -> H (Z_to_bv 64 a) = false)
by (intros a Ha Hc; exact (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH Ha Hc)).
assert (VFR : forall x : word, s - 2200 <= bv_unsigned x < s -> H x = false).
{ intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply VIS; unfold s in Hx; lia. }
assert (VST : forall x : word, Ja0DrvRead.STAGE <= bv_unsigned x < Ja0DrvRead.STAGE + 65536 -> H x = false).
{ intros x Hx. unfold Ja0DrvRead.STAGE in Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply VIS; lia. }
assert (CV : forall a n v, In (a, n, v) RD_CELLS ->
rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v))).
{ intros a n v Hin. unfold MV, H. rewrite rdn_mrestrict_eq; [exact (rd_cell scfg L ar C IL HI HIok sp0 DL Hcells _ _ _ _ _ _ _ a n v HH Hin)|].
apply (avoid_img scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ _ a (Z.to_nat n) HH);
unfold RD_CELLS in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]); destruct Hin. }
destruct (wrap_read_pre_run MV (seg_rom ASEGS) (Z_to_bv 64 s) (Z_to_bv 64 ra) s 3 0x65d350 cnt
ltac:(apply u_small; lia) Hs WOK ltac:(lia) ltac:(lia) ltac:(lia)) with (regs := R)
as (Ra & RUN1 & A17 & A10 & A11 & A12 & _ & _ & _ & _ & A2 & A1 & A8 & A9 & A18 & A19 & A20 & KB1).
1: { rewrite <- (w_lit 0x13b9d8 (0x13b9d8%bv : word) eq_refl). exact (CV 0x13b9d8 1 1 ltac:(unfold RD_CELLS; cbn [In]; tauto)). }
1: { rewrite <- (w_lit 0x134490 (0x134490%bv : word) eq_refl). exact (CV 0x134490 8 0x12b3b0 ltac:(unfold RD_CELLS; cbn [In]; tauto)). }
1: exact R10. 1: exact R11. 1: exact R12. 1: exact R2. 1: exact R1.
rewrite (w_lit 0x62a38 (0x62a38%bv : word) eq_refl).
apply (rz_msteps_lz ASEGS scfg H A R _ M Ra _ _ model K HOFF asegs_wx HLC HAWF HMI Hh RUN1).
intros model1 MI1 SBM1 EQV1.
destruct (sbm_fds _ _ SBM1) as (F1 & F2).
eapply (rz_read_dir_cnt_lz ASEGS scfg Ra _ _ model1 ECALLW (Z_to_bv 64 3) cnt K); try apply is_ecall_ECALLW.
- vm_compute. reflexivity.
- rewrite (sbm_halted_eq _ _ SBM1). exact Hh.
- exact A17.
- exact A10.
- rewrite u_small by lia. lia.
- rewrite F1. exact Hfd.
- exact A12.
- lia.
- rewrite A11, u_small by lia. unfold TASK_SIZE. lia.
- replace (v_addi (0x125984%bv : word) 4) with (0x125988%bv : word) by (apply bv_eq; reflexivity).
set (raw := Z_to_bv 64 ra) in *.
set (R2' := regupd Ra 10 (errno_ret EISDIR)).
assert (Hbs : Z.of_nat (length (@nil byte)) <= 65536) by (cbn; lia).
change (munrestrict H M (RDA MV raw s R)) with (rd_M2 H M s raw R []).
set (M2 := rd_M2 H M s raw R []).
set (MV2 := rd_MV2 H M s raw R []).
assert (EL1 : m_vm_lazy model1 = m_vm_lazy model) by exact (sbm_lazy_eq _ _ SBM1).
assert (EH1 : ahid A model1 = H) by (unfold H; apply ahid_same_lazy; exact EL1).
assert (Hh1 : m_halted model1 = None) by (rewrite (sbm_halted_eq _ _ SBM1); exact Hh).
pose proof (RDA_slots (mrestrict H M) raw s Hs R) as (SL1 & SL2 & SL3 & SL4 & SL5 & SL6 & SL7).
assert (T1 : rdn ASEGS MV2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 raw)) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 8) by lia; exact SL1).
assert (T2 : rdn ASEGS MV2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 16) by lia; exact SL2).
assert (T3 : rdn ASEGS MV2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr R 9))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 24) by lia; exact SL3).
assert (T4 : rdn ASEGS MV2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr R 18))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 32) by lia; exact SL4).
assert (T5 : rdn ASEGS MV2 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr R 19))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 40) by lia; exact SL5).
assert (T6 : rdn ASEGS MV2 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr R 20))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 48) by lia; exact SL6).
assert (T7 : rdn ASEGS MV2 (Z_to_bv 64 (s - 2136)) 8 = Some (word_to_le_bytes 8 (0x64c64%bv : word))) by (unfold MV2, rd_MV2; rewrite (rd_MV2_slot H M s raw R [] Hs Hbs VFR 2136) by lia; exact SL7).
assert (Hret : ret_ok raw) by (apply ret_ok_even; unfold raw; rewrite u_small by lia; exact Hra2).
assert (Q4 : getr R2' 4 = Z_to_bv 64 0x66ed80).
{ unfold R2'. rewrite getr_other by discriminate. rewrite (KB1 4%bv); [exact R4 | cbv; tauto | cbv; intuition discriminate]. }
destruct (read_icpt_post_err_run (seg_rom ASEGS) raw s 0x66ed80 Hs ltac:(lia) Hret R R2' MV2) as (R3 & RUN3 & O10 & O2 & O1 & O8 & O9 & O18 & O19 & O20 & KB3).
1: { unfold R2'. rewrite getr_same by discriminate. apply bv_eq. vm_compute. reflexivity. }
1: { unfold R2'. rewrite getr_other by discriminate. exact A2. }
1: { unfold R2'. rewrite getr_other by discriminate. exact A1. }
1: { unfold R2'. rewrite getr_other by discriminate. exact A8. }
1: { unfold R2'. rewrite getr_other by discriminate. exact A20. }
1: exact Q4.
1: { apply (store_ok_mono ASEGS _ (mrestrict H M) MV2); [exact (rd_MV2_grows H M s raw R []) | exact WOK]. }
1: { apply (store_ok_window ASEGS _ (Z_to_bv 64 0x66ecdc) (Z_to_bv 64 (0x66ed80 - 164)) 4%nat 4%nat 0x66ecdc 0x66ece0);
first [exact wseg_errno | reflexivity | lia | (rewrite u_small by lia; lia)]. }
1: exact T7. 1: exact T1. 1: exact T2. 1: exact T3. 1: exact T4. 1: exact T5. 1: exact T6.
set (M3' := RDE s 0x66ed80 MV2) in *.
assert (MI1' : MInv A model1) by exact MI1.
apply (rz_msteps_lz ASEGS scfg H A R2' _ M2 R3 _ M3' model1 K HOFF asegs_wx ltac:(rewrite EL1; exact HLC) HAWF MI1' Hh1 RUN3).
intros model3 MI3 SBM3 EQV3.
set (M3 := munrestrict H M2 M3') in *.
assert (OUT3 : forall x : word, ~ (s - 2200 <= bv_unsigned x < s) -> ~ (0x66ecdc <= bv_unsigned x < 0x66ece0) -> M3' x = MV2 x).
{ intros x N1 N2. unfold M3'. apply RDE_out; lia. }
assert (GR3 : mem_grows MV2 M3') by (unfold M3'; apply RDE_grows).
assert (FRM : forall a, 0 <= a < 2 ^ 64 -> ~ (s - 2200 <= a < s) -> ~ (0x66ecdc <= a < 0x66ecdc + 4) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N1 N2. unfold M3, munrestrict.
assert (E2 : M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ unfold M2, rd_M2. cbn [wbytes]. unfold munrestrict. destruct (H (Z_to_bv 64 a)) eqn:Hx; [reflexivity|].
rewrite (RDA_out (mrestrict H M) raw s Hs R (Z_to_bv 64 a)) by (rewrite u_small by lia; lia). unfold mrestrict. rewrite Hx. reflexivity. }
destruct (H (Z_to_bv 64 a)) eqn:Hx; [exact E2|].
rewrite OUT3 by (rewrite u_small by lia; lia). unfold MV2, rd_MV2, mrestrict. rewrite Hx. exact E2. }
assert (GRW : forall x : word, M x <> None -> M3 x <> None).
{ intros x Hd. unfold M3, munrestrict.
assert (E2 : M2 x <> None) by (unfold M2; apply (rd_M2_grows H M s raw R []); exact Hd).
destruct (H x) eqn:Hx; [exact E2|]. apply GR3. unfold MV2, rd_MV2, mrestrict. rewrite Hx. exact E2. }
assert (EV3 : vml_of model3 = vml_of model) by (rewrite (sbm_vml _ _ SBM3); exact (sbm_vml _ _ SBM1)).
assert (Hh3 : m_halted model3 = None) by (rewrite (sbm_halted_eq _ _ SBM3); exact Hh1).
assert (EH3 : ahid A model3 = H) by (rewrite (ahid_sbm A model1 model3 SBM3); exact EH1).
assert (DI3 : dinvA LB LK cr A M3 model3).
{ apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M M3 model model3 DI); [ | exact GRW | exact EV3 | exact MI3 | exact Hh3].
intros a Ha NC. apply FRM; [exact Ha | |]; intros Hr; apply NC; unfold CWA.
- right. left. unfold s in Hr. lia.
- right. right. exists 0x65d350, 0x66ed28. split; [unfold IMG_W_A; cbn [In]; tauto | lia]. }
assert (HL' : length (vals ++ junk_vals R3) = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (P0' : vals_ev (vals ++ junk_vals R3) 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
assert (KEPT : forall r : reg, In r c_kept -> getr R3 r = getr R r).
{ assert (KK : forall r : reg, In r callee_saved -> ~ In r Ja0ReadIcpt.RIPL -> getr R3 r = getr R r).
{ intros r Hr Hn'. rewrite (KB3 r Hr Hn'). unfold R2'. rewrite getr_other; [exact (KB1 r Hr Hn')|].
intros ->. clear - Hr. cbv in Hr. intuition discriminate. }
intros r Hr. unfold c_kept in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
- rewrite O2, R2. reflexivity.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate.
- exact O8.
- exact O9.
- exact O18.
- exact O19.
- exact O20.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate.
- apply KK; cbv; intuition discriminate. }
apply (CONT R3 M3 model3 HL').
+ rewrite (vals_ev_junkA vals R3 10) by lia. exact O10.
+ exact (regs_after_keeps vals ebs sr R R3 c_kept Hsv HR KEPT c_kept_no0A).
+ rewrite EH3. unfold keep_readEA.
pose proof (env_app_know ASEGS vals (junk_vals R3) ebs _ kn Hkv HK) as HK1.
refine (know_keep_sound ASEGS 0 so 2200 bls vbnd [] IMG_NOERRNO IMG_RW_A
(Env (vals_ev (vals ++ junk_vals R3)) ebs)
(fun a => H (Z_to_bv 64 a) = false /\ ~ (s - 2200 <= a < s) /\ ~ (0x66ecdc <= a < 0x66ecdc + 4))
(fun a => s - 2200 <= a < s)
_ MV (mrestrict H M3) _ _ kn HK1).
* constructor; cbn [ev]; rewrite ?P0'.
-- lia.
-- lia.
-- intros z Hz Hnot. split; [apply VIS; lia|]. unfold s. split; lia.
-- intros z Hz. right. unfold s. lia.
-- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & SBk). rewrite vals_ev_app_l by exact Hi32.
pose proof (sub_blockA_hz L ar IL sp0 DL _ _ _ SBk) as (Z1 & Z2 & Z3).
destruct SBk as (cap & Hnb & Hin & HB).
split; [lia|]. intros z Hz. split; [|unfold s; split; lia].
apply VIS; [lia|]. right. right. exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin | cbn [fst snd]; lia].
-- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
-- intros i [].
-- intros lo hi Hin. unfold IMG_NOERRNO in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; (split; [apply VIS; lia | unfold s; split; lia])|]).
destruct Hin.
-- intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
intros Mx d m Hd Hm.
apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x65d350) (Z_to_bv 64 d) 65536%nat m 0x65d350 0x66d350);
first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
* intros a Ha (V1 & N1 & N2). unfold MV, mrestrict. rewrite V1. apply FRM; assumption.
* intros a Ha. unfold mrestrict. rewrite (VFR (Z_to_bv 64 a)) by (rewrite u_small by (unfold s in Ha; lia); exact Ha).
apply GRW. apply (window_defined sp0 Hsp vals ebs H M kn HK Hiw P0). unfold s in Ha. lia.
+ exact DI3.
+ rewrite (proj1 (sbm_fds _ _ SBM3)). exact F1.
+ rewrite (proj2 (sbm_fds _ _ SBM3)). exact F2.
+ exact FRM.
Qed.
End SE.
End DrvReadDir.
End FPX_1.
