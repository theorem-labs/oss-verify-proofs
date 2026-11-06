(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
HeapIface HeapIfaceA HeapIfaceANull IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ja0DrvEntry Ja0Drv_defs Ja0DrvLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DrvFreeNull () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "1O"; "1Some"; "1app"; "1bool"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"]; ["2eq"; "3add"; "4le"; "4lt"; "5map"; "6Z"; "0E"; "0E'"; "0HI"; "0K"; "0L"; "0LB"; "0LK"; "7mkCfg"; "8Model"; "8event"]; ["9bvmap"; "0M"; "0M'"; "0M0"; "0R"; "0R'"; ":mrestrict"; ";find_nz"; "<credit"; "<in_block"; "=ahid"; "=fframe"; "=model_rt"; ">dinv"; ">has_window"; ">sub_blockA"]; ["?IMG_CLIENT_A"; "?c_kept"; "?keep_allocA"; "@getr"; "@mkst"; "@seg_rom"; "Asrealizes"; "Bjunk_vals"; "Bsr_after_call_j"; "CEnv"; "Cenv"; "Cexpr"; "Ckentry"; "Cridx"; "Dknow_ok"; "Dregs_ok"]; ["Ekn_vars_lt"; "Esr_vars_lt"; "Evals_ev"; "Floaded_segments"; "GIn"; "Gincl"; "Hadd"; "Hle"; "Hlt"; "Hmodulo"; "Hopp"; "Hpow"; "0a"; "0ar"; "0b"; "0bls"]; ["0cr"; "0ebs"; "0fx"; "0hi"; "0i"; "0kn"; "0lo"; "0model"; "0model'"; "0nb"; "0ra"; "0scfg"; "0so"; "0sp0"; "0sr"; "IBV"]; ["IZ_to_bv"; "Ibv"; "Ibv_unsigned"; "0v"; "0vals"; "0vals'"; "0vbnd"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section FreeNull.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Hypothesis FNULL : afree_null_spec L ar scfg HI.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
Hypothesis DL : drv_layoutA L ar IL sp0.
Variable M0 : word -> option byte.
Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
#[local] Notation dinvA := (dinv ar HI sp0 M0).
Lemma afree_null_site : ltac2:(TCodec.tc2 tcn__Ja0DrvFreeNull "Z@'7'S1yR0%211%411'8y8%611%811p041'QK%;11'QL%=11&Q0y5%221=':%11;p0@1'N'<'E%2211%H11&Q;%J11&Q8%72G6%M11'O%O11!pV@21'QJ(QI&R2r@%211r?%5221&QOr1r=%33251&QN&R3r2&Q6&Q:r8r<%3221%521:%94871?'@'5&R1&6rC%22QI1rA%5221(=%93821&R0rD%92R01%3217%>3=16'Bu1rE%?2R61%4231rF(2%Q9221vRM%H3R<21&Q>%11?%K3J1C&QC(RO+2(>%33R821%52F1&S0&R6&S2%12RJ>%321QB%52RL1%Q83RL71'?&R7&R:&R;+F%22@1%411r>%7221z%9231%;231&R9+@%22R71%QH3RI16rG+:%N3S31L%Q0231%K2SB;%QN3SB21rH+4%Q43S91Q2%Q6231+V]k\0%Q22SI1%R53SI31rI+1%Q;3S@1Q9%Q=231%Q82SORJ%R;3SO21%Q22JRN&R8+R0%Q32QA1%32S21%Q8251%M2R<QD%RC3SD1Q1'Q=vR=vHvQ3rKrJ%6:54R33DKQ1R621%T11SL&Q7%12S5Q4(3%12T0S<%S03531&Cr3rQ4%S12TH1%4231&Q?vJrM%SL267%R62TO1%554F31SC%R3271p0=1pUDT?1pU:U11rQ5%S>2U51%A2@1%T623A%R@2U91%R;21SM%R=241p0G1pTNTI1pV8U;1(9%11TD%SA11&4rQ8&QGr4%211%53UF41%TF1T@%TH216%T22UIT=&ArQ:%T52UL1uQ0%4221%T;3UM61&QHrQ9&D%V51UG&QM&QA%443V421rQ;%TA2V81%93831r7%U53TO21r5r6%U0221%U2215&QBrQ1+TP0rQ0rO%554321D%U<4U;R071rQ6%R@:R?R>T=R=1QDR1;U9>&Q<%12Q8U;&R5%13V8QHU=%SO2T4UF+Q?%SO2T=1%RO2UI1%T4241%T<2W3UF%UK11rQ=%113%UB3VG31p061pTJVE1%T;2T3V2%S92V3S7%T>221&Q9rQ<%221V2%TI2W@RI%V<11rQ?%113%UO3W431p061p0:1pTJW31&R4(;%14W6W6S3V=&Q@%43W721%TN2R8V@%SL2VAS7%U1221rB%11ArQB%11C%V?3WD31p061p0:1pTJWC1pU8WD1pU>WE1'QFvRK(M&QDvRB%UH2X?S:&QE%11W5%554W=3U=1%721W:%:4W891SLp0<1p0O1p0Q>1p0QK1p0QN1p0R11p0R41p0R@1p0RM1tQ@WNS51tV<XMS81p4X:1pUBX?1pR6XA1pR<XE1+_SeL%V>2Y51%I5HRD1RBE%K21RB%N4WLM1VOp061p0SI1p0SM1p0T81p0TN1p0U61p0U91p0U@1p0UG1p0UO1p0V61p0V;1p0VH1p0W61p0W:1p0W@1p0WF1p0WL1p0X71p0XB1tQ>XMXG1pQDXO1pUFY;1pV>Y51pU0Y61pUJY>1p2Y=1pU2Y;1pQJY=1pQHY@1pU@YE1pR4YG1pR:YK1pU<YO1pUNZ21pU4Z51pV:Z;1").
Proof.
intros vals ebs sr kn R M model LB LK cr A so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
R2 Hso Hsoal R10 R4 R1 Hra Hra2 DI Hbl Hvb HK0 CONT.
set (FF := @nil fframe) in *.
pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
pose proof (dinv_stack_defined scfg L ar C HI HIok sp0 Hsp M0 M0_def _ _ _ _ _ _ DI) as Hdef.
pose proof Hsp as Hsp'. pose proof (dla_scr L ar IL sp0 DL) as (SC1 & SC2 & SC3).
pose proof (FNULL fx R M model LB FF LK cr A K) as MS.
rewrite (dla_segs L ar IL sp0 DL), (dla_free L ar IL sp0 DL), (dla_tp L ar IL sp0 DL) in MS. rewrite R1 in MS.
apply MS; clear MS; try assumption.
- apply ret_ok_even. rewrite u_small by lia. exact Hra2.
- rewrite R2, u_small by lia.
eapply (astack_ok_of_window L ar IL HI sp0 Hsp Hal DL vals ebs (ahid A model) M kn so); eauto; lia.
- intros R' M' model' A' HP HPRES HRT HINC HMI' HH'.
rewrite R2, u_small in HPRES by lia. destruct HPRES as (PR1 & PR2).
assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
assert (CLI : forall a, aclient L ar LB FF (bv_unsigned sp0 + so) 4096 a -> aclient L ar LB FF (bv_unsigned sp0 + so) (hl_scr_free L) a)
by (intros a; apply (aclient_scr_mono L ar sp0 Hsp); lia).
apply (CONT R' M' model' A' HL'); try assumption.
+ apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA sp0 Hsp R R' HP) c_kept_no0A).
+ unfold keep_allocA.
pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
(Env (vals_ev (vals ++ junk_vals R')) ebs)
(CPa L ar LB FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) 4096)
_ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
* eapply (regions_callA scfg L ar C IL HI HIok sp0 Hsp DL (vals ++ junk_vals R') ebs so 4096 bls vbnd LB LB LB FF FF LK LK cr cr A A' M M' model model');
[exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
-- intros a Ha. exact Ha.
-- intros a Ha; exact Ha.
-- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
-- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
* intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; [exact Ha | apply CLI; exact HC].
* intros a HS. unfold SCa in HS. unfold mrestrict.
rewrite (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH') by lia.
destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_free L)) as [Hlo|Hhi].
-- rewrite PR1; [apply (window_defined sp0 Hsp vals ebs (ahid A model) M kn HK Hiw P0); lia | lia |].
unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). lia.
-- apply PR2. lia.
+
apply (dinv_call scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LB LB LK LK cr cr A A' M M' model model' (bv_unsigned sp0 + so) (hl_scr_free L) DI ltac:(lia)); assumption.
+ intros a Ha. apply PR1; [lia|]. unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). lia.
+ intros a Ha Hb. apply PR1; [exact Ha | left; exact Hb].
+ intros lo hi a Hin' Ha. assert (0 <= a < 2 ^ 64).
{ destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3). lia. }
apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo L ar IL sp0 DL), (dla_img_hi L ar IL sp0 DL).
split; [destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3); lia | exact (dla_client L ar IL sp0 DL lo hi a Hin' Ha)].
Qed.
End FreeNull.
End FPX_1.
