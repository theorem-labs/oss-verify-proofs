(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare
SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 RefMemcpyLib
HeapIface DrvKit Ju0MainEntry Ju0Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0DrvLib () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Decimal."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Number."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0DrvLib.FPX_1.DrvLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2D0"]; ["2D1"; "2D2"; "2D4"; "2D5"; "2D6"; "2D7"; "2D8"; "2D9"; "2Nil"; "3False"; "3I"; "3True"; "3and"; "3eq"; "3ex"; "3not"]; ["4add"; "4of_num_uint"; "5UIntDecimal"; "6le"; "6lt"; "7map"; "8Z"; "0E"; "0E'"; "0HI"; "0K"; "0L"; "0LB"; "9store_ok"; ":mkCfg"; ";Model"]; [";VmMaps"; ";event"; ";m_halted"; ";m_vm_lazy"; ";m_vm_materialized"; ";m_vmmaps"; "<bvmap"; "0M"; "0M'"; "0R"; "0R'"; "=wbytes"; ">find_nz"; ">kentry_eqb"; ">kn_keep_g"; ">log_in_b"]; [">regions_ok"; "?block_range"; "?blocks_apart"; "?credit"; "?credit_ok"; "?debit"; "?defined"; "?hi_heap"; "?in_block"; "?lb_remove"; "?model_but_vm"; "?regs_preserved"; "?stack_ok"; "@CPm"; "@CPout"; "@CPstk"]; ["@CW"; "@IMG_W"; "@SCm"; "@has_window"; "@hz"; "@sub_block"; "AIMG_CLIENT"; "AIMG_RW"; "Ac_kept"; "Akeep_alloc"; "Akn_blk"; "Bgetr"; "Bmkst"; "Brdn"; "Bseg_rom"; "Csrealizes"]; ["Dwseg_ok"; "Ejunk_vals"; "Esr_after_call_j"; "FEVar"; "FEnv"; "FKWr"; "FSA"; "Fenv"; "Fexpr"; "Fkentry"; "Fridx"; "Fsentry"; "Gknow_ok"; "Gmem_denot"; "Gregs_ok"; "Hkn_vars_lt"]; ["Hsr_vars_lt"; "Hvals_ev"; "Iloaded_segments"; "JIn"; "Jexistsb"; "Jnth_error"; "Kadd"; "Kle"; "Klt"; "Kmodulo"; "Kof_nat"; "Kopp"; "Kpow"; "0VM"; "0a"; "0b"]; ["0bls"; "0bs"; "0cr"; "0ebs"; "0fx"; "0i"; "0k"; "0kn"; "0log"; "0m"; "0model"; "0model'"; "0n"; "0nb"; "0r"; "0ra"]; ["0scfg"; "0so"; "0sp0"; "0sr"; "LBV"; "LZ_to_bv"; "Lbv"; "Lbv_unsigned"; "0v"; "0vals"; "0vals'"; "0vbnd"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Record drv_layout (L : heap_layout) (sp0 : word) : Prop := DRV_LAYOUT {
dl_segs : hl_segs L = RSEGS;
dl_malloc : hl_malloc L = 0x9bb08;
dl_free : hl_free L = 0x9b9c8;
dl_tp : hl_tp L = 0xc8cb0;
dl_img_lo : hl_img_lo L = 0x10000;
dl_img_hi : hl_img_hi L = 0xea000;
dl_static : forall a, hl_alloc_static L a -> 0xe90b8 <= a < 0xe9460;
dl_ro : forall a, hl_alloc_ro L a -> (0x10000 <= a < 0xb6000) \/ (0xe8f20 <= a < 0xe8f28) \/ (0xe8f40 <= a < 0xe90b8) \/ (0xe9460 <= a < 0xe9468) \/ (0xe98a4 <= a < 0xe98a8) \/ bv_unsigned sp0 <= a;
dl_errno : hl_errno L = 0xc8c0c;
dl_sptop : hl_sptop L = bv_unsigned sp0;
dl_stack : 0 <= hl_stack L <= 16384;
dl_k : 0 <= hl_k_per_malloc L;
dl_b : 0 <= hl_b_overhead L
}.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvLayout.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L scfg HI.
Variable sp0 : word.
Hypothesis Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
Hypothesis DL : drv_layout L sp0.
Lemma wseg_ac5b0 : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "J'M'5&S0&SB&TEyR0+fPP0%3221&Q1(Q2(A(B(C(E(D(H%211%411%611%811%:11%<11%>11%E3D@1(>%I3H21").
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_5f000 : OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim.wseg_ok Ubsan.M.loaded_segments (Z_to_bv 64 0xb6000) 212992 = true.
Proof. vm_compute. reflexivity. Qed.
Definition CPm (LB : list (Z * Z)) (sp : Z) (a : Z) : Prop := client_addr L LB sp (hl_stack L) a /\ ~ in_errno L a.
Definition SCm (sp : Z) (a : Z) : Prop := sp - hl_stack L <= a < sp.
Definition sub_block (LB : list (Z * Z)) (A nb : Z) : Prop :=
exists cap, 0 < nb <= cap /\ In (A, cap) LB /\ block_range L A cap.
Definition hz (A n : Z) : Prop := 4096 <= A /\ (A + n <= 0x10000 \/ 0xea000 <= A) /\ A + n <= bv_unsigned sp0 - 8388608.
Lemma hz_of_block_range : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "<'Q6&R1vQ;r2r1%43321&RDr3%2215p041pXJ:1p2;1").
Proof.
clear Hsp Hal. intros A n (B1 & B2 & B3 & B4 & B5). pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
pose proof (dl_sptop L sp0 DL) as TOP. unfold hz. rewrite IL, IH in B2. rewrite TOP in B5. repeat split; try lia.
Qed.
Lemma hz_sub : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "I'Q6&RDr4r3%3221&SGr5%2214z%4216&SF%1259r7r6%4221%:241%?23:p021p091p0<1p0@1pXDE1pWNF1pXJG1p2H1").
Proof. clear Hsp Hal. intros A n a m (H1 & H2 & H3) Ha Hm Ham. unfold hz. lia. Qed.
Lemma sub_block_hz : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "@'8'='Q6%2211%411&REr3r2r1%43321&RD%1254p031pXL;1p2<1pRJ;1").
Proof.
clear Hsp Hal. intros LB A nb (cap & Hnb & _ & HB). apply hz_of_block_range in HB. eapply hz_sub; [exact HB | lia | lia | lia].
Qed.
Section SE.
Local Abbreviation SEC_T_regions_alloc := (ltac2:(TCodec.tc2 tcn__Ju0DrvLib "SD'8'TFyR0%211%411'9y8%611%811p041'Q6'=%1272%=11%3244%?11'S7(S4&SAr6%211r5%5221'Mr7(2%8221vTB%53I21'L&SG&SK&SL+2+F%3221%511%721Bz%92D1%;231';%11Q0&QLr2r8%3221(3r1%22Q71%K3841&RE&TGr<r3%Q5221%42QF1%63Q11=p081pXLQA1pX<QG1r=%Q<218%;2QM1%Q221Dp0?1pX0QH1pYBQN1&SC(6u3u4(:%11R4%53R531%63R651%83R7L1%I2R;QB%QL2AQ2%K2R=1%QB231&SF+D%QC2QB1%3251+R0%QF2QE1%QI231%QK281p0=1pX<RE1'R0&SBr:+`P0r9&RF&RG&R=%B2F6%22R<1&RB%113%<<;R>:98QJL76RD31p0>1p0Q61p0Q>1p0R31p0R@1tR@RMRG1pRJRO1pYHS21pX2S31pY4S71pX8S91pYDS?1")) (only parsing).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_regions_alloc) 0%nat 0%nat).
Variable ebs : ltac:(sec_ty2 constr:(SEC_T_regions_alloc) 1%nat 0%nat).
Variable so : ltac:(sec_ty2 constr:(SEC_T_regions_alloc) 2%nat 0%nat).
Variable bls : ltac:(sec_ty2 constr:(SEC_T_regions_alloc) 3%nat 0%nat).
Variable vbnd : ltac:(sec_ty2 constr:(SEC_T_regions_alloc) 4%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_regions_alloc) 5%nat 0%nat).
Lemma regions_alloc : ltac:(sec_stmt2 constr:(SEC_T_regions_alloc) 6%nat 0%nat).
Proof.
intros E P0 Hso Hbl Hvb Hhi.
pose proof (dl_stack L sp0 DL) as ST. pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
pose proof (dl_errno L sp0 DL) as ER. pose proof (dl_sptop L sp0 DL) as TOP.
assert (NE : forall a, 0xc8c10 <= a \/ a < 0xc8c0c -> ~ in_errno L a) by (intros a Ha; unfold in_errno; rewrite ER; lia).
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CPm, client_addr. split; [right; left; rewrite TOP; lia | apply NE; lia].
- intros z Hz. destruct (Z.lt_ge_cases (bv_unsigned sp0 + z) (bv_unsigned sp0 + so - hl_stack L)) as [A|A].
+ left. unfold CPm, client_addr. split; [right; left; rewrite TOP; lia | apply NE; lia].
+ right. unfold SCm. lia.
- intros i nb Hf. pose proof (sub_block_hz _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). pose proof (hz_of_block_range _ _ HB) as (Y1 & Y2 & Y3).
split; [lia|].
intros z Hz. unfold CPm, client_addr.
split; [left; exists (bv_unsigned (vals_ev vals i), cap); split; [exact Hin|]; cbn [fst snd]; lia | apply NE; lia].
- exact Hvb.
- intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
intros z Hz. unfold CPm, client_addr. split; [right; left; rewrite TOP; lia | apply NE; lia].
- intros lo hi Hin. unfold IMG_CLIENT in Hin.
destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]);
intros a Ha; unfold CPm, client_addr; (split; [| apply NE; lia]); right; right; rewrite IL, IH; (split; [lia|]);
intros Hs; apply (dl_static L sp0 DL) in Hs; lia.
- intros lo hi Hin. unfold IMG_RW in Hin.
destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb0000) _ 24576%nat m 0xb0000 0xb6000);
[reflexivity | reflexivity | lia | exact wseg_ac5b0 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb6000) _ 212992%nat m 0xb6000 0xea000);
[reflexivity | reflexivity | lia | exact wseg_5f000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
End SE.
Lemma regs_preserved_kept : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "J&QFy5'TFyR0%211%5241&R;r2r1%3221%819&SC&RH%23351'M&RKr4%221:r5%421<%63@31p081pXN<1p0>1pSFC1pSDD1").
Proof.
intros R R' HP r Hr. apply HP. unfold c_kept in Hr. unfold callee_saved_idx.
repeat (destruct Hr as [<-|Hr]; [cbn; tauto|]). destruct Hr.
Qed.
Lemma c_kept_no0 : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "=&O&SC'TFy5%211(TDz(J%33521/015&RH%:3721%<11").
Proof. unfold c_kept. intros H. repeat (destruct H as [H|H]; [discriminate|]). exact H. Qed.
Lemma has_entry_nth : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "M'8'S9%211'M'5&SD&QMr1%211r2%53921(>%93821'N'9';%11?&SEr4%23B1<(3r3%22E1%D3741qX<:1%<2;1p0>1pRFJ1pX@J1").
Proof.
intros kn K H. apply existsb_exists in H as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'.
apply In_nth_error in Hin. exact Hin.
Qed.
Lemma block_store_ok : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "RH'8'TFyR0%211%411'9y8%611%811p041';%114p091'S9%>11'Q6'S7(S4&SAr9%211r8%5221&S<&SBr1r7%443261'M'5&SD&QM(S5(S6(S3%119z%4221r6%7221%911%;3L1D(>%?3>21r<%K21H&TE%12Q=9%D3Q=31&SG%12>H&SH&SL+2+R0%3221%52Q31%82EQ4&SF&SJ%11Q7%32Q:1r;%>221&Q=r?r:%9251%F2R21%54Q=41QB%Q:3Q91Lp081p0?1p0A1p0H1p0K1p0Q11p0QB1tR@QNQH1pXDR:1pX>R11p2R21pXJR31pYBR>1pX@R61pS@R91pX8R=1pYDRC1").
Proof.
intros vals ebs M kn v n A k m E HK Hhas Pv HA HAn Hk Hm.
destruct (has_entry_nth kn _ Hhas) as [i Hi].
pose proof (kwr_store_ok RSEGS E M kn i (EVar v) 0 n k m HK Hi Hk Hm) as W.
unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite Pv in W. unfold v_addi in W.
rewrite u_small in W by lia. exact W.
Qed.
Definition has_window (kn : list kentry) : bool := existsb (kentry_eqb (KWr (SA (EVar 0) (-8388608)) 8388608)) kn.
Lemma has_window_nth : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "Q1'8'S9%211'M'5&RCr1%211(>%63521'N'9';%11<&SEr3%23?1:(3(S5(S6(S3(2%211-XPPP0%5221+XPPP0%8221%:2J1%I3?<1qX<B1%D2C1p0F1pX@N1").
Proof.
intros kn H. unfold has_window in H. apply existsb_exists in H as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
apply In_nth_error in Hin. exact Hin.
Qed.
Lemma stack_ok_of_window : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "R<'8'TFyR0%211%411'9y8%611%811p041';%114p091'S9%>11'Q6'S7(S4&SAr5%211r4%5221&S<&SBr1r3%443261'M'5&RC%11:(>%53421r8(2%B221vTB%:3Q321'L&SG&SK&SL+2+F%3221%511%721Lz%92N1%;231&SIr6+@%3221%K3Q817&R<vQ;r9&SF&TG%12QKHr7%4221%83761p0:1p0@1p0M1p0Q31p0Q:1tR@QFQ@1pY4QH1pX@QJ1pS@QM1pX8R11pYDR71").
Proof.
intros vals ebs M kn so E HK Hw P0 Hso Hsoal. destruct (has_window_nth kn Hw) as [i Hn]. pose proof (dl_stack L sp0 DL) as ST.
pose proof Hsp as Hsp'. pose proof Hal as Hal'. pose proof (dl_sptop L sp0 DL) as TOP.
unfold stack_ok. rewrite TOP. split; [|split; [lia|split; [lia|split; [lia|]]]].
{ rewrite Z.add_mod, Hal, Hsoal by lia. reflexivity. }
intros d m Hd Hm.
pose proof (kwr_store_ok RSEGS E M kn i (EVar 0) (-8388608) 8388608 (so - hl_stack L + d) m HK Hn ltac:(lia) ltac:(lia)) as W.
unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W.
rewrite (dl_segs L sp0 DL).
replace (bv_unsigned sp0 + so - hl_stack L + d) with (bv_unsigned sp0 + (so - hl_stack L + d)) by lia. exact W.
Qed.
Lemma kn_blk_ok : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "QH'8'TFyR0%211%411'9y8%611%811p041';%114p091'Q6'S7(S4&SAr6%211r5%5221'Mr7r4%8221&TEr2%22I1%73I41r8(2%?221vTB%<3N21&R1vQ;%231=A&R6%139CE&S<&SBr9&RJ%12>E%544I31p071p0:1p0>1p0D1tR@Q3M1p2Q51pXJQ61pYBQ?1pSBQ91pX8Q=1pYDQC1").
Proof.
intros vals ebs M' v n A E Pv P0 HBR Hdef. pose proof HBR as (_ & _ & B2 & B3 & _).
pose proof (hz_of_block_range _ _ HBR) as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
assert (EA : bv_unsigned (edenot E (EVar v)) = A) by (cbn [edenot ev E]; rewrite Pv; apply u_small; lia).
unfold kn_blk, know_ok.
apply Forall_cons. { cbn [kentry_ok]. rewrite EA. lia. }
apply Forall_cons. { cbn [kentry_ok]. rewrite EA. split; [lia | exact B2]. }
apply Forall_cons.
{ cbn [kentry_ok]. split. { unfold flat, estart. cbn [a_base a_off]. rewrite EA. lia. }
intros d m Hd Hm. unfold estart. cbn [a_base a_off]. rewrite EA.
destruct m as [|m']; [reflexivity|]. set (m := S m') in *.
apply store_ok_of_all; [rewrite u_small by lia; lia|].
intros x Hx. rewrite u_small in Hx by lia.
specialize (Hdef (bv_unsigned x - A) ltac:(lia)). replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in Hdef by lia.
rewrite Z_to_bv_bv_unsigned in Hdef. unfold wview. destruct (M' x); [discriminate | exfalso; apply Hdef; reflexivity]. }
apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E]. rewrite P0.
change (ev E v) with (vals_ev vals v). rewrite Pv, u_small by lia. right. lia. }
apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E].
change (ev E v) with (vals_ev vals v). rewrite Pv, !u_small by lia. lia. }
apply Forall_nil.
Qed.
Definition IMG_W : list (Z * Z) := [(0xb6000, 0xe8f20); (0xe8f28, 0xe8f40); (0xe9478, 0xe98a4); (0xe98a8, 0xea000)]%Z.
Definition CW (LB : list (Z * Z)) (a : Z) : Prop := ~ alloc_private L LB a.
Section SE.
Local Abbreviation SEC_T_regions_write := (ltac2:(TCodec.tc2 tcn__Ju0DrvLib "R='8'TFyR0%211%411'9y8%611%811p041'='Q6%2271%=11%4233%?11'S7(S4&SAr4%211r3%5221'Mr5(2%8221vTB%53I21';%11C&QLr2r6%3221(3r1%22J1%?3841'L&Q4&7r9%22Q81%42G1&RE&TG%M25J%22Q>1%43@1A%;261p0=1pXLQ91pX<Q@1'R0&SB&SL+2+Q8%3221(:%11QA%21QI&RA%41QB&R@%11Q?'Kq0QI1%?<>Q<::Q=8765Q@31p0A1p0Q;1tR@QHQB1pRJQJ1pX2QM1pX8R21pYDR81")) (only parsing).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_regions_write) 0%nat 0%nat).
Variable ebs : ltac:(sec_ty2 constr:(SEC_T_regions_write) 1%nat 0%nat).
Variable bls : ltac:(sec_ty2 constr:(SEC_T_regions_write) 2%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_regions_write) 3%nat 0%nat).
Lemma regions_write : ltac:(sec_stmt2 constr:(SEC_T_regions_write) 4%nat 0%nat).
Proof.
intros E P0 Hbl.
pose proof (dl_stack L sp0 DL) as ST. pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
pose proof (dl_sptop L sp0 DL) as TOP.
assert (RO := dl_ro L sp0 DL). assert (STA := dl_static L sp0 DL).
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CW, alloc_private. intros [[A _]|A]; [rewrite TOP in A; lia|].
apply RO in A. lia.
- intros z Hz. right. exact I.
- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi & HSB). pose proof (sub_block_hz _ _ _ HSB) as (Z1 & Z2 & Z3).
destruct HSB as (cap & Hnb & Hin & HB). pose proof (hz_of_block_range _ _ HB) as (Y1 & Y2 & Y3).
split; [lia|]. intros z Hz. unfold CW, alloc_private. intros [[_ [A _]]|A].
+ apply A. exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia.
+ apply RO in A. lia.
- intros v b Hf. discriminate.
- intros i [].
- intros lo hi Hin. unfold IMG_W in Hin.
destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]);
intros a Ha; unfold CW, alloc_private; intros [[_ [_ A]]|A];
[ apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
| apply RO in A; lia
| apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
| apply RO in A; lia
| apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
| apply RO in A; lia
| apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
| apply RO in A; lia ].
- intros lo hi [].
Qed.
End SE.
Lemma heap_block : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "RO'8'TFyR0%211%411'9y8%611%811p041'='Q6%2271%=11%4233%?11&R3';%11;p0@1'Q@'S;%F11'S7(S4&SAr8%211r7%5221'Mr9(2%8221vTB%53Q021%C1I&QLr2r:%3221(3r1%22Q01%>3841'L&Q4r3&7r=%22Q?1%5241&RE&TG%M257%22QE1%43A1B%<261p0>1pXLQ@1pX<QG1'5&QO&SL+2+Q8%3221(:%11QO&RAr4%97Q755Q8321(>%Q;3<21&R7vQ9r6%352Q>QCQA1&S=r5%231QF4%756Q:QB1QEp051p0:1p0H1p0QB1tR@QOQI1pXBR11pWLR41pS@R61pX6R:1pRJR<1pX2R?1pX8RD1pYDRJ1").
Proof.
intros vals ebs bls LB cr M VM log E P0 Hbl Hlog HH.
apply (hio_frame L scfg HI HIok LB cr M (mem_denot E M log) VM HH).
- intros a Ha Hp. apply (mem_denot_frame_Z RSEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W E (CW LB) (fun _ => True) []
(regions_write vals ebs bls LB P0 Hbl) M log a Hlog Ha).
unfold CW. tauto.
- intros x Hx. exact (mem_denot_grows E M log x Hx).
Qed.
Definition CPstk (a : Z) : Prop := a < 4096 \/ (0x10000 <= a < 0xea000) \/ bv_unsigned sp0 - 8388608 <= a.
Lemma regions_stk : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "Q>'8'TFyR0%211%411'9y8%611%811p041'S7(S4&SAr2%211r1%5221'Mr3(2%8221vTB%53C21'R0&SB&SL+2+Q8%3221(:'='Q6%22K1%411%51M&RA%6255%811&R?'Kq091%B<AF==88764L31p0D1tR@Q1K1pX8Q31pYDQ91").
Proof.
intros vals ebs E P0.
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CPstk. lia.
- intros z Hz. right. exact I.
- intros i nb Hf. discriminate.
- intros v b Hf. discriminate.
- intros i [].
- intros lo hi Hin. unfold IMG_W in Hin.
destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPstk; lia.
- intros lo hi [].
Qed.
Lemma mem_heap_frame : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "QO'8'TFyR0%211%411'9y8%611%811p041';%114p091'S;%>11'Q6'S7(S4&SAr5%211r4%5221'Mr6(2%8221vTB%53I21'5&QO&SL+2+Q8%3221(:'=%12Q0F%311%41Q2&RA%;7@77321D(>%D3>21&RD+1%22I1&S=r7&TE%12Q@O%44N3K1%412%N3Q:21p081p0<1p0L1tR@Q9Q31pWNQ;1pXBQ=1pS@Q@1pX8QD1pYDQJ1").
Proof.
intros vals ebs M log a E P0 Hlog (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
apply (mem_denot_frame_Z RSEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_W E CPstk (fun _ => True) [] (regions_stk vals ebs P0) M log a Hlog).
- lia.
- unfold CPstk. lia.
Qed.
Lemma rdn_heap_frame : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "R6'8'TFyR0%211%411'9y8%611%811p041';%114p091'S;%>11'Q6'S7(S4&SAr6%211r5%5221'Mr7(2%8221vTB%53I21'5&QO&SL+2+Q8%3221(:'=%12Q0F%311%41Q2&RA%;7@77321D(>%D3>21&RD&SJr4%211%42K1%Q71Q9&RM&SB&S=r8%2381N&TE%12QFQ5%74631Q4%84752Q5%Q43:21p0<1p0B1p0Q21tR@Q?Q91pXJQK1pWNQB1pXBQD1pS@QG1pX8QK1pYDR11").
Proof.
intros vals ebs M log a n E P0 Hlog HZ. pose proof HZ as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
apply rdn_agree. intros j Hj. rewrite u_small by lia.
apply (mem_heap_frame vals ebs M log); [exact P0 | exact Hlog | eapply hz_sub; [exact HZ| lia | lia | lia]].
Qed.
Lemma heap_wbytes : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "R3'8'='Q6%2211%411&R3'TFyR0%211';y8%511%311p051'Q@%?14&R7vQ9r8r7r6r5%6554321&SC(<r4%24HH51r9%53I21&SG%12:5&SF&SJ&7%12G9%311%52?1%62BA%9221%82ED&SL+2+R0%3221%?251r=r<&QKr;&TE%12Q;O%4331Or:%Q55Q48721p0:1p0A1p0J1p0M1p0Q41pX4Q<1pWNQJ1pXJQK1p2QL1pWLQA1pS@QC1pX6QL1pRJQN1").
Proof.
intros LB cr M VM A n a bs HH Hin H1 H2 H3.
destruct (hio_wf L scfg HI HIok LB cr M VM HH) as [WF _]. destruct (WF _ Hin) as (HBR & _ & _). cbn [fst snd] in *.
pose proof (hz_of_block_range _ _ HBR) as (Z1 & Z2 & Z3).
apply (hio_frame L scfg HI HIok LB cr M _ VM HH).
- intros x Hx Hp. apply wbytes_out; [rewrite u_small by lia; lia|]. rewrite !u_small by lia.
destruct (Z.lt_ge_cases x a) as [Hlt|Hge]; [left; exact Hlt|]. right.
destruct (Z.lt_ge_cases x (a + Z.of_nat (length bs))) as [Hlt2|Hge2]; [|exact Hge2].
exfalso. destruct Hp as [[_ [Hnb _]]|Hro].
+ apply Hnb. exists (A, n). split; [exact Hin|]. cbn [fst snd]. lia.
+ apply (dl_ro L sp0 DL) in Hro. pose proof Hsp. lia.
- intros x Hx. exact (wbytes_grows bs M (Z_to_bv 64 a) x Hx).
Qed.
Definition CPout (A n : Z) (a : Z) : Prop := ~ (A <= a < A + n).
Lemma regions_blockwrite : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "R?'8'TFyR0%211%411'9y8%611%811p041'Q6'S7(S4&SAr4%211r3%5221'Mr5(2%8221vTB%53D21&RD%12;9&SCr1(6u3u4(:%11K%53L31%63M51%93N81'L&SG&TG%12Q5Ar9r2%M221%52Q91%7251&SF&SL+2+D%3221%5271+R0%6251%@231%B2:1p0D1pX<QC1'R0&SBz'=%12QHQC%O11&RF&RG&R>r6%221Q@'Iq0QK1%=<<QB;;88Q476QH31p0?1p0Q?1p0QB1tR@QOQI1pXJR11p2R21pX8R41pYDR:1").
Proof.
intros vals ebs A n E P0 (Z1 & Z2 & Z3) Hhi. pose proof Hsp as Hsp'.
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CPout. lia.
- intros z Hz. exfalso. lia.
- intros i nb Hf. discriminate.
- intros v b Hf. discriminate.
- intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. intros z Hz. unfold CPout. lia.
- intros lo hi Hin. unfold IMG_CLIENT in Hin.
destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPout; lia.
- intros lo hi Hin. unfold IMG_RW in Hin.
destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb0000) _ 24576%nat m 0xb0000 0xb6000);
[reflexivity | reflexivity | lia | exact wseg_ac5b0 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb6000) _ 212992%nat m 0xb6000 0xea000);
[reflexivity | reflexivity | lia | exact wseg_5f000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
Lemma know_blockwrite : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "S9'8'TFyR0%211%411'9y8%611%811p041';%114p091'Q6'S9%?11'S7(S4&SAr8%211r7%5221'Mr9(2%8221vTB%53I21&RDr6%22:1&SG%12>3&SF&SJ&7%12N7%311%52B1%62@E%9221&SCr1(6u3u4(:%11Q;%53Q<31%63Q=51%93Q>81'L&TG%12QDKr?r2%Q7221%52QH1%K251&SL+2+D%3221%N261+R0%6251%Q3231%@291p0B1pX<R11&S<&SBr<%342Q<1QE&QKr=&TEr:%22R=1%5341QH&QNz'=%12R?R7%Q611&RF&RG%79QO6633Q621R5%B4AR491p0@1p0E1p0QC1p0QL1p0QO1p0R31tR@R@R:1pX@RB1pX4RJ1pWNRF1pXJRG1p2RH1pS@RJ1pX8RN1pYDS41").
Proof.
intros vals ebs M A n a bs kn E P0 HZ Ha Hbs Hhi HK. pose proof HZ as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
eapply (know_keep_g_sound RSEGS 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW E (CPout A n) (fun _ => False)
(regions_blockwrite vals ebs A n P0 HZ Hhi) M).
- intros x Hx Hout. unfold CPout in Hout. apply wbytes_out; rewrite ?u_small by lia; [lia|lia].
- intros x [].
- apply wbytes_grows.
- exact HK.
Qed.
Lemma vals_ev_junk : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "Q6'8'TFyR0%211%411&QFy5%2214'9&Q4r1uQ0%3221'M&SA&4r4&S1r3%211%53A41&Q0&7%12D7r2%4221%<261&RK&TE&SJ%116%32I1%52>1%D3N71p0F1pX<K1pSFM1pYDQ11").
Proof.
intros vals R' i Hi. rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite nth_map_seq by exact Hi. reflexivity.
Qed.
Lemma malloc_site : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "\D'8'TFyR0%211%411'9y8%611%811p041'S8%;11'S9%=11&QFy5%221=';%11;p0@1'Q?'='Q6%2211%H11&R3%52E4%K11'QA%M11!pYJ21'S7(S4&SAr?%211r>%5221&S>r1r<%33251&S<&SBr2%342159'M'5&S@&7rB%22QA1r@%5221(>%93821&S?rC%92QH1%3217%>3=16'Q3u5rD%?2QN1%4231rE(2%Q3221vTB%H3R421&SC(6u3u4(:%11R8%53R931%63R:51%83R;Q81'L&SG&TG%12RB>rH%QD21Q9%42RE1%6241&SF&SL+2+D%3221%5271+R0%6251%?231%A2:1p0C1pX<RO1&RC%11Q6%QH3QG1Q@&RK(TD(J%23RL@1%42Q<1&TE%E2JR9%22S=1%R13S=41&SK+F%I2H1%311%Q321RBz%Q52RD1%Q7231&SI+@%22R61%R=3S616rG+:%F3S@1E%H231%D2SOR>%RC3SO21&SH%12>R:+K%Q<2Q;1%QE2R=1%QG241&R4vQ;%231R8R;rJ+4%Q53SO1Q4%Q7231+iSU@%Q42T?1%S33T?31rK+1%Q<3T61Q;%Q>231%S83TD1F%R62Q2RN%F2ROQI%R9221%Q22RKR0%S=3T61Q6&R7vQ9rM&QErL%211%655@G41%TC1U1&QB%117(1%11U5%SJ3531%TE2U7U7%U;11&QCrN%211%S315%T13521&QDrO%211%S81UA%T63UA21%U51U0&QL%12T;I(3%12U4TB%T<3531&Q4r3rQ9%T=2UL1%4231&RErQ2%U1256%SA2V21%4331TH%SE261p0<1pXLUB1pX<V41rQ:%TI2V81%@2?1%U;23@%SK2V<1%SM21U2%SO241p0F1pX0UL1pYBV>1%T81UH%R911&4rQ=&S1r4%211%53VH41%UJ1UD%UL216%U<2VKUA&Q0rQ?%U?2VN1uQ0%4221%UE3VO61rQ@%UD2W31u:%9221%V72Q<1%SM2W8A%UL3W821&S2&Q5%W=1VO&S:&RH%443W<21rQA%V12W@1%83D31r8%V?3QI21&RJrQB%V72WF1%K21C%421QM&RIrQ8rQ7rQ6%44321Q0%Q;3WE61%VG4VFQ9=1(<r7%24W?W?1QKrQ<%UN3W@21&R5rQ;%23T01R0r9%S<1G%S@5S?6321&R:rQ>%2215&R1%13T87<&R2r:%231QNQE%V32XDW>%V52V31%WE1W;rQD%11W=%W<3X931p051pYJXJ1%V<2U8WF%TL2WGUO%V?221&R8rQC%221WFrA%UH2Y3S8%211rQF%113%WJ3XG31p071p0;1pWNXF1+RPP0%VL21X6+mXP0%U=2X81%W0231&O+mTUH%W221X7+mUS0%UC2X91%W6231%611+iSP<%W821SM+iSP@%UI2SO1%W<231%<11%X51RErQH%11RG%XC3Y@31p051p0<1p0D1pWNY@1'ROvT@(Q>&RLvT4%VO2Z:SE&RN%11Y2%554Q;3XJ1%721Y=%:4Y591R;p0<1p0Q71p0QG1p0R01p0R41p0R71p0R;1p0RG1p0S41p0S@1p0SH1tRBYMT01tYFZJT31p2Z91pXHZ<1pSBZ>1pSFZB1+c^h8%WG2[21rQ5%L5KS721HrQ4%O221%Q24YMQ11V8p081p0TF1p0TI1p0U41p0UI1p0UO1p0V71p0V>1p0VF1p0VI1p0VM1p0W31p0W;1p0W?1p0WF1p0WM1p0X21p0X;1p0XE1p0XI1p0YG1p0YM1p0Z31p0Z91p0ZD1p0ZI1tR@[4ZN1pRF[61pY0[@1pYH[<1pX2[=1pY4[C1pXJ[D1pX6[B1pRJ[D1pXF[I1pS@[K1pSD[O1pX@\31pY8\61pX8\91pYD\?1").
Proof.
intros vals ebs sr kn R M model LB cr n so bls vbnd ra K E HR HK Hsv Hkv HL5 P0 Hhi Hiw
R2 Hso Hsoal R10 Hn Hcr R4 R1 Hra Hra2 HH Hh Hlz Hmt Hbl Hvb HK0 CONT.
pose proof (hio_malloc L scfg HI HIok fx R M model LB cr n K) as MS.
rewrite (dl_segs L sp0 DL), (dl_malloc L sp0 DL), (dl_tp L sp0 DL) in MS.
rewrite R1 in MS.
apply MS; clear MS; try assumption.
- apply ret_ok_even. rewrite u_small by lia. exact Hra2.
- rewrite R2, u_small by lia. eapply stack_ok_of_window; eassumption.
- intros R' M' model' A HA HP HBR HAP HDEF HPRES HBUT HH'.
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (HA' : vals_ev (vals ++ junk_vals R') (length vals + 10) = Z_to_bv 64 A).
{ rewrite vals_ev_junk by lia. exact HA. }
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0).
{ rewrite vals_ev_app_l by lia. exact P0. }
apply (CONT R' M' model' A HL' HA').
+ apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_kept R R' HP) c_kept_no0).
+ apply Forall_app. split.
* eapply kn_blk_ok; [exact HA' | exact P0' | exact HBR | exact HDEF].
* unfold keep_alloc.
pose proof (env_app_know RSEGS vals (junk_vals R') ebs M kn Hkv HK) as HK1.
destruct HPRES as (PR1 & PR2).
eapply (know_keep_sound RSEGS 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW
(Env (vals_ev (vals ++ junk_vals R')) ebs) (CPm LB (bv_unsigned sp0 + so)) (SCm (bv_unsigned sp0 + so))).
-- apply regions_alloc; try assumption.
++ intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1).
rewrite vals_ev_app_l by exact Hi32. exact H1.
++ intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
++ intros i Hi. rewrite vals_ev_app_l; [apply Hhi; exact Hi|]. destruct Hi as [<-|[<-|[]]]; lia.
-- intros a Ha [HC HE]. rewrite R2, u_small in PR1 by lia. apply PR1; assumption.
-- intros a HS. rewrite R2, u_small in PR2 by lia. apply PR2. exact HS.
-- exact HK1.
+ exact HH'.
+ exact HBUT.
+ exact HBR.
+ exact HAP.
+ intros x Hx. destruct HPRES as (PR1 & _). rewrite R2, u_small in PR1 by lia.
rewrite <- (Z_to_bv_bv_unsigned 64 x). apply PR1.
* pose proof (u64_range x). lia.
* unfold client_addr. right. left. rewrite (dl_sptop L sp0 DL).
pose proof (u64_range x). pose proof (dl_stack L sp0 DL). lia.
* unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
+ intros a Ha Hb. destruct HPRES as (PR1 & _). rewrite R2, u_small in PR1 by lia. apply PR1; [exact Ha | left; exact Hb |].
destruct Hb as (b & Hbin & Hr). destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
destruct (WF b Hbin) as (HBRb & _ & _). pose proof (hz_of_block_range _ _ HBRb) as (Y1 & Y2 & Y3).
unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
+ intros a Ha Hs He. destruct HPRES as (PR1 & _). rewrite R2, u_small in PR1 by lia. apply PR1; [lia | |].
* unfold client_addr. right. right. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|].
intros Hst. apply (dl_static L sp0 DL) in Hst. lia.
* unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
Qed.
Lemma free_site : ltac2:(TCodec.tc2 tcn__Ju0DrvLib "[J'8'TFyR0%211%411'9y8%611%811p041'S8%;11'S9%=11&QFy5%221=';%11;p0@1'Q?'='Q6%2211%H11&R3%52E4%K11'QA%M11!pYJ21'S7(S4&SAr@%211r?%5221&S>r1r=%33251&S<&SBr2%342159'M'5&S@&7rC%22QA1rA%5221(>%93821&S?rD%92QH1%3217%>3=16'Q3u5rE%?2QN1%4231rF(2%Q3221vTB%H3R421&SC(6u3u4(:%11R8%53R931%63R:51%83R;Q81'L&SG&TG%12RB>rI%QD21Q9%42RE1%6241&SF&SL+2+D%3221%5271+R0%6251%?231%A2:1p0C1pX<RO1&RC%11Q6%QH3QG1Q@&RK(TD(J%23RL@1%42Q<1&TEr>%F2K1%32S>1%R23S>51&SK+F%J2I1%311%Q421RAz%Q62RC1%Q8231&SI+@%22RI1%R>3S716(<rB%24S:S:R=1%QI3S:1R1+:%J3SD1I%L2Q?1%H2T3R;%RG3T321rJ+4%Q03SJ1O%Q2231+iSU@%O2T:1%RN3T:31rK+1%Q73T11Q6%Q9231%Q52T@RM%S43T@21%R22ME&SH%12GQF%R6231%N2S5QM%S:3T31Q2&R7vQ9rM&QErL%211%655BI41%T@1TN&QB%117(1%11U2%SG3531%TB2U4U4%U811&QCrN%211%S015%SN3521&QDrO%211%S51U>%T33U>21%U21TM&QL%12T8G(3%12U1T?%T93531&Q4r3rQ9%T:2UI1%4231&RE&R9rQ0rQ2%3221%U1289%SA2V21%7331TH%SE291p0?1pXLUB1pX<V41rQ:%TI2V81%C2B1%U;23C%SK2V<1%SM21U2%SO241p0I1pX0UL1pYBV>1%T81UH%T011&4rQ<&S1%11O%43VG31%UI1UC%UK215%U;2VJU@&Q0rQ>%U>2VM1uQ0%4221%UD3VN61&S2rQ=&Q5%W61VH&S:&RH%443W521rQ?%UJ2W91%93831r6%V83V221&RIrQ5rQ4rQ3%44321?%V:4V9QK71rQ8%QH21Q=r7%RL1;%S05RO3QO21&R:%12Q54%U:2WKVE%U<2U:1r;%11VCrQ@%11VE%VD3WA31p061pYJX21%UD2T?VN%SB2VOU7%UG221&R8%R;2Q5O%221VN%TO2X:RB%W411rQB%113%W13WN31p061p0:1pWNWM1+RPP0%V321W=+mXP0%T22W?1%V7231&O+mTUH%V921W>+mUS0%T82W@1%V=231%611+iSP<%V?21S7+iSP@%T>2S91%VC231%<11r4%UJ2Y51%X311rQD%113%WL3XI31p071p0>1p0F1pWNXI1'ROvT@(Q>&RLvT4%V82YCQOr<&RN%11X<%655X@431%821QKrQ7%<4X@;21p0>1p0Q;1p0QJ1p0R41p0R71p0R=1p0RD1p0S11tRBY5S91tYFZ2S<1pXHYC1pSBYE1pSFYI1rQ6+c^^8%VO2Z:1%J5I31RLE%L21RL%O4Y3N1V1p071p0SL1p0SO1p0T:1p0U21p0U81p0U@1p0UG1p0UO1p0V21p0V71p0V>1p0VF1p0VL1p0W11p0W61p0W?1p0WJ1p0WN1p0XL1p0Y21p0Y81p0Y>1p0YI1p0YN1tR@Z9Z31pRFZ;1pY0ZE1pYHZA1pX2ZB1pY4ZH1pXJZI1p2ZJ1pX6ZH1pRJZJ1pXFZO1pS@[11pSD[51pX@[91pY8[<1pX8[?1pYD[E1").
Proof.
intros vals ebs sr kn R M model LB cr A n so bls vbnd ra K E HR HK Hsv Hkv HL5 P0 Hhi Hiw
R2 Hso Hsoal Hin R10 R4 R1 Hra Hra2 HH Hh Hlz Hmt Hbl Hvb HK0 CONT.
pose proof (hio_free L scfg HI HIok fx R M model LB cr A n K) as MS.
rewrite (dl_segs L sp0 DL), (dl_free L sp0 DL), (dl_tp L sp0 DL) in MS.
rewrite R1 in MS.
apply MS; clear MS; try assumption.
- apply ret_ok_even. rewrite u_small by lia. exact Hra2.
- rewrite R2, u_small by lia. eapply stack_ok_of_window; eassumption.
- intros R' M' model' HP HPRES HBUT HH'.
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0).
{ rewrite vals_ev_app_l by lia. exact P0. }
apply (CONT R' M' model' HL').
+ apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_kept R R' HP) c_kept_no0).
+ unfold keep_alloc.
pose proof (env_app_know RSEGS vals (junk_vals R') ebs M kn Hkv HK) as HK1.
destruct HPRES as [[PR1 PR2] _].
eapply (know_keep_sound RSEGS 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW
(Env (vals_ev (vals ++ junk_vals R')) ebs) (CPm (lb_remove A LB) (bv_unsigned sp0 + so)) (SCm (bv_unsigned sp0 + so))).
* apply regions_alloc; try assumption.
-- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1).
rewrite vals_ev_app_l by exact Hi32. exact H1.
-- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
-- intros i Hi. rewrite vals_ev_app_l; [apply Hhi; exact Hi|]. destruct Hi as [<-|[<-|[]]]; lia.
* intros a Ha [HC HE]. rewrite R2, u_small in PR1 by lia. apply PR1; assumption.
* intros a HS. rewrite R2, u_small in PR2 by lia. apply PR2. exact HS.
* exact HK1.
+ exact HH'.
+ exact HBUT.
+ intros x Hx. destruct HPRES as [[PR1 _] _]. rewrite R2, u_small in PR1 by lia.
rewrite <- (Z_to_bv_bv_unsigned 64 x). apply PR1.
* pose proof (u64_range x). lia.
* unfold client_addr. right. left. rewrite (dl_sptop L sp0 DL).
pose proof (u64_range x). pose proof (dl_stack L sp0 DL). lia.
* unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
+ intros a Ha Hb. destruct HPRES as [[PR1 _] _]. rewrite R2, u_small in PR1 by lia. apply PR1; [exact Ha | left; exact Hb |].
destruct Hb as (b & Hbin & Hr).
assert (Hbin' : In b LB).
{ clear -Hbin. induction LB as [|c LB' IH]; [destruct Hbin|]. cbn [lb_remove] in Hbin.
destruct (Z.eqb (fst c) A); [right; exact Hbin|]. destruct Hbin as [<-|Hbin]; [left; reflexivity | right; apply IH; exact Hbin]. }
destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
destruct (WF b Hbin') as (HBRb & _ & _). pose proof (hz_of_block_range _ _ HBRb) as (Y1 & Y2 & Y3).
unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
+ intros a Ha Hs He. destruct HPRES as [[PR1 _] _]. rewrite R2, u_small in PR1 by lia. apply PR1; [lia | |].
* unfold client_addr. right. right. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|].
intros Hst. apply (dl_static L sp0 DL) in Hst. lia.
* unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
Qed.
End DrvLayout.
End FPX_1.
