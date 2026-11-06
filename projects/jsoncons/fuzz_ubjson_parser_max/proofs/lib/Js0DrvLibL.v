(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg ShapeLaws SpinAlg SpinAlgX
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Hoare AsanAcct
HeapIface LibIface DrvKit Js0Drv_defs Js0DrvLib Js0DrvD_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0DrvLibL () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvD_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvLibL.FPX_1.DrvLibLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"]; ["2I"; "2and"; "2eq"; "2not"; "2or"; "3add"; "4le"; "4lt"; "5map"; "6Z"; "0E"; "0E'"; "0HI"; "0K"; "0L"; "0LB"]; ["0LSt"; "0Lay"; "7store_ok"; "8mkCfg"; "9Model"; "9event"; "9m_halted"; "9m_vm_lazy"; "9m_vm_materialized"; "9m_vmmaps"; ":bvmap"; "0M"; "0M'"; "0R"; "0R'"; ";segs_below_b"]; ["<find_nz"; "<regions_ok"; "=credit"; "=hi_heap"; "=in_block"; "=model_but_vm"; ">IMG_LIB"; ">keep_lib"; "?has_window"; "?sub_block"; "@CPl"; "@SCl"; "@credit_scale"; "AIMG_RW"; "Ac_kept"; "Bcredit_le"]; ["Bcredit_sub"; "Bin_foot"; "Bll_credit"; "Bls_ok"; "Bls_state"; "CFPState"; "Cgetr"; "Cmkst"; "Crdn"; "Cseg_rom"; "Dsrealizes"; "Ejunk_vals"; "Esr_after_call_j"; "FELit"; "FEnv"; "Fedenot"]; ["Fenv"; "Fexpr"; "Fkentry"; "Fridx"; "Fsr_upd"; "Gknow_ok"; "Gregs_ok"; "Hkn_vars_lt"; "Hsr_vars_lt"; "Hvals_ev"; "Iloaded_segments"; "JIn"; "Kadd"; "Kle"; "Klt"; "Kmodulo"]; ["Kof_nat"; "Kopp"; "Kpow"; "Ksub"; "0a"; "0b"; "0bls"; "0c"; "0cr"; "0cr'"; "0e"; "0ebs"; "0fx"; "0fx'"; "0g"; "0g'"]; ["0i"; "0k"; "0kn"; "0model"; "0model'"; "0nb"; "0payload"; "0ptr"; "0ra"; "0rd"; "0scfg"; "0so"; "0sp0"; "0sr"; "LBV"; "LZ_to_bv"]; ["Lbv"; "Lbv_unsigned"; "0v"; "0vals"; "0vals'"; "0vbnd"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Record drv_lib_layout (Lay : lib_layout) (L : heap_layout) : Prop := DRV_LIB_LAYOUT {
dll_heap : ll_heap Lay = L;
dll_entry : ll_entry Lay = 0x3404c;
dll_gp : ll_gp Lay = 0x10800;
dll_empty : ll_empty Lay = 0xc6240;
dll_stack : ll_stack Lay = 65536;
dll_rw_lo : ll_rw_lo Lay <= 0xb60d0;
dll_foot : forall iv, In iv (ll_foot Lay) -> (0xc6250 <= fst iv /\ snd iv <= 0xc73d8) \/ (0xc7b88 <= fst iv /\ snd iv <= 0xc7b90)
\/ (0xe7ca8 <= fst iv /\ snd iv <= 0xe7ec8);
dll_initc : forall iv, In iv (ll_initc Lay) ->
(0xc7b98 <= fst iv /\ snd iv <= 0xc7c60) \/ (0xe7ed0 <= fst iv /\ snd iv <= 0xe7ed8) \/ (0xe7ef8 <= fst iv /\ snd iv <= 0xe7f00)
\/ (0xe7f28 <= fst iv /\ snd iv <= 0xe7f58)
\/ (0xe7ef3 <= fst iv /\ snd iv <= 0xe7ef4) \/ (0xe7fc8 <= fst iv /\ snd iv <= 0xe7fcc);
dll_credit_pos : forall n, 0 <= n -> 0 <= fst (ll_credit Lay n) /\ 0 <= snd (ll_credit Lay n);
dll_init_cells : ll_init_cells Lay = [(0xe7cb0, 4%nat, 1); (0xe7cb8, 8%nat, 0xe7cc0); (0xe7cc8, 8%nat, 0x98a7c); (0xe7dc8, 8%nat, 0x33fd4)];
dll_init_img : ll_init_img Lay = [(0x10000, 0xb61e0); (0xc6235, 0xc7b90); (0xe7c68, 0xe7c88);
(0xe7ca8, 0xe7cb0); (0xe7cb4, 0xe7cb8); (0xe7cc0, 0xe7cc8); (0xe7cd0, 0xe7dc8); (0xe7dd0, 0xe7ec8);
(0xe7ef3, 0xe7ef4); (0xe7fc8, 0xe7fcc)];
dll_td_self : ll_td_self Lay = 0xc7b98;
dll_td_tid : ll_td_tid Lay = 0xc7bb8;
dll_td_locale : ll_td_locale Lay = 0xc7c30;
dll_locale : ll_locale Lay = 0xe7f28;
dll_td_canary : ll_td_canary Lay = 0xc7c50;
dll_guard : ll_guard Lay = 0xe7ed0;
dll_auxvp : ll_auxvp Lay = 0xe7ef8;
dll_phdr : ll_phdr Lay = 0x10040;
dll_phent : ll_phent Lay = 56;
dll_phnum : ll_phnum Lay = 10
}.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Lemma regs_ok_upd_same : ltac2:(TCodec.tc2 tcn__Js0DrvLibL "Q='R@'8'RA%211&Q:y5'T0yR0%211%5241%415&RFr5r4r3%43321&C'B(SNz(@%33@21%53<81%711&R?r7%221<&R6%12@?%<3E31r8&RD&RC%11E%3391Er6%I3621p081p0?1p0H1pVFQ61pWDO1pRLQ11pWLQ81pQFQ<1").
Proof.
intros E sr R rd e HR Hrd He r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. exact HR.
- rewrite nth_sr_upd. destruct (Nat.eqb (ridx r) (ridx rd)) eqn:Hi.
+ apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r. symmetry. exact He.
+ specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. exact HR.
Qed.
Lemma segs_below : ltac2:(TCodec.tc2 tcn__Js0DrvLibL "8'B'4&Q?&RJ+mTP0%3221(?%73621").
Proof. vm_compute. reflexivity. Qed.
Lemma window_defined : ltac2:(TCodec.tc2 tcn__Js0DrvLibL "Q='T0yR0%211';y8%511%311p051'I&RM+mTP0r1%3221&RNr2&S2+2+R0%3221%6251'B'4&Q2&RJr4&SOr3%22J1u1%746521(?%;3:21&Cr5%92Q1:%211(0%11Q0%B3Q031%711p091p0F1p0N1pV:Q31pRHQ51").
Proof.
intros M a Ha Ha2 Hst.
pose proof (store_ok_all RSEGS M 1%nat (Z_to_bv 64 a) ltac:(rewrite u_small by lia; cbn; lia) Hst (Z_to_bv 64 a)
ltac:(rewrite u_small by lia; cbn; lia)) as W.
unfold wview in W. destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [congruence|].
rewrite (find_segment1_none_above RSEGS 0xe9000 (bv_unsigned (Z_to_bv 64 a)) segs_below) in W by (rewrite u_small by lia; lia).
exact W.
Qed.
Section DrvLibLayout.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L scfg HI.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
Hypothesis DL : drv_layout L sp0.
Variable Lay : lib_layout.
Variable LSt : lib_statics.
Hypothesis DLL : drv_lib_layout Lay L.
Hypothesis LIok : lib_iface_ok Lay scfg HI LSt.
Definition CPl (LB : list (Z * Z)) (sp : Z) (a : Z) : Prop :=
client_addr L LB sp 65536 a /\ ~ in_foot Lay a /\ ~ in_errno L a.
Definition SCl (sp : Z) (a : Z) : Prop := sp - 65536 <= a < sp.
Lemma not_foot : ltac2:(TCodec.tc2 tcn__Js0DrvLibL "O'I'D&RNr1+hhb@%3221'A&RM+hlnH%2216+hnl8%9281%6231+hnl@%721;+loU8%>2=1%;231+lof8%<21@%C231%D291%E2A1&C&R1vQ1r2%3221%511p071pV:N1").
Proof.
intros a Ha (iv & Hin & Hr). apply (dll_foot Lay L DLL) in Hin. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_regions_lib := (ltac2:(TCodec.tc2 tcn__Js0DrvLibL "SE'8'T0yR0%211%411'9y8%611%811p041'I'=%1272%=11%3244%?11'R@(R>&RIr6%211r5%5221'Br7(1%8221vSL%53I21'A&RM&S1&S2+2+F%3221%511%721Bz%92D1%;231';%11Q0&Q@r2r8%3221(2r1%22Q71%K3841&QIvN&T1r<r3%Q6221%42QG1%746Q21>p091pW<QB1pW2QH1r=%Q=218%;2QN1%Q321Ep0@1pV<QI1pX6QO1&RK(5u3u4(:%11R5%53R631%63R751%83R8M1%I2R<QC%QM2AQ3%K2R>1%QC231&RL+D%QD2QC1%3251+R0%QG2QF1%QJ231%QL281p0=1pW2RF1'QA&RJr:+RPP0r9&QF&QM&QJ%B2F6%22R=1&QK%113%<<;R?:98QKL76RE31p0>1p0Q61p0Q>1p0R41p0RA1tQFRNRH1pR0S01pX<S31pV>S41pWHS81pVHS:1pX8S@1")) (only parsing).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_regions_lib) 0%nat 0%nat).
Variable ebs : ltac:(sec_ty2 constr:(SEC_T_regions_lib) 1%nat 0%nat).
Variable so : ltac:(sec_ty2 constr:(SEC_T_regions_lib) 2%nat 0%nat).
Variable bls : ltac:(sec_ty2 constr:(SEC_T_regions_lib) 3%nat 0%nat).
Variable vbnd : ltac:(sec_ty2 constr:(SEC_T_regions_lib) 4%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_regions_lib) 5%nat 0%nat).
Lemma regions_lib : ltac:(sec_stmt2 constr:(SEC_T_regions_lib) 6%nat 0%nat).
Proof.
intros E P0 Hso Hbl Hvb Hhi.
pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH. pose proof (dl_errno L sp0 DL) as ER.
pose proof (dl_sptop L sp0 DL) as TOP.
assert (NE : forall a, 0xc7bc0 <= a \/ a < 0xc7bbc -> ~ in_errno L a) by (intros a Ha; unfold in_errno; rewrite ER; lia).
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CPl, client_addr. split; [right; left; rewrite TOP; lia |]. split; [apply not_foot; lia | apply NE; lia].
- intros z Hz. destruct (Z.lt_ge_cases (bv_unsigned sp0 + z) (bv_unsigned sp0 + so - 65536)) as [A|A].
+ left. unfold CPl, client_addr. split; [right; left; rewrite TOP; lia |]. split; [apply not_foot; lia | apply NE; lia].
+ right. unfold SCl. lia.
- intros i nb Hf. pose proof (sub_block_hz L sp0 DL _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). pose proof (hz_of_block_range L sp0 DL _ _ HB) as (Y1 & Y2 & Y3).
split; [lia|].
intros z Hz. unfold CPl, client_addr.
split; [left; exists (bv_unsigned (vals_ev vals i), cap); split; [exact Hin|]; cbn [fst snd]; lia |].
split; [apply not_foot; lia | apply NE; lia].
- exact Hvb.
- intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
intros z Hz. unfold CPl, client_addr. split; [right; left; rewrite TOP; lia |]. split; [apply not_foot; lia | apply NE; lia].
- intros lo hi Hin. unfold IMG_LIB in Hin.
destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]);
intros a Ha; unfold CPl, client_addr; (split; [| split; [apply not_foot; lia | apply NE; lia]]); right; right; rewrite IL, IH; (split; [lia|]);
intros Hs; apply (dl_static L sp0 DL) in Hs; lia.
- intros lo hi Hin. unfold IMG_RW in Hin.
destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xaf000) _ 24576%nat m 0xaf000 0xb5000);
[reflexivity | reflexivity | lia | apply wseg_5a000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb5000) _ 212992%nat m 0xb5000 0xe9000);
[reflexivity | reflexivity | lia | apply wseg_5f000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
End SE.
Definition credit_scale (k : Z) (c : credit) : credit := (k * fst c, k * snd c).
Lemma credit_le_step : ltac2:(TCodec.tc2 tcn__Js0DrvLibL "Q8'I'=%1222&QB&RM+1r4%3221z&6%13::4%7231&>r5%23>>1%;271&QO&QLr7r6%3221%5218&R0%1245%821;&S3r9%221Fr8%<221%>21;p071p0;1p0B1p0G1p0L1pVDQ11pVBQ21pV@Q41pW4Q71").
Proof.
intros k c cr cr' Hk H1 H2 [A B] [C D]. unfold credit_scale, credit_sub, credit_le in *. cbn [fst snd] in *. nia.
Qed.
Lemma credit_le_head : ltac2:(TCodec.tc2 tcn__Js0DrvLibL "N'I'=%1222&QB&RM+1r3%3221z&6%13::4%7231&>r4%23>>1%;271&QO&QLr6r5%3221%5218%6243p021p091p0>1p0C1pVBH1pV@J1pW4M1").
Proof. intros k c cr Hk H1 H2 [A B]. unfold credit_scale, credit_le in *. cbn [fst snd] in *. nia. Qed.
Lemma lib_site : ltac2:(TCodec.tc2 tcn__Js0DrvLibL "^K'8'T0yR0%211%411'9y8%611%811p041'RA%;11'RB%=11&Q:y5%221=';%11;p0@1'Q4'='I%2211%H11&QB&R4vQ0%211%82H7%N11'Q5%Q011!pX>21'R@(R>&RIrA%211r@%5221&RFr1r>%33251&RE&RJr2%342159'B'4&RH&7rD%22QD1rB%5221(?%93821&RGrE%92QK1%3217%>3=16'Fu5rF%?2R11%4231rG(1%Q3221vSL%H3R721&RK(5u3u4(:%11R;%53R<31%63R=51%83R>Q81'A&RM&T1%12RE>rJ%QD21Q9%42RH1%6241&RL&S2+2+D%3221%5271+R0%6251%?231%A2:1p0C1pW2S21&QH%11Q6%QH3QG1Q@&R6(SN(@%23RO@1%42Q<1&SO%E2JR9%22S@1%R13S@41&S1+F%I2H1%311%Q321RBz%Q52RD1%Q7231&RO+@%22R61%R=3S916rI+1%F3SC1E%H231r?%E2T31%RD3T331%QB2>RO&RN+Q?%Q=2Q<1%32S31%QH251%A2S7Q?%RL3SH1ErL+3%Q53T21Q4%Q7231+RRP0%Q42TB1%S33TB31rM+4%Q<3T91Q;%Q>231+hoS0%Q;2TI1%S:3TI31rN+:%QC3T@1QB%QE231%QA2TOS4%S@3TO21rO+;%QI3TF1QH%QK231&S0%SC2U1SB%211%QJ2U81%SI3U851%SG2U5S?%611+J%RB2RA1%Q8231'D%SM2U;S?%T13U>1S<rH+hhb0%T43U021%S3241%A16%QA2R01(<%14U5U573%SA3U51O%S9241%=271%U>1UG&R8rQ1%RB2V0R2%T>2ULSM%44TE321(2%12UNT0%TE3831&QO&R2vQ1%TF2V4G%Q511%4231%621Q;&R3rQ3%23UFQ>1&QCvLrQ2rQ4&Q9%117%6554G31%V81VF&Q6%116(0%11VJ%U<3531%V:2VLVL%W011&Q7rQ5%211%TE15%UC3521&Q8rQ6%211%TJ1W6%UH3W621%VJ1VE&Q@%12UMH%Q92VHV3%UM3421&Gr3rQ@%UN2W@1%4231&QIvNrQ9%VC267%U32WG1%54431V:%U7271p0=1pW<W71pW2WI1rQA%V;2WM1%A2@1%VM23A%U=2X11%U?21VD%UA241p0G1pV<WA1pX6X31%UJ1W:%S711'R5&3rQF&R;r5%211%53X>41%W=1W7%W?216%VO2XAW4&ErQH%W22XD1uQ0%4221%W83XE61&RD&R<rQG&H%XN1X@&RC&QN%443XM21rQI%W?2Y11%93831%61T7(R=%11U?%>3431r8%X13WK21&QGrQ?rQ>%34QM21B%X24X1QO61rQDr6r9%RN1:%S35S24321&QE%12Q:4r;%S:3XN61&R0%X62YD>%TE11%SD2SC1%42QA1%SG21<%W:2YNXE%W<2W:1%UN1XBrQL%11XD%XC3YC31p051pX>Z41%WC2V?XM%V12XNW6%WF221&QDrQK%221XM%VN2Z<RM%Y911rQN%113%Y03Z031p061p0:1pV:YO1+RPP0%X221Y<+mTP0%VA2Y>1%X6231&C+mPS8%X821Y=+mQP@%VG2Y?1%X<231%611+hnmL%X>21SB+hnn0%VM2SD1%XB231%<11r4+hhb@%W2221+hlnH%XG214+hnl8%W6261%XK231+hnl@%XL219+loU8%W;2;1%Y0231+lof8%Y121>%V6231%V7291%V82?1%X:2[HS;%Z511rR1%113%Z<3[<31p061p0I1p0Q01p0Q81pV:[=1'R:vSJ(Q3&R7%XH2\6RG&R9%11ZK%45ZC[53[31%621X8rQB%:4ZO921p0<1p0QK1p0R:1p0RC1p0RJ1p0RM1p0S01p0S61p0S<1p0SN1tQH[FT61tX:\FT91pVD\21pW0\01pW:\91pRJ\;1pRN\?1pVLTE1vS<rQ=+V`R<%YD2]21rQ<%O55421LrQ;%Q2221%Q54[JQ41W8p0:1p0U11p0U41p0U?1p0V41p0V:1p0VB1p0VI1p0W11p0W51p0W=1p0WG1p0X61p0X<1p0XF1p0XM1p0Y51p0Y=1p0Y@1p0YG1p0YO1p0Z41p0Z=1p0ZG1p0ZK1p0[I1p0[O1p0\51p0\;1p0\F1p0\K1tQF]6]01pQL]81pW>^31pWB]F1pW@]G1pX<]@1pV>]A1pWH]J1pVN]E1pVB]I1pR0]K1pW8^01pRH^21pRL^61pW6^:1pWL^=1pVH^@1pX8^F1").
Proof.
intros vals ebs sr kn R M model LB cr g so bls vbnd ptr ra payload K E HR HK Hsv Hkv HL5 P0 Hhi Hiw
R2 Hso Hsoal R1 Hra Hra2 R3 R4 R10 R11 Hlen Hptr Hpay Hcr Hls HH Hh Hlz Hmt Hbl Hvb HK0 CONT.
pose proof (lio_call Lay scfg HI LSt LIok fx g LB cr (bv_unsigned sp0 + so) ptr ra payload R M model K) as MS.
unfold lib_cfg in MS. rewrite (dll_heap Lay L DLL), (dl_segs L sp0 DL), (dll_entry Lay L DLL) in MS.
pose proof (dl_stack L sp0 DL) as ST.
apply MS; clear MS; try assumption.
-
constructor; rewrite ?(dll_heap Lay L DLL), ?(dl_segs L sp0 DL), ?(dl_tp L sp0 DL), ?(dll_empty Lay L DLL), ?(dll_stack Lay L DLL),
?(dll_gp Lay L DLL), ?(dl_sptop L sp0 DL); try assumption.
+ lia.
+
destruct (has_window_nth kn Hiw) as [i Hn].
split; [rewrite Z.add_mod, Hal, Hsoal by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
* intros d m Hd Hm.
pose proof (kwr_store_ok RSEGS E M kn i (EVar 0) (-8388608) 8388608 (so - 65536 + d) m HK Hn ltac:(lia) ltac:(lia)) as W.
unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W.
replace (bv_unsigned sp0 + so - 65536 + d) with (bv_unsigned sp0 + (so - 65536 + d)) by lia. exact W.
* intros a Ha.
pose proof (kwr_store_ok RSEGS E M kn i (EVar 0) (-8388608) 8388608 (a - bv_unsigned sp0) 1%nat HK Hn ltac:(lia) ltac:(cbn; lia)) as W.
unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W.
replace (bv_unsigned sp0 + (a - bv_unsigned sp0)) with a in W by lia.
apply (window_defined M a); [lia | lia | exact W].
-
intros fx' g' R' M' model' cr' HPOST HH' HBUT.
destruct HPOST as [Qa0 Qregs Qcr Qframe Qscr Qls].
rewrite (dll_stack Lay L DLL) in Qframe, Qscr. rewrite (dll_heap Lay L DLL) in Qframe.
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
apply (CONT fx' R' M' model' g' cr' HL').
+
apply regs_ok_upd_same; [| discriminate | cbn [edenot]; symmetry; exact Qa0].
apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_kept sp0 Hsp R R' Qregs) c_kept_no0).
+
unfold keep_lib.
pose proof (env_app_know RSEGS vals (junk_vals R') ebs M kn Hkv HK) as HK1.
eapply (know_keep_sound RSEGS 0 so 65536 bls vbnd [3%nat; 4%nat] IMG_LIB IMG_RW
(Env (vals_ev (vals ++ junk_vals R')) ebs) (CPl LB (bv_unsigned sp0 + so)) (SCl (bv_unsigned sp0 + so))).
* apply regions_lib; try assumption.
-- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
-- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
-- intros i Hi. rewrite vals_ev_app_l; [apply Hhi; exact Hi|]. destruct Hi as [<-|[<-|[]]]; lia.
* intros a Ha (HC & HF & HE). apply Qframe; assumption.
* intros a HS. apply Qscr. exact HS.
* exact HK1.
+ exact HH'.
+ exact HBUT.
+ exact Qls.
+ exact Qcr.
+ intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Qframe.
* pose proof (u64_range x). lia.
* unfold client_addr. right. left. rewrite (dl_sptop L sp0 DL). pose proof (u64_range x). lia.
* apply not_foot. lia.
* unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
+ intros a Ha Hb. apply Qframe; [exact Ha | left; exact Hb | |].
* destruct Hb as (b & Hin & Hr). destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
destruct (WF b Hin) as (BR & _). pose proof (hz_of_block_range L sp0 DL _ _ BR) as (Y1 & Y2 & Y3). apply not_foot. lia.
* destruct Hb as (b & Hin & Hr). destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
destruct (WF b Hin) as (BR & _). pose proof (hz_of_block_range L sp0 DL _ _ BR) as (Y1 & Y2 & Y3).
unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
+ intros a Ha Hs He Hf. apply Qframe; [lia | | apply not_foot; exact Hf |].
* unfold client_addr. right. right. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|].
intros Hst. apply (dl_static L sp0 DL) in Hst. lia.
* unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
Qed.
End DrvLibLayout.
End FPX_1.
