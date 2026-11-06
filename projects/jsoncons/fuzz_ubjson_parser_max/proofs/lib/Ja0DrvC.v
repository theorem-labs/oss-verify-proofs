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
PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
LibTail RefReadLib RefPrintfLib RefNodes HeapIface HeapIfaceA IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ja0DrvEntry Ja0Drv_defs Ja0DrvLib Ja0DrvRead Ja0DrvA
Ja0DrvG_defs Ja0DrvG Ja0DrvC_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DrvC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Instr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvC.FPX_1.DrvC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvC_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvG_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A0"; "0A1"; "0CAP"; "1Some"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"]; ["3le"; "3lt"; "4nth"; "5Z"; "0HI"; "0KT"; "0LEN"; "0LK"; "0LK0"; "6word_to_le_bytes"; "7Model"; "7event"; "8ALU_ADD"; "8BC_LTU"; "0M"; "0M0"]; ["0MV"; "9mrestrict"; ":credit"; ";ahid"; ";fframe"; "<ENVA"; "=B0A"; "=B1A"; "=B2A"; "=CFGA"; "=target_kA"; ">cfglen_xA"; ">knGLA"; "?close_kgA"; "@knGA"; "Adinv"]; ["AhzA"; "Brdn"; "CTSet"; "DEAlu"; "DELit"; "DEVar"; "DKRange"; "DKWord"; "DSA"; "DSCBr"; "Ekentry_ok"; "Eknow_ok"; "Esc_denot"; "Fvals_ev"; "Gloaded_segments"; "Hadd"]; ["Hle"; "Hlt"; "Hltb"; "Hof_nat"; "Hpow"; "Hto_nat"; "0ar"; "0bs"; "0can"; "0cr"; "0crC"; "0data"; "0fdata"; "0fs0"; "0fx"; "0hi"]; ["0j"; "0k"; "0lo"; "0m"; "0model"; "0n"; "0p0"; "0p1"; "0scfg"; "0sp0"; "IZ_to_bv"; "Ibv"; "Ibv_unsigned"; "0t"; "0u"; "0v"]; ["0vals"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma w2le1_byteA : ltac2:(TCodec.tc2 tcn__Ja0DrvC "E'RKy8%211'?'8%113&Iu1&RJyR0&RLr1%22;1%5241%8271(6(:%11?%33@71%@3>51pV4B1").
Proof.
intros x. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 8) with 256 in Hx.
unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
Qed.
Lemma content_byteA : ltac2:(TCodec.tc2 tcn__Ja0DrvC "R7'RKyR0%211';y8%511%311p051'C'8%115'9'?%:13&QA&QNr4&RJr3%22B1&7r2%22A1%948741(4%12?4%>3=31&A%82G:%2281&R0zr5%3221&R1&QOr6&R3%B2Q16%211%5241&R4+2+R0%3221%;251r8r7%;1@%>221%Q12QA1u1%Q64Q5621&I&RL&B%Q72QDI%24QDIE1%42QF1%Q:2QJ1%7291%Q52QC1%QB3QA:1p0B1p0O1p0Q41p0Q81pU2QH1pTHQJ1p2QM1pQNQO1").
Proof.
intros M A data j Hc Hj HA HA2.
pose proof (SeqExec.rdn_nth ASEGS M (length data) _ data j Hc Hj) as H.
rewrite w_add_nat in H. rewrite u_small in H by lia. rewrite w2le1_byteA. exact H.
Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvC.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
Hypothesis DL : drv_layoutA L ar IL sp0.
Variable fs0 : Fs.Fs.
Variable fdata : list byte.
Variables p0 p1 can : word.
Variable M0 : word -> option byte.
Variable LK0 : list fframe.
Variable A0 : list (Z * Z).
Variable CAP : Z.
Hypothesis HCAP : 65536 <= CAP <= 67108864.
Variable crC : credit.
Hypothesis HLEN : Z.of_nat (length fdata) < CAP.
#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation ENVG := (ENVA fdata).
Let LEN : Z := Z.of_nat (length fdata).
Definition B0A : Z := bv_unsigned (nth 0 fdata (Z_to_bv 8 0)).
Definition B1A : Z := bv_unsigned (nth 1 fdata (Z_to_bv 8 0)).
Definition B2A : Z := bv_unsigned (nth 2 fdata (Z_to_bv 8 0)).
Definition CFGA : Z := (B0A + 256 * B1A) mod 32768.
Definition PLA : Z := LEN - 6 - CFGA.
Lemma B0A_range : ltac2:(TCodec.tc2 tcn__Ja0DrvC "9'>&R0z&Q6%3221&R1+X0%2241%8241").
Proof. clear HLEN. unfold B0A. pose proof (bv_unsigned_in_range _ (nth 0 fdata (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256 in H. lia. Qed.
Lemma B1A_range : ltac2:(TCodec.tc2 tcn__Ja0DrvC "9'>&R0z&Q7%3221&R1+X0%2241%8241").
Proof. clear HLEN. unfold B1A. pose proof (bv_unsigned_in_range _ (nth 1 fdata (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256 in H. lia. Qed.
Lemma B2A_range : ltac2:(TCodec.tc2 tcn__Ja0DrvC "9'>&R0z&Q8%3221&R1+X0%2241%8241").
Proof. clear HLEN. unfold B2A. pose proof (bv_unsigned_in_range _ (nth 2 fdata (Z_to_bv 8 0))) as H. change (bv_modulus 8) with 256 in H. lia. Qed.
Lemma CFGA_range : ltac2:(TCodec.tc2 tcn__Ja0DrvC "9'>&R0z&Q9%3221&R1+QPP0%2241%8241").
Proof. clear HLEN. unfold CFGA. apply Z.mod_pos_bound. lia. Qed.
Definition target_kA (KT : TSet) : Prop :=
forall vals R M (model : Model) A (A1 : Z),
length vals = 81%nat -> hdr_valsA sp0 p0 p1 can vals -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 LEN ->
vals_ev vals 71 = Z_to_bv 64 B0A -> vals_ev vals 72 = Z_to_bv 64 B1A -> vals_ev vals 73 = Z_to_bv 64 CFGA ->
vals_ev vals 79 = Z_to_bv 64 PLA -> vals_ev vals 80 = Z_to_bv 64 B2A ->
regs_ok (ENVG vals) srT0A R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knT0A ->
rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
dinvA [(A1, CAP)] LK0 crC A M model -> incl A0 A ->
m_fds model = fds0 -> m_fs model = fs0 ->
srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa747c) M (seg_rom ASEGS)) model) KT.
Lemma ltu_hdr_scA : ltac2:(TCodec.tc2 tcn__Ja0DrvC "R1'8'RKyR0%211%411';y8%611%311p061'5'?&QMr3uR6%3221&RJvF%22@1%83@41r4uR7%:221&Q6%82F1%>3F31r5uR8%@221&Q7%>2L1%D3L31&R2&QO&Q9+6%3221%52D1%K3L1B&QL&QNr6&Q5vR<r7%3221(QI(M(QE%11Q3(QC(L&Q;(QD%11C%53431%:4N971%B4A@<1p0D1p0L1p0Q31p0Q:1pULQD1pQNQF1pV2QL1").
Proof.
intros vals M t P70 P71 P72 Ht. pose proof B0A_range as R0. pose proof B1A_range as R1. pose proof CFGA_range as RC.
cbn [sc_denot branch_taken].
change (edenot (ENVG vals) (EAlu ALU_ADD cfglen_xA (ELit 6))) with (alu64 ALU_ADD (edenot (ENVG vals) cfglen_xA) (Z_to_bv 64 6)).
change (edenot (ENVG vals) (EVar 70)) with (vals_ev vals 70).
unfold ENVA. rewrite cfglen_x_cfgFA, P70, P71, P72, cfgF_valA by lia. fold CFGA.
rewrite alu_add_Z. unfold bv_ltu. rewrite !u_small by (unfold LEN in *; lia). exact Ht.
Qed.
Lemma content_visA : ltac2:(TCodec.tc2 tcn__Ja0DrvC "R9'8&Q4%211&Q2'='C%2211%711'RKyR0%211';y8%511%311p051'J'9%B15'Q?vR6vDvRIvO(6(<r4r3%34GG21(:%11H%73I31r9r8r7r6r5%B:A@?>654321&R0&R3%11=%321?'?%Q01I&QA&QN&RJ%12Q6<%443?1F(4%12Q0G%93831&Q1&Q3r:%221F%421H%;2Q@G%>4=21F%:2Q9Q1%B3A21p0:1p0E1p0J1pT@Q>1pU8Q@1pU<QM1pUNQN1pU:QD1pQNQF1p2QO1pTDR41pQ@R61").
Proof.
intros LK cr A M model u n m bs D Hm HC. pose proof Hsp as Hsp'.
destruct (inv_block1 scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ _ D (or_introl eq_refl)) as (_ & _ & (Z1 & Z2 & Z3)).
rewrite <- HC. apply rdn_agree. intros j Hj. rewrite u_small by lia. unfold mrestrict.
rewrite (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ (u + Z.of_nat j) (di_inv _ _ _ _ _ _ _ _ _ _ D) ltac:(lia)); [reflexivity|].
right. right. exists (u, n). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.
Lemma kbyte48A : ltac2:(TCodec.tc2 tcn__Ja0DrvC "RB'8'RKyR0%211%411';y8%611%311p061'C'9'?&QMr5uQ@%3221&RJr3%22A1%83A41&Q@vRIr4v3%43321%J1C%F11&QA&QNr6%>2MA&7vR<%22K1%746541(4%12;4%J3;31&R0z%221K&A&R5%11>%321;r:%Q221A&RL&Br7%811%Q32Q><%44Q>2D1%62Q@1%Q62QE1%Q<3QE91&QJ&Q5r;%22K1(QG(QH(QE%11QAr8%4221u1%51B%83321%=4Q9:H1p0?1p0K1p0Q01p0Q41p0QB1p0QH1pV0R21pU4R41p6R51pR2R71pV2R=1").
Proof.
intros vals MV A1 k v P48 (Z1 & Z2 & Z3) HC Hk Hkl Pv. pose proof Hsp as Hsp'.
cbn [kentry_ok]. split; [lia|]. split.
- apply flat_intro; cbn [edenot ev ENVA]; rewrite ?P48, ?u_small by lia; lia.
- unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVA]. rewrite P48, Pv, u_small by lia.
replace (A1 + k) with (A1 + Z.of_nat (Z.to_nat k)) by lia. apply content_byteA; [exact HC | exact Hkl | lia | lia].
Qed.
Lemma krange_litA : ltac2:(TCodec.tc2 tcn__Ja0DrvC "QJ'8'RKyR0%211%411';y8%611%311p061'9'C'?&QMr6r4%3221&RJr3%22A1%83A41'>&R0z%2219&R1&R4+2+R0%3221%52?1%:271r5%;2B1%<22@%>221&QJ&QN&Q5vR<r9%3221r8(QF(QEr7%211%431?Q0%<4;761p0>1p0C1p0O1pU0Q91pU6Q:1pV4Q;1pV0Q=1pR2Q?1pV2QE1").
Proof. intros vals MV v x lo hi Pv Hx Hr. cbn [kentry_ok edenot ev ENVA]. rewrite Pv, u_small by lia. lia. Qed.
Lemma know_GLA : ltac2:(TCodec.tc2 tcn__Ja0DrvC "RA'8'RKyR0%211%411';y8%611%311p061'C'?'9&7r3%22<1uR9%63521&QMr4uQ@%3221&RJr2%22F1%>3F41&Q@vRIv3%332?1%N1G%J11&QA&QNr5%=2Q1@vR<%H2N1%645431(4%12:4%N3:31'@u6%2217r8uR7%M221&Q6%K2Q?1%Q73Q?31r9uR8%Q3221&Q7%Q12QE1%Q=3QE31&QK&Q5r:%22H1&Q>+6+QooooO%3221%84Q05>1r;%92O1&Q<%<4Q42:1p051p0?1p0F1p0M1p0Q11p0Q>1p0QC1p0QL1p6R41pR2R61pV2R<1").
Proof.
intros vals MV A1 HL P48 HZ HC H6 P71 P72 HK. pose proof B0A_range as R0. pose proof B1A_range as R1.
unfold knGLA, kn_hdrA. apply Forall_app. split; [|exact HK].
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply kbyte48A; [exact P48 | exact HZ | exact HC | lia | cbn; lia | exact P71].
- eapply kbyte48A; [exact P48 | exact HZ | exact HC | lia | cbn; lia | exact P72].
- eapply krange_litA; [exact P71 | lia | lia].
- eapply krange_litA; [exact P72 | lia | lia].
Qed.
Ltac drv_blockH0 HIok Hsp DL HR HK DI P0 scr NX :=
let HZ := fresh "HZ" in
pose proof (dinv_lzinv _ _ _ _ _ _ HIok _ DL _ _ _ _ _ _ _ DI) as HZ;
run_block_lz_with HR HK HZ asegs_wx FUELA STOPS_HA scr NX true;
[ .. | drv_block_post0 HIok Hsp DL DI P0 HZ ].
Theorem hdr_okA : ltac2:(TCodec.tc2 tcn__Ja0DrvC "Q6&R0&QO+6&Q9%3221vF%6221&QB&Q:r1%211r2(:'K%211%411&Q=vR>vRHvR6vDvRIvR=vR<vRFvRGvR8vOvHv1v3vR:r3%A@@?>=<;:987654321p0C1p0I1pQ<M1p0O1").
Proof.
intros Hok KT HKT HKT0. unfold close_kgA.
intros vals R M model A A1 HL HV P48 P70 HR HK HC DI HINC G1 G2.
pose proof Hsp as Hsp'. pose proof Hal as Hal'.
destruct (inv_block1 scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & HDEF & HZ). pose proof HZ as (Z1 & Z2 & Z3).
pose proof HV as (P0 & P1 & P2 & P3).
pose proof B0A_range as HB0r. pose proof B1A_range as HB1r. pose proof B2A_range as HB2r. pose proof CFGA_range as HCr.
assert (ELEN : LEN = Z.of_nat (length fdata)) by reflexivity.
assert (Hge : (6 <= length fdata)%nat) by lia.
specialize (HK 6 67108863 ltac:(lia)).
set (vals1 := vals ++ [Z_to_bv 64 B0A; Z_to_bv 64 B1A]).
assert (HL1 : length vals1 = 73%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
assert (YV : hdr_valsA sp0 p0 p1 can vals1) by (subst vals1; unfold hdr_valsA in *; rewrite !vals_ev_app_l by (rewrite HL; lia); exact HV).
pose proof YV as (Y0 & _).
assert (Y48 : vals_ev vals1 48 = Z_to_bv 64 A1) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
assert (Y70 : vals_ev vals1 70 = Z_to_bv 64 LEN) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
assert (Y71 : vals_ev vals1 71 = Z_to_bv 64 B0A).
{ subst vals1. rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
assert (Y72 : vals_ev vals1 72 = Z_to_bv 64 B1A).
{ subst vals1. replace 72%nat with (length vals + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
pose proof (env_app_regs vals [Z_to_bv 64 B0A; Z_to_bv 64 B1A] _ srGLA R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
pose proof (env_app_know ASEGS vals [Z_to_bv 64 B0A; Z_to_bv 64 B1A] _ _ (knGA 6 67108863) ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK0.
fold vals1 in HR1, HK0. change (Env (vals_ev vals1) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals1) in HR1, HK0.
pose proof (content_visA _ _ _ _ _ _ _ (length fdata) fdata DI ltac:(lia) HC) as HCV.
pose proof (know_GLA vals1 _ A1 HL1 Y48 HZ HCV Hge Y71 Y72 HK0) as HK1.
clear HR HK HK0 HCV.
drv_blockH0 HIok Hsp DL HR1 HK1 DI Y0 scr_fallA 73%nat.
{ apply (ltu_hdr_scA vals1 _ false Y70 Y71 Y72). apply Z.ltb_ge. lia. }
pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
assert (HC1 : rdn ASEGS M1 (Z_to_bv 64 A1) (length fdata) = Some fdata).
{ rewrite <- HC. apply rdn_agree. intros j Hj. apply EQA. }
clear EQM EQH EQA SBM HR1 HK1 DI HC G1 G2 HDEF. clear M model R.
set (ext := [Z_to_bv 64 CFGA; sx8FA (Z_to_bv 64 B1A);
Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (2 + CFGA)) fdata (Z_to_bv 8 0)));
Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (3 + CFGA)) fdata (Z_to_bv 8 0)));
Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (4 + CFGA)) fdata (Z_to_bv 8 0)));
Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (5 + CFGA)) fdata (Z_to_bv 8 0)))]).
set (vals2 := vals1 ++ ext).
assert (HL2 : length vals2 = 79%nat) by (subst vals2 ext; rewrite length_app, HL1; reflexivity).
assert (WV : hdr_valsA sp0 p0 p1 can vals2) by (subst vals2; unfold hdr_valsA in *; rewrite !vals_ev_app_l by (rewrite HL1; lia); exact YV).
pose proof WV as (W0 & _).
assert (W48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y48).
assert (W70 : vals_ev vals2 70 = Z_to_bv 64 LEN) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y70).
assert (W71 : vals_ev vals2 71 = Z_to_bv 64 B0A) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y71).
assert (W72 : vals_ev vals2 72 = Z_to_bv 64 B1A) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Y72).
assert (WX : forall i, (i < 6)%nat -> vals_ev vals2 (73 + i) = nth i ext (Z_to_bv 64 0)).
{ intros i Hi. subst vals2. replace (73 + i)%nat with (length vals1 + i)%nat by (rewrite HL1; reflexivity).
rewrite vals_ev_app_r. reflexivity. }
pose proof (WX 0%nat ltac:(lia)) as W73. pose proof (WX 1%nat ltac:(lia)) as W74.
pose proof (WX 2%nat ltac:(lia)) as W75. pose proof (WX 3%nat ltac:(lia)) as W76.
pose proof (WX 4%nat ltac:(lia)) as W77. pose proof (WX 5%nat ltac:(lia)) as W78.
cbn [nth ext Nat.add] in W73, W74, W75, W76, W77, W78. clear WX.
pose proof (env_app_regs vals1 ext _ srHa _ ltac:(rewrite HL1; vm_compute; reflexivity) HR) as HR1.
pose proof (env_app_know ASEGS vals1 ext _ _ knGLA ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK0.
fold vals2 in HR1, HK0. change (Env (vals_ev vals2) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals2) in HR1, HK0.
assert (Ecfg : edenot (ENVG vals2) cfglen_xA = edenot (ENVG vals2) (EVar 73)).
{ unfold ENVA. rewrite cfglen_x_cfgFA, W71, W72, cfgF_valA by lia. fold CFGA. symmetry. exact W73. }
assert (Esx8 : edenot (ENVG vals2) sx8_xA = edenot (ENVG vals2) (EVar 74)).
{ unfold ENVA. rewrite sx8_x_sx8FA, W72. symmetry. exact W74. }
pose proof (regs_ok_esub _ _ _ _ _ Esx8 (regs_ok_esub _ _ _ _ _ Ecfg HR1)) as HR2.
lazymatch type of HR2 with regs_ok ?Ex ?srx ?Rx => assert (HRb : regs_ok Ex srHb0 Rx) by (exact HR2) end.
clear HR HR1 HR2.
pose proof (content_visA _ _ _ _ _ _ _ (length fdata) fdata DI0 ltac:(lia) HC1) as HCV.
assert (HKb : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A model0) M1) knHb0).
{ rewrite knHb0_eq. unfold kn_bmA. apply Forall_app. split; [|exact HK0].
assert (PXv : edenot (ENVG vals2) PXA = Z_to_bv 64 (A1 + CFGA)).
{ cbn [edenot ev ENVA PXA]. rewrite W48, W73. apply alu_add_Z. }
assert (KB : forall (j : Z) (v : nat), 2 <= j <= 5 ->
vals_ev vals2 v = Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (j + CFGA)) fdata (Z_to_bv 8 0))) ->
kentry_ok ASEGS (ENVG vals2) (mrestrict (ahid A model0) M1) (KWord (SA PXA j) 1 (EVar v))).
{ intros j v Hj Pv. cbn [kentry_ok]. split; [lia|]. split.
- unfold flat, estart. cbn [a_base a_off]. rewrite PXv, u_small by lia. lia.
- unfold adenot, v_addi. cbn [a_base a_off]. rewrite PXv, u_small by lia.
change (edenot (ENVG vals2) (EVar v)) with (vals_ev vals2 v). rewrite Pv.
replace (A1 + CFGA + j) with (A1 + Z.of_nat (Z.to_nat (j + CFGA))) by lia.
apply content_byteA; [exact HCV | lia | lia | lia]. }
constructor; [eapply krange_litA; [exact W73 | lia | lia]|].
constructor; [apply (KB 2); [lia | exact W75]|].
constructor; [apply (KB 3); [lia | exact W76]|].
constructor; [apply (KB 4); [lia | exact W77]|].
constructor; [apply (KB 5); [lia | exact W78]|].
assert (BR : forall (v : nat) k, vals_ev vals2 v = Z_to_bv 64 (bv_unsigned (nth k fdata (Z_to_bv 8 0))) ->
kentry_ok ASEGS (ENVG vals2) (mrestrict (ahid A model0) M1) (KRange (EVar v) 0 255)).
{ intros v k Pv. pose proof (bv_unsigned_in_range _ (nth k fdata (Z_to_bv 8 0))) as Hb. change (bv_modulus 8) with 256 in Hb.
eapply krange_litA; [exact Pv | lia | lia]. }
constructor; [exact (BR _ _ W75)|]. constructor; [exact (BR _ _ W76)|].
constructor; [exact (BR _ _ W77)|]. constructor; [exact (BR _ _ W78)|]. constructor. }
clear HK HK0.
drv_blockH0 HIok Hsp DL HRb HKb DI0 W0 scr0 79%nat.
pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
destruct (sbm_fds _ _ SBM) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
assert (HC2 : rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata).
{ rewrite <- HC1. apply rdn_agree. intros j Hj. apply EQA. }
pose proof (content_visA _ _ _ _ _ _ _ (length fdata) fdata DI ltac:(lia) HC2) as HCV2.
clear EQM EQH EQA SBM HRb HKb DI0 HC1 HCV F1 F2. clear M1 model0 R0.
set (ext2 := [Z_to_bv 64 PLA; Z_to_bv 64 B2A]).
set (vals3 := vals2 ++ ext2).
assert (HL3 : length vals3 = 81%nat) by (subst vals3 ext2; rewrite length_app, HL2; reflexivity).
assert (V79 : vals_ev vals3 79 = Z_to_bv 64 PLA).
{ subst vals3. rewrite <- HL2, <- (Nat.add_0_r (length vals2)). rewrite vals_ev_app_r. reflexivity. }
assert (V80 : vals_ev vals3 80 = Z_to_bv 64 B2A).
{ subst vals3. replace 80%nat with (length vals2 + 1)%nat by (rewrite HL2; reflexivity). rewrite vals_ev_app_r. reflexivity. }
pose proof (env_app_regs vals2 ext2 _ srHb _ ltac:(rewrite HL2; vm_compute; reflexivity) HR) as HR1.
pose proof (env_app_know ASEGS vals2 ext2 _ _ knHb0 ltac:(rewrite HL2; vm_compute; reflexivity) HK) as HK0.
fold vals3 in HR1, HK0. change (Env (vals_ev vals3) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals3) in HR1, HK0.
assert (TV : hdr_valsA sp0 p0 p1 can vals3) by (subst vals3; unfold hdr_valsA in *; rewrite !vals_ev_app_l by (rewrite HL2; lia); exact WV).
assert (T70 : vals_ev vals3 70 = Z_to_bv 64 LEN) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W70).
assert (T71 : vals_ev vals3 71 = Z_to_bv 64 B0A) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W71).
assert (T72 : vals_ev vals3 72 = Z_to_bv 64 B1A) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W72).
assert (T73 : vals_ev vals3 73 = Z_to_bv 64 CFGA) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W73).
assert (T48 : vals_ev vals3 48 = Z_to_bv 64 A1) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL2; lia); exact W48).
assert (Epl : edenot (ENVG vals3) plen_xA = edenot (ENVG vals3) (EVar 79)).
{ unfold ENVA. rewrite (plen_valA LEN CFGA vals3 _ ltac:(lia) ltac:(unfold LEN in *; lia) T70 T73). symmetry. exact V79. }
pose proof (regs_ok_esub _ _ _ _ _ Epl HR1) as HR2.
lazymatch type of HR2 with regs_ok ?Ex ?srx ?Rx => assert (HRt : regs_ok Ex srT0A Rx) by (exact HR2) end.
clear HR HR1 HR2.
assert (HKt : know_ok ASEGS (ENVG vals3) (mrestrict (ahid A model) M) knT0A).
{ eapply ksubl_sound; [|exact knT0A_sub]. apply Forall_app. split; [|exact HK0]. unfold kn_tgtA.
constructor; [eapply krange_litA; [exact T73 | lia | lia]|].
constructor; [eapply krange_litA; [exact V79 | unfold PLA, LEN in *; lia | unfold PLA, LEN in *; lia]|].
constructor; [eapply kbyte48A; [exact T48 | exact HZ | exact HCV2 | lia | cbn; lia | exact V80]|].
constructor; [eapply krange_litA; [exact V80 | lia | lia]|]. constructor. }
clear HK HK0.
apply (HKT vals3 R M model A A1 HL3 TV T48 T70 T71 T72 T73 V79 V80 HRt HKt HC2 DI HINC G1 G2).
Qed.
End DrvC.
End FPX_1.
