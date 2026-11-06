(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
RefNodes HeapIface HeapIfaceA IcptIfaceAB0 LibIface LibIfaceAJ DrvKitA DrvNodesLazyK As0DrvKitA Jb0DrvEntry Jb0Drv_defs Jb0DrvLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DrvLibL () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvLibL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvLibL.FPX_1.LibSite."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIfaceAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"]; ["2and"; "2eq"; "2ex"; "2not"; "2or"; "3add"; "4le"; "4lt"; "5map"; "6Z"; "0E"; "0E'"; "0HI"; "0K"; "0L"; "0LB"]; ["0LK"; "0LK'"; "0LSt"; "0Lay"; "7mkCfg"; "8Model"; "8event"; "9bvmap"; "0M"; "0M'"; "0M0"; "0R"; "0R'"; ":mrestrict"; ";find_nz"; ";regions_ok"]; ["<credit"; "<in_block"; "=ahid"; "=ff_cap"; "=ff_count"; "=fframe"; "=model_rt"; "=ri_inv"; "=vml_of"; ">SCa"; ">dinv"; ">has_window"; ">sub_blockA"; "@CPl"; "?IMG_LIB_A"; "?LIB_HOLES"]; ["?keep_libA"; "AIMG_CLIENT_A"; "AIMG_RW_A"; "Ac_kept"; "Bcredit_le"; "Bcredit_sub"; "Bin_foot"; "Bls_ok"; "Bls_state"; "Cin_junk"; "Clib_view"; "Clla_credit"; "Clla_empty"; "Clla_frames"; "Clla_leak"; "Clla_stack"]; ["DFPState"; "Dgetr"; "Dmkst"; "Drdn"; "Dseg_rom"; "Esrealizes"; "Fjunk_vals"; "Fsr_after_call_j"; "GELit"; "GEnv"; "Gedenot"; "Genv"; "Gexpr"; "Gkentry"; "Gridx"; "Gsr_upd"]; ["Hknow_ok"; "Hregs_ok"; "Ikn_vars_lt"; "Isr_vars_lt"; "Ivals_ev"; "Jloaded_segments"; "KIn"; "Kincl"; "Ladd"; "Lle"; "Llt"; "Lmodulo"; "Lof_nat"; "Lopp"; "Lpow"; "0a"]; ["0ar"; "0b"; "0bls"; "0cr"; "0cr'"; "0e"; "0ebs"; "0fx"; "0fx'"; "0g"; "0g'"; "0hh"; "0hi"; "0hi'"; "0hl"; "0i"]; ["0k"; "0kn"; "0lo"; "0lo'"; "0model"; "0model'"; "0nb"; "0payload"; "0ptr"; "0ra"; "0rd"; "0scfg"; "0scr"; "0so"; "0sp0"; "0sr"]; ["MBV"; "MZ_to_bv"; "Mbv"; "Mbv_unsigned"; "0stk"; "0v"; "0vals"; "0vals'"; "0vbnd"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition IMG_LIB_A : list (Z * Z) :=
[(0x10000, 0x136000); (0x138ac0, 0x139380); (0x65f090, 0x66f0c0); (0x66f0c2, 0x66f2f0); (0x6701b0, 0x670a68);
(0x670a70, 0x670ab8); (0x670ad4, 0x670ae8); (0x670af0, 0x690b10); (0x690d30, 0x691f78); (0x691f80, 0x693000)].
Definition LIB_HOLES : list (Z * Z) := [(0x66f0c0, 0x66f0c2); (0x66f2f0, 0x6701b0); (0x690b10, 0x690d30)].
Definition keep_libA (so sc : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
kn_keep 0 so sc bls vbnd [] IMG_LIB_A IMG_RW_A kn.
Section SE.
Local Abbreviation SEC_T_img_lib_sub := (ltac2:(TCodec.tc2 tcn__Jb0DrvLibL "Q@'I&S6'=%1233(<r2r1%347721&QN%83621'@'B&R1%<3:61&S9r5%22;1r4%421<%9231%:271qWLE1%;2F1qX8G1%=2H1+RPP0r3%=221+Vb\P0%?2H1%@24I&QO%O3MI1'D%D2C8r6%F2O1%4231p061pWHQ71pWNQ81%O2;1%Q02=1%Q12@1%Q22D1p0Q41pWJQ>1pX6Q?1")) (only parsing).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_img_lib_sub) 0%nat 0%nat).
Variable hi : ltac:(sec_ty2 constr:(SEC_T_img_lib_sub) 1%nat 0%nat).
Lemma img_lib_sub : ltac:(sec_stmt2 constr:(SEC_T_img_lib_sub) 2%nat 0%nat).
Proof.
intros Hin.
unfold IMG_LIB_A in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-;
(split; [first [ (exists 0x10000, 0x136000; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
| (exists 0x138ac0, 0x139380; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
| (exists 0x65f090, 0x670a68; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
| (exists 0x670a70, 0x670ab8; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
| (exists 0x670ad4, 0x670ae8; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
| (exists 0x670af0, 0x691f78; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
| (exists 0x691f80, 0x693000; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia]) ] |]);
(split; [lia|]); (split; [lia|]); (split; [lia|]);
intros hl hh Hh; unfold LIB_HOLES in Hh; cbn [In] in Hh; repeat (destruct Hh as [Hh|Hh]; [injection Hh as <- <-; lia|]); destruct Hh |]).
destruct Hin.
Qed.
End SE.
Record drv_lib_layoutA (Lay : lib_layoutA) (L : asan_layout) : Prop := DRV_LIB_LAYOUTA {
dlla_L : lla_L Lay = L;
dlla_entry : lla_entry Lay = 0xa791c;
dlla_gp : lla_gp Lay = 0x10800;
dlla_stack : 4096 <= lla_stack Lay <= 2 ^ 20 /\ lla_stack Lay mod 8 = 0;
dlla_empty : lla_empty Lay = 0x66f0a0;
dlla_foot : forall iv, In iv (lla_foot Lay) -> exists hl hh, In (hl, hh) LIB_HOLES /\ hl <= fst iv /\ snd iv <= hh;
dlla_junk : forall iv, In iv (lla_junk Lay) -> exists hl hh, In (hl, hh) LIB_HOLES /\ hl <= fst iv /\ snd iv <= hh;
dlla_credit_pos : forall n, 0 <= n -> 0 <= fst (lla_credit Lay n) /\ 0 <= snd (lla_credit Lay n);
dlla_frames : forall k, In k [0; 1; 2; 3; 4] -> 0 <= lla_leak Lay k /\ 4 * lla_leak Lay k + lla_frames Lay k <= ff_cap k
}.
Lemma regs_ok_upd_sameA : ltac2:(TCodec.tc2 tcn__Jb0DrvLibL "Q='RK'8'RL%211&Q7y5'TByR0%211%5241%415&S1r5r4r3%43321&C'A(T@z(?%33@21%53<81%711&RJr7%221<&RA%12@?%<3E31r8&RO&RN%11E%3391Er6%I3621p081p0?1p0H1pW<Q61pXFO1pRHQ11pY0Q81pQFQ<1").
Proof.
intros E sr R rd e HR Hrd He r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. exact HR.
- rewrite nth_sr_upd. destruct (Nat.eqb (ridx r) (ridx rd)) eqn:Hi.
+ apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r. symmetry. exact He.
+ specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. exact HR.
Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section LibSite.
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
Variable M0 : word -> option byte.
Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
Variable Lay : lib_layoutA.
Variable LSt : lib_statics.
Hypothesis DLL : drv_lib_layoutA Lay L.
Hypothesis LIok : lib_call_okA Lay ar scfg HI LSt.
#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation LV := (lib_view Lay ar).
#[using="L sp0 Hsp DLL"] Lemma not_foot_of_hole : ltac2:(TCodec.tc2 tcn__Jb0DrvLibL "Q0'I&S6'=%1233(<r2r1%347721&QO%83621&C'@&S9r3r4%3221&S:%123<%7231%911p0;1pWHE1pWNF1&R6&R:vQ3vS@%3221%521G%C11p081pW0O1").
Proof.
intros a Hn (iv & Hin & Hr). cbn [lib_view ll_foot] in Hin. destruct (dlla_foot Lay L DLL iv Hin) as (hl & hh & Hh & H1 & H2).
apply (Hn hl hh Hh). lia.
Qed.
#[using="L sp0 Hsp DLL"] Lemma not_foot_off_image : ltac2:(TCodec.tc2 tcn__Jb0DrvLibL "F'I&C'@&S9+V[lT@r1%3221&S:+Vb\P0%2241%8241%:11&R6&R:vQ3vS@%3221r2%6221%B11p091pW0E1").
Proof.
intros a Ha. apply not_foot_of_hole. intros hl hh Hh. unfold LIB_HOLES in Hh. cbn [In] in Hh.
repeat (destruct Hh as [Hh|Hh]; [injection Hh as <- <-; lia|]). destruct Hh.
Qed.
#[using="L sp0 Hsp DLL"] Lemma not_junk_of_hole : ltac2:(TCodec.tc2 tcn__Jb0DrvLibL "M'I&S6'=%1233(<r2r1%347721&QO%83621&C'@&S9r3r4%3221&S:%123<%7231%911p0;1pWHE1pWNF1&R9vQ3%221D%@11p051pW0L1").
Proof.
intros a Hn (iv & Hin & Hr). destruct (dlla_junk Lay L DLL iv Hin) as (hl & hh & Hh & H1 & H2).
apply (Hn hl hh Hh). lia.
Qed.
#[using="L sp0 Hsp DLL"] Lemma not_junk_off_image : ltac2:(TCodec.tc2 tcn__Jb0DrvLibL "C'I&C'@&S9+V[lT@r1%3221&S:+Vb\P0%2241%8241%:11&R9vQ3r2%3221%?11p061pW0B1").
Proof.
intros a Ha. apply not_junk_of_hole. intros hl hh Hh. unfold LIB_HOLES in Hh. cbn [In] in Hh.
repeat (destruct Hh as [Hh|Hh]; [injection Hh as <- <-; lia|]). destruct Hh.
Qed.
Definition CPl (LBc : list (Z * Z)) (sp scr : Z) (H H' : word -> bool) (a : Z) : Prop :=
(aclient L ar LBc [] sp scr a /\ ~ in_foot LV a /\ ~ in_junk Lay a) /\ H (Z_to_bv 64 a) = false /\ H' (Z_to_bv 64 a) = false.
#[using="scfg C IL HIok Hsp DL DLL"] Lemma regions_callL : ltac2:(TCodec.tc2 tcn__Jb0DrvLibL "T>'8'TByR0%211%411'9y8%611%811p041'I'=%1272%=11%3244%?11&QE%A11&Q@';%11=p0B1'Q5'RK(RI&S4rA%211r@%5221'ArB(2%8221vT>%53Q021'@&S9&S=&S>+2+F%3221%511%721Bz%92D1%;231%;23F+E%;2:1%>2I1%@241&QGvLr?(:%11Q9r>r<r:r8&QHr6%211%<8;:876541%=8<Q6987652%Q@1QI&Q>r2rE%3221(3r1%22R01%Q=3841&QLvNvS@rD&TCrJr3%QJ221%42RB1%958761@p0;1pX>R=1pX0RC1rK%R1218%;2RI1%QG21Gp0B1pW4RD1pY<RJ1'Q?&S5rGrF%Q<1RO&QN&R2&QMrC&S8%J2S8R8%2219&QB%12QCQAr=r9%4221%:596>41&QI%128@%D<CRDBAQ>Q5@?>QG31p0F1p0N1p0QE1p0QG1p0R51p0R;1p0RH1tQFS5RO1pX<S71pX:S81pRDS:1pRBS;1p4SB1p2SC1pW:SA1pW8SB1pR4SD1pR2SE1pR0SH1pYBSK1pW6SL1pXJT01pXLT11pW>T31pY>T91").
Proof.
intros vals ebs so scr bls vbnd LB LK LK' cr cr' A A' M M' model model' E P0 Hso Hscr HH HH' Hbl Hvb.
pose proof Hsp as Hsp'.
assert (VIS : forall a, 0 <= a < 2 ^ 64 -> (a < 0x693000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LB a) ->
ahid A model (Z_to_bv 64 a) = false /\ ahid A' model' (Z_to_bv 64 a) = false).
{ intros a Ha Hc. split.
- apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH Ha). destruct Hc as [Hc|[Hc|Hc]]; auto.
- apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH' Ha). destruct Hc as [Hc|[Hc|Hc]]; auto. }
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CPl. split; [split|apply VIS; lia].
+ unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). lia.
+ split; [apply not_foot_off_image | apply not_junk_off_image]; lia.
- intros z Hz. right. unfold SCa. lia.
- intros i nb Hf. pose proof (sub_blockA_hz L ar IL sp0 DL _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HB) as (Y1 & Y2 & Y3).
split; [lia|]. intros z Hz.
assert (IB : in_block LB (bv_unsigned (vals_ev vals i) + z)).
{ exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia. }
unfold CPl. split; [split; [left; exact IB | split; [apply not_foot_off_image | apply not_junk_off_image]; lia] | apply VIS; [lia | right; right; exact IB]].
- exact Hvb.
- intros i [].
- intros lo hi Hin. destruct (img_lib_sub lo hi Hin) as ((lo' & hi' & Hin' & S1 & S2) & I1 & I2 & I3 & HOLE).
split; [lia|]. split; [lia|]. intros a Ha. unfold CPl. split; [split|apply VIS; lia].
+ unfold aclient. right. right. left. rewrite (dla_img_lo L ar IL sp0 DL), (dla_img_hi L ar IL sp0 DL). split; [lia|].
apply (dla_client L ar IL sp0 DL lo' hi' a Hin'). lia.
+ split; [apply not_foot_of_hole | apply not_junk_of_hole]; intros hl hh Hh; destruct (HOLE hl hh Hh); lia.
- intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
intros Mx d m Hd Hm.
apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x65f090) (Z_to_bv 64 d) 65536%nat m 0x65f090 0x66f090);
first [exact (wseg_stage) | reflexivity | lia | (rewrite u_small by lia; lia)].
Qed.
Section SE.
Local Abbreviation SEC_T_alib_site := (ltac2:(TCodec.tc2 tcn__Jb0DrvLibL "^F'8'TByR0%211%411'9y8%611%811p041'RL%;11'RM%=11&Q7y5%221=';%11;p0@1'Q5'='I%2211%H11&QE%J11&Q@&R8vQ2%211%:2J9%Q011'Q6%Q211!pYD21'RK(RI&S4rD%211rC%5221&S1r1rA%33251&S0&S5r2&Q=&QBr<r@%3221%521:%94871?'A'5&S3&7rG%22QL1rE%5221(>%93821&S2rH%92R31%3217%>3=16'Fu1rI%?2R91%4231rJ(2%Q9221vT>%H3R?21&QK%11?%K3J1C&RA(T@+2(?%33R;21%52F1&TA&S8&TC%12RM>%321Q:%52RO1%Q83RO71'@&S9&S=&S>+E%22@1%411%621QLz%82QN1%:231&S;rB+@%3221%QH3RL17&R?vQ3%211%B217%C28?%E221rL+1%Q43S<1Q2%Q6231r?%Q22SL1%R53SL31%L2ER:&S:+Q?%M2Q;1%32R>1%Q2251%H2RHQ>%R=3SA1LrO+3%QC3SK1QA%QE231+RRP0%QA2T;1%RD3T;31rQ0+4%QJ3T21QH%QL231+V^Rf0%QH2TB1%RK3TB31rQ1+:%R13T91QO%R3231%QN2THRJ%S13TH21rQ2+;%R73T?1R5%R9231&S<%S42TJSI%211%R72U11%S:3U151%S82TNS5%611+J%R22R@1%Q8231'DrF%S?2U51%SC3U81RN&R<%11QK%SF3TJS;1%R>241%B16%QB2R81&S6(<%14U0U0SA4%33U01Q1%RE251%?281%U91UB&RCrQ4%S12UKSB%T12UGT0%44T>321(3%12UIT3%T83831&R4&R;%T82UNT0%Q611%32RC1%521QB(6(:%11UE%33UFQL1%43UGR41%53UHSF1%63UIRE1%73UJS51%M3UKU41&QDrQ5%22U21%QE11&R=%12S3U5%SK231&QC%11U8%SG231p0;1pX2V71&R7rQ7%23V3R:1'QJvS@vLvQ:rQ6rQ3rQ8%7:65TG43EQ<219%VH1VC&Q>%12UIR?%Q<2VFUO%UC3421&Gr3rQA%UD2W>1%4231&QLvNrQ:%V?267%TI2WE1%554F31V6%TF271p0=1pX>W51pX0WG1rQB%V12WK1%A2@1%VI23A%U32WO1%TN21V@%U0241p0G1pW4W?1pY<X11rM%QN1W7%211'R@&4rQI&RFr7%211%53X=41%W:1W4%W<216%VF2X@W1&ErQK%VI2XC1uQ0%4221%VO3XD61&RO&RGrQJ&H%XM1X?&RN&R3%443XL21rQL%W62Y01%93831%61T=(RH%11UL%>3431r:%WN3WH21r5r9%WI221%WK215&R0rQ@rQ?rQ>%45R3321G%X44X3R561rQGr8r6r;%RH:RGRFW8RE4Q;321@&QF%12Q?3&S7rQF%23Y718%S=2X=X:%U011%S?2X?Q<%U211&R>%12V@XB%W8231%W2261p0SF1pX2YB1r=%S<3Y=1V=&R5%X?2Z5RL%U=11%T:2VJ1%42QC1%T=217%W=2WBY4%VA2Y5V?%W@221%WH2ZBY2%Y;11rR1%113%XN3Z631p061pW0Z41%WG2W@Y>+R0%WG2X51%VM2YA1%WL241&QArR0%221Y@%X72[1SD%Y411rR3%113%Y=3ZE31p061p0:1pW0ZD1%UF4ZEZESLYI&QN%UI3ZF21r4%X;21YM%W?2YNT1%X>221%Y=1?rR6%11A%YK3[331p051p0:1pW0[21pWJ[31pX6[41'REvT;(Q4&RB%Y32[MR2&RD%11Z@%45VGZ23ZJ1%621ZIrQD%:4ZD921p0<1p0M1p0Q>1p0QI1p0R01p0R31p0R>1p0RB1p0RE1p0RK1p0S61p0SH1tQH[=T01tY@\?T31p4[L1pR4[K1pW:[K1pWF[I1pX<\41pRD\61pRJ\:1pWBTA1vSG+dnXL%Z22\L1rQ=%Q254S>21OrQ<%Q5221%Q84[BQ71XKp091p0TL1p0U01p0U;1p0V01p0V91p0V=1p0W31p0W:1p0WD1p0X51p0X;1p0XE1p0XL1p0Y41p0Y<1p0Y?1p0YF1p0YN1p0Z51p0Z;1p0ZG1p0[51p0[91p0[?1p0[E1p0[K1p0\61p0\A1tQF\L\F1pQL\N1pX@]K1pXD]>1pXB]?1pYB]61pW6]71pY:]B1pXL]C1pWD]<1p2]C1pW8]A1pR2]C1pR0]F1pX:]K1pRB]M1pRH^11pX4^51pY0^81pW>^;1pY>^A1")) (only parsing).
Variable vals : ltac:(sec_ty2 constr:(SEC_T_alib_site) 0%nat 0%nat).
Variable ebs : ltac:(sec_ty2 constr:(SEC_T_alib_site) 1%nat 0%nat).
Variable sr : ltac:(sec_ty2 constr:(SEC_T_alib_site) 2%nat 0%nat).
Variable kn : ltac:(sec_ty2 constr:(SEC_T_alib_site) 3%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_alib_site) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_alib_site) 5%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_alib_site) 6%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_alib_site) 7%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_alib_site) 8%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_alib_site) 9%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_alib_site) 10%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_alib_site) 11%nat 0%nat).
Variable so : ltac:(sec_ty2 constr:(SEC_T_alib_site) 12%nat 0%nat).
Variable stk : ltac:(sec_ty2 constr:(SEC_T_alib_site) 13%nat 0%nat).
Variable bls : ltac:(sec_ty2 constr:(SEC_T_alib_site) 14%nat 0%nat).
Variable vbnd : ltac:(sec_ty2 constr:(SEC_T_alib_site) 15%nat 0%nat).
Variable ptr : ltac:(sec_ty2 constr:(SEC_T_alib_site) 16%nat 0%nat).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_alib_site) 17%nat 0%nat).
Variable payload : ltac:(sec_ty2 constr:(SEC_T_alib_site) 18%nat 0%nat).
Variable K : ltac:(sec_ty2 constr:(SEC_T_alib_site) 19%nat 0%nat).
Lemma alib_site : ltac:(sec_stmt2 constr:(SEC_T_alib_site) 20%nat 0%nat).
Proof using C IL HIok Hsp Hal DL M0_def DLL LIok vals ebs sr kn R M model LB LK cr A g so stk bls vbnd ptr ra payload K.
intros E HR HK Hsv Hkv HL1 P0 Hiw
R2 Hso Hsoal Hstk R1 Hra Hra2 R3 R4 R10 R11 Hlen Hptr Hpay Hcr Hroom Hls DI Hbl Hvb HK0 CONT.
pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
pose proof (dinv_stack_defined scfg L ar C HI HIok sp0 Hsp M0 M0_def _ _ _ _ _ _ DI) as Hdef.
pose proof Hsp as Hsp'. pose proof Hal as Hal'. destruct (dlla_stack Lay L DLL) as ((ST1 & ST2) & ST3).
set (sp := bv_unsigned sp0 + so) in *.
assert (WDEF : forall a, bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 -> M (Z_to_bv 64 a) <> None)
by (exact (window_defined sp0 Hsp vals ebs (ahid A model) M kn HK Hiw P0)).
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & (B4096 & TOPEQ & _ & _) & TOP47 & _).
pose proof (LIok fx g LB [] LK cr A sp ptr ra payload R M model K) as MS.
unfold lib_cfgA in MS. rewrite (dlla_L Lay L DLL), (dla_segs L ar IL sp0 DL), (dlla_entry Lay L DLL) in MS.
apply MS; clear MS; try assumption.
-
constructor; rewrite ?(dlla_L Lay L DLL), ?(dla_segs L ar IL sp0 DL), ?(dla_tp L ar IL sp0 DL), ?(dlla_gp Lay L DLL); try assumption.
+ split; [exact Hra | exact Hra2].
+
rewrite (dla_sptop L ar IL sp0 DL). unfold sp.
split; [rewrite Z.add_mod, Hal', Hsoal by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
* intros i Hi. apply WDEF. lia.
* intros i Hi. destruct (Z_lt_le_dec (bv_unsigned sp0 + so + i) (bv_unsigned sp0)) as [Hlo|Hhi].
-- apply WDEF. lia.
-- replace (bv_unsigned sp0 + so + i) with (bv_unsigned sp0 + (so + i)) by ring. apply Hdef. lia.
+ intros f [].
+
intros j Hj. apply (di_stksh _ _ _ _ _ _ _ _ _ _ DI). unfold STKTOP, in_shadow_of, S, SB. rewrite (dla_sptop L ar IL sp0 DL) in *.
set (mx := Z.max (bv_unsigned sp0) (ar_stack_top ar)) in *.
replace (bv_unsigned sp0 - 8388608 + (mx - (bv_unsigned sp0 - 8388608)) - 1) with (mx - 1) by ring.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
unfold sp in *. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
-
intros fx' g' R' M' model' cr' LK' A' POST HRT HINC Hh' HMI' HLEAK HH'.
destruct POST as [Qa0 Qregs Qcr Qframe Qscr Qgrows Qstk Qls].
rewrite ?(dlla_L Lay L DLL) in *.
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
assert (FR : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB [] sp stk a -> ~ in_foot LV a /\ ~ in_junk Lay a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha Hc [Hf Hj]. apply Qframe; [exact Ha | | exact Hf | exact Hj]. apply (aclient_scr_mono L ar sp0 Hsp LB [] sp stk (lla_stack Lay) a); [lia | exact Hc]. }
assert (ABOVE : forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha. apply FR; [lia | | split; [apply not_foot_off_image | apply not_junk_off_image]; lia]. unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). unfold sp. lia. }
apply (CONT fx' R' M' model' g' cr' LK' A' HL'); try assumption.
+
apply regs_ok_upd_sameA; [| discriminate | cbn [edenot]; symmetry; exact Qa0].
apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA sp0 Hsp R R' Qregs) c_kept_no0A).
+
unfold keep_libA.
pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
refine (know_keep_sound ASEGS 0 so stk bls vbnd [] IMG_LIB_A IMG_RW_A
(Env (vals_ev (vals ++ junk_vals R')) ebs)
(CPl LB sp stk (ahid A model) (ahid A' model')) (SCa sp stk)
_ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
* eapply (regions_callL (vals ++ junk_vals R') ebs so stk bls vbnd LB LK LK' cr cr' A A' M M' model model');
[exact P0' | lia | lia | exact HH | exact HH' | | ].
-- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
-- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
* intros a Ha ((HC & HF) & V1 & V2). unfold mrestrict. rewrite V1, V2. apply FR; assumption.
* intros a HS. unfold SCa in HS. unfold mrestrict.
rewrite (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH') by (unfold sp in *; lia).
destruct (Z_lt_le_dec a (sp - lla_stack Lay)) as [Hlo|Hhi].
-- rewrite Qframe; [apply WDEF; unfold sp in *; lia | unfold sp in *; lia | | apply not_foot_off_image; unfold sp in *; lia | apply not_junk_off_image; unfold sp in *; lia].
unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). unfold sp in *. lia.
-- replace a with (sp - lla_stack Lay + (a - (sp - lla_stack Lay))) by ring. apply Qscr. lia.
+
apply DINV; [exact HH' | exact HMI' | exact Hh' | | |].
* intros a Ha. rewrite (ABOVE a Ha). exact (di_above _ _ _ _ _ _ _ _ _ _ DI a Ha).
* intros x Hx. destruct (stksh_rng scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ _ x HH Hx) as (XR & XC).
unfold STKTOP, in_shadow_of, S, SB in Hx. rewrite (dla_sptop L ar IL sp0 DL) in Hx.
set (mx := Z.max (bv_unsigned sp0) (ar_stack_top ar)) in *.
replace (bv_unsigned sp0 - 8388608 + (mx - (bv_unsigned sp0 - 8388608)) - 1) with (mx - 1) in Hx by ring.
destruct (Z_lt_le_dec x (S (sp - lla_stack Lay))) as [Hlo|Hhi].
-- unfold byte_at. rewrite FR; [exact (di_stksh _ _ _ _ _ _ _ _ _ _ DI x ltac:(unfold STKTOP, in_shadow_of, S, SB; rewrite (dla_sptop L ar IL sp0 DL); fold mx;
replace (bv_unsigned sp0 - 8388608 + (mx - (bv_unsigned sp0 - 8388608)) - 1) with (mx - 1) by ring; exact Hx)) | lia | | split; [apply not_foot_off_image | apply not_junk_off_image]; lia].
unfold aclient. right. right. right. right. left. exact XC.
-- replace x with (S (sp - lla_stack Lay) + (x - S (sp - lla_stack Lay))) by ring. apply Qstk.
rewrite (dla_sptop L ar IL sp0 DL). fold mx. unfold S, SB in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
unfold sp in *. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
* intros x Hx. pose proof (hish_rng L ar IL sp0 Hsp DL x Hx) as XR. unfold byte_at.
rewrite FR; [exact (di_hish _ _ _ _ _ _ _ _ _ _ DI x Hx) | lia | unfold aclient; right; right; right; right; left; exact Hx | split; [apply not_foot_off_image | apply not_junk_off_image]; lia].
+ intros a Ha Hb. apply FR; [exact Ha | left; exact Hb |].
destruct Hb as (b & Hb & Hr). destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _). destruct (WF b Hb) as (HBR & _).
pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR) as (Y1 & Y2 & Y3). split; [apply not_foot_off_image | apply not_junk_off_image]; lia.
+ intros lo hi a Hin Ha. destruct (img_lib_sub lo hi Hin) as ((lo' & hi' & Hin' & S1 & S2) & I1 & I2 & I3 & HOLE).
apply FR; [lia | | split; [apply not_foot_of_hole | apply not_junk_of_hole]; intros hl hh Hhol; destruct (HOLE hl hh Hhol); lia].
unfold aclient. right. right. left. rewrite (dla_img_lo L ar IL sp0 DL), (dla_img_hi L ar IL sp0 DL). split; [lia|].
apply (dla_client L ar IL sp0 DL lo' hi' a Hin'). lia.
Qed.
End SE.
End LibSite.
End FPX_1.
