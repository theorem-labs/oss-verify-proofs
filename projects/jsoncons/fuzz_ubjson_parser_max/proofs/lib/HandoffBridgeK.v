(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec AgentLib AsanAcct BackingAlgebra AsanPlacement AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__HandoffBridgeK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3SoundK.AX2SK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BackingAlgebra."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffBridgeK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffBridgeK.Generic."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffBridgeK.Image."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1O"; "1Some"; "1andb"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1negb"; "1nil"; "1option"]; ["1orb"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3le"; "3lt"; "4Forall"; "4map"; "4nth"; "5Z"]; ["0E"; "0FS0"; "0FULL"; "0HSc"; "0HSf"; "0K"; "0LIMIT"; "6Fs"; "7store_ok"; "7word_to_le_bytes"; "8entry_stack_image"; "8segments_reserved"; "9build_stack_bytes"; ":FdEntry"; ":Model"; ":m_fds"]; [":m_fs"; ":m_halted"; ":m_tid"; ":m_vm_lazy"; ":m_vmmaps"; ":maps_subtract"; ":page_base"; ":page_in_ranges"; ":sp_window_hi"; ":sp_window_lo"; ":vm_brk"; ":vm_init_sp"; ":vm_limit"; ":vm_maps"; ":vm_noaccess"; ":vm_reserved"]; [":vm_start_brk"; ";bvmap"; "0R"; "<A_bytes"; "<A_wf"; "<MInv"; "<eager_used"; "<range_avoids"; "=E0"; "=LIMIT"; "=SINV0"; "=argH0"; ">FdStd"; ">HCons"; ">HSub"; ">KNONE"]; [">KNONELAZY"; ">KRWLAZY"; ">NX0"; ">PID_MAX"; ">a_abytes"; ">a_brk"; ">a_eager"; ">a_fd"; ">a_ghost"; ">a_hlz"; ">a_hna"; ">a_maps"; ">a_ss"; ">a_tidset"; ">a_totsz"; ">a_vis"]; [">acs"; ">afd"; ">am_base"; ">am_kind"; ">am_len"; ">amap"; ">e_sp0"; ">e_sppg"; ">hop"; ">img_hi"; ">img_lo"; ">kentry_eqb"; ">kn"; ">mkind"; ">no_fog"; "?Mr"]; ["?allowA"; "?amap_den"; "?cs_ok"; "?fds_std"; "?hid"; "?hreplay"; "?in_ghost"; "?in_hull"; "?in_ivs"; "?pagedown"; "?seps"; "?sum_sizes"; "?uE"; "?utop"; "?vis"; "@KAlign"]; ["@KDisj"; "@KFill"; "@KImg"; "@KRange"; "@KUnk"; "@KWord"; "@KWr"; "@KZero"; "@SA"; "@adenot"; "@edenot"; "@env"; "@ev"; "@expr"; "@kentry"; "@lin_nowrapR"]; ["@s_regs"; "@saddr"; "@sr_get"; "@xhi"; "@xlo"; "AelenZ"; "Aestart"; "Aflat"; "Akentry_ok"; "BB"; "BS"; "Bmodel_ivs_wf"; "Dallow1Z"; "DamapZ"; "Damaps_lin"; "Dkfind_at"]; ["Dkfind_fill"; "Dkfind_img"; "Dkfind_ranges"; "Dkfind_word"; "Dkfind_wr"; "Dkfind_zero"; "Dvis_lin"; "EMAPS"; "EWsb"; "CLZ"; "CVZ"; "Callow1Z"; "CamapZ"; "Fgetr"; "Frdn"; "Fwrap_mem"]; ["0SEGS"; "0SINV"; "GIn"; "Gexistsb"; "Gflat_map"; "Hadd"; "Hdiv"; "Hle"; "Hleb"; "Hlt"; "Hltb"; "Hmodulo"; "Hmul"; "Hof_nat"; "Hpow"; "0a"]; ["0a0"; "0a1"; "0a2"; "0argH"; "0argv"; "0b"; "0brk0"; "0bs"; "0c"; "0ch"; "0cs"; "0d"; "0e"; "0envp"; "0fs"; "0h"]; ["0hi"; "0hw"; "0i"; "0iv"; "0j"; "0k"; "0lo"; "0m"; "0model"; "0n"; "0n1"; "0n2"; "0off"; "0ph"; "0r"; "0rdraw"]; ["0sp"; "IZ_to_bv"; "Ibv"; "Ibv_unsigned"; "0t"; "0uid"; "0v"; "0w"; "0z"]]).
Definition VZ (E : env) (n : nat) : Z := bv_unsigned (ev E n).
Definition LZ (E : env) (e : expr) : Z := lden E (lin_of e).
Section Generic.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation MR := (Mr A argH).
#[local] Notation HID := (hid A argH).
Lemma hb_kn : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q>'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T>'SBvU@v0vQ6vUAvV3vQ1r6r5r4r3r2%<;;:987654321&UB&S<%118%33A51&THr8&S?r7%26C@31<=%54E41<p071p0<1pR<J1p]BL1pR6N1pT6Q41p\FQ;1pR2Q=1").
Proof. intros E cs R FULL model K HC Hin. exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) K Hin). Qed.
Lemma hb_knb_In : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "C'T>';%112'F'6&UC&S;r2%211r1%53:21(D%93821&UBr3%23?18p041p]<?1pR<B1").
Proof.
intros K k H. apply existsb_exists in H as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'. exact Hin.
Qed.
Lemma hb_knb : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QD'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T>'SBvU@v0vQ6vUAvV3vQ1r6r5r4r3r2%<;;:987654321'F'6&UC&S;%116&S<%11<%53E31(D%93821&THr8&S?r7%26IF31BC%54K41Bp071p0B1pR<Q01p]BQ21pR6Q41pT6Q:1p\FQA1pR2QC1").
Proof. intros E cs R FULL model K HC H. exact (hb_kn E cs R FULL model K HC (hb_knb_In K _ H)). Qed.
Lemma hb_mr_some : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q3'T;'S0'Q>'W2yR0%211'?y8%511%311p051'F&S?v0vV3r6r5r4r3r2%877654321(3r1%22?1%=3?41%817%52B7%@3B21p041p\<E1p\0I1pR6E1p]BN1p\FQ01pR2Q21").
Proof. intros E cs model FULL a b H. unfold Mr, mrestrict in H. destruct (HID E cs model a); [discriminate| exact H]. Qed.
Lemma hb_mr_visible : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q6'T;'S0'Q>'W2yR0%211'?y8%511%311p051'F&S?v0vV3r6r5r4r3r2%877654321(3r1%22?1%=3?41'6&SDr7%26?>1=<:(8%C3521p071p\<H1p\0L1pR6H1p]BQ11p\FQ31pR2Q51").
Proof. intros E cs model FULL a b H. unfold Mr, mrestrict in H. destruct (HID E cs model a); [discriminate| reflexivity]. Qed.
Lemma hb_mr_rdn : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QC'T;'S0'Q>'W2yR0%211'?y8%511%311p051'<';%115'F%912&U>vU@&S?v0vV3r7r6r5r4%76654321r3r2%<4;321(3r1%22B1%B3A41'E%B4A;:8%62F8%F3E21&R7&SDr8%25ED1CB%431A?%9261p0;1p\@O1p]DQ21p\0Q91pR6Q51p]BQ>1p\FQ@1pR2QB1").
Proof.
intros E cs model FULL a n bs H. unfold Mr in H. rewrite <- ov_rdn in H |- *.
exact (ov_read_bytes_restrict SEGS _ (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) n FULL a bs H).
Qed.
Lemma hb_mr_store_ok : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q='T;'S0'Q>'W2yR0%211'?y8%511%311p051'<'F'6&Q8vU@&S?v0vV3r6r5r4r3%76654321r2r1%<4;321(D%@3?21'E%@4?986%C3B14&R7&SDr7%25BA1@?%431><%8261p0:1p]DL1p\0Q31pR6O1p]BQ81p\FQ:1pR2Q<1").
Proof.
intros E cs model FULL a n H. unfold Mr in H.
exact (store_ok_restrict SEGS _ (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) n FULL a H).
Qed.
Lemma hb_mr_hull : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q5'T;'S0'Q>'W2yR0%211'?y8%511%311p051'F'6&SGv0&W3r1%22=1%5241(D%93821&S?vV3r6r5r4r3r2%77>654321%312%C3E21p0;1p\0K1pR6G1p]BQ01p\FQ21pR2Q41").
Proof. intros E cs model FULL a H. unfold Mr, mrestrict. rewrite (hid_hull A HULL_ok argH argH_high E cs model a H). reflexivity. Qed.
Lemma hb_lin : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QE'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T='SBvU@v0vQ6vUAvV3vQ1r6r5r4r3r2%<;;:987654321'F'6&T?&S<%11:%3217(D%73621'O&W3&T:r8%221?%42Q41&U9%124B%@3831p0:1p0C1p\JQ11p]BQ31pR6Q51pT6Q;1p\FQB1pR2QD1").
Proof. intros E cs R FULL model e HC H. exact (lin_nowrapR_sound SEGS E _ (kn cs) e (co_know _ _ _ _ _ _ _ _ _ _ _ HC) H). Qed.
Lemma hb_xlo : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QG'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T='O'SBvU@v0vQ6vUAvV3vQ1r7r6r5r4r3%<;;:987654321'F%F1?&TD&S<%11:%3217(3r2%22F1%93841&UG&W3&T:r9%221A%42Q71%62B1p081p0C1p]>Q11p\JQ31p]BQ51pR6Q71pT6Q=1p\FQD1pR2QF1").
Proof. intros E cs R FULL model e lo HC H. exact (xlo_sound SEGS E _ (kn cs) e lo (co_know _ _ _ _ _ _ _ _ _ _ _ HC) H). Qed.
Lemma hb_xhi : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QG'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T='O'SBvU@v0vQ6vUAvV3vQ1r7r6r5r4r3%<;;:987654321'F%F1?&TC&S<%11:%3217(3r2%22F1%93841&UG&W3&T:r9%221A%42Q71%621Bp081p0C1p]2Q11p\JQ31p]BQ51pR6Q71pT6Q=1p\FQD1pR2QF1").
Proof. intros E cs R FULL model e hi HC H. exact (xhi_sound SEGS E _ (kn cs) e hi (co_know _ _ _ _ _ _ _ _ _ _ _ HC) H). Qed.
Lemma hb_bounds_e : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R1'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T='O'SBvU@v0vQ6vUAvV3vQ1r8r7r6r5r4%<;;:987654321'F%F1?&TD&S<%11:%3217(3r3%22F1%93841&TCr9%911%321@%>3=16'E&UG&W3&T:r;%221H%42Q=1%62I1%722I%9221p0;1p0A1p0L1p]2Q:1p]>Q;1p\JQ=1p]BQ?1pR6QA1pT6QG1p\FQN1pR2R01").
Proof. intros E cs R FULL model e lo hi HC H1 H2. split; [eapply hb_xlo; eassumption | eapply hb_xhi; eassumption]. Qed.
Lemma hb_estart : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "F'T;'T='O'F&TFr3(T8r2r1%3221%6251&UE&W3yR0&T:%12:8%4231%6219%?3@81p]JA1p\<C1pR2E1").
Proof. reflexivity. Qed.
Lemma hb_adenot : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "H'T;'TA'O&TGr3r2r1%43321'F'W2yR0%211&T9r4%221:&W1&TF%124=%3281%;3851p0=1p]DC1p\0E1pR2G1").
Proof.
intros E a n Hf. apply bv_eq. rewrite (flat_u E a n Hf). destruct Hf as (H1 & H2 & _).
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [reflexivity|]. cbn. lia.
Qed.
Lemma hb_word : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "RA'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'TA'<'T='SBvU@v0vQ6vUAvV3vQ1r8r7r6r5r4%<;;:987654321&UB'T>(T5r3r2%33721&S<%11=%83731'E'Ju8%22>1&TGr:&UM%11B%433D1'F';%11Q8%Q;11&U>&T9%12:K%34Q5N1K(3&Q9&T:%12?J%32Q01%52;1%>3;71&R7&SDr9%25Q?Q<F1Q8%431=Q7%M261%N2F1%O2L1p0Q11p0Q;1p^>QI1p^@QK1p\0QM1p]BQO1pR6R11pT6R71p\FR>1pR2R@1").
Proof.
intros E cs R FULL model a w v HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as (Hw & Hf & Hr).
destruct (hb_mr_rdn E cs model FULL _ _ _ Hr) as [H1 H2]. auto.
Qed.
Lemma hb_rdn_bytes : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R9'W2yR0%211'?y8%511%311p051'<';%115'F%912&U>vU@r4r2r3%544321(3r1%22;1%;3:41&Kr5%2251'6&SGv0&UE&W3%12N7&UM%11A%5231%8271(8%J3;21p0=1p]:O1&UG%;2Q8J%:1B%>221&UN+2+R0%3221%8251r7%K2N1r9&W1%G2QD4%I21E%32QF1%511&Nr6z%82QH1%44QHQ=31%Q;2QI1%QD3QI71p0>1p]:QI1p0B1p0L1p0Q>1p\@QK1p\2R41p]DQO1pR6R11").
Proof.
intros FULL n. induction n as [|n IH]; intros a0 bs Hrd Hh Hnw j Hj; [lia|].
cbn [rdn] in Hrd.
destruct (FULL a0) as [b|] eqn:Hb.
- destruct (rdn SEGS FULL (a0 + 1)%bv n) as [rest|] eqn:Hr2; [|discriminate]. injection Hrd as <-.
destruct j as [|j].
+ cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hb.
+ cbn [nth]. pose proof (u64_range a0).
assert (Hu1 : bv_unsigned (a0 + 1)%bv = bv_unsigned a0 + 1) by (apply u_add1; lia).
replace (bv_unsigned a0 + Z.of_nat (Datatypes.S j)) with (bv_unsigned (a0 + 1)%bv + Z.of_nat j) by lia.
apply (IH (a0 + 1)%bv rest Hr2); [| lia | lia].
intros j' Hj'. rewrite Hu1. replace (bv_unsigned a0 + 1 + Z.of_nat j') with (bv_unsigned a0 + Z.of_nat (Datatypes.S j')) by lia. apply Hh. lia.
-
exfalso. pose proof (Hh 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
unfold seg_rom, memory_read in Hrd. cbn [Z.of_N] in Hrd. rewrite (SEGS_in_hull a0 H0) in Hrd. discriminate.
Qed.
Lemma hb_word_bytes : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "RI'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'TA'<'T='SBvU@v0vQ6vUAvV3vQ1r8r7r6r5r4%<;;:987654321&UB'T>(T5r3r2%33721&S<%11=%83731&Kr1%221>'F'6&SG&UE&TFr<%221G&UM%11@%6231%82Q11(8%<3;21p0>1p]:Q91%B2AOr:&W1r=%?21Q5%A21<%42QJ1%611(3&N&Q9&T:%129Q;%32Q=1z%=2QO1%74QOQ731%92R01%Q13R0;1p0C1p]:QN1p0F1p0Q91p0QC1p^>R11p^@R31p\0R51p]BR71pR6R91pT6R?1p\FRF1pR2RH1").
Proof.
intros E cs R FULL model a w v HC Hin Hoff j Hj.
destruct (hb_word E cs R FULL model a w v HC Hin) as (Hw & Hf & Hr & _).
pose proof (flat_u E a _ Hf) as Hu. rewrite <- Hu. rewrite <- Hu in Hoff.
apply (hb_rdn_bytes FULL w (adenot E a) _ Hr Hoff); [|exact Hj].
destruct Hf as (?&?&?&?). rewrite Hu. lia.
Qed.
Lemma hb_zero_k : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R?'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'TA'T='SBvU@v0vQ6vUAvV3vQ1r7r6r5r4r3%<;;:987654321&UB'T>(T7r2%2261&S<%11<%73631'E&TGr9&TE%122>%433@1'O&UGzr1%3221&UIr:%:21H%3251%?251'Fr8&W1&UE&TFr;%221Q3%421L%62QH1%811(3%92QGC%22QG1%=3QG41p0?1p]6I1%Q02K1p0Q21p0Q;1p]DQI1p\0QK1p]BQM1pR6QO1pT6R51p\FR<1pR2R>1").
Proof.
intros E cs R FULL model a n HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [Hf Hz].
split; [exact Hf|]. intros i Hi. exact (hb_mr_some E cs model FULL _ _ (Hz i Hi)).
Qed.
Lemma hb_fill : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "RA'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'TA'T='O'SBvU@v0vQ6vUAvV3vQ1r8r7r6r5r4%<;;:987654321&UB'T>(T1r3r2%33721&S<%11=%83731'E&TGr:&TE%122?%433A1&UGzr1%3221&UIr;%921H%3251%>251'Fr9&W1&UE&TFr<%221Q3%421K%62QI1%811(3%92QHQ6%22QH1%=3QH41p0?1p]6QE1%O2J1p0Q11p0Q;1p\BQI1p]DQK1p\0QM1p]BQO1pR6R11pT6R71p\FR>1pR2R@1").
Proof.
intros E cs R FULL model a n c HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [Hf Hz].
split; [exact Hf|]. intros i Hi. exact (hb_mr_some E cs model FULL _ _ (Hz i Hi)).
Qed.
Lemma hb_unk : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R@'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'TA'T='SBvU@v0vQ6vUAvV3vQ1r7r6r5r4r3%<;;:987654321&UB'T>(T4r2%2261&S<%11<%73631'E&TGr9&TE%122>%433@1'O&UGzr1%3221&UIr:%:21H%3251%?251&H'Fr8&W1&UE&TFr;%221Q4%421M%62QI1%811(1%11QG%<3QG31%>11p0@1p]6J1%Q12L1p0Q31p0Q<1p]DQJ1p\0QL1p]BQN1pR6R01pT6R61p\FR=1pR2R?1").
Proof.
intros E cs R FULL model a n HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [Hf Hz].
split; [exact Hf|]. intros i Hi Hn. apply (Hz i Hi). unfold Mr, mrestrict. rewrite Hn. destruct (HID E cs model _); reflexivity.
Qed.
Lemma hb_img : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R4'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'O'SBvU@v0vQ6vUAvV3vQ1r7r6r5r4r3%<;;:987654321&UB'T>(T2r2%2261&S<%11<%73631'E&UGr1%22?1&UI%123@%6231'F'6&SG%12M?(D%53421r9&W1%12Q>I%311(1%11Q<%<3Q<31p081p0?1p]6Q<1p0H1p0Q11p]2Q?1p]>Q@1p]BQB1pR6QD1pT6QJ1p\FR11pR2R31").
Proof.
intros E cs R FULL model lo hi HC Hin i Hi Hh. destruct (hb_kn E cs R FULL model _ HC Hin) as (H0 & H1 & Hn).
rewrite <- (hb_mr_hull E cs model FULL (Z_to_bv 64 i)); [exact (Hn i Hi)|].
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [exact Hh| cbn; lia].
Qed.
Lemma hb_wr : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "RH'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'TA'T='SBvU@v0vQ6vUAvV3vQ1r7r6r5r4r3%<;;:987654321&UB'T>(T6r2%2261&S<%11<%73631'E&TGr9&TE%122>%433@1'O'<&UGz%221?&UE&UM%11B%32H1r<%=21M%9231'F'6&Q8r:&W1&TFr=r8%3221%@21Q6%62QL1%94QA81Q7(D%=3<21&R7&SD%15QEQB:CQ0%3317Q=%Q4251p0D1p0L1p]@Q01p\HQ21%Q92Q41p0Q;1p0QD1p]DR21p\0R41p]BR61pR6R81pT6R>1p\FRE1pR2RG1").
Proof.
intros E cs R FULL model a n HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [Hf Hs].
split; [exact Hf|]. intros d m Hd Hm. exact (hb_mr_store_ok E cs model FULL _ _ (Hs d m Hd Hm)).
Qed.
Lemma hb_range : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QJ'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T='O'SBvU@v0vQ6vUAvV3vQ1r8r7r6r5r4%<;;:987654321&UB'T>(T3r3r2%33721&S<%11=%83731'E&UG&W3&T:r:%221A%42Q71%62B1%722>%9221p0;1p0E1p]2Q31p]>Q41p\JQ61p]BQ81pR6Q:1pT6Q@1p\FQG1pR2QI1").
Proof. intros E cs R FULL model e lo hi HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [H1 H2]. lia. Qed.
Lemma hb_disj : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R1'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'TA'T='SBvU@v0vQ6vUAvV3vQ1r9r8r7r6r5%<;;:987654321&UB'T>(T0r4r3r2%448321&S<%11>%93831'I&UG&UE&TFr;%221B&TE%123C%6231%625@%9221%527A%:231%<218%>241p0@1p0K1p]HQ91p\6Q;1p]FQ;1p\4Q=1p]BQ?1pR6QA1pT6QG1p\FQN1pR2R01").
Proof. intros E cs R FULL model a1 n1 a2 n2 HC Hin. exact (hb_kn E cs R FULL model _ HC Hin). Qed.
Lemma hb_align : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QL'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T='O'SBvU@v0vQ6vUAvV3vQ1r7r6r5r4r3%<;;:987654321&UB'T>(SOr2%2261&S<%11<%73631'E&UIz%221='F&UK&W3&T:r9%221D%42Q:1%621E%83Q21:%=2:1p0?1p0H1p]@Q61p\JQ81p]BQ:1pR6Q<1pT6QB1p\FQI1pR2QK1").
Proof. intros E cs R FULL model e m HC Hin. exact (hb_kn E cs R FULL model _ HC Hin). Qed.
Lemma hb_reg : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q@'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>%:1;'SBvU@v0vQ6vUAvV3vQ1r6r5r4r3r2%<;;:987654321'F&U=%1274&T:r7&TB&T@&RL%11>%311%521<%8271%<3Q2:1p0>1p]NL1p]BN1pR6Q01pT6Q61p\FQ=1pR2Q?1").
Proof. intros E cs R FULL model r HC. exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC r). Qed.
Lemma hb_regZ : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QO'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>%:1;'SBvU@v0vQ6vUAvV3vQ1r6r5r4r3r2%<;;:987654321'F'6&T?&S<%11:&TB&T@&RL%11>%311%521<%9271(D%=3<21'O&W3&U=%12GD%32Q91&U9r8r7%?11%A11%C21K%6251%J3<81p0>1p0M1p]NQ;1p]BQ=1pR6Q?1pT6QE1p\FQL1pR2QN1").
Proof. intros E cs R FULL model r HC H. rewrite (hb_reg E cs R FULL model r HC). exact (hb_lin E cs R FULL model _ HC H). Qed.
Lemma hb_maps : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QK'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F'6&S>&RK%11:%311(D%73621';'B%12OO%311&QM&QD%11B%311&M'S5&SAr7%211r6%C11%746=31%H3=91p0B1p0K1p]BQ91pR6Q;1pT6QA1p\FQH1pR2QJ1").
Proof.
intros E cs R FULL model HC Hnf.
exact (proj1 (maps_match_exact 0%nat (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) E (a_maps cs) _ Hnf)
(co_maps _ _ _ _ _ _ _ _ _ _ _ HC)).
Qed.
Definition amapZ (E : env) (m : amap) : Z * Z := (LZ E (am_base m), LZ E (am_base m) + LZ E (am_len m)).
Definition amaps_lin (k : list kentry) (ms : list amap) : bool :=
forallb (fun m => lin_nowrapR k (am_base m) && lin_nowrapR k (am_len m)) ms.
Lemma hb_maps_Z : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R?'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F'6&S>&RK%11:%311(D%73621&TN&S<r6%211%912%5221%>3=18';'B'O%2211%411&M%52Q:Q:(A&TI%11J&UE&TJ%11M%3241%74<<51q\J91&QM&QD%11Q6%311%?4>A51'S5&TMr8%211r7%Q611%F46H31%Q;3H81p0N1p0Q61p0Q?1p]BQM1pR6QO1pT6R51p\FR<1pR2R>1").
Proof.
intros E cs R FULL model HC Hnf Hl. rewrite (hb_maps E cs R FULL model HC Hnf). rewrite map_map. apply map_ext_in.
intros m Hm. unfold amaps_lin in Hl. pose proof (proj1 (forallb_forall _ _) Hl m Hm) as Hb. apply andb_prop in Hb as [H1 H2].
unfold amapZ, amap_den, B, S. cbn [fst snd].
rewrite (hb_lin E cs R FULL model _ HC H1), (hb_lin E cs R FULL model _ HC H2). reflexivity.
Qed.
Lemma hb_res : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q='T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F';'B%12HH%311&QO&QD%11:%311&Q;%11F%;3731p0=1p]BK1pR6M1pT6Q31p\FQ:1pR2Q<1").
Proof. intros E cs R FULL model HC. exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_limit : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q8'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F'O&QL&QD%117%311%6351@p081p]BF1pR6H1pT6N1p\FQ51pR2Q71").
Proof. intros E cs R FULL model HC. exact (co_limit _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_brk : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q<'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F&QJ&QD%116%311&T:r6&RE%11>%4231%:3O61p0<1p]BJ1pR6L1pT6Q21p\FQ91pR2Q;1").
Proof. intros E cs R FULL model HC. exact (co_brk _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_brkZ : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QI'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F'6&T?&S<%11:&RE%11<%5231(D%93821'O&W3&QJ&QD%11B%311%52Q61&U9r7r6%?11%4231%F3<61p0>1p0I1p]BQ71pR6Q91pT6Q?1p\FQF1pR2QH1").
Proof. intros E cs R FULL model HC H. rewrite (hb_brk E cs R FULL model HC). exact (hb_lin E cs R FULL model _ HC H). Qed.
Lemma hb_sbrk : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q<'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321&UG&W3&R0&QD%117%311%52L1&QJ%114%82O1%:241p0<1p]BJ1pR6L1pT6Q21p\FQ91pR2Q;1").
Proof. intros E cs R FULL model HC. exact (co_sbrk _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_isp : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QL'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'E'F'O&W3&QK&QD%119%311%52N1&SLr6&S6%3221%<3;51&UG&QI%2214&QH%4261%C231&S7%<2;1&SI%11;%G3F31%I261%J2=1p0L1p]BQ:1pR6Q<1pT6QB1p\FQI1pR2QK1").
Proof. intros E cs R FULL model HC. exact (co_isp _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_seps : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q7'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'SJ&QM&QD%116%311%511p071p]BE1pR6G1pT6M1p\FQ41pR2Q61").
Proof. intros E cs R FULL model HC. exact (co_seps _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_wf : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q3'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321&TK%114p031p]BA1pR6C1pT6I1p\FQ01pR2Q21").
Proof. intros E cs R FULL model HC. exact (co_wf _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_bounds : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R@'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'L'B%12GG'E&UIz&W3&C%13MM:%32O1%6251'F'O&UK&9%13Q4Q4A%:2Q61+TP0%5221%8371>%72;3%:391@'I&UG&UE%129@&S:%11Q6%5231&S9%11Q9%821?%:241&SMr7%211%=2;1%Q2251%Q32A1%Q42D1%Q52N1q]8Q71&QM&QD%11Q?%311%Q>3Q<51p0Q@1p]BQN1pR6R01pT6R61p\FR=1pR2R?1").
Proof. intros E cs R FULL model HC. exact (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_lazyb : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R0'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'L'B%12GG'E'I&UG&UE&W3&9%13NN;%32Q01&C%13Q1Q1>%62Q31%8241&S:%11K%<231&S9%11N%?21:%A241&SMr7%211%D2;1%G251q]8I1&QC%11Q0%N3L31p0Q01p]BQ>1pR6Q@1pT6QF1p\FQM1pR2QO1").
Proof. intros E cs R FULL model HC. exact (co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_nasub : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QC'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'O'SBvU@v0vQ6vUAvV3vQ1r6r5r4r3r2%<;;:987654321'F'6&SH&QN&QD%118%311%5291(D%93821&QM%71?%211%;2@1%>3=16p061p0A1p^BO1p]BQ11pR6Q31pT6Q91p\FQ@1pR2QB1").
Proof. intros E cs R FULL model z HC. exact (co_nasub _ _ _ _ _ _ _ _ _ _ _ HC z). Qed.
Lemma hb_totsz : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QA'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321&UG&SK&5'B%12II&QO&QD%11:%311&QM%113%93731%;11&RN%11D%?231p0A1p]BO1pR6Q11pT6Q71p\FQ>1pR2Q@1").
Proof. intros E cs R FULL model HC. exact (co_totsz _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_none : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QM'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'S5'SBvU@v0vQ6vUAvV3vQ1r6r5r4r3r2%<;;:987654321&UB&RK%118%33A51'I'F'S=&S3%11;(R?%53421(R@%73641%9231'B%12Q5Q5&SAr9%221F&QN&QD%11J%311%G3851p0;1p0F1p0K1p]@Q91p]BQ;1pR6Q=1pT6QC1p\FQJ1pR2QL1").
Proof. intros E cs R FULL model m HC Hm Hk. exact (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m Hm Hk). Qed.
Lemma hb_lazykind : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "RH'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'S5'SBvU@v0vQ6vUAvV3vQ1r7r6r5r4r3%<;;:987654321&UB&RK%118%33A51'F'S=&S3%11:(RA%53421'E&UG&W3&T:r:&S2%11D%4231%62Q91%72Q:F%9221&UI&UE&S4%11L%<2;1%>2QA1%5291%7291%C291'6&SH%D2QGQ4&QN&QD%11Q9%311%6251(8%Q33921&QG&QF%11Q>&QC%11QB%5231(D%Q;3A21%Q6291p0D1p0Q91p0Q@1p0QE1p\0R;1p]@R41p]BR61pR6R81pT6R>1p\FRE1pR2RG1").
Proof. intros E cs R FULL model m a HC Hm Hk Ha. exact (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m Hm Hk a Ha). Qed.
Lemma hb_noacc : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q@'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F';'B%12HH%311&QN&QD%11:%311&SEr6&RJ%11B%4231%>3:61p0@1p]BN1pR6Q01pT6Q61p\FQ=1pR2Q?1").
Proof. intros E cs R FULL model HC. exact (co_hna _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_lazy : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q>'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F';'B%12HH%311&QC%119&SEr6&RI%11@%4231%<3861p0>1p]BL1pR6N1pT6Q41p\FQ;1pR2Q=1").
Proof. intros E cs R FULL model HC. exact (co_hlz _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_tid : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QK'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F'6&RM%119(D%53421'G'E%K1M&QB%11?(3%12Q1>%=3531&UIz&W3%12Q7C%4231&RC%6231%>231%?291q^:Q<1%B2Q=1p0D1p0K1p]BQ91pR6Q;1pT6QA1p\FQH1pR2QJ1").
Proof. intros E cs R FULL model HC Ht. exact (co_tidv _ _ _ _ _ _ _ _ _ _ _ HC Ht). Qed.
Lemma hb_tid_range : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QI'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F'6&RM%119(D%53421%I1K&QB%11=(3%12O<%;3531'E&UIz&W3%12Q6C%4231+TPPP0%6231%8231p0:1p^:Q;1p0B1p0I1p]BQ71pR6Q91pT6Q?1p\FQF1pR2QH1").
Proof.
intros E cs R FULL model HC Ht t Hm. destruct (hb_tid E cs R FULL model HC Ht) as (t' & Hm' & Hr).
rewrite Hm in Hm'. injection Hm' as ->. unfold PID_MAX in Hr. exact Hr.
Qed.
Lemma hreplay_nil : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "B'T;'F';'B'W2yR0%211%4211%611&SEr1(>'S8%211%5241%418%?3821pR2A1"). Proof. reflexivity. Qed.
Lemma hreplay_cons : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q2'T;'T=';'S8%211'F'B'W2yR0%211%4211%911&SEr4(7(R=r3r2%3221r1%63A21%9281(A&T:%12;8%22<8%44AA21%?2>8%>3B21%H3B81p]0J1p]DN1p\<O1pR2Q11"). Proof. reflexivity. Qed.
Lemma hreplay_sub : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q6'T;'T=';'S8%211'F'B'W2yR0%211%4211%911&SEr4(7(R>r3r2%3221r1%63A21%9281&QE%;2:4&W3&T:%12=:%32C1&UE%42@<%62F1%3241%:3951%L3F<1p]0N1p]DQ21p\<Q31pR2Q51").
Proof. reflexivity. Qed.
Lemma hb_eager : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q7'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321&UG&R6%115&RF%11:%5231p071p]BE1pR6G1pT6M1p\FQ41pR2Q61").
Proof. intros E cs R FULL model HC. exact (co_eager _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_abytes : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q:'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321&UG&R3&S@r6%23?1:%411&RD%11=%8231p0:1p]BH1pR6J1pT6Q01p\FQ71pR2Q91").
Proof. intros E cs R FULL model HC. exact (co_abytes _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_minv : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q6'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'R5&S@r6%23>19%4217p061p]BD1pR6F1pT6L1p\FQ31pR2Q51").
Proof. intros E cs R FULL model HC. exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_allowA_wf : ltac2:(TCodec.tc2 tcn__HandoffBridgeK ";'T;'S0&R4&S@v0r2r1%43321%611p\F81pR2:1").
Proof. intros E cs. exact (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E cs). Qed.
Definition allow1Z (E : env) (p : expr * expr) : list (Z * Z) :=
let b := LZ E (fst p) in let n := LZ E (snd p) in
[(pagedown b, pageup (b + n)); (pagedown (shadow_off A + b / 8), pageup (shadow_off A + (b + n) / 8))].
Definition vis_lin (k : list kentry) (ps : list (expr * expr)) : bool :=
forallb (fun p => lin_nowrapR k (fst p) && lin_nowrapR k (snd p)) ps.
Lemma flat_map_ext_In {X Y} : forall (f g : X -> list Y) l, (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof. intros f g l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy. Qed.
Lemma hb_allowA_Z : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R3'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F'6&U6&S<%11:&5'B'T=%2211&RO%11@&RH%11B%83531%<2:1(D%@3?21';'O%=211%311&S@r7r6%33Q321&UD&TL%115%C15%B16%I3F21%64G<41%Q03<81p0A1p0Q31p]BQA1pR6QC1pT6QI1p\FR01pR2R21").
Proof.
intros E cs R FULL model HC Hl. unfold allowA. apply flat_map_ext_In.
intros p Hp. pose proof (proj1 (forallb_forall _ _) Hl p Hp) as Hb. apply andb_prop in Hb as [H1 H2].
unfold allow1, allow1Z, sh_lo, sh_hi, APSK.uE. rewrite (hb_lin E cs R FULL model _ HC H1), (hb_lin E cs R FULL model _ HC H2). reflexivity.
Qed.
Lemma hb_halt : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q8'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F%D1F&QA%116(1%11J%63531p081p]BF1pR6H1pT6N1p\FQ51pR2Q71").
Proof. intros E cs R FULL model HC. exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_fds_std : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QA'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F'S1&RG%119(R<%53421';'B'Q=%22N1%411&Q?%11@&SC%>3421p0:1p0A1p]BO1pR6Q11pT6Q71p\FQ>1pR2Q@1").
Proof. intros E cs R FULL model HC Hfd. pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as H. rewrite Hfd in H. exact H. Qed.
Lemma hb_fs : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q6'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F&Q7&Q@%116%4331;p061p]BD1pR6F1pT6L1p\FQ31pR2Q51").
Proof. intros E cs R FULL model HC. exact (co_fs _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_tid_none : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q>'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321'F'6&RM%119(8%53421%I1K&QB%11<(1%11O%;3531p071p0>1p]BL1pR6N1pT6Q41p\FQ;1pR2Q=1").
Proof. intros E cs R FULL model HC. exact (co_tid _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma hb_zero : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "RC'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r6r5r4r3r2%<;;:987654321'F'6&SDr7%26?<1:76(D%63521&SH&W3%12O<&QM&QD%11@%311%7251%?3>1:%82Q6D&QN%71G%211%=241(8%F3E21&QG&QF%11N&QC%11Q1%5231%M3L1H&SFr;r:%I2QGQ7%43321%Q33Q21>r9%11Q2(3&W1z%22QK1%42QK1%Q;3QK61p091p0@1p0H1p0Q01p0Q:1p0QB1p\0R71p]BR11pR6R31pT6R91p\FR@1pR2RB1").
Proof. intros E cs R FULL model a HC. exact (co_zero _ _ _ _ _ _ _ _ _ _ _ HC a). Qed.
Lemma hb_hid_unfold : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "L'T;'S0'Q>'W2yR0%211'F'6&SDv0vV3r4r3r2r1%76654321&@%7263&=&SN%15;9876%311%6251%A3@81p\0C1p]BG1p\FI1pR2K1").
Proof. reflexivity. Qed.
Lemma hb_sinv : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q3'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0vQ6vUAvV3vQ1r5r4r3r2r1%<;;:987654321r6%:215p031p]BA1pR6C1pT6I1p\FQ01pR2Q21").
Proof. intros E cs R FULL model HC. exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Definition kfind_word (k : list kentry) (b : expr) (off : Z) (w : nat) : option expr :=
match List.find (fun K => match K with
| KWord a w' _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off && Nat.eqb w' w)%bool
| _ => false end) k with
| Some (KWord _ _ v) => Some v
| _ => None
end.
Lemma kfind_word_In : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q0';'T>%211'T='O'<'F'?%115&U3r5r4r3r2%544321(3r1%22>1%<3:41&UB(T5(T8%12<;%331;:r6%63H21p081p^>H1p^@G1p]JI1p\<K1p]<M1").
Proof.
intros k b off w v H. unfold kfind_word in H.
destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
apply find_some in Hf as [Hin HK]. destruct K as [a w' v'| | | | | | | | |]; try discriminate.
injection H as <-. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. apply Nat.eqb_eq in H3. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.
Lemma hb_word_at : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "RE'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T='O'<'SBvU@v0vQ6vUAvV3vQ1r9r8r7r6r5%<;;:987654321'F%G1A&U3&S<%11:r4r3%543921(3r2%22J1%;3:41'E'Ju8%22:1&TGr;(T8%12FE&UM%11@%63531';%11Q<%Q?11&U>&T9%12;9%34Q9Q21H&Q9&T:%12?J%32L1%J2:1%Q33:61&R7&SDr:%25QBQ?F1Q;%431<Q3%M261%N2D1%O2L1p0Q11p0Q>1p^>QN1p^@QM1p]JQO1p\<R11p]BR31pR6R51pT6R;1p\FRB1pR2RD1").
Proof. intros E cs R FULL model b off w v HC H. exact (hb_word E cs R FULL model _ w v HC (kfind_word_In _ _ _ _ _ H)). Qed.
Definition kfind_zero (k : list kentry) (b : expr) (off : Z) : option expr :=
match List.find (fun K => match K with
| KZero a _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off)%bool
| _ => false end) k with
| Some (KZero _ n) => Some n
| _ => None
end.
Lemma kfind_zero_In : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "M';'T>%211'T='O'F'?%114&U5r4r3r2%43321(3r1%22<1%;3941&UB(T7(T8%12;:%321:r5%63F21p081p]DF1p]JF1p\<H1p]<J1").
Proof.
intros k b off n H. unfold kfind_zero in H.
destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
apply find_some in Hf as [Hin HK]. destruct K as [ |a n'| | | | | | | |]; try discriminate.
injection H as <-. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.
Lemma hb_zero_at : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "RC'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T='O'SBvU@v0vQ6vUAvV3vQ1r8r7r6r5r4%<;;:987654321'F%F1@&U5&S<%11:r3%43281(3r2%22H1%:3941'E&TGr:(T8%12BA&TE%124<%63531&UGzr1%3221&UIr;%921K%3251%@251r9&W1&UE&TFr<%C2Q6Q5%3221%521K%72QL1%911%92QJB%Q02QJ1%Q83QJ31p0>1p]6QH1%Q02I1p0Q21p0Q>1p]DQM1p]JQM1p\<QO1p]BR11pR6R31pT6R91p\FR@1pR2RB1").
Proof. intros E cs R FULL model b off n HC H. exact (hb_zero_k E cs R FULL model _ n HC (kfind_zero_In _ _ _ _ H)). Qed.
Definition kfind_fill (k : list kentry) (b : expr) (off : Z) : option (expr * Z) :=
match List.find (fun K => match K with
| KFill a _ _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off)%bool
| _ => false end) k with
| Some (KFill _ n c) => Some (n, c)
| _ => None
end.
Lemma kfind_fill_In : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q3';'T>%211'T='O'F'?'B%1254%311&U0r5r4r3%43321(3(Ar2r1%34@?21%52<1%@3<71&UB(T1(T8%12>=%331=9r6%63K21p081p\BJ1p]DL1p]JL1p\<N1p]<Q01").
Proof.
intros k b off n c H. unfold kfind_fill in H.
destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
apply find_some in Hf as [Hin HK]. destruct K as [ | | | | | | | |a n' c'| ]; try discriminate.
injection H as <- <-. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.
Lemma hb_fill_at : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "RI'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T='O'SBvU@v0vQ6vUAvV3vQ1r9r8r7r6r5%<;;:987654321'F'B%12A@%H11&U0&S<%11<r4%432:1(3(Ar3r2%34LK21%52<1%?3<71'E&TGr;(T8%12GF&TE%124?%63531&UGzr1%3221&UIr<%921Q0%3251%@251r:&W1&UE&TFr=%C2Q;Q:%3221%521L%72R11%911%92QOQ=%Q32QO1%Q=3QO31p0>1p]6QM1%Q02I1p0Q21p0QC1p\BR11p]DR31p]JR31p\<R51p]BR71pR6R91pT6R?1p\FRF1pR2RH1").
Proof. intros E cs R FULL model b off n c HC H. exact (hb_fill E cs R FULL model _ n c HC (kfind_fill_In _ _ _ _ _ H)). Qed.
Definition kfind_wr (k : list kentry) (b : expr) (off : Z) : option expr :=
match List.find (fun K => match K with
| KWr a _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off)%bool
| _ => false end) k with
| Some (KWr _ n) => Some n
| _ => None
end.
Lemma kfind_wr_In : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "M';'T>%211'T='O'F'?%114&U4r4r3r2%43321(3r1%22<1%;3941&UB(T6(T8%12;:%321:r5%63F21p081p]DF1p]JF1p\<H1p]<J1").
Proof.
intros k b off n H. unfold kfind_wr in H.
destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
apply find_some in Hf as [Hin HK]. destruct K as [ | | | | | |a n'| | | ]; try discriminate.
injection H as <-. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.
Lemma hb_wr_at : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "RM'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T='O'SBvU@v0vQ6vUAvV3vQ1r8r7r6r5r4%<;;:987654321'F%F1@&U4&S<%11:r3%43281(3r2%22H1%:3941'E&TGr:(T8%12BA&TE%124<%63531'<&UGz%221>&UE&UM%11A%32E1r=%<21Q0%9231'6&Q8r;&W1&TFr>r9%G21Q;%4231%@21Q9%72R01%:4QE91Q4(D%Q;3=21&R7&SD%15QIQF;CQ1%3317Q:%Q5251p0D1p0L1p]@Q01p\HR21%Q:2Q31p0Q<1p0QH1p]DR71p]JR71p\<R91p]BR;1pR6R=1pT6RC1p\FRJ1pR2RL1").
Proof. intros E cs R FULL model b off n HC H. exact (hb_wr E cs R FULL model _ n HC (kfind_wr_In _ _ _ _ H)). Qed.
Definition kfind_img (k : list kentry) (z : Z) : option (Z * Z) :=
match List.find (fun K => match K with KImg lo hi => (Z.leb lo z && Z.ltb z hi)%bool | _ => false end) k with
| Some (KImg lo hi) => Some (lo, hi)
| _ => None
end.
Lemma kfind_img_In : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "Q5';'T>%211'O'F'?'B%1244%311&U1r4r3%3221(3(Ar2r1%34>>21%52;1%?3;71'E&UB(T2%12<8r5%43H21&UG%12@A&UI%12C>%:231%;261p0=1p]2N1p]>O1p^BQ01p]<Q21").
Proof.
intros k z lo hi H. unfold kfind_img in H.
destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
apply find_some in Hf as [Hin HK]. destruct K as [ | | |lo' hi'| | | | | | ]; try discriminate.
injection H as <- <-. apply andb_prop in HK as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. auto.
Qed.
Lemma hb_img_at : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R;'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'O'SBvU@v0vQ6vUAvV3vQ1r8r7r6r5r4%<;;:987654321'F'B%12@@%G11&U1&S<%11<%3219(3(Ar3r2%34JJ21%52;1%>3;71'E&UGr1%22E1&UI%123F%6231'6&SG%12Q3=(D%J3421r:&W1%12QDC%311(1%11QB%Q13QB31p081p0>1p]6QB1p0G1p0Q71p]2QE1p]>QF1p^BQG1p]BQI1pR6QK1pT6R11p\FR81pR2R:1").
Proof. intros E cs R FULL model z lo hi HC H. destruct (kfind_img_In _ _ _ _ H) as [Hin _]. exact (hb_img E cs R FULL model lo hi HC Hin). Qed.
Definition kfind_at (k : list kentry) (b : expr) (off : Z) : list kentry :=
List.filter (fun K => match K with
| KWord a _ _ | KZero a _ | KBlob a _ _ | KWr a _ | KFill a _ _ | KUnk a _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off)%bool
| _ => false end) k.
Lemma kfind_at_In : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "D';'T>%211'T='O&UBr1&TOr4r3r2%43321%73;61r5%93=41p031pR<?1p]J=1p\<?1p]<A1").
Proof. intros k b off K H. unfold kfind_at in H. apply filter_In in H as [H _]. exact H. Qed.
Definition kfind_ranges (k : list kentry) (e : expr) : list (Z * Z) :=
flat_map (fun K => match K with KRange e' lo hi => if expr_eqb e' e then [(lo, hi)] else [] | _ => [] end) k.
Lemma hb_ranges_of : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QL'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'T='SBvU@v0vQ6vUAvV3vQ1r6r5r4r3r2%<;;:987654321'L'B'O%2211'E&UG&9r1%23661&W3&T:r8%221?%42Q41%9261&C%13>>9%<241%>241q]N@1&U2&S<%11L%321I%H3E51p0J1p\JQ81p]BQ:1pR6Q<1pT6QB1p\FQI1pR2QK1").
Proof.
intros E cs R FULL model e HC. unfold kfind_ranges. apply Forall_forall. intros r Hr.
apply in_flat_map in Hr as (K & Hin & Hr). destruct K as [ | | | | |e' lo hi| | | | ]; try (destruct Hr; fail); try contradiction.
destruct (expr_eqb e' e) eqn:He; [|destruct Hr]. destruct Hr as [<-|[]]. apply expr_eqb_eq in He. subst e'. cbn.
exact (hb_range E cs R FULL model e lo hi HC Hin).
Qed.
End Generic.
Ltac hb_linZ :=
unfold LZ;
repeat (match goal with |- context [lin_of ?e] => let l := eval vm_compute in (lin_of e) in change (lin_of e) with l end);
cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE edenot];
repeat (match goal with |- context [bv_unsigned (ev ?E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) end);
rewrite ?Z.add_0_r.
Ltac hb_in := apply hb_knb_In; vm_compute; reflexivity.
Section Image.
Variable SEGS : list Segment.
Variable A : atable.
Variable ph : PhdrInfo.
Hypothesis IMG : img_facts SEGS A ph.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Variable HSf : nat -> option acs.
Variable HSc : nat -> acs.
Hypothesis HSf_some : forall h, (h < 2)%nat -> HSf h = Some (HSc h).
Hypothesis HSf_none : forall h, (2 <= h)%nat -> HSf h = None.
Hypothesis NOFOG : forall h, (h < 2)%nat -> no_fog (a_maps (HSc h)) = true.
Hypothesis MAPSLIN : forall h, (h < 2)%nat -> amaps_lin (kn (HSc h)) (a_maps (HSc h)) = true.
Hypothesis VISLIN : forall h, (h < 2)%nat -> vis_lin (kn (HSc h)) (a_vis (HSc h) ++ a_ghost (HSc h)) = true.
Hypothesis BRKLIN : forall h, (h < 2)%nat -> lin_nowrapR (kn (HSc h)) (a_brk (HSc h)) = true.
Hypothesis FDSTD : forall h, (h < 2)%nat -> a_fd (HSc h) = FdStd.
Variables (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk SEGS brk0.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).
#[local] Notation CSOK := (cs_ok SEGS A AsanInitK.LIMIT SINV argH fs).
Let argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a := argH0_high ph sp rdraw argv envp uid hw Hsp Hva.
Lemma hbi_ch : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "H'<'S0'F'?%113vQ4r2%211(3r1%2291%93741'EvQ3r3%211%>3?:1&Ku2%2251%8241p0:1p\DE1p]0G1").
Proof.
intros h ch H. destruct (Nat.lt_ge_cases h 2) as [Hl|Hl].
- rewrite (HSf_some h Hl) in H. injection H as <-. auto.
- rewrite (HSf_none h Hl) in H. discriminate.
Qed.
Definition MAPS (h : nat) (E : env) : list (word * word) := map (amap_den E) (a_maps (HSc h)).
Lemma hbi_maps : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QN'<'T;&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>&Kr5u2%3221'SBvU@v0&R9&R:vVMvW0vVOvV6vV4vV=vW5vVA%9887654321&R;%17:986543vV>vQ3r6%211r4r3r2%G;FED:87J4321'F';'B%12Q7Q7%311&QM&QD%11:%311&U7r7%221A%<3841p0>1p0Q71p]BQ<1pR6Q>1pT6QD1pR2QK1p]0QM1").
Proof. intros h E R FULL model Hh HC. exact (hb_maps SEGS A _ _ _ _ E _ R FULL model HC (NOFOG h Hh)). Qed.
Lemma hbi_maps_Z : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "RA'<'T;&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>&Kr5u2%3221'SBvU@v0&R9&R:vVMvW0vVOvV6vV4vV=vW5vVA%9887654321&R;%17:986543vV>vQ3r6%211r4r3r2%G;FED:87J4321'F';'B'O%2211%411&M%52Q;Q;(A&TIr1%211&UE&TJ%114%3241%84==51q\J:1&QM&QD%11G%311%@4?B51'S5&U<%11O&RKr7%Q311%311%H47J51%O3J91p0Q11p0QJ1p]BQO1pR6R11pT6R71pR2R>1p]0R@1").
Proof. intros h E R FULL model Hh HC. exact (hb_maps_Z SEGS A _ _ _ _ E _ R FULL model HC (NOFOG h Hh) (MAPSLIN h Hh)). Qed.
Lemma hbi_maps_len : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R1'<'T;&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>&Kr5u2%3221'SBvU@v0&R9&R:vVMvW0vVOvV6vV4vV=vW5vVA%9887654321&R;%17:986543vV>vQ3r6%211r4r3r2%G;FED:87J4321'F&:'B%12Q7Q7&QM&QD%119%311%7251'S5&RKr7%C11%311%=251%?3QI71p0A1p0Q:1p]BQ?1pR6QA1pT6QG1pR2QN1p]0R01").
Proof. intros h E R FULL model Hh HC. rewrite (hbi_maps h E R FULL model Hh HC). apply length_map. Qed.
Lemma hbi_brkZ : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R0'<'T;&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>&Kr5u2%3221'SBvU@v0&R9&R:vVMvW0vVOvV6vV4vV=vW5vVA%9887654321&R;%17:986543vV>vQ3r6%211r4r3r2%G;FED:87J4321'F'O&W3&QJ&QD%118%311%52Q<1&U9&REr7%B11%311%52C1%>3=71p0@1p0Q91p]BQ>1pR6Q@1pT6QF1pR2QM1p]0QO1").
Proof. intros h E R FULL model Hh HC. exact (hb_brkZ SEGS A _ _ _ _ E _ R FULL model HC (BRKLIN h Hh)). Qed.
Lemma hbi_allowA_Z : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R8'<'T;&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>&Kr5u2%3221'SBvU@v0&R9&R:vVMvW0vVOvV6vV4vV=vW5vVA%9887654321&R;%17:986543vV>vQ3r6%211r4r3r2%G;FED:87J4321'F';'B'O%2211%411&S@r7%?11%33O?1&UD'T=%:211&U;%12Q4D&5&RO%119&RH%11;%53831%;49A71%F3A=1p0H1p0QA1p]BQF1pR6QH1pT6QN1pR2R51p]0R71").
Proof. intros h E R FULL model Hh HC. exact (hb_allowA_Z SEGS A _ _ _ _ E _ R FULL model HC (VISLIN h Hh)). Qed.
Lemma hbi_fds : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QK'<'T;&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>&Kr5u2%3221'SBvU@v0&R9&R:vVMvW0vVOvV6vV4vV=vW5vVA%9887654321&R;%17:986543vV>vQ3r6%211r4r3r2%G;FED:87J4321'F';'B'Q=%22Q81%411&Q?%11:&SC%93421p0;1p0Q41p]BQ91pR6Q;1pT6QA1pR2QH1p]0QJ1").
Proof. intros h E R FULL model Hh HC. exact (hb_fds_std SEGS A _ _ _ _ E _ R FULL model HC (FDSTD h Hh)). Qed.
Lemma hbi_E0 : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QI'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0&R9&R:vVMvW0vVOvV6vV4vV=vW5vVA%9887654321&R;%17:986543vV>r5r4r3r2r1%F;EDC97654321'<&K&RB%2251'F&T<r8%221:&R8%18KJIHGFED%521=%73Q:41p091p]D=1p0?1p]BQ71pR6Q91pT6Q?1p\FQF1pR2QH1").
Proof. intros E cs R FULL model HC. exact (proj1 (hb_sinv SEGS A _ _ _ _ E cs R FULL model HC)). Qed.
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation envc := (Z.of_nat (length envp)).
Definition Wsb : Z := (Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rdraw)) - 16 - (8 * argc + 8 * envc + 184)) / 8.
Lemma hbi_vals : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "SL'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0&R9&R:vVMvW0vVOvV6vV4vV=vW5vVA%9887654321&R;%17:986543vV>r5r4r3r2r1%F;EDC97654321'E'F'O&U:r6(2%3221&UF&W3%12Q9J+QPP0%4221%;3:61u6%;2:1&UK+TP0%2281+@%<221%C3B61u1%C2B1&UM&:';%11QE%321Q9%511%L3K71u2%L2K1%826Q=%:11%Q13Q031u3%Q12Q01&N(>%11R2%34>Q3QF1%A2R41%C11%Q:3Q971u7%Q:2Q91%94DIQL7%G2R:1%I11%Q@3Q?41u4%Q@2Q?1&U8%QD3QC21u5%QD2QC1%Q@2RHR7%QB21Q9%QI3QH31&T<u8%22QI1%QM3RM1R:u9%52QL1%R03S01R<u:%R02QO1%QE2QKQJ%QN21QE%R53R431%R7261%R82:1%R92?1%R:2E1%R;2J1%R<2Q11%R=2Q;1%R>2QA1%R?2QK1%R@2R41p0RB1p]BS:1pR6S<1pT6SB1p\FSI1pR2SK1").
Proof.
intros E cs R FULL model HC. pose proof (hbi_E0 E cs R FULL model HC) as HE.
pose proof (uE0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
pose proof (uE0_L1 ph sp rdraw brk0 argv envp uid hw Hva) as U8.
pose proof (uE0_s2a ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U9.
unfold APSK.uE in *. cbn [edenot] in U1, U2, U3, U4, U5, U6, U7, U8, U9.
unfold V_S1, V_S2, V_S2A, V_ARGC, V_ENVC, V_L0, V_L1, V_W, V_BRK, V_UID, V_HW in *. unfold VZ. rewrite !HE by (unfold NX0; lia).
repeat split; try assumption; try reflexivity.
Qed.
Lemma hbi_sp0 : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R2'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0&R9&R:vVMvW0vVOvV6vV4vV=vW5vVA%9887654321&R;%17:986543vV>r5r4r3r2r1%F;EDC97654321'F'O&UE&UL+QPP0&U:r6(2%3221%6251+@u6%7261%:231%<251+TP0u:%<2;1%?231%A251&W3%12QEQ6%F3E31p0H1p]BQ@1pR6QB1pT6QH1p\FQO1pR2R11").
Proof.
intros E cs R FULL model HC. destruct (hbi_vals E cs R FULL model HC) as (U1 & U2 & _ & _ & _ & _ & _ & _ & _ & _ & U3). rewrite U1, U2, U3.
pose proof Hsp as (_ & _ & Hal). pose proof (u64_range sp).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma hbi_sppg : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R0'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0&R9&R:vVMvW0vVOvV6vV4vV=vW5vVA%9887654321&R;%17:986543vV>r5r4r3r2r1%F;EDC97654321'F'O&UE&UL+QPP0&U:r6(2%3221%6251+TP0u:%7261%:231%<251&UF&W3%12QAQ2%3218%@219%D3C61p0F1p]BQ>1pR6Q@1pT6QF1p\FQM1pR2QO1").
Proof.
intros E cs R FULL model HC. destruct (hbi_vals E cs R FULL model HC) as (U1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & U3). rewrite U1, U3.
pose proof Hsp as (_ & _ & Hal). pose proof (u64_range sp).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma hbi_brk0 : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QG'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0&R9&R:vVMvW0vVOvV6vV4vV=vW5vVA%9887654321&R;%17:986543vV>r5r4r3r2r1%F;EDC97654321'F'O&UL+TP0&U:r6u5%3221%6251&W3%12Q:I%;3:31p0=1p]BQ51pR6Q71pT6Q=1p\FQD1pR2QF1").
Proof.
intros E cs R FULL model HC. destruct (hbi_vals E cs R FULL model HC) as (_ & _ & _ & _ & _ & _ & _ & U & _). rewrite U.
pose proof (brk_range SEGS A ph sp rdraw brk0 argv envp uid hw IMG Hbrk) as [_ Hm].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma hbi_sp_range : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "C'E&UG&QI&W3yR0vW0%3221%6251&QH%8231%:231'F'O&UK+@%2291z%63521%B281").
Proof. pose proof Hsp as (H1 & H2 & H3). auto. Qed.
Lemma hbi_argblock : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "QG'T;'S0&R1y5'W2yR0%211%5241'?y8%611%311p061'Q>'SBvU@v0&R9&R:vVMvW0vVOvV6vV4vV=vW5vVA%9887654321&R;%17:986543vV>r5r4r3r2r1%F;EDC97654321'F'6r7%<9EDCA@?>15(D%53421%<19&U?%18JIFEDCH;%93Q331p051p\0Q:1p0=1p]BQ51pR6Q71pT6Q=1p\FQD1pR2QF1").
Proof. intros E cs R FULL model HC. exact (proj2 (hb_sinv SEGS A _ _ _ _ E cs R FULL model HC)). Qed.
Lemma hbi_argH : ltac2:(TCodec.tc2 tcn__HandoffBridgeK "R>'T;'W2yR0%211'F'6&R;vVMvW0vVOvV4vV=vW5vVAr2r1%:9987654321&4&UH&SL&S6%2271&W3%12E8%6231&@&UE%52IC+H%3221%<217&UJ&UL+8&UM&:';y8%Q511%311%521N%711%:291%A2@1%925Q1%;11%>2=1%E241%F21D%B2J1%Q12D1+UH%J251%Q321N&U8%G2F1%N241%J2Q21%Q9251%Q2291&Q<%17QFQEQCQBQAQ@QD%K2H1%M11%Q62Q51%Q?21Q:&Q:%17QLQKQIQHQGQFQJ%Q12N1%Q311%Q<2Q;1%Q82Q@1%QG271%Q@2>1%QI2QB1%R73R6QK1p\0R91pR2R=1").
Proof. reflexivity. Qed.
End Image.
