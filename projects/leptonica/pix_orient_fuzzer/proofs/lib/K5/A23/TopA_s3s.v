(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS23 Require Import AsanTablesA AsanStartup StartupHSAsan StartupPlanAsan AsanStartupCert.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_rep D_libiface TopA_iodefs RT_io TopA_start TopA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_TopA_s3s () := "K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib2K53A234TopA9hs_all_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K54AS23=StartupHSAsan9HS_asan_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23=StartupHSAsan<HS_asan_1000C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23=StartupHSAsan<HS_asan_2000C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23=StartupHSAsan<HS_asan_3000C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes6option01I79OSSVerify5KrLib2K52AS8AsanPlan2AP3acs00C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indc69OSSVerify5KrLib2K53A238TopA_s3s=hs_if_some_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23=StartupHSAsan7HS_asanC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01c69OSSVerify5KrLib2K53A238TopA_s3s:hs_ok_3000C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238TopA_s3s:hs_ok_2000C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238TopA_s3s:hs_ok_1000C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238TopA_s3s7hs_ok_0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C69OSSVerify5KrLib2K53A23:D_libiface<fuzz_one_cpsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A238RT_iface<rt_contracts00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib2K53A238RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;TopA_iodefs9io_constsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A234TopA8s3s_A_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23?AsanStartupCert3IT0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23?AsanStartupCert6IT0_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23?StartupPlanAsan<startup_planC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23?AsanStartupCert=startup_shapeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23?AsanStartupCert3KC0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23?AsanStartupCert5BFUELC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23?AsanStartupCert4FUELC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23?AsanStartupCert<startup_certC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238TopA_s3sCstartup_shape_holesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238TopA_s3s:HS_asan_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236RT_rep3RTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:D_libiface5LIB_AC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03c69OSSVerify5KrLib2K53A238TopA_s3s5s3s_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235RT_io6rta_ioC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239RT_refill9refill_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239RT_malsec<mal_core_secC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23>RT_drain_istmt5dl_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237RT_dsec;item_sec_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<RT_drain_fin8drain_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:RT_freeFin8rta_freeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<RT_contracts=rta_contractsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238TopA_s3s8s3s_A_rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<RT_sys_fixed?fixed_commit_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<RT_sys_grant=grant_node_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<RT_sys_fixedCfixed_commit_pab_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;RT_sys_stmt;munmap_nodeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;RT_sys_stmt<madvise_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A23>RT_drain_ldefs3dlp00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=RT_sys_munmap9munmap_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23>RT_sys_madvise:madvise_okC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma hs_ok_0 : hs_all_ok HS_asan_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_s3s ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Dj30Tg001^R0g002>R1'2g002^#1=001do"). Qed.
Lemma hs_ok_1000 : hs_all_ok HS_asan_1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_s3s ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Dj30Tg001^R0g002>R1'2g003b#1=001do"). Qed.
Lemma hs_ok_2000 : hs_all_ok HS_asan_2000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_s3s ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Dj30Tg001^R0g002>R1'2g004i#1=001do"). Qed.
Lemma hs_ok_3000 : hs_all_ok HS_asan_3000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_s3s ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Dj30Tg001^R0g002>R1'2g0060#1=001do"). Qed.

(* [comment removed for export] *)
Lemma hs_if_some_ok : forall (P : acs -> Prop) (b : bool) (s : acs) (r : option acs) (ch : acs),
  P s -> (r = Some ch -> P ch) -> (if b then Some s else r) = Some ch -> P ch.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_s3s ()) [] "p'0h01Hh12Prh22chh32H0h41Ph52Psh61bi001bh71eh81rh91si011ai021op;1p;3p;6p;7p;2g0077R0j15Tg001Dj30Tg007Yj62Tg0086j74Tg008Rj23Tg0094R1f0R2'3p=1p-0\1g001^R3%51R4f4R5f2R6O1f1R7#19046f6R8P6O1[P3P4f5R9%15R:f3R;n0110000020000%16504P3P3P4P2%18R3P9n0110000020000=04:f9R<P9O1]0P8%19%1;R;504P4P1P0P1P1P2P2f7R0n10110200021010100X74P3P:P2E2A0185A0109P1f8R9%129049f<P7O1R7[P7]1X21%199040f;P<O1[P8W1P8P2P5F4W0P2O1b3W0A045;P6P2O1W0n0110000020000P2O1W0W1W5X21W8X91W6W4o"). Qed.

Lemma HS_asan_ok : forall h ch, HS_asan h = Some ch -> hs_all_ok ch = true.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_s3s ()) [] "p'0h01Hh12H0h21ch32chh41eh51hi001op;1p;2p;3p;6p;7g000Jj18Tg00:0j24Tg0077R0j1=Tg008Rj22Tg00:Pj1<Tg001Dj36Tg0086j6;Tg00;2j29Tg00;Qj73Tg00<Sj1:Tg00=Uj11Tg001^R1f0R2g002>36p=7%12#1#1#1#1#1#1#1p=5%12#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00>4g0094R3%82#7X23R4f1R5g00>SR6#5#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0R7#5#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0R8#5#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0'4g0060P1%=3R91458R8g004iR:,23P1P91457R7g003bR;,23P1P91456R6g002^R1,23%<3R<n0100000020000R=n0100000020000R>n0100000020001P2g00?2P4P8P:P>P2g00@1P4P7P;P=P2g00A0P4P6P1P<P2g00Ao1232R1969<P9P<P0P3p-0P2g00BkR0g00CHn10110000021000000X49g00Cd1235P2E;P0f2#8#7/92b1W0F3F3F3F3%:5=691%85#7[eW3W5o"). Qed.

(* [comment removed for export] *)
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_s3s ()) [] "p;2g0000j20Tg001^g002>'0o"). Qed.

(* [comment removed for export] *)
Theorem s3s_A : fuzz_one_cps RTA LIB_A -> rt_contracts RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) ->
  S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_s3s ()) [] "h02FZh13IOCh22RCh31mh42Σp;2p;1p;3p;>g00D@j2:Tg00ECj19Tg00FFj14Tg00G>j10Tg00Gcj12Tg00HAj11Tg0077j18Tg00Hdj35Tg00I\j16Tg00J]l>3Tg00KVg00LVg00<Sg00MYg00Nbg00Olg00Plg00Qng00Rog00T8g00U@f2R0f1R1f0R2M>3p=7g00V?R3g00W5':%93%43g00X1#0#0#0R4#0#0#0#2#1%24#1#8[A5312%61[]3]4A7012W1W2W0o"). Qed.


(* [comment removed for export] *)
Theorem s3s_A_rc : fuzz_one_cps RTA LIB_A -> rt_contracts RTA ->
  S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_s3s ()) [] "h02FZh12RCp;2p;1p;3g00D@j22Tg00ECj11Tg00XVj30Tg00V?R0g00W5'2%10f1f0g00YP30W1W0o"). Qed.


(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin RT_freeFin RT_dsec.
Theorem s3s_A02_of_cone : fuzz_one_cps RTA LIB_A ->
  S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof.
ltac2:(KReplay.run1 (kr_t_TopA_s3s ()) [] "h02ANh12FZh23HOKh32MNh41pp;2p;1p;4p;3g00D@j28Tg00ZHj17Tg00[Gj20Tg00\Ij11Tg00]Ij46Tg00^Hj22Tg00_Ij23Tg00`Hj34Tg00aNj25Tg00V?g00W5'8f0R0g00bKR1#7g00cSg00dY'0g00eeg00fhg00gl%10f1f3f2P0C6W2W4W0W3g00hlg00ioO2,21/3134'5W1o"). Qed.
