(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt ZBridge Arr HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame BBFrame LibTail MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt ARtDrv. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import Restrict RestrictLib RestrictRun NodesA SymDriveA SymDriveAX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_base A_exit_lib A_exit_defs A_unreg_globals A_exit A_stdio_defs A_stdio_write A_stdio_call A_rip A_amem_lib A_imemcpy A_fwrite_oom A_oomtail A_printf1 A_refused.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tailkit_defs A_tailkit_exit2 A_splice A_imz A_icpt_str A_icpt_strnlen A_icpt_strnlenJ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_main_inv A_main_loop A_main_fin A_main_hdr A_main_target A_main_open.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tail_lib A_tail_openfail_defs
     A_tail_openfail_S1 A_tail_openfail_S2 A_tail_openfail_S3 A_tail_openfail_S4 A_tail_openfail_S5 A_tail_openfail_S6 A_tail_openfail_S7
     A_tail_openfail_S8 A_tail_openfail_S9 A_tail_openfail_S10.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
#[local] Existing Instance Lib.PropExec.fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Lemma mrd_high : forall m (x : Z), AIMG_HI <= x < 2 ^ 64 -> mrd asegs m (wa x) = m (wa x).
Proof. intros m x Hx. unfold mrd. destruct (m (wa x)); [reflexivity|]. apply seg_rom_high. exact Hx. Qed.

Section Tail.
  Variable R : art_layout.
  Variable HIA : artA asegs R.
  Let AL := arl_AL R.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis HIMGCS : forall h, A_unreg_globals.img_cs AL (hcs asegs R HIA h).
  Variable sp0 : word.
  Hypothesis SPlo : 0x7fff80000000 <= bv_unsigned sp0.
  Hypothesis SPhi : bv_unsigned sp0 <= 0x800000000000.
  Hypothesis SPal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis STKLO : arl_stklo R = bv_unsigned sp0 - 8388608.
  Variables (path : list byte) (pathp : word) (fs0 : Fs).
  Variables (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  Variables (TOP STKHI : Z).
  Hypothesis HSTKHI : bv_unsigned sp0 <= STKHI.
  Hypothesis STKHImax : STKHI <= 2^47.
  Hypothesis STKHI64 : STKHI mod 64 = 0.

  Let msp : Z := bv_unsigned sp0 - 128.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00Y0@L10812571693.93 L1123598903.76  L11602724311.90 L11758983131.95 L16352041034.77 L187041400.74   L18983755483.83 L19122796294.78 L21538903817.75 L22049003770.83 L25071619629.103L25325058361.70 L32114292796.88 L36037975560.103L3610556270.95  L3788567612.90  L37960836342.82 L38081936810.97 L38990142939.83 L39231319166.95 L39583005574.96 L41140478957.92 L42435749866.95 L45786986535.80 L51695985839.83 L51819007707.90 L52619446531.95 L55686439908.96 L56254184707.88 L5738458375.96  L5744940978.91  L57629198784.89 L59315053158.94 L61885532617.93 L64880210292.104L64890695873.104L65459772779.91 L66247761411.95 L67543774492.77 L67752153213.94 L9840393242.87  00001801o02g03O03n04J04i05?05[06:07D07^08X09G09m0:m0;U0<g0=F0>O0?@0?m0A70AY0B80C40Ce0DH0E:0F=0G@0H20Hf0Io0Jb0KV0LW0Ma0N70Nf0OeS1R3sp04SPlo4path5pathp5STKHI7STKHI643msp3PLO3PHI3spw2lo5SPlo'5extra3LEXS1R3sp04SPlo4SPal4path5pathp5STKHI7STKHI643PLO3PHI2lo1LS1R3sp04SPlo4path5pathp5STKHI3msp3PLO3PHI3spw2lo1L5SPlo'S1R3sp04path5pathp5STKHI3msp3spw2lo1x2HxS3sp04SPlo4path5STKHI3msp3spw1LS1R3sp04SPlo4path5STKHI2lo1LS1R3sp04path5STKHI3msp3spw2lo1LS3sp04path5STKHI3spw1LS1R3sp04SPhi4path5STKHI2lo1LS1R3sp04path5STKHI3msp3spw2lo1LS1R3sp04SPlo4path5pathp5STKHI3PLO3ALO3spw1L5SPlo'5extra3LEX4PL161c4BAND2C0S3sp04SPlo4SPhi4path5STKHIS1R3sp04SPlo4path5pathp5STKHI3msp3PLO3PHI3spw1L5SPlo'1x2HxS1R3sp04path5pathp5STKHI3msp3spw2lo1L5extra3LEXS1R3sp04path5STKHI3msp3spw2lo1L1s1g2HgS3sp04SPlo4path5pathp5STKHI3msp3PLO3PHI3spw1L5SPlo'7STKHIhi1x2HxS1R3sp04path5STKHI8STKHImax3msp3spw2lo1LS1R3sp04SPlo5STKLO4path5pathp5STKHI3msp3PLO3PHI3spw2lo1L5SPlo'4LOlo7STKHIhi1s1g2HgS1R3sp04path5STKHI3msp3spw2lo1LS1R3sp04SPlo5STKLO4path5STKHI6HSTKHI3msp3SH83spw2lo1L5SPlo'4LOlo1s3LO82HgS1R3sp04path5pathp5STKHI3msp3PHI3spw2lo5extra3LEXS1R3sp04path5pathp5STKHI3msp3spw2lo5extra3LEXS1R3sp04SPlo5STKLO4path5pathp5STKHI3msp3PLO3PHI3spw2lo1L5SPlo'4LOlo1s1g2HgS1R3sp04path5STKHI6HSTKHI3spw2lo1LS1R3sp04path5STKHI3msp3spw2lo1LS1R3sp04SPlo4path5pathp5STKHI3msp3PHI3spw2lo1L5SPlo'7STKHIhiS1R3sp04path5pathp5STKHI3msp3PHI3spw2lo5extra3LEXS1R3sp04path5STKHI3msp3spw2lo1L1s1gS3sp04SPlo4path5pathp5STKHI3PLO3PHI3spw5SPlo'1x2HxS1R3sp04SPlo4path5pathp5STKHI3msp3PLO3PHI3spw2lo5SPlo'7STKHIhi1x2HxS1R3sp04SPlo4path5pathp5STKHI3msp3PLO3PHI3spw2lo5SPlo'7STKHIhi1x2HxS3sp04SPlo4path5pathp5STKHI3PLO3PHI3spw5SPlo'1x2HxS3sp04SPlo4path5pathp5STKHI3PLO3PHI3spw5SPlo'1x2Hx1CS1R3sp04SPlo5STKLO4path5STKHI6HSTKHI3msp3SH83spw2lo1L5SPlo'4LOlo1s2Hs3LO8S1R3sp04path5pathp5STKHI3msp3spw2lo1L5extra3LEX3L62S1R3sp04path5pathp5STKHI3msp3spw2lo1L5extra3LEX4L63ES1R3sp04SPlo5STKLO4path5STKHI6HSTKHI3msp3SL83SH83spw1L5SPlo'4LOloS1R3sp04SPlo5STKLO4path5pathp5STKHI3msp3PLO3PHI3spw2lo1L5SPlo'4LOlo1s1g2HgS3sp04path5STKHI3spw1LS1R3sp04path5pathp5STKHI3PLO3spw2lo1L5extra3LEXS1R3HIA3sp04SPlo4path5STKHI3msp1h2HS3spw2lo1L5SPlo'7STKHIhi1c1H". (* [comment removed for export] *)
  #[using="AL IMG ASB HIMGCS SPlo SPhi SPal STKLO HSTKHI STKHImax STKHI64 msp"] Theorem openfail_tail : openfail_stmtA R HIA sp0 path pathp fs0 can tid wp0 rp0 wp1 rp1 TOP STKHI.
  Proof.
    unfold openfail_stmtA. intros t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m mo h NHM HKh HT HS MI TM ST SSH BY NZ PLO PHI FD FS PLEN.
    ddestruct NHM as (m0 & HM0 & MU0 & WM0).
    pose proof (u64_range sp0) as SPR. pose proof (u64_range pathp) as PR.
    pose proof (art_alwf _ _ HIA) as ALWF. pose proof (hcs_ok _ _ HIA h) as CSOK. pose proof (art_lo _ _ HIA) as ALO.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. cbv delta [AL] in IMG'. ddestruct IMG' as (HGOT & HILO & HIHI & HGSB2).
    set (CS := hcs asegs R HIA h). set (KI := HK asegs R HIA h).
    set (spw := Z_to_bv 64 msp).
    assert (Uspw : bv_unsigned spw = msp) by (subst spw msp; apply unsigned_lit; lia).
    set (lo := arl_stklo R).
    set (L := Z.of_nat (length path)).
    (* [comment removed for export] *)
    assert (SPlo' : (0x7fff7f000000 + 16384 <= bv_unsigned spw)%Z) by (rewrite Uspw; subst msp; lia).
    assert (SPhi' : (bv_unsigned spw + 128 <= 0x800000000000)%Z) by (rewrite Uspw; subst msp; lia).
    assert (SPal' : (bv_unsigned spw mod 16 = 0)%Z) by (rewrite Uspw; subst msp; lia).
    assert (LOlo : (0x10007fff7fff < lo)%Z) by (subst lo; rewrite STKLO; lia).
    assert (LOhi : (lo + 16384 <= bv_unsigned spw)%Z) by (subst lo; rewrite Uspw, STKLO; subst msp; lia).
    assert (LOdeep : (bv_unsigned spw - 8388608 <= lo)%Z) by (subst lo; rewrite Uspw, STKLO; subst msp; lia).
    assert (STKHIlo : (bv_unsigned spw + 128 <= STKHI)%Z) by (rewrite Uspw; subst msp; lia).
    assert (STKHIhi : (STKHI <= 0x800000000000)%Z) by lia.
    assert (SCS : crange CS lo (STKHI - lo)). { subst CS lo. rewrite <- HS. apply (hcs_stack _ _ HIA h). }
    assert (FCS : crange CS 0x208c0 64).
    { subst CS. refine (HIMGCS h 0x208c0 64 _ _ _ _); cbv delta [AL]; rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia. }
    assert (CSTOP : forall c, CS c -> (c < 2^47)%Z). { subst CS. intros c Hc. pose proof (hcs_below_top _ _ HIA h c Hc). lia. }
    assert (TMw : tail_memA spw m can tid wp0 rp0 wp1 rp1) by (subst spw msp; exact TM).
    (* [comment removed for export] *)
    assert (MAPD : mapped m lo (bv_unsigned spw)).
    { rewrite Uspw. intros x Hx. ddestruct ST as (_ & _ & STK). destruct (STK x ltac:(subst lo; lia)) as [_ [b Hb]].
      exists b. rewrite <- (mrd_high m x) by (unfold AIMG_HI; subst lo; rewrite STKLO in Hx; lia). exact Hb. }
    (* [comment removed for export] *)
    assert (ZSH : forall s : Z, (0x7fff8000 + lo / 8 <= s < 0x7fff8000 + STKHI / 8)%Z -> m (Z_to_bv 64 s) = Some (Z_to_bv 8 0)).
    { intros s Hs. ddestruct SSH as (SL8 & SH8 & SSZ).
      assert (LO8 : lo mod 8 = 0) by (subst lo; rewrite STKLO; lia).
      set (g := 8 * (s - 0x7fff8000)).
      assert (Hg : lo <= g /\ g + 8 <= STKHI /\ g mod 8 = 0) by (subst g; lia).
      destruct (SSZ g ltac:(lia) ltac:(lia) ltac:(lia)) as [[_ Bg] _].
      ddestruct Bg as (_ & _ & B1). specialize (B1 0%nat ltac:(cbn; lia)). cbn [cells_bytes cbytes app nth_error] in B1.
      change (Z.of_nat 0) with 0 in B1. rewrite Z.add_0_r in B1. unfold shadow_of in B1.
      replace (al_sb (arl_AL R)) with 2147450880 in B1 by (symmetry; exact ASB).
      replace (2147450880 + g / 8) with s in B1 by (subst g; lia).
      change (Z_to_bv 64 s) with (wa s).
      rewrite <- (mrd_high m s) by (unfold AIMG_HI; pose proof LOlo; lia). exact B1. }
    (* [comment removed for export] *)
    assert (RD7 : mapped m (bv_unsigned pathp + L + 1) (bv_unsigned pathp + L + 1 + Z.of_nat 7)).
    { intros x Hx. subst L.
      assert (W0 : wview asegs m0 (wa x) <> None).
      { apply (hm_stack_readable _ _ HIA h [] [] m0 x HM0). rewrite HS. subst lo. rewrite STKLO. subst msp. lia. }
      assert (E0 : m (wa x) = m0 (wa x)). { apply MU0. rewrite wa_unsigned by lia. cbn. subst msp lo. rewrite STKLO. lia. }
      rewrite E0. unfold wview in W0. destruct (m0 (wa x)) as [b|] eqn:Mx; [exists b; reflexivity|].
      exfalso. destruct (find_segment asegs (bv_unsigned (wa x)) 1) as [seg|] eqn:FS1; [|exact (W0 eq_refl)].
      pose proof (find_segment_cov asegs asegs (bv_unsigned (wa x)) 1 seg FS1 ltac:(auto) 0 ltac:(lia)) as C.
      rewrite Z.add_0_r in C. apply asegs_segcov in C. unfold wa in C. rewrite unsigned_lit in C by lia. unfold AIMG_LO, AIMG_HI in C. subst lo msp. rewrite STKLO in *. lia. }
    ddestruct (u8arr_of_mapped m (bv_unsigned pathp + L + 1) 7 RD7 ltac:(lia) ltac:(lia)) as (extra & LEX & (BYX & _)).
    assert (BYbuf : bytes_at asegs m (bv_unsigned pathp) (path ++ Z_to_bv 8 0 :: extra)).
    { change (path ++ Z_to_bv 8 0 :: extra) with (path ++ ([Z_to_bv 8 0] ++ extra)). rewrite app_assoc.
      apply bytes_at_app. split; [exact BY|]. rewrite length_app. cbn [length]. subst L.
      replace (bv_unsigned pathp + Z.of_nat (length path + 1)) with (bv_unsigned pathp + Z.of_nat (length path) + 1) by lia. exact BYX. }
    assert (WIN8 : ((bv_unsigned pathp + L) / 8 * 8 + 8 <= bv_unsigned pathp + Z.of_nat (length (path ++ Z_to_bv 8 0 :: extra)))%Z).
    { rewrite length_app. cbn [length]. rewrite LEX. subst L. lia. }
    assert (Plo' : (bv_unsigned spw + 128 <= bv_unsigned pathp)%Z) by (rewrite Uspw; subst msp; lia).
    assert (Phi' : (bv_unsigned pathp + Z.of_nat (length (path ++ Z_to_bv 8 0 :: extra)) <= STKHI)%Z).
    { rewrite length_app. cbn [length]. rewrite LEX. subst L. lia. }
    assert (PL16 : (bv_unsigned pathp + L + 16 <= STKHI)%Z) by (subst L; lia).
    (* [comment removed for export] *)
    assert (SHRD : forall c, CS c -> exists b, bytes_at asegs m (shadow_of AL c) [b]).
    { subst CS. intros c Hc. destruct (hm_shadow_rd _ _ HIA h [] [] m0 c HM0 Hc) as (b & Bb & _). exists b.
      pose proof (hcs_shadow_band _ _ HIA h c Hc) as BAND. dpose (proj1 CSOK c Hc) as (C0 & C1 & C2 & _).
      eapply bytes_at_transport; [exact Bb | exact MU0 |]. cbn [disjoint_from fst snd length Z.of_nat].
      unfold shadow_of in *. cbv delta [AL] in *. rewrite ASB in *. subst lo msp. rewrite STKLO in *. lia. }
    (* [comment removed for export] *)
    set (Rg := mkR (Z_to_bv 64 0x097120) spw (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) pathp t1 t2
                  (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
                  pathp (Z_to_bv 64 (bv_unsigned sp0 + 32))
                  (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6).
    change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None m ?rom) with (mkst Rg pc m rom).
    rewrite <- FS. unfold t_die.
    (* [comment removed for export] *)
    pose proof (hk_halted _ _ HIA h) as Kh. pose proof (hk_mat _ _ HIA h) as Km. pose proof (hk_vmonly _ _ HIA h) as Kv.
    fold KI in Kh, Km, Kv, HKh. fold CS in Km.
    assert (CASES : L <= 62 \/ L = 63 \/ 64 <= L) by lia.
    destruct CASES as [L62 | [L63E | L64]].
    - (* [comment removed for export] *)
      assert (L63 : L <= 63) by lia.
      pose proof (stage_E AL CS KI IMG ALWF CSOK ASB (HIMGCS h) Kh Km Kv spw mo SPlo' SPhi' SPal' lo LOlo LOhi STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw pathp path extra Plo' PL16 PLEN L62) as N7.
      pose proof (stage_D AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH pathp path extra BYbuf Plo' PL16 PLEN L62 SHRD CSTOP N7) as N6.
      pose proof (stage_C1 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH pathp path extra eq_refl BYbuf Plo' PL16 PLEN L63 SHRD CSTOP N6) as N5.
      pose proof (stage_B2 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH pathp path extra eq_refl BYbuf NZ WIN8 Plo' Phi' PL16 PLEN SHRD CSTOP N5) as N4.
      pose proof (stage_B1 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD pathp path extra Plo' PL16 N4) as N3.
      pose proof (stage_A2 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH pathp path extra eq_refl BYbuf NZ Plo' PL16 PLEN SHRD CSTOP N3) as N2.
      exact (openfail_tailA AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' HKh FD lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl TMw MAPD pathp path extra eq_refl Plo' PL16 N2).
    - (* [comment removed for export] *)
      assert (L63 : L <= 63) by lia.
      pose proof (stage_D63 AL CS KI IMG ALWF CSOK ASB (HIMGCS h) Kh Km Kv spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw pathp path extra Plo' PL16 PLEN L63E) as N6.
      pose proof (stage_C1 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH pathp path extra eq_refl BYbuf Plo' PL16 PLEN L63 SHRD CSTOP N6) as N5.
      pose proof (stage_B2 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH pathp path extra eq_refl BYbuf NZ WIN8 Plo' Phi' PL16 PLEN SHRD CSTOP N5) as N4.
      pose proof (stage_B1 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD pathp path extra Plo' PL16 N4) as N3.
      pose proof (stage_A2 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH pathp path extra eq_refl BYbuf NZ Plo' PL16 PLEN SHRD CSTOP N3) as N2.
      exact (openfail_tailA AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' HKh FD lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl TMw MAPD pathp path extra eq_refl Plo' PL16 N2).
    - (* [comment removed for export] *)
      pose proof (stage_D64 AL CS KI IMG ALWF CSOK ASB (HIMGCS h) Kh Km Kv spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH pathp path extra BYbuf Plo' PL16 PLEN L64 SHRD CSTOP) as N6.
      pose proof (stage_C1X AL CS KI IMG CSOK ASB Kh Km Kv spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH pathp path extra eq_refl BYbuf Plo' PL16 PLEN L64 SHRD CSTOP N6) as N5.
      pose proof (stage_B2 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH pathp path extra eq_refl BYbuf NZ WIN8 Plo' Phi' PL16 PLEN SHRD CSTOP N5) as N4.
      pose proof (stage_B1 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD pathp path extra Plo' PL16 N4) as N3.
      pose proof (stage_A2 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH pathp path extra eq_refl BYbuf NZ Plo' PL16 PLEN SHRD CSTOP N3) as N2.
      exact (openfail_tailA AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' HKh FD lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl TMw MAPD pathp path extra eq_refl Plo' PL16 N2).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Tail.

