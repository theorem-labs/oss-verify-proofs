(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells CellsX Step Frame RegsExt ZBridge Arr HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame BBFrame LibTail MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt ARtDrv. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import Restrict RestrictLib RestrictRun NodesA SymDriveA SymDriveAX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_base A_exit_lib A_exit_defs A_unreg_globals A_exit A_stdio_defs A_stdio_write A_stdio_call A_rip A_amem_lib A_imemcpy A_fwrite_oom A_oomtail A_printf1 A_refused.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tailkit_defs A_tailkit_exit2 A_splice A_imz A_icpt_str A_icpt_strnlen A_icpt_strnlenJ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_main_inv A_main_loop A_main_fin A_main_hdr A_main_target A_main_open.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tailkit_exit3 A_tail_lib A_tail_usage_defs
     A_tail_usage_S1 A_tail_usage_S2 A_tail_usage_S3 A_tail_usage_S4 A_tail_usage_S5 A_tail_usage_S6 A_tail_usage_S7
     A_tail_usage_S8 A_tail_usage_S9 A_tail_usage_S10.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
#[local] Existing Instance Lib.PropExec.fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Lemma mrd_highU : forall m (x : Z), AIMG_HI <= x < 2 ^ 64 -> mrd asegs m (wa x) = m (wa x).
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
  Variables (fs0 : Fs) (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  Variables (TOP STKHI : Z).
  Hypothesis STKHImax : STKHI <= 2^47.
  Hypothesis STKHI64 : STKHI mod 64 = 0.
  Variables (argc : Z) (a0p : word) (a0s : list byte).

  Let msp : Z := bv_unsigned sp0 - 128.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@L1123598903.82  L11602724311.97 L11759212507.101L16352041034.83 L17745104047.89 L18707356141.99 L191187780.80   L19122796294.84 L21538903817.81 L24983406586.80 L25325058361.71 L26008783236.79 L32114292796.94 L33375739167.93 L35284942895.105L3610556270.102 L36413574617.60 L36601947693.100L37362952829.101L37638448561.80 L3788567612.96  L37960836342.88 L38081936810.104L38273664771.102L39231319166.102L39583005574.103L42435749866.102L42573235972.92 L44736016091.89 L47206185255.86 L48388952314.89 L51170975195.89 L51819007707.97 L55686439908.103L56254184707.95 L5738458375.102 L59315053158.100L61885532617.100L65459772779.98 L66247761411.102L67543774492.83 L8666413217.115 L9719102676.116 L9725394273.116 L9840393242.93  00001202802f03M04404g05K05i06M07007I07h08c09A0:20:`0;N0<j0>60>Y0?Z0@J0A]0BT0Ce0D\0Eg0FE0Fl0GV0H=0Hd0If0JQ0KU0Lj0Ml0O=0PF0QQ0Qo0Rd0S]0TW0U^S1R3sp04SPlo4SPal5STKHI7STKHI644argc3a0p3a0s3pad3PLO3PHI4ARGC2lo1LS1R3sp04SPlo5STKHI4argc3a0p3a0s3msp3pad3PLO4ARGC6HSTKHI3spw2lo1L5SPlo'S1R3sp05STKHI4argc3a0p3a0s3msp3pad3spw2lo1x2HxS3sp04SPlo5STKHI4argc3a0s3msp3pad3spw1LS1R3sp05STKHI4argc3a0s3msp3pad3spw2lo1LS1R3sp05STKHI4argc3a0p3a0s3msp3pad3spw2lo5extra3LEXS1R3sp04SPlo5STKHI4argc3a0s3pad2lo1LS3sp05STKHI4argc3a0s3pad3spw1LS1R3sp04SPhi5STKHI4argc3a0s3pad2lo1LS1R3sp05STKHI4argc3a0s3msp3pad2lo1LS3sp04SPlo4SPhi5STKHI3a0sS1R3sp05STKHI4argc3a0s3pad2lo1LS1R3sp04SPlo5STKHI4argc3a0s3msp3pad6HSTKHI3spw1L5SPlo'1x2HxS3sp05STKHI4argc3a0s3pad3spw1LS1R3sp05STKHI4argc3a0p3a0s3pad3spw2lo1L5extra3LEXS1R3sp05STKHI4argc3a0s3msp3pad3spw2lo1L1s1g2HgS3sp04SPlo5STKHI4argc3a0p3a0s3msp3PLO3PHI4ARGCS1R3sp04SPlo5STKHI7STKHI644argc3a0p3a0s3msp3pad3PLO4ARGC3spw4Uspw2lo5SPlo'7STKHIlo5extra3LEXS1R3sp04SPlo5STKHI4argc3a0p3a0s3pad3PLO4ARGC6HSTKHI3spw2lo1L5SPlo'5extra3LEXS1R3sp05STKHI4argc3a0s3msp3pad2lo1LS3sp04SPlo5STKHI4argc3a0s3msp3pad6HSTKHI3spw1L5SPlo'7STKHIhi1x2HxS1R3sp05STKHI8STKHImax4argc3a0s3msp3pad3spw2lo1LS1R3sp04SPlo5STKLO5STKHI4argc3a0s3msp3pad6HSTKHI3spw2lo1L5SPlo'4LOlo7STKHIhi1s1g2HgS1R3sp05STKHI4argc3a0p3a0s3msp3pad3PHI3spw2lo5extra3LEXS1R3sp04SPlo5STKLO5STKHI4argc3a0s3msp3pad3SH86HSTKHI3spw2lo1L5SPlo'4LOlo1s3LO82HgS1R3sp05STKHI4argc3a0p3a0s3msp3pad3PHI3spw2lo5extra3LEXS1R3sp04SPlo5STKLO5STKHI4argc3a0s3msp3pad6HSTKHI3spw2lo1L5SPlo'4LOlo1s1g2HgS3sp05STKHI4argc3a0s3pad3spw1LS1R3sp05STKHI4argc3a0s3msp3pad3spw2lo1LS1R3sp05STKHI4argc3a0s3pad6HSTKHI3spw2lo1LS1R3sp05STKHI4argc3a0s3msp3pad3spw2lo1LS1R3sp05STKHI4argc3a0s3msp3pad3spw2lo1LS1R3sp04SPlo5STKHI4argc3a0p3a0s3msp3pad3PHI3spw2lo1L5SPlo'7STKHIhiS1R3sp05STKHI4argc3a0s3msp3pad3spw2lo1L1s1gS3sp04SPlo5STKHI4argc3a0p3a0s3pad3PLO3PHI4ARGC6HSTKHI3spw5SPlo'1x2HxS1R3sp04SPlo5STKHI4argc3a0p3a0s3msp3pad3PLO3PHI4ARGC6HSTKHI3spw2lo5SPlo'7STKHIhi1x2HxS3sp04SPlo5STKHI4argc3a0p3a0s3pad3PLO4ARGC6HSTKHI3spw5SPlo'1x2Hx1CS1R3sp04SPlo5STKLO5STKHI4argc3a0s3msp3pad3SH86HSTKHI3spw2lo1L5SPlo'4LOlo1s2Hs3LO8S1R3sp04SPlo5STKLO5STKHI4argc3a0s3msp3pad3SL83SH86HSTKHI3spw1L5SPlo'4LOloS1R3sp04SPlo5STKLO5STKHI4argc3a0s3msp3pad6HSTKHI3spw2lo1L5SPlo'4LOlo1s1g2HgS3sp05STKHI4argc3a0s3pad3spw1LS1R3sp05STKHI4argc3a0p3a0s3msp3pad3spw2lo1L5extra3LEXS1R3sp05STKHI4argc3a0p3a0s3msp3pad3spw2lo1L5extra3LEX3L62S1R3sp05STKHI4argc3a0p3a0s3msp3pad3spw2lo1L5extra3LEX4L63ES1R3HIA3sp04SPlo5STKHI4argc3a0s3msp3pad1h2HS3spw2lo1L5SPlo'7STKHIhi1c1H". (* [comment removed for export] *)
  #[using="AL IMG ASB HIMGCS SPlo SPhi SPal STKLO STKHImax STKHI64 msp"] Theorem usage_tail : usage_stmtA R HIA sp0 fs0 can tid wp0 rp0 wp1 rp1 TOP STKHI argc a0p a0s.
  Proof.
    unfold usage_stmtA. intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 pad m mo h HM0 HKh HT HS MI TM ST SSH UF AV BY NZ PLO PHI FD FS PLEN ARGC.
    assert (HSTKHI : bv_unsigned sp0 + 24 <= STKHI) by lia.
    pose proof (u64_range sp0) as SPR. pose proof (u64_range a0p) as PR.
    pose proof (art_alwf _ _ HIA) as ALWF. pose proof (hcs_ok _ _ HIA h) as CSOK. pose proof (art_lo _ _ HIA) as ALO.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. cbv delta [AL] in IMG'. ddestruct IMG' as (HGOT & HILO & HIHI & HGSB2).
    set (CS := hcs asegs R HIA h). set (KI := HK asegs R HIA h).
    set (spw := Z_to_bv 64 msp).
    assert (Uspw : bv_unsigned spw = msp) by (subst spw msp; apply unsigned_lit; lia).
    set (lo := arl_stklo R).
    set (L := Z.of_nat (length a0s)).
    (* [comment removed for export] *)
    pose proof (rw_cells_bound asegs m msp _ UF) as UFB.
    unfold UFRAME in UF.
    change ([CB 8 pad; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (bv_unsigned sp0 + 8 * argc + 16));
             C8 (Z_to_bv 64 0x0970e0); C8 (Z_to_bv 64 argc); C8 (Z_to_bv 64 (bv_unsigned sp0 + 8)); C8 (Z_to_bv 64 0x0e0aa8)])
      with ([CB 8 pad] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (bv_unsigned sp0 + 8 * argc + 16));
             C8 (Z_to_bv 64 0x0970e0); C8 (Z_to_bv 64 argc); C8 (Z_to_bv 64 (bv_unsigned sp0 + 8))] ++ [C8 (Z_to_bv 64 0x0e0aa8)]) in UF.
    pose proof (rw_cells_split3 asegs m msp _ _ _ UF) as (UF0 & FRW & FRA). cbn [cells_size csize Nat.add] in FRW, FRA.
    change (Z.of_nat 8) with 8 in FRW, FRA. change (Z.of_nat 64) with 64 in FRA.
    replace (msp + 8 + 64) with (bv_unsigned spw + 72) in FRA by (rewrite Uspw; lia).
    replace (msp + 8) with (bv_unsigned spw + 8) in FRW by (rewrite Uspw; lia).
    assert (AV0 : rw_cells asegs m (bv_unsigned spw + 136) [C8 a0p]) by (rewrite Uspw; subst msp; replace (bv_unsigned sp0 - 128 + 136) with (bv_unsigned sp0 + 8) by lia; exact AV).
    (* [comment removed for export] *)
    assert (SPlo' : (0x7fff7f000000 + 16384 <= bv_unsigned spw)%Z) by (rewrite Uspw; subst msp; lia).
    assert (SPhi' : (bv_unsigned spw + 128 <= 0x800000000000)%Z) by (rewrite Uspw; subst msp; lia).
    assert (SPal' : (bv_unsigned spw mod 16 = 0)%Z) by (rewrite Uspw; subst msp; lia).
    assert (LOlo : (0x10007fff7fff < lo)%Z) by (subst lo; rewrite STKLO; lia).
    assert (LOhi : (lo + 16384 <= bv_unsigned spw)%Z) by (subst lo; rewrite Uspw, STKLO; subst msp; lia).
    assert (LOdeep : (bv_unsigned spw - 8388608 <= lo)%Z) by (subst lo; rewrite Uspw, STKLO; subst msp; lia).
    assert (STKHIlo : (bv_unsigned spw + 144 <= STKHI)%Z) by (rewrite Uspw; subst msp; lia).
    assert (STKHIhi : (STKHI <= 0x800000000000)%Z) by lia.
    assert (SCS : crange CS lo (STKHI - lo)). { subst CS lo. rewrite <- HS. apply (hcs_stack _ _ HIA h). }
    assert (FCS : crange CS 0x16bc0 64).
    { subst CS. refine (HIMGCS h 0x16bc0 64 _ _ _ _); cbv delta [AL]; rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia. }
    assert (CSTOP : forall c, CS c -> (c < 2^47)%Z). { subst CS. intros c Hc. pose proof (hcs_below_top _ _ HIA h c Hc). lia. }
    assert (TMw : tail_memA spw m can tid wp0 rp0 wp1 rp1) by (subst spw msp; exact TM).
    assert (MAPD : mapped m lo (bv_unsigned spw)).
    { rewrite Uspw. intros x Hx. ddestruct ST as (_ & _ & STK). destruct (STK x ltac:(subst lo; lia)) as [_ [b Hb]].
      exists b. rewrite <- (mrd_highU m x) by (unfold AIMG_HI; subst lo; rewrite STKLO in Hx; lia). exact Hb. }
    (* [comment removed for export] *)
    assert (UFR : stk asegs m (bv_unsigned spw) (bv_unsigned spw + 80)).
    { rewrite Uspw. pose proof (stk_release asegs m lo msp _ ST UF ltac:(subst lo; rewrite STKLO; subst msp; lia)) as ST80.
      cbn [cells_size csize Nat.add app length] in ST80.
      exact (proj2 (stk_split asegs m lo msp (msp + 80) ST80 ltac:(subst lo; rewrite STKLO; subst msp; lia))). }
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
      rewrite <- (mrd_highU m s) by (unfold AIMG_HI; pose proof LOlo; lia). exact B1. }
    (* [comment removed for export] *)
    assert (RD7 : mapped m (bv_unsigned a0p + L + 1) (bv_unsigned a0p + L + 1 + Z.of_nat 7)).
    { intros x Hx. subst L.
      assert (W0 : wview asegs m (wa x) <> None).
      { apply (hm_stack_readable _ _ HIA h [] [] m x HM0). rewrite HS. subst lo. rewrite STKLO. subst msp. lia. }
      unfold wview in W0. destruct (m (wa x)) as [b|] eqn:Mx; [exists b; reflexivity|].
      exfalso. destruct (find_segment asegs (bv_unsigned (wa x)) 1) as [seg|] eqn:FS1; [|exact (W0 eq_refl)].
      pose proof (find_segment_cov asegs asegs (bv_unsigned (wa x)) 1 seg FS1 ltac:(auto) 0 ltac:(lia)) as C.
      rewrite Z.add_0_r in C. apply asegs_segcov in C. unfold wa in C. rewrite unsigned_lit in C by lia. unfold AIMG_LO, AIMG_HI in C. subst lo msp. rewrite STKLO in *. lia. }
    ddestruct (u8arr_of_mapped m (bv_unsigned a0p + L + 1) 7 RD7 ltac:(lia) ltac:(lia)) as (extra & LEX & (BYX & _)).
    assert (BYbuf : bytes_at asegs m (bv_unsigned a0p) (a0s ++ Z_to_bv 8 0 :: extra)).
    { change (a0s ++ Z_to_bv 8 0 :: extra) with (a0s ++ ([Z_to_bv 8 0] ++ extra)). rewrite app_assoc.
      apply bytes_at_app. split; [exact BY|]. rewrite length_app. cbn [length]. subst L.
      replace (bv_unsigned a0p + Z.of_nat (length a0s + 1)) with (bv_unsigned a0p + Z.of_nat (length a0s) + 1) by lia. exact BYX. }
    assert (WIN8 : ((bv_unsigned a0p + L) / 8 * 8 + 8 <= bv_unsigned a0p + Z.of_nat (length (a0s ++ Z_to_bv 8 0 :: extra)))%Z).
    { rewrite length_app. cbn [length]. rewrite LEX. subst L. lia. }
    assert (Plo' : (bv_unsigned spw + 128 <= bv_unsigned a0p)%Z) by (rewrite Uspw; subst msp; lia).
    assert (Phi' : (bv_unsigned a0p + Z.of_nat (length (a0s ++ Z_to_bv 8 0 :: extra)) <= STKHI)%Z).
    { rewrite length_app. cbn [length]. rewrite LEX. subst L. lia. }
    assert (PL16 : (bv_unsigned a0p + L + 16 <= STKHI)%Z) by (subst L; lia).
    (* [comment removed for export] *)
    assert (SHRD : forall c, CS c -> exists b, bytes_at asegs m (shadow_of AL c) [b]).
    { subst CS. intros c Hc. destruct (hm_shadow_rd _ _ HIA h [] [] m c HM0 Hc) as (b & Bb & _). exists b. exact Bb. }
    (* [comment removed for export] *)
    unfold UREGS. fold msp. fold spw.
    replace (MS (mkR (Z_to_bv 64 0x0e0aa8) spw (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
                  (Z_to_bv 64 2) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (bv_unsigned sp0 + 8))
                  (Z_to_bv 64 (bv_unsigned sp0 + 8 * argc + 16)) a3 a4 a5 a6 a7
                  (Z_to_bv 64 0x0970e0) (Z_to_bv 64 (bv_unsigned sp0 + 8 * argc + 16))
                  (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6))
      with (MS (mkR (Z_to_bv 64 0x0e0aa8) spw (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
                  (Z_to_bv 64 2) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (bv_unsigned spw + 136))
                  (Z_to_bv 64 (bv_unsigned sp0 + 8 * argc + 16)) a3 a4 a5 a6 a7
                  (Z_to_bv 64 0x0970e0) (Z_to_bv 64 (bv_unsigned sp0 + 8 * argc + 16))
                  (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6))
      by (rewrite Uspw; subst msp; do 2 f_equal; f_equal; lia).
    set (Rg := mkR (Z_to_bv 64 0x0e0aa8) spw (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
                  (Z_to_bv 64 2) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (bv_unsigned spw + 136))
                  (Z_to_bv 64 (bv_unsigned sp0 + 8 * argc + 16)) a3 a4 a5 a6 a7
                  (Z_to_bv 64 0x0970e0) (Z_to_bv 64 (bv_unsigned sp0 + 8 * argc + 16))
                  (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6).
    change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None m ?rom) with (mkst Rg pc m rom).
    rewrite <- FS. unfold t_die.
    (* [comment removed for export] *)
    set (w8 := Z_to_bv 64 0). set (w40 := Z_to_bv 64 (bv_unsigned sp0 + 8 * argc + 16)). set (w48 := Z_to_bv 64 0x0970e0).
    set (w56 := Z_to_bv 64 argc). set (w64 := Z_to_bv 64 (bv_unsigned sp0 + 8)).
    fold w8 w40 w48 w56 w64 in FRW.
    (* [comment removed for export] *)
    pose proof (hk_halted _ _ HIA h) as Kh. pose proof (hk_mat _ _ HIA h) as Km. pose proof (hk_vmonly _ _ HIA h) as Kv.
    fold KI in Kh, Km, Kv, HKh. fold CS in Km.
    assert (CASES : L <= 66 \/ 67 <= L <= 73 \/ 74 <= L) by lia.
    destruct CASES as [L62 | [L63E | L64]].
    - (* [comment removed for export] *)
      assert (L63 : L <= 73) by lia.
      pose proof (stage_E AL CS KI IMG ALWF CSOK ASB (HIMGCS h) Kh Km Kv spw mo SPlo' SPhi' SPal' lo LOlo LOhi STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw UFR w8 w8 w8 w8 w40 w48 w56 w64 FRW a0p a0s extra Plo' PL16 PLEN L62) as N7.
      pose proof (stage_D AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH a0p a0s extra BYbuf Plo' PL16 PLEN L62 SHRD CSTOP N7) as N6.
      pose proof (stage_C1 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH a0p a0s extra BYbuf Plo' PL16 PLEN L63 SHRD CSTOP N6) as N5.
      pose proof (stage_B2 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH a0p a0s extra BYbuf NZ WIN8 Plo' Phi' PL16 PLEN SHRD CSTOP N5) as N4.
      pose proof (stage_B1 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD a0p a0s extra Plo' N4) as N3.
      pose proof (stage_A2 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH a0p a0s extra BYbuf NZ Plo' PL16 PLEN SHRD CSTOP N3) as N2.
      exact (usage_tailA AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' HKh FD lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl TMw MAPD a0p a0s extra eq_refl AV0 FRA Plo' PL16 N2).
    - (* [comment removed for export] *)
      assert (L63 : L <= 73) by lia.
      pose proof (stage_D63 AL CS KI IMG ALWF CSOK ASB (HIMGCS h) Kh Km Kv spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw UFR w8 w8 w8 w8 w40 w48 w56 w64 FRW a0p a0s extra Plo' PL16 PLEN L63E) as N6.
      pose proof (stage_C1 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH a0p a0s extra BYbuf Plo' PL16 PLEN L63 SHRD CSTOP N6) as N5.
      pose proof (stage_B2 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH a0p a0s extra BYbuf NZ WIN8 Plo' Phi' PL16 PLEN SHRD CSTOP N5) as N4.
      pose proof (stage_B1 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD a0p a0s extra Plo' N4) as N3.
      pose proof (stage_A2 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH a0p a0s extra BYbuf NZ Plo' PL16 PLEN SHRD CSTOP N3) as N2.
      exact (usage_tailA AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' HKh FD lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl TMw MAPD a0p a0s extra eq_refl AV0 FRA Plo' PL16 N2).
    - (* [comment removed for export] *)
      pose proof (stage_D64 AL CS KI IMG ALWF CSOK ASB (HIMGCS h) Kh Km Kv spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD UFR w8 w8 w8 w8 w40 w48 w56 w64 FRW ZSH a0p a0s extra BYbuf Plo' PL16 PLEN L64 SHRD CSTOP) as N6.
      pose proof (stage_C1X AL CS KI IMG CSOK ASB Kh Km Kv spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH a0p a0s extra BYbuf Plo' PL16 PLEN L64 SHRD CSTOP N6) as N5.
      pose proof (stage_B2 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH a0p a0s extra BYbuf NZ WIN8 Plo' Phi' PL16 PLEN SHRD CSTOP N5) as N4.
      pose proof (stage_B1 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD a0p a0s extra Plo' N4) as N3.
      pose proof (stage_A2 AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 TMw MAPD ZSH a0p a0s extra BYbuf NZ Plo' PL16 PLEN SHRD CSTOP N3) as N2.
      exact (usage_tailA AL CS KI IMG ALWF CSOK ASB Kh Km spw mo SPlo' SPhi' SPal' HKh FD lo LOlo LOhi LOdeep STKHI STKHIlo STKHIhi STKHI64 SCS FCS Rg m can tid wp0 rp0 wp1 rp1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl TMw MAPD a0p a0s extra eq_refl AV0 FRA Plo' PL16 N2).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Tail.
