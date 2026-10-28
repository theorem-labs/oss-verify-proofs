(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Shape Mem Cells Frame HeapIface Asn1Aux RegsExt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt ARtDrv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import ATopContract24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_unreg_globals A_tailkit_defs ATopContract A_main_inv A_main_loop A_main_fin A_main_hdr A_main_target A_main_open A_main_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import CatExec AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AHeapR AH0Spec0 AH0Spec AH0Bridge AHeapMallocH AFreePost AW_Populate AHeapHIA AHeapHID AH0Base AH0Layout AH0Mem1 AW_FreePhPZ AW_ModDieT AW_B12WalkP.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_entry_bridge A_entry_mem A_tail_openfail A_tail_readerr A_tail_usage.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_A_entry_pack () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Lists.ListDef.nth"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.me_params"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.me_init"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.cnst"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.cnst_ok"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.me_cnsts"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.me_regs"; "RocqVerifyHarness.AgentSubmission.B.A_main_open.MREGS"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.list"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L36993529711.4L4702142353.4 00000500:S1r1RS1r1R". (* [comment removed for export] *)
Lemma reg_cases : ltac2:(CDefT.buildp (gd_tbl_A_entry_pack ()) "PP,P,(0.&5.)SpP,Pk,$1.P,(2.R1.#20.)A1.R3.(3.&5.(4.R2.))Pr,(0.&5.)A1.R3.R1.")
(* [comment removed for export] *).
Proof.
  intros P H r. rewrite <- (bitvector.definitions.Z_to_bv_bv_unsigned 5 r).
  pose proof (bitvector.definitions.bv_unsigned_in_range 5 r) as R. unfold bitvector.definitions.bv_modulus in R. cbn in R.
  replace (bv_unsigned r) with (Z.of_nat (Z.to_nat (bv_unsigned r))) by lia. apply H. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L12593543204.3300001hS2x12x22x32x42x52x62x72x82x93x103x113x123x133x143x153x163x173x183x193x203x213x223x233x243x253x263x273x283x293x303x311k1H". (* [comment removed for export] *)
Lemma getr_mkR : ltac2:(CDefT.buildp (gd_tbl_A_entry_pack ()) "Px1,(0.&40.)Px2,(0.&40.)Px3,(0.&40.)Px4,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px8,(0.&40.)Px9,(0.&40.)Px10,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Px18,(0.&40.)Px19,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Px25,(0.&40.)Px26,(0.&40.)Px27,(0.&40.)Px28,(0.&40.)Px29,(0.&40.)Px30,(0.&40.)Px31,(0.&40.)Pk,$1.P,(2.R1.#20.)(5.(0.&40.)(6.(7.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)(3.&5.(4.R2.)))(8.(0.&40.)R2.(9.(0.&40.)(3.&40.=)(9.(0.&40.)R21.(9.(0.&40.)R20.(9.(0.&40.)R1?.(9.(0.&40.)R1>.(9.(0.&40.)R1=.(9.(0.&40.)R1<.(9.(0.&40.)R1;.(9.(0.&40.)R1:.(9.(0.&40.)R19.(9.(0.&40.)R18.(9.(0.&40.)R17.(9.(0.&40.)R16.(9.(0.&40.)R15.(9.(0.&40.)R14.(9.(0.&40.)R13.(9.(0.&40.)R12.(9.(0.&40.)R11.(9.(0.&40.)R10.(9.(0.&40.)R?.(9.(0.&40.)R>.(9.(0.&40.)R=.(9.(0.&40.)R<.(9.(0.&40.)R;.(9.(0.&40.)R:.(9.(0.&40.)R9.(9.(0.&40.)R8.(9.(0.&40.)R7.(9.(0.&40.)R6.(9.(0.&40.)R5.(9.(0.&40.)R4.(9.(0.&40.)R3.(:.(0.&40.))))))))))))))))))))))))))))))))))(3.&40.=)))")
(* [comment removed for export] *).
Proof.
  intros. do 32 (destruct k as [|k]; [reflexivity|]). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zreg H :=
  lazymatch type of H with ?g ?R ?r = ?v =>
    let z := eval vm_compute in (bv_unsigned r) in change (getr R (Z_to_bv 5 z) = v) in H end.

Section Pack.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Let hAR : arun := arun_of sp Hsp.
  #[local] Existing Instance hAR.
  Let STKLO : Z := bv_unsigned sp - 2 ^ 23.
  Let R : art_layout := R0 STKLO.
  (* [comment removed for export] *)
  Let B12 : b12_T := AW_B12WalkP.b12_walk.      (* [comment removed for export] *)
  Let MOD_DIE : mod_die_T := AW_ModDieT.mod_die_walk.      (* [comment removed for export] *)
  Let FH : @freeH_T hAR STKLO := @AW_FreePhPZ.freeH hAR STKLO (STKLO_OK_of sp Hsp).      (* [comment removed for export] *)
  Let HIA : artA asegs R := @artA_i hAR STKLO (STKLO_OK_of sp Hsp) B12 MOD_DIE FH.
  (* [comment removed for export] *)
  Let HID : artD asegs R HIA := @artD_i hAR STKLO (STKLO_OK_of sp Hsp) B12 MOD_DIE FH.      (* [comment removed for export] *)
  Let HID_fresh : forall (h : HST asegs R HIA) (c : Z), r_mapped_user (h_reg (hh STKLO h) c) = 0 -> hfresh asegs R HIA HID h c
    := @AHeapHID.HID_fresh hAR STKLO (STKLO_OK_of sp Hsp) B12 MOD_DIE FH.
  (* [comment removed for export] *)
  Variable SI : sinv (arl_L R).
  Hypothesis SIFP : forall a, ~ outside (si_fp SI) a -> 0x63c0a0 <= a < 0x63c180.
  Variables (PHI : Z -> Z) (FPHI : Z).
  Hypothesis PHI_max : forall n, 0 <= n < 2^26 -> 0 <= PHI n <= FPHI.
  Variable FSTK : Z.
  Hypothesis FSTK_range : 0 <= FSTK <= 2^22.
  Variables (FFR : Z -> Z) (FFFR : Z).
  Hypothesis FFR_max : forall n, 0 <= n < 2^26 -> 0 <= FFR n <= FFFR.
  Variable C24f : Z.
  Hypothesis C24F_max : C24f <= 65536.
  Hypothesis FUZZ : fuzz_entry_stmtA24 asegs R HIA SI PHI FSTK C24f FFR FUZZ_ENTRY.
  (* [comment removed for export] *)
  Definition V0c : Z := 402392064.
  Definition FR0c : Z := 63.
  Hypothesis HVF : V0c + 2^28 + 4 * FPHI + 8 * ARt.AVOL_CALL <= ARt.AVOL_MAX.
  Hypothesis HFRF : FR0c + 4 * FFFR + 16 <= ARt.FR_MAX.
  (* [comment removed for export] *)

  Let sp0 : Z := bv_unsigned sp.
  Let STKHI : Z := ESTKHI sp rdraw argv envp uid hw.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L28701528336.45L3826535641.45 L55254847920.45L65351717296.4500000b01R02D036S2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI1a1n2H2S2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI1a2H1S2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI1a1n2H4S2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI1a1n2H3". (* [comment removed for export] *)
  #[using="rdraw argv envp uid hw sp0 STKHI"] Lemma HIMGCS : forall h, A_unreg_globals.img_cs (arl_AL R) (hcs asegs R HIA h).
  Proof.
    intros h a n H1 H2 H3 H4. apply (hcs_img asegs R HIA h a n); cbn [arl_AL R R0 al_img_lo al_img_hi al_got al_gsb AL0] in *; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Hsp"] Lemma SPal : sp0 mod 16 = 0.
  Proof. dpose Hsp as (_ & _ & AL). exact AL. Qed.
  (* [comment removed for export] *)
  #[using="Hsp"] Lemma SPlo : 0x7fff80000000 <= sp0.
  Proof. dpose Hsp as (LO & _ & _). exact LO. Qed.
  #[using="Hsp"] Lemma SPhi : sp0 <= 0x800000000000.
  Proof. dpose Hsp as (_ & HI & _). exact HI. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L10842337764.3800000[S2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI". (* [comment removed for export] *)
  #[using="sp rdraw argv envp uid hw STKLO sp0 STKHI"] Lemma HV0 : V0c + 2^29 <= ARtDrv.AVOL_SPLIT.
  Proof. unfold V0c, ARtDrv.AVOL_SPLIT. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L1412672389.70 L15524745311.70L16088256383.67L50735752720.71L7081782237.70 00000b01X02G03:03jS2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI2LO3HIwS2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI3AVL3SPR2HkS2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI3AVLS2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI2Rg1k2HkS2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI1p2Hk". (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit STKLO sp0 STKHI"] Lemma entry_regs : ltac2:(CDefT.buildp (gd_tbl_A_entry_pack ()) "Pp,$;.PRg,(<.&5.(0.&40.))P,(=.Vsp,Vbrk0,Vrdraw,Vargv,Venvp,Vuid,Vhw,R2.)P,(>.$?.$10.(11.R3.))P,(12.R4.R3.)Pr,(0.&5.)(5.(0.&40.)(6.R5.R1.)(6.(13.Vsp,(6.R5.(3.&5.+5.))(6.R5.(3.&5.+6.))(6.R5.(3.&5.+7.))(6.R5.(3.&5.+=.))(6.R5.(3.&5.+>.))(6.R5.(3.&5.+?.))(6.R5.(3.&5.+10.))(6.R5.(3.&5.+11.))(6.R5.(3.&5.+1<.))(6.R5.(3.&5.+1=.))(6.R5.(3.&5.+1>.))(6.R5.(3.&5.+1?.))(4.(14.(15.(0.&8.))Vargv,)))R1.))")
(* [comment removed for export] *).
  Proof.
    intros p Rg HI HCN HR.
    dpose (me_regs_sp sp brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit p Rg HI HR) as (H1 & H2 & H3 & H4 & H10 & H11 & H8 & H9 & H18 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    pose proof HR as X. unfold me_regs in X. ddestruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H12 & _ & _ & _ & _ & _ & _ & H19 & _).
    zreg H1. zreg H2. zreg H3. zreg H4. zreg H8. zreg H9. zreg H10. zreg H11. zreg H12. zreg H18. zreg H19.
    zreg H20. zreg H21. zreg H22. zreg H23. zreg H24. zreg H25. zreg H26. zreg H27.
    pose proof (r_s1 p HCN) as R1. pose proof (r_s2 p HCN) as R2. pose proof (HSP sp brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit p HI HCN) as E.
    pose proof (valid_argv_len argv Hva) as AVL.
    assert (ARGC : argc p = Z_to_bv 64 (Z.of_nat (length argv))) by (ddestruct HI as (_ & X & _); exact X).
    assert (Hargc : uv p v_argc = Z.of_nat (length argv)). { unfold uv. cbn [pget]. rewrite ARGC. apply u_lit64. lia. }
    assert (SPR : 0x7fff80000000 <= bv_unsigned sp <= 2 ^ 47) by (dpose Hsp as (LO & HIw & _); unfold sp_window_lo in LO; unfold sp_window_hi in HIw; lia).
    unfold MREGS. cbv zeta. apply reg_cases. intros k Hk. rewrite getr_mkR by exact Hk.
    do 32 (destruct k as [|k]; [lazy [nth]; match goal with |- getr _ (Z_to_bv 5 ?z) = _ => let z' := eval vm_compute in z in change z with z' end;
      first [ reflexivity
            | assumption
            | rewrite H2; rewrite <- v_addi_alu; unfold ABoot.PropExec.v_addi; f_equal; lia
            | rewrite H11; rewrite <- v_addi_alu; unfold ABoot.PropExec.v_addi; f_equal; lia
            | rewrite H8; rewrite <- v_addi_alu; unfold ABoot.PropExec.v_addi; f_equal; lia
            | rewrite H10; exact ARGC | rewrite H9; exact ARGC
            | rewrite H12; symmetry; apply (w64_zev p); [cbn [zev]; rewrite Hargc, E; unfold SP; lia | lia]
            | rewrite H19; symmetry; apply (w64_zev p); [cbn [zev]; rewrite Hargc, E; unfold SP; lia | lia] ] | ]).
    lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?L10310197428.82L1412672389.74 L14351803558.74L14355133690.76L22302910508.84L22307109561.87L30220617564.86L30224815561.89L36056276022.8 L37006658063.87L39589161951.86L39589161951.87L39589161951.89L4178072435.87 L42845160614.86L42845160614.89L43368281014.8 L45264393012.76L46523320165.77L50200610567.79L55684177831.86L55696756018.83L56216305487.86L56216305487.89L56331684701.87L59323266950.82L71837489.87   00000b01X02J03<03o04f05]06T07808608l09g0:b0;Y0<K0=F0=j0>Y0?H0@70@i0AW0BP0CV0DS0E=0F4S2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI3AVN2LES2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI3AVN2LO3HIwS2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI2T13AVNS2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI2T13AVNS2sp5rdraw4envp3uid2hw3a0s4path5STKLO3sp05STKHI3AVNS2sp5rdraw4envp3uid2hw3a0s4path5STKLO3sp05STKHI3AVN3LOpS2sp5rdraw4envp3uid2hw3a0s4path1x1l5STKLO3sp05STKHI3AVNS2sp5rdraw4envp3uid2hw3a0s4path1x1l5STKLO3sp05STKHI3AVNS2sp5rdraw4argv4envp3uid2hw5STKHI2T2S2sp5rdraw4envp3uid2hw3a0s4path5STKLO3sp05STKHI2T13AVN3SPR3LOpS2sp5rdraw4envp3uid2hw3a0s5STKLO3sp05STKHI3AVN3LOp3HIpS2sp5rdraw4envp3uid2hw3a0s4path5STKLO3sp05STKHI3AVN3LOp3HIpS2sp5rdraw4envp3uid2hw3a0s4path1x1l5STKLO3sp05STKHI3AVN3HIpS2sp5rdraw4envp3uid2hw3a0s4path5STKLO3sp05STKHI3AVN3LOpS2sp5rdraw4envp3uid2hw3a0s5STKLO3sp05STKHI3AVN3LOpS2sp5rdraw4envp3uid2hw3a0s4path1x1l5STKLO3sp05STKHI3AVL3AVNS2sp5rdraw4argv4envp3uid2hw5STKHI2T2S2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI3AVNS2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI3AVNS2sp5rdraw4argv4envp3uid2hw5STKLO3sp05STKHI3AVNS2sp5rdraw4envp3uid2hw3a0s5STKLO3sp05STKHI3AVN3LOpS2sp5rdraw4envp3uid2hw3a0s5STKLO3sp05STKHI3AVNS2sp5rdraw4envp3uid2hw3a0s5STKLO3sp05STKHI2T13AVN3SPR3LOpS2sp5rdraw4envp3uid2hw3a0s4path1x1l5STKLO3sp05STKHI2T13AVL3AVN3SPR3LOpS2sp5rdraw4envp3uid2hw3a0s4path5STKLO3sp05STKHI2bp2FR3AVN3LOpS2sp5rdraw4envp3uid2hw5STKLO3sp05STKHI3AVNS2sp5rdraw4envp3uid2hw3a0s4path5STKLO3sp05STKHI3AVN3LOp". (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit hAR STKLO R B12 MOD_DIE FH HIA HID HID_fresh SI SIFP PHI FPHI PHI_max FSTK FSTK_range FFR FFFR FFR_max C24f C24F_max FUZZ HVF HFRF sp0 STKHI"] Theorem entry_bridge : entry_bridgeA (main_entry_A sp brk0 rdraw argv envp fs uid hw) argv fs sp.
  Proof.
    intros Rg mem md ME Hfs.
    ddestruct (@main_entry_h0X hAR sp brk0 rdraw argv envp fs uid hw Hsp Hva Hve Hfit (HACsp_of sp Hsp) Rg mem md ME)
      as (bp & Hbsp & Hbhi & PIN & HOK & HMi & HKi & VOL & FR & FRESH & TOPe & SHIe).
    ddestruct ME as (p & HI & HCN & HREG & HMOD & HMEM). ddestruct HMEM as (HCOM & HRC & Hzero & Hargs & Hwin & [HNN HDEF]).  (* [comment removed for export] *)
    dpose (stkhi_facts sp rdraw argv envp uid hw Hfit) as (T1 & T2 & T3 & T4). fold STKHI in T1, T2, T3, T4.
    pose proof (valid_argv_len argv Hva) as AVL. pose proof (valid_argv_nonempty argv Hva) as AVN.
    assert (SPR : 0x7fff80000000 <= sp0 <= 2 ^ 47) by (dpose Hsp as (LO & HIw & _); unfold sp_window_lo in LO; unfold sp_window_hi in HIw; unfold sp0; lia).
    set (h := HS STKLO (h0_of bp) HOK : hst STKLO).
    assert (HSTKHI' : bv_unsigned sp <= STKHI) by (unfold sp0 in *; lia).
    assert (STKHI64 : STKHI mod 64 = 0).
    { clear - T2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    unshelve eexists (MKDP sp fs R HIA HID AL0_img eq_refl eq_refl eq_refl eq_refl eq_refl HIMGCS eq_refl
                        SI SIFP PHI FPHI PHI_max FSTK FSTK_range FFR FFFR FFR_max C24f C24F_max FUZZ SPlo SPhi SPal
                        (CAN p) (TID p) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                        (sp0 - 48) STKHI V0c _ _ _ _ HV0 HVF FR0c HFRF
                        (fun path pathp => openfail_tail R HIA AL0_img eq_refl HIMGCS sp SPlo SPhi SPal eq_refl path pathp fs (CAN p) (TID p)
                                              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (sp0 - 48) STKHI HSTKHI' T3 STKHI64)
                        (fun pathp => readerr_tail R HIA AL0_img eq_refl HIMGCS sp SPlo SPhi SPal eq_refl dot_path pathp fs (CAN p) (TID p)
                                         (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (sp0 - 48) STKHI HSTKHI' T3 STKHI64 ltac:(cbn; lia))
                        (fun argc a0p a0s => usage_tail R HIA AL0_img eq_refl HIMGCS sp SPlo SPhi SPal eq_refl fs (CAN p) (TID p)
                                                (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (sp0 - 48) STKHI T3 STKHI64 argc a0p a0s)).
    - unfold sp0. lia.
    - unfold sp0 in *. lia.
    - clear - T2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    - exact T3.
    - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      dexists Rg, (getr Rg (Z_to_bv 5 5)), (getr Rg (Z_to_bv 5 6)), (getr Rg (Z_to_bv 5 7)), (getr Rg (Z_to_bv 5 13)),
             (getr Rg (Z_to_bv 5 14)), (getr Rg (Z_to_bv 5 15)), (getr Rg (Z_to_bv 5 16)), (getr Rg (Z_to_bv 5 17)),
             (getr Rg (Z_to_bv 5 28)), (getr Rg (Z_to_bv 5 29)), (getr Rg (Z_to_bv 5 30)), (getr Rg (Z_to_bv 5 31)), mem, md, h.
      split; [reflexivity|].
      split; [exact (entry_regs p Rg HI HCN HREG)|].
      cbn [dp_R dp_HIA dp_HID dp_SI dp_can dp_tid dp_wp0 dp_rp0 dp_wp1 dp_rp1 dp_TOP dp_STKHI dp_V0 dp_FR0].
      (* [comment removed for export] *)
      pose proof (entry_tailA sp brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit mem p HI HCN HCOM HDEF) as TAIL.
      pose proof (entry_sshad sp brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit mem p HI HCN HCOM) as SSH. fold STKHI in SSH.
      pose proof (entry_stk sp brk0 rdraw argv envp uid hw Hsp Hva Hve Hfit mem p HI HCN HCOM) as STK.
      assert (STKe : stk asegs mem (sp0 - 2 ^ 23) (sp0 - 48)) by exact (proj1 (stk_split asegs mem (sp0 - 2 ^ 23) (sp0 - 48) sp0 STK ltac:(unfold sp0 in *; lia))).
      assert (FDS : m_fds md = FDS2) by (ddestruct HMOD as (_ & X & _); exact X).
      assert (Henvc : 0 <= Z.of_nat (length envp) <= 256) by (destruct Hve as (LE & _); lia).
      destruct argv as [|a0s [|path rest]]; [cbn in AVN; lia | | destruct rest as [|x l]].
      + (* [comment removed for export] *)
        exists (APTR sp [a0s] envp 0).
        ddestruct (entry_argv_str sp brk0 rdraw [a0s] envp uid hw Hsp Hfit mem Hargs 0%nat ltac:(cbn; lia)) as (BA & LOp & HIp).
        fold STKHI in HIp. cbn [nth length Z.of_nat] in BA, LOp, HIp.
        constructor.
        * exact HMi.
        * exact HKi.
        * rewrite Hbsp in TOPe. exact TOPe.
        * rewrite Hbhi in SHIe. exact SHIe.
        * exact TAIL.
        * exact SSH.
        * exact STKe.
        * exact (entry_argv_ptr0 sp brk0 rdraw [a0s] envp uid hw Hsp Hva Hve Hfit mem p HI HCN HCOM Hwin).
        * exact BA.
        * exact (valid_argv_str_nz [a0s] 0%nat Hva ltac:(cbn; lia)).
        * cbn [length Z.of_nat Pos.of_succ_nat] in LOp |- *. lia.
        * cbn [length Z.of_nat] in HIp |- *. lia.
        * cbn [length Z.of_nat Pos.of_succ_nat]. lia.
        * exact FDS.
        * exact Hfs.
        * exact (valid_argv_str_len [a0s] 0%nat Hva ltac:(cbn; lia)).
      + (* [comment removed for export] *)
        exists (APTR sp [a0s; path] envp 1).
        ddestruct (entry_argv_str sp brk0 rdraw [a0s; path] envp uid hw Hsp Hfit mem Hargs 1%nat ltac:(cbn; lia)) as (BA & LOp & HIp).
        fold STKHI in HIp. cbn [nth length Z.of_nat Pos.of_succ_nat Pos.succ] in BA, LOp, HIp.
        constructor.
        * exact HMi.
        * exact HKi.
        * rewrite Hbsp in TOPe. exact TOPe.
        * rewrite Hbhi in SHIe. exact SHIe.
        * (* [comment removed for export] *) change (h_havol (h0_of bp) + 402392064 <= V0c). rewrite VOL. unfold V0c. lia.
        * (* [comment removed for export] *) change (AModelX.hfr (h0_of bp) + 63 <= FR0c). unfold FR0c. lia.
        * (* [comment removed for export] *) intros c. apply HID_fresh. exact (FRESH c).
        * exact TAIL.
        * exact (entry_files sp mem p HCOM).
        * exact SSH.
        * (* [comment removed for export] *) apply (si_init SI). intros a Ha Hfp. apply (entry_sifp sp mem p HCOM). apply SIFP. exact Hfp.
        * exact STKe.
        * exact (entry_argv_ptr1 sp brk0 rdraw [a0s; path] envp uid hw Hsp Hva Hve Hfit mem p HI HCN HCOM Hwin ltac:(cbn; lia)).
        * exact BA.
        * exact (valid_argv_str_nz [a0s; path] 1%nat Hva ltac:(cbn; lia)).
        * (* [comment removed for export] *) dpose Hva as (_ & _ & _ & _ & PL). cbn [tl] in PL. exact (Forall_inv PL).
        * lia.
        * lia.
        * exact FDS.
        * exact Hfs.
        * exact (valid_argv_str_len [a0s; path] 1%nat Hva ltac:(cbn; lia)).
      + (* [comment removed for export] *)
        exists (APTR sp (a0s :: path :: x :: l) envp 0).
        ddestruct (entry_argv_str sp brk0 rdraw (a0s :: path :: x :: l) envp uid hw Hsp Hfit mem Hargs 0%nat ltac:(cbn; lia)) as (BA & LOp & HIp).
        fold STKHI in HIp. cbn [nth] in BA, LOp, HIp.
        constructor.
        * exact HMi.
        * exact HKi.
        * rewrite Hbsp in TOPe. exact TOPe.
        * rewrite Hbhi in SHIe. exact SHIe.
        * exact TAIL.
        * exact SSH.
        * exact STKe.
        * exact (entry_argv_ptr0 sp brk0 rdraw (a0s :: path :: x :: l) envp uid hw Hsp Hva Hve Hfit mem p HI HCN HCOM Hwin).
        * exact BA.
        * exact (valid_argv_str_nz (a0s :: path :: x :: l) 0%nat Hva ltac:(cbn; lia)).
        * cbn [length] in LOp, AVL |- *. lia.
        * lia.
        * cbn [length] in AVL |- *. lia.
        * exact FDS.
        * exact Hfs.
        * exact (valid_argv_str_len (a0s :: path :: x :: l) 0%nat Hva ltac:(cbn; lia)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Pack.

(* [comment removed for export] *)
