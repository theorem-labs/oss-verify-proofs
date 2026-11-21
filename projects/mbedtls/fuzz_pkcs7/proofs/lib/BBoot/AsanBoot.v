(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the boot chain restated over the launch's whole ProcInput and mmap base with the launch premises the start-up now reads (valid_mmap_base, valid_launch, the channel reader and entry_launch_ok_va) in place of entry_stack_fits, the abort-terminal and va-size premises, and wired to the certificates of the renumbered plans at the run's CONFIG_RSEQ flag, from and against the hand-off states computed from the run, the main entry's facts given that flag with its definition; every encoded statement written out in plain text). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec ShapeAlg SpinAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs AsanPlanImages. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanInit. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanStartup AsanMainEntry. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PlanCut.
  From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import StartupPlanAsan StartupPiecesAsan StartupRegenAsan MainEntryPlanAsan MainEntryPiecesAsan MainEntryRegenAsan
  AsanStartupCertP1 AsanStartupCertP2 AsanStartupCertP3A AsanStartupCertP3B AsanStartupCertP3C MainEntryCertAsanR0 MainEntryCertAsanA1 MainEntryCertAsanA2 MainEntryCertAsanA3 MainEntryCertAsanA4 MainEntryCertAsanA5 MainEntryCertAsanB1 MainEntryCertAsanB2 MainEntryCertAsanB3 MainEntryCertAsanB4 MainEntryCertAsanB5.
  From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanMainEntryKit. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma init_pc_is_entry : Z.of_N AsanUbsan.M.init_pc = a_entry BOTH.
Proof. reflexivity. Qed.
Lemma APH_is_phdrs : APH = AsanUbsan.M.phdrs.
Proof. reflexivity. Qed.

Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. unfold IT0. apply APS.mk_itab_ranges_sound. Qed.
Lemma IT1_ok : itab_sound ASEGS IT1.
Proof. unfold IT1. apply APS.mk_itab_ranges_sound. Qed.

Lemma HS_asan_only0 : forall rz h ch, su_P3_tab rz h = Some ch -> ch = HS_0 rz.
Proof. intros rz [|h] ch H; cbn [su_P3_tab] in H; [injection H as <-; reflexivity | discriminate H]. Qed.
Lemma HNX1 : (NX0 <= NX1)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma HS_main_pc : forall rz h ch, HS_main rz h = Some ch -> pc ch = 0x970e0.
Proof.
  intros rz h ch Hh. destruct h as [|[|[|h]]]; cbn [HS_main] in Hh; try discriminate Hh; injection Hh as <-;
    unfold HS_main_1, HS_main_2, rzsel; destruct (Z.eqb rz 1); vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma su_P1_holes : only_holes su_P1_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P1_hole : has_hole_all su_P1_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P2_holes : only_holes su_P2_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P2_hole : has_hole_all su_P2_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P3A_holes : only_holes su_P3A_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P3A_hole : has_hole_all su_P3A_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P3B_holes : only_holes su_P3B_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P3B_hole : has_hole_all su_P3B_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P3C_holes : only_holes su_P3C_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P3C_hole : has_hole_all su_P3C_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_R0_holes : only_holes me_R0_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_R0_hole : has_hole_all me_R0_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A1_holes : only_holes me_A1_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A1_hole : has_hole_all me_A1_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A2_holes : only_holes me_A2_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A2_hole : has_hole_all me_A2_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A3_holes : only_holes me_A3_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A3_hole : has_hole_all me_A3_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A4_holes : only_holes me_A4_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A4_hole : has_hole_all me_A4_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A5_holes : only_holes me_A5_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A5_hole : has_hole_all me_A5_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B1_holes : only_holes me_B1_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B1_hole : has_hole_all me_B1_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B2_holes : only_holes me_B2_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B2_hole : has_hole_all me_B2_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B3_holes : only_holes me_B3_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B3_hole : has_hole_all me_B3_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B4_holes : only_holes me_B4_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B4_hole : has_hole_all me_B4_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B5_holes : only_holes me_B5_shape = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B5_hole : has_hole_all me_B5_shape = true.  Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma su_P1_guard : spin_guarded su_P1_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P2_guard : spin_guarded su_P2_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P3A_guard : spin_guarded su_P3A_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P3B_guard : spin_guarded su_P3B_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma su_P3C_guard : spin_guarded su_P3C_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_R0_guard : spin_guarded me_R0_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A1_guard : spin_guarded me_A1_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A2_guard : spin_guarded me_A2_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A3_guard : spin_guarded me_A3_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A4_guard : spin_guarded me_A4_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_A5_guard : spin_guarded me_A5_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B1_guard : spin_guarded me_B1_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B2_guard : spin_guarded me_B2_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B3_guard : spin_guarded me_B3_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B4_guard : spin_guarded me_B4_planR = true.  Proof. vm_compute. reflexivity. Qed.
Lemma me_B5_guard : spin_guarded me_B5_planR = true.  Proof. vm_compute. reflexivity. Qed.

Section Boot.
  (* the image's own entry pc: [init_config]'s entry argument, which [Run.run] passes *)
  #[local] Notation apc := AsanUbsan.M.init_pc (only parsing).
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  #[local] Notation SINV := (SINV0 APH apc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (E0 sp rdraw brk0 inp).
  #[local] Notation SP0 := (bv_unsigned sp).
  #[local] Notation RB := (kb_rseq (in_kernel inp)).
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
  #[local] Notation fs := (in_fs inp).

  Variable MAIN : env -> Fs.Fs -> TSet.
  Hypothesis MAIN_agree : forall E E' fs', env_agree NX0 E E' -> MAIN E fs' = MAIN E' fs'.
  Hypothesis MAIN_nil : forall E fs', MAIN E fs' [].

  Section Chain.
    (** the main phase's holes, at the run's flag *)
    Hypothesis MS : holes_stmt ASEGS BOTH ALIMIT (HS_main RZ) SP0 SINV argH (fun _ => MAIN) fs.
    #[local] Notation FROM := (from_state apc sp rdraw brk0 mbase inp MAIN).
    Lemma F_HSm_1013 : FROM (HSm_1013 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (me_A5_cert RB).
      all: first [ exact HNX1 | exact IT1_ok | exact me_A5_guard | exact me_A5_holes | exact me_A5_hole | exact MS
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma T_me_A4 : holes_stmt ASEGS BOTH ALIMIT (me_A4_tab RZ) SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_A4_tab. apply hs_tab_holes. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HSm_1013]. Qed.
    Lemma F_HSm_1012 : FROM (HSm_1012 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (me_A4_cert RB).
      all: first [ exact HNX1 | exact IT1_ok | exact me_A4_guard | exact me_A4_holes | exact me_A4_hole | exact T_me_A4
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma T_me_A3 : holes_stmt ASEGS BOTH ALIMIT (me_A3_tab RZ) SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_A3_tab. apply hs_tab_holes. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HSm_1012]. Qed.
    Lemma F_HSm_1011 : FROM (HSm_1011 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (me_A3_cert RB).
      all: first [ exact HNX1 | exact IT1_ok | exact me_A3_guard | exact me_A3_holes | exact me_A3_hole | exact T_me_A3
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma T_me_A2 : holes_stmt ASEGS BOTH ALIMIT (me_A2_tab RZ) SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_A2_tab. apply hs_tab_holes. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HSm_1011]. Qed.
    Lemma F_HSm_1010 : FROM (HSm_1010 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (me_A2_cert RB).
      all: first [ exact HNX1 | exact IT1_ok | exact me_A2_guard | exact me_A2_holes | exact me_A2_hole | exact T_me_A2
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma T_me_A1 : holes_stmt ASEGS BOTH ALIMIT (me_A1_tab RZ) SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_A1_tab. apply hs_tab_holes. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HSm_1010]. Qed.
    Lemma F_HSm_1000 : FROM (HSm_1000 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (me_A1_cert RB).
      all: first [ exact HNX1 | exact IT1_ok | exact me_A1_guard | exact me_A1_holes | exact me_A1_hole | exact T_me_A1
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma F_HSm_1023 : FROM (HSm_1023 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (me_B5_cert RB).
      all: first [ exact HNX1 | exact IT1_ok | exact me_B5_guard | exact me_B5_holes | exact me_B5_hole | exact MS
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma T_me_B4 : holes_stmt ASEGS BOTH ALIMIT (me_B4_tab RZ) SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_B4_tab. apply hs_tab_holes. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HSm_1023]. Qed.
    Lemma F_HSm_1022 : FROM (HSm_1022 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (me_B4_cert RB).
      all: first [ exact HNX1 | exact IT1_ok | exact me_B4_guard | exact me_B4_holes | exact me_B4_hole | exact T_me_B4
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma T_me_B3 : holes_stmt ASEGS BOTH ALIMIT (me_B3_tab RZ) SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_B3_tab. apply hs_tab_holes. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HSm_1022]. Qed.
    Lemma F_HSm_1021 : FROM (HSm_1021 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (me_B3_cert RB).
      all: first [ exact HNX1 | exact IT1_ok | exact me_B3_guard | exact me_B3_holes | exact me_B3_hole | exact T_me_B3
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma T_me_B2 : holes_stmt ASEGS BOTH ALIMIT (me_B2_tab RZ) SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_B2_tab. apply hs_tab_holes. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HSm_1021]. Qed.
    Lemma F_HSm_1020 : FROM (HSm_1020 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (me_B2_cert RB).
      all: first [ exact HNX1 | exact IT1_ok | exact me_B2_guard | exact me_B2_holes | exact me_B2_hole | exact T_me_B2
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma T_me_B1 : holes_stmt ASEGS BOTH ALIMIT (me_B1_tab RZ) SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_B1_tab. apply hs_tab_holes. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HSm_1020]. Qed.
    Lemma F_HSm_1001 : FROM (HSm_1001 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (me_B1_cert RB).
      all: first [ exact HNX1 | exact IT1_ok | exact me_B1_guard | exact me_B1_holes | exact me_B1_hole | exact T_me_B1
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma T_me_R0 : holes_stmt ASEGS BOTH ALIMIT (me_R0_tab RZ) SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_R0_tab. apply hs_tab_holes. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[H|[]]]; injection H as <- <-; [exact F_HSm_1000 | exact F_HSm_1001]. Qed.
    Lemma F_HS_0 : FROM (HS_0 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (me_R0_cert RB).
      all: first [ exact HNX1 | exact IT1_ok | exact me_R0_guard | exact me_R0_holes | exact me_R0_hole | exact T_me_R0
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    (* the start-up's one hand-off state at 0 *)
    Lemma T_HS_asan : holes_stmt ASEGS BOTH ALIMIT (su_P3_tab RZ) SP0 SINV argH (fun _ => MAIN) fs.
    Proof. eapply hs_const_holes; [exact (HS_asan_only0 RZ) | exact F_HS_0]. Qed.
    Lemma F_HS_1001 : FROM (HS_1001 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (su_P3A_cert RB).
      all: first [ exact (le_n NX0) | exact IT0_ok | exact su_P3A_guard | exact su_P3A_holes | exact su_P3A_hole | exact T_HS_asan
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma F_HS_1002 : FROM (HS_1002 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (su_P3B_cert RB).
      all: first [ exact (le_n NX0) | exact IT0_ok | exact su_P3B_guard | exact su_P3B_holes | exact su_P3B_hole | exact T_HS_asan
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma F_HS_1003 : FROM (HS_1003 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (su_P3C_cert RB).
      all: first [ exact (le_n NX0) | exact IT0_ok | exact su_P3C_guard | exact su_P3C_holes | exact su_P3C_hole | exact T_HS_asan
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma T_su_P2 : holes_stmt ASEGS BOTH ALIMIT (su_P2_tab RZ) SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold su_P2_tab. apply hs_tab_holes. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[H|[H|[]]]]; injection H as <- <-; [exact F_HS_1001 | exact F_HS_1002 | exact F_HS_1003]. Qed.
    Lemma F_HS_1000 : FROM (HS_1000 RZ).
    Proof.
      eapply piece_sound.
      all: try exact (su_P2_cert RB).
      all: first [ exact (le_n NX0) | exact IT0_ok | exact su_P2_guard | exact su_P2_holes | exact su_P2_hole | exact T_su_P2
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
    Lemma T_su_P1 : holes_stmt ASEGS BOTH ALIMIT (su_P1_tab RZ) SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold su_P1_tab. apply hs_tab_holes. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HS_1000]. Qed.
    Theorem boot_chain :
      srealizes ASEGS (init_config ASEGS apc APH sp brk0 mbase rdraw AsanInit.LIMIT inp) (MAIN E0a fs).
    Proof.
      eapply asan_boot1.
      all: try exact (su_P1_cert RB).
      all: first [ exact IT0_ok | exact su_P1_guard | exact su_P1_holes | exact su_P1_hole | exact T_su_P1
                 | exact MAIN_agree | exact MAIN_nil | exact init_pc_is_entry | assumption ].
    Qed.
  End Chain.

  Theorem asan_boot_closed :
    holes_stmt ASEGS BOTH ALIMIT (HS_main RZ) SP0 SINV argH (fun _ => MAIN) fs ->
    srealizes ASEGS (init_config ASEGS apc APH sp brk0 mbase rdraw AsanInit.LIMIT inp) (MAIN E0a fs).
  Proof. intros MS. exact (boot_chain MS). Qed.

  (** the main phase, from [main_entry_A] at main's entry *)
  Hypothesis MAIN_entry : forall (R : bvmap 5 word) (mem : word -> option byte) (md : Model) (E : env),
    (forall n : nat, (n < NX0)%nat -> ev E n = ev E0a n) ->
    main_entry_A sp brk0 rdraw (in_argv inp) (in_envp inp) fs (in_uid inp) (in_hwcap inp) R mem md ->
    m_fs md = fs ->
    srealizes ASEGS (cfg_of ASEGS R 0x970e0 mem md) (MAIN E fs).

  Theorem asan_boot_entry :
    srealizes ASEGS (init_config ASEGS apc APH sp brk0 mbase rdraw AsanInit.LIMIT inp) (MAIN E0a fs).
  Proof.
    apply asan_boot_closed.
    intros h ch Hh E R FULL md HC.
    rewrite (HS_main_pc RZ h ch Hh).
    pose proof (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hfs. rewrite Hfs.
    apply (MAIN_entry R FULL md E).
    - exact (proj1 (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)).
    - exact (hs_main_entry_A sp brk0 mbase rdraw (in_argv inp) (in_envp inp) fs (in_uid inp) (in_hwcap inp) Hsp Hva
               inp eq_refl eq_refl eq_refl eq_refl Hlaunch Hlau RZ h ch E R FULL md eq_refl Hh HC).
    - exact Hfs.
  Qed.
End Boot.

(** The boot theorem over the launch's input, as the top proofs apply it: the start-up and main
    entry run from Linux's launch of the image to main's entry, where [MAIN_entry] takes over. *)
Theorem asan_boot_entry_inp :
  forall (sp brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk ASEGS brk0 -> valid_mmap_base mbase ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_id (in_uid inp) ->
    valid_launch inp -> in_channel_reader inp = true ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
  forall MAIN : env -> Fs.Fs -> TSet,
    (forall E E' fs', env_agree NX0 E E' -> MAIN E fs' = MAIN E' fs') ->
    (forall E fs', MAIN E fs' []) ->
    (forall (R : bvmap 5 word) (mem : word -> option byte) (md : Model) (E : env),
       (forall n : nat, (n < NX0)%nat -> ev E n = ev (E0 sp rdraw brk0 inp) n) ->
       main_entry_A sp brk0 rdraw (in_argv inp) (in_envp inp) (in_fs inp) (in_uid inp) (in_hwcap inp) R mem md ->
       m_fs md = in_fs inp ->
       srealizes ASEGS (cfg_of ASEGS R 0x970e0 mem md) (MAIN E (in_fs inp))) ->
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mbase rdraw AsanInit.LIMIT inp)
      (MAIN (E0 sp rdraw brk0 inp) (in_fs inp)).
Proof.
  intros sp brk0 mbase rdraw inp Hsp Hbrk Hmb Hva Hve Huid Hlaunch Hrdr Hlau MAIN MAIN_agree MAIN_nil MAIN_entry.
  eapply asan_boot_entry; eassumption.
Qed.

(* [comment removed for export] *)
