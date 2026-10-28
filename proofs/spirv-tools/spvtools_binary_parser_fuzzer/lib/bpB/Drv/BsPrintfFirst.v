(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BAgentLib BpecConsts BFrame BStreamSim BFileSim BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BLibKnowFrame BSymAux BHoare BRefPrintfLib BLibTail BazyRestrict BazySR BazyFdNodes BazySym.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BRefExitBase BRefStdioDefs BsLazyRun BsStdioWrite BsStdioCall BsScLib.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition AP1_FR : Z := 3400%Z.
Definition STOPS1 : list Z := [0x16cdd0; 0xe87a0]%Z.
Definition FUEL1 : nat := 8000.

Definition ASP_LO : Z := 0x7fff7f000000%Z.
Definition ASP_HI : Z := 0x7fffffffffff%Z.

Definition ap1_dirsA : list bool := [false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false].
Definition scrA : scripts := SCR ap1_dirsA [] [].
Definition scr0 : scripts := SCR [] [] [].

Definition ap1_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 1 => ELit 0xe87a0%Z | 2 => EVar 0 | 11 => ELit 0%Z
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

Definition apf1_cells : list (Z * nat * Z) :=
  [(0x186fc0, 8%nat, 0x174764)    ;
   (0x186fc8, 8%nat, 0x16e480)    ;
   (0x187140, 8%nat, 0x176aa0)    ;
   (0x187148, 8%nat, 0x176ea4)    ;
   (0x191038, 8%nat, 0x7fff8000)    ;
   (0x191d18, 1%nat, 0x1)    ;
   (0x191d19, 1%nat, 0x1)    ;
   (0x222bbc, 1%nat, 0x1)    ;
   (0x189b00, 4%nat, 0x5)    ;
   (0x189b20, 8%nat, 0x0)    ;
   (0x189b28, 8%nat, 0x0)    ;
   (0x189b38, 8%nat, 0x0)    ;
   (0x189b48, 8%nat, 0x16dfd4)    ;
   (0x189b58, 8%nat, 0x6e6480)    ;
   (0x189b60, 8%nat, 0x400)    ;
   (0x189b78, 4%nat, 0x1)    ;
   (0x189b88, 4%nat, 0x0)    ;
   (0x189b8c, 4%nat, 0xffffffff)    ;
   (0x189b90, 4%nat, 0xa)    ;
   (0x7fffa9e8, 8%nat, 0x0)    ;
   (0x800d4c90, 8%nat, 0x0)    ]%Z.

Definition cell_kn (c : Z * nat * Z) : kentry :=
  match c with (a, w, v) => KWord (SA (ELit 0) a) w (ELit v) end.
Definition kn_cells (cs : list (Z * nat * Z)) : list kentry := map cell_kn cs.

Definition ap1_shx : expr :=
  EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 0) (ELit (-912))) (ELit 3)) (ELit 2147450880)) (ELit (-8)).
Definition ASH_LO : Z := 0x10006fdf7f88%Z.
Definition ASH_HI : Z := 0x10007fff7f88%Z.

Definition ap1_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI;
   KWr (SA (EVar 0) (-3400)) 3400;
   KImg 0x10000 0x91000; KImg 0x17e000 0x186000;
   KWord (SA (ELit 0) 0x6e5898) 8 (EVar 1);
   KWr (SA (ELit 0) 0x189b00) 232; KWr (SA (ELit 0) 0x6e6480) 1024;
   KRange ap1_shx ASH_LO ASH_HI; KZero (SA ap1_shx 0) (ELit 8)]%Z
  ++ kn_cells apf1_cells.

Definition p1_rA := Eval vm_compute in (sym_exec RSEGS FUEL1 true STOPS1 scrA (SS 0xe884c ap1_sr [] ap1_kn 34) []).
Definition p1_cA := Eval vm_compute in (carry (s_log (fst (fst p1_rA))) ap1_kn []).
Definition p1_srA : list expr := Eval vm_compute in (s_regs (fst (fst p1_rA))).
Definition p1_knA : list kentry := Eval vm_compute in (fst (fst p1_cA)).
Definition p1_scsA : list sidecond := Eval vm_compute in (snd (fst p1_rA)).

Definition p1_srA' : list expr := Eval vm_compute in (sr_upd p1_srA (ridx 10) (ELit (2^64 - 25)%Z)).

Definition p1_rB := Eval vm_compute in (sym_exec RSEGS FUEL1 true STOPS1 scr0 (SS 0x16e034 p1_srA' [] p1_knA 34) []).
Definition p1_cB := Eval vm_compute in (carry (s_log (fst (fst p1_rB))) p1_knA []).
Definition p1_srB : list expr := Eval vm_compute in (s_regs (fst (fst p1_rB))).
Definition p1_knB : list kentry := Eval vm_compute in (fst (fst p1_cB)).

Definition p1_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 p1_srB p1_knB with Some r => r
   | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end).

Definition p1_rC := Eval vm_compute in (sym_exec RSEGS FUEL1 true STOPS1 scr0 (SS 0x16e054 (sc_sr p1_sc) [] (sc_kn p1_sc) 66) []).
Definition p1_cC := Eval vm_compute in (carry (s_log (fst (fst p1_rC))) (sc_kn p1_sc) []).
Definition p1_srF : list expr := Eval vm_compute in (s_regs (fst (fst p1_rC))).
Definition p1_knF : list kentry := Eval vm_compute in (fst (fst p1_cC)).

Lemma p1_itinerary :
  s_pc (fst (fst p1_rA)) = 0x16e030%Z /\ snd (fst p1_rA) = p1_scsA /\ snd (fst p1_cA) = []
  /\ s_pc (fst (fst p1_rB)) = 0x16cdd0%Z /\ snd (fst p1_rB) = [] /\ snd (fst p1_cB) = []
  /\ stdio_call 34 p1_srB p1_knB = Some p1_sc
  /\ s_pc (fst (fst p1_rC)) = 0xe87a0%Z /\ snd (fst p1_rC) = [] /\ snd (fst p1_cC) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem rz_run_lf_lazy `{fx : DFP} : forall segs L S Zr fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R msF mo T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst R (Z_to_bv 64 pc) M rom ->
  (forall R' M' msF' mo', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
     lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst R' (Z_to_bv 64 (s_pc ss')) M' rom ->
     realizes segs (mkCfg msF' mo') T) ->
  realizes segs (mkCfg msF mo) T.
Proof.
  intros segs L S Zr fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R msF mo T
         Hex Hc HR HK Hsc Hsc2 Hok Hr Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply (rz_msteps_lazy_mkst segs L S Zr); [exact Hok | exact Hr | exact Hms |].
  intros msF' mo' Hok' Hsb Hhs Hr'.
  apply (Hcont R' (mem_denot E M (s_log ss')) msF' mo' HR'); [| reflexivity | exact Hlf | exact Hok' | exact Hsb | exact Hhs | exact Hr'].
  eapply carry_after; eassumption.
Qed.

Definition p1_regions : list sregion :=
  [(SA (EVar 0) (-3400), 3400); (SA (ELit 0) 0x189b00, 232); (SA (ELit 0) 0x6e6480, 1)]%Z.

Lemma p1_covA : log_covered p1_regions (s_log (fst (fst p1_rA))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma p1_covB : log_covered p1_regions (s_log (fst (fst p1_rB))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma p1_covC : log_covered p1_regions (s_log (fst (fst p1_rC))) = true. Proof. vm_compute. reflexivity. Qed.

Lemma sw_post_frame_mod : forall mem su f bufp bufsz mem' (rs : list (word * Z)),
  sw_post mem su f bufp bufsz mem' ->
  (forall x : word, outside x rs -> ~ (su - 112 <= bv_unsigned x < su)%Z /\ ~ (f + 32 <= bv_unsigned x < f + 48)%Z
                                     /\ ~ (f + 56 <= bv_unsigned x < f + 64)%Z) ->
  frame_mod mem mem' rs.
Proof.
  intros mem su f bufp bufsz mem' rs [Hag Hgr _ _ _] Hrs. split; [|exact Hgr].
  intros a Ha. destruct (Hrs a Ha) as (N1 & N2 & N3). apply Hag; assumption.
Qed.

Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev []).

Lemma ap1_scs_ok : forall vals M (sp0 : word),
  vals_ev vals 0 = sp0 -> (ASP_LO <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= ASP_HI)%Z ->
  scs_denot RSEGS M (ENV vals) p1_scsA.
Proof.
  intros vals M sp0 P0 Hlo Hhi. unfold ASP_LO, ASP_HI in *. unfold p1_scsA, scs_denot.
  repeat (apply Forall_cons; [cbn [sc_denot edenot ev ENV]; rewrite P0; asc_br |]).
  apply Forall_nil.
Qed.

Section First.
  Context {fx : DFP}.
  Variable sp0 : word.
  Variables (L S Zr : list (word * word)).

  Definition p1_regions_w : list (word * Z) :=
    [(Z_to_bv 64 (bv_unsigned sp0 - 3400), 3400%Z); (Z_to_bv 64 0x189b00, 232%Z); (Z_to_bv 64 0x6e6480, 1%Z)].

  Lemma p1_regions_denot : forall vals, vals_ev vals 0 = sp0 ->
    (ASP_LO <= bv_unsigned sp0)%Z ->
    map (rdenot (ENV vals)) p1_regions = p1_regions_w.
  Proof.
    intros vals P0 Hlo. unfold ASP_LO in Hlo. unfold p1_regions, p1_regions_w, rdenot, estart. cbn [map fst snd a_base a_off edenot ev ENV].
    rewrite P0. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    repeat f_equal; lia.
  Qed.

  Lemma p1_regions_flat : forall vals, vals_ev vals 0 = sp0 ->
    (ASP_LO <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= ASP_HI)%Z ->
    regions_flat (ENV vals) p1_regions.
  Proof.
    intros vals P0 Hlo Hhi r Hr. unfold ASP_LO, ASP_HI in *. unfold p1_regions in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[]]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV];
      rewrite ?P0; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  Qed.

  Theorem ap1_sound : forall vals R M msF mo (K : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) ap1_sr R -> know_ok RSEGS (ENV vals) M ap1_kn ->
    fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0xe884c) M (seg_rom RSEGS) ->
    K [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) p1_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' p1_knF ->
       frame_mod M M' p1_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 0xe87a0) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo)
             (t_emit [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 48); WriteEv (Z_to_bv 64 1) (Z_to_bv 8 10)] K).
  Proof.
    intros vals R M msF mo K HL P0 HR HK Hfd1 OK RS HKnil HCONT.

    pose proof (know_nth RSEGS _ _ ap1_kn 1%nat _ HK eq_refl) as Hrg. cbn [kentry_ok edenot ev ENV] in Hrg. rewrite P0 in Hrg.
    unfold ASP_LO, ASP_HI in Hrg.
    pose proof (p1_regions_flat vals P0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF.
    pose proof (p1_regions_denot vals P0 ltac:(unfold ASP_LO; lia)) as RD.
    pose proof p1_itinerary as (PCA & SCA & CCA & PCB & SCB & CCB & SC & PCC & SCC & CCC).

    eapply (rz_run_lf_lazy RSEGS L S Zr FUEL1 STOPS1 scrA 0xe884c ap1_sr ap1_kn 34 (fst (fst p1_rA)) (snd (fst p1_rA)) (snd p1_rA)
              (fst (fst p1_cA)) (snd (fst p1_cA)) (snd p1_cA) (ENV vals) M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ p1_rA) | vm_cast_no_check (@eq_refl _ p1_cA)
      | exact HR | exact HK
      | rewrite SCA; apply (ap1_scs_ok vals M sp0 P0); unfold ASP_LO, ASP_HI; lia
      | rewrite CCA; constructor | exact OK | exact RS | ].
    clear HR HK. intros RA MA msFA moA HR HK EQA LFA OKA SBA HSA RSA.
    pose proof (log_covered_frame (ENV vals) M p1_regions _ p1_covA RF LFA) as FA. rewrite <- EQA, RD in FA.
    change (s_regs (fst (fst p1_rA))) with p1_srA in HR. change (fst (fst p1_cA)) with p1_knA in HK.
    rewrite PCA in RSA.

    eapply (rz_ioctl_winsz_lazy RSEGS L S Zr msFA RA (Z_to_bv 64 0x16e030) MA moA ECALLW (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)));
      [ vm_compute; reflexivity | apply is_ecall_ECALLW | exact OKA | exact RSA
      | regv HR (17 : reg); reflexivity | regv HR (10 : reg); reflexivity
      | change (bv_unsigned (Z_to_bv 64 1)) with 1%Z; lia
      | rewrite (same_but_materialized_fds _ _ SBA); exact Hfd1
      | regv HR (11 : reg); reflexivity | ].
    intros msFA' OKA' RSA' HSA'.
    rewrite v_addi_pc4 in RSA' by lia. change (0x16e030 + 4)%Z with 0x16e034%Z in RSA'.
    pose proof (regs_set_a0 (ENV vals) _ _ (errno_ret ENOTTY) (ELit (2^64 - 25)%Z) HR
                  ltac:(cbn [edenot]; apply bv_eq; reflexivity)) as HR'.
    clear HR. change (sr_upd p1_srA (ridx 10) (ELit (2 ^ 64 - 25)%Z)) with p1_srA' in HR'.

    eapply (rz_run_lf_lazy RSEGS L S Zr FUEL1 STOPS1 scr0 0x16e034 p1_srA' p1_knA 34 (fst (fst p1_rB)) (snd (fst p1_rB)) (snd p1_rB)
              (fst (fst p1_cB)) (snd (fst p1_cB)) (snd p1_cB) (ENV vals) MA (seg_rom RSEGS) _ msFA' moA);
      [ vm_cast_no_check (@eq_refl _ p1_rB) | vm_cast_no_check (@eq_refl _ p1_cB)
      | exact HR' | exact HK | rewrite SCB; constructor | rewrite CCB; constructor | exact OKA' | exact RSA' | ].
    clear HR' HK. intros RB MB msFB moB HR HK EQB LFB OKB SBB HSB RSB.
    pose proof (log_covered_frame (ENV vals) MA p1_regions _ p1_covB RF LFB) as FB. rewrite <- EQB, RD in FB.
    change (s_regs (fst (fst p1_rB))) with p1_srB in HR. change (fst (fst p1_cB)) with p1_knB in HK.
    rewrite PCB in RSB.

    apply (stdio_call_sound_post vals (blobs_ev []) p1_srB p1_knB RB MB L S Zr msFB moB p1_sc [Z_to_bv 8 48] [Z_to_bv 8 10] K
             HR HK (eq_trans (f_equal (fun n => stdio_call n p1_srB p1_knB) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn p1_sc length edenot ev ENV Z.of_nat Pos.of_succ_nat Pos.succ].
    - change (bv_unsigned (Z_to_bv 64 7234688)) with 7234688%Z. change (bv_unsigned (Z_to_bv 64 7234689)) with 7234689%Z. lia.
    - change (bv_unsigned (Z_to_bv 64 7234689)) with 7234689%Z. lia.
    - change (bv_unsigned (Z_to_bv 64 7234688)) with 7234688%Z. change (bv_unsigned (Z_to_bv 64 7234689)) with 7234689%Z. lia.
    - reflexivity.
    - lia.
    - left. change (bv_unsigned (Z_to_bv 64 7234689)) with 7234689%Z. rewrite P0, alu_add, vadd_wZ. unorm. lia.
    - left. change (bv_unsigned (Z_to_bv 64 85869)) with 85869%Z. change (bv_unsigned (Z_to_bv 64 1)) with 1%Z.
      rewrite P0, alu_add, vadd_wZ. unorm. lia.
    - change (bv_unsigned (Z_to_bv 64 85869)) with 85869%Z. change (bv_unsigned (Z_to_bv 64 1)) with 1%Z. lia.
    -   change (bv_unsigned (Z_to_bv 64 7234688)) with 7234688%Z. krd_solve HK.
    -   krd_solve HK.
    - rewrite (same_but_materialized_fds _ _ SBB), (same_but_materialized_fds _ _ SBA). exact Hfd1.
    - exact OKB.
    - exact RSB.
    - exact HKnil.
    -
      clear HR HK. intros Rj MC msFC moC HR HK HPOST OKC SBC HSC RSC.
      assert (FC0 : frame_mod MB MC p1_regions_w).
      { eapply sw_post_frame_mod; [exact HPOST|]. intros x Hx. unfold p1_regions_w in Hx. cbn [outside] in Hx.
        unfold in_rng in Hx. rewrite P0, alu_add, vadd_wZ. revert Hx. unorm. intros (N1 & N2 & N3 & _). lia. }
      set (vals' := vals ++ junk_vals Rj) in *.
      assert (HL' : length vals' = 66%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      pose proof (p1_regions_flat vals' P0' ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF'.
      pose proof (p1_regions_denot vals' P0' ltac:(unfold ASP_LO; lia)) as RD'.
      change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK.
      eapply (rz_run_lf_lazy RSEGS L S Zr FUEL1 STOPS1 scr0 0x16e054 (sc_sr p1_sc) (sc_kn p1_sc) 66 (fst (fst p1_rC)) (snd (fst p1_rC)) (snd p1_rC)
                (fst (fst p1_cC)) (snd (fst p1_cC)) (snd p1_cC) (ENV vals') MC (seg_rom RSEGS) _ msFC moC);
        [ vm_cast_no_check (@eq_refl _ p1_rC) | vm_cast_no_check (@eq_refl _ p1_cC)
        | exact HR | exact HK | rewrite SCC; constructor | rewrite CCC; constructor | exact OKC | exact RSC | ].
      clear HR HK. intros RC MF msFF moF HR HK EQC LFC OKF SBF HSF RSF.
      pose proof (log_covered_frame (ENV vals') MC p1_regions _ p1_covC RF' LFC) as FC. rewrite <- EQC, RD' in FC.
      change (s_regs (fst (fst p1_rC))) with p1_srF in HR. change (fst (fst p1_cC)) with p1_knF in HK.
      rewrite PCC in RSF.
      apply (HCONT Rj RC MF msFF moF HR HK).
      + eapply frame_mod_trans_same; [exact FA|]. eapply frame_mod_trans_same; [exact FB|].
        eapply frame_mod_trans_same; [exact FC0 | exact FC].
      + exact OKF.
      + eapply same_but_materialized_trans; [exact SBA|]. eapply same_but_materialized_trans; [exact SBB|].
        eapply same_but_materialized_trans; [exact SBC | exact SBF].
      + eapply hid_same_trans; [exact HSA|]. eapply hid_same_trans; [exact HSA'|]. eapply hid_same_trans; [exact HSB|].
        eapply hid_same_trans; [exact HSC | exact HSF].
      + exact RSF.
  Qed.
End First.

Definition ap1_shw (spz : Z) : Z := (8 * (((spz - 912) / 8 + 2147450880) / 8))%Z.

Lemma land_m8' : forall y, (0 <= y < 2^64)%Z -> Z.land y 18446744073709551608 = (8 * (y / 8))%Z.
Proof.
  intros y Hy. transitivity (Z.ldiff (Z.land y (Z.ones 64)) (Z.ones 3)).
  - rewrite Z.ldiff_land. rewrite <- Z.land_assoc. f_equal.
  - rewrite Z.land_ones, Z.mod_small by lia. rewrite Z.ldiff_ones_r by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z. lia.
Qed.

Lemma ap1_shx_denot : forall E (sp : word),
  ev E 0 = sp -> (ASP_LO <= bv_unsigned sp)%Z -> (bv_unsigned sp <= ASP_HI)%Z ->
  bv_unsigned (edenot E ap1_shx) = ap1_shw (bv_unsigned sp).
Proof.
  intros E sp E0 Hlo Hhi. unfold ASP_LO, ASP_HI in *. unfold ap1_shx, ap1_shw. cbn [edenot]. rewrite E0.
  cbn [alu64 alu].
  rewrite bv_and_unsigned, bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned, bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  change ((-912) mod 2 ^ 64)%Z with (2 ^ 64 - 912)%Z. change (3 mod 2 ^ 64)%Z with 3%Z. change (63 mod 2 ^ 64)%Z with 63%Z.
  change (Z.land 3 63) with 3%Z. change (2147450880 mod 2 ^ 64)%Z with 2147450880%Z.
  change ((-8) mod 2 ^ 64)%Z with 18446744073709551608%Z.
  replace ((bv_unsigned sp + (2 ^ 64 - 912)) mod 2 ^ 64)%Z with (bv_unsigned sp - 912)%Z by (Z.div_mod_to_equations; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
  rewrite (Z.mod_small (_ / 8 + _)) by (Z.div_mod_to_equations; lia).
  rewrite land_m8' by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma ap1_shw_range : forall spz, (ASP_LO <= spz <= ASP_HI)%Z -> (ASH_LO <= ap1_shw spz <= ASH_HI)%Z
  /\ (2147450880 + (spz - 4096) / 8 <= ap1_shw spz)%Z /\ (ap1_shw spz + 8 <= 2147450880 + spz / 8)%Z.
Proof. intros spz H. unfold ASP_LO, ASP_HI, ASH_LO, ASH_HI, ap1_shw in *. Z.div_mod_to_equations. lia. Qed.

Definition allregs32 : list reg :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_allregs32 : forall n, (n < 32)%nat -> nth n allregs32 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

Lemma regs_ok_by_idx : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i allregs32 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
    reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_allregs32 in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Definition cell_ok (mem : word -> option byte) (c : Z * nat * Z) : Prop :=
  match c with (a, w, v) =>
    rdn RSEGS mem (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)) end.
Definition cells_ok (mem : word -> option byte) (cs : list (Z * nat * Z)) : Prop :=
  Forall (cell_ok mem) cs.

Definition cell_wf_b (c : Z * nat * Z) : bool :=
  match c with (a, w, v) =>
    ((1 <=? Z.of_nat w) && (Z.of_nat w <=? 8) && (0 <=? a) && (a + Z.of_nat w <=? 2 ^ 64))%Z end.

Lemma cell_know : forall E mem c, cell_wf_b c = true -> cell_ok mem c -> kentry_ok RSEGS E mem (cell_kn c).
Proof.
  intros E mem [[a w] v] Hwf Hc. unfold cell_wf_b in Hwf.
  repeat (apply andb_true_iff in Hwf; destruct Hwf as [Hwf ?]).
  apply Z.leb_le in Hwf. repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  unfold cell_kn. eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0) a w (ELit v) (Z_to_bv 64 v));
    [reflexivity | reflexivity | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia |].
  rewrite u_small by lia. rewrite Z.add_0_l. exact Hc.
Qed.

Lemma cells_know : forall E mem cs,
  forallb cell_wf_b cs = true -> cells_ok mem cs -> know_ok RSEGS E mem (kn_cells cs).
Proof.
  intros E mem cs. induction cs as [|c cs IH]; intros Hwf Hok.
  - constructor.
  - cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 H2].
    inversion Hok; subst. constructor; [apply cell_know; assumption | apply IH; assumption].
Qed.

Section Plain.
  Context {fx : DFP}.
  Variables (L S Zr : list (word * word)).

  Record ap1H (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z) : Prop := AP1H {
    Q1  : getr regs 1 = Z_to_bv 64 0xe87a0;
    Q2  : getr regs 2 = sp;
    Q11 : getr regs 11 = Z_to_bv 64 0;
    Qsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    QspLo : (ASP_LO <= bv_unsigned sp)%Z;
    QspHi : (bv_unsigned sp <= ASP_HI)%Z;
    Qstk  : stk_ok RSEGS mem sp 3400;
    Qimg  : forall i, (0x10000 <= i < 0x91000)%Z -> mem (Z_to_bv 64 i) = None;
    Qgot  : forall i, (0x17e000 <= i < 0x186000)%Z -> mem (Z_to_bv 64 i) = None;
    Qcells : cells_ok mem apf1_cells;
    Qcan  : rdn RSEGS mem (Z_to_bv 64 0x6e5898) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Qcan64 : (0 <= can < 2 ^ 64)%Z;
    Qsh0  : forall a, (2147450880 + (bv_unsigned sp - 4096) / 8 <= a < 2147450880 + bv_unsigned sp / 8)%Z ->
              mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0) }.

  Record ap1Post (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z)
                 (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := AP1P {
    P_sp  : getr regs' 2 = sp;
    P_ra  : getr regs' 1 = Z_to_bv 64 0xe87a0;
    P_a0  : getr regs' 10 = Z_to_bv 64 2;
    P_cs  : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;

    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 3400), 3400%Z); (Z_to_bv 64 0x189b00, 232%Z); (Z_to_bv 64 0x6e6480, 1%Z)];

    P_flags : rdn RSEGS mem' (Z_to_bv 64 0x189b00) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0x189b08) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0x189b10) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wend  : rdn RSEGS mem' (Z_to_bv 64 0x189b20) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e6880));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0x189b28) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e6480));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0x189b38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e6480));
    P_write : rdn RSEGS mem' (Z_to_bv 64 0x189b48) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x16cdd0));
    P_buf   : rdn RSEGS mem' (Z_to_bv 64 0x189b58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e6480));
    P_bsz   : rdn RSEGS mem' (Z_to_bv 64 0x189b60) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
    P_fd    : rdn RSEGS mem' (Z_to_bv 64 0x189b78) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
    P_mode  : rdn RSEGS mem' (Z_to_bv 64 0x189b88) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0x189b8c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lbf   : rdn RSEGS mem' (Z_to_bv 64 0x189b90) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_can   : rdn RSEGS mem' (Z_to_bv 64 0x6e5898) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    P_stk   : stk_ok RSEGS mem' sp 3400 }.

  Definition p1_vals (regs : bvmap 5 word) (sp : word) (can : Z) : list word :=
    [sp; Z_to_bv 64 can] ++ junk_vals regs.

  Lemma p1_ev_junk : forall regs sp can i, (2 <= i < 34)%nat ->
    ev (ENV (p1_vals regs sp can)) i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2))).
  Proof.
    intros regs sp can i Hi. unfold ENV, p1_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 can] + (i - 2))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma p1_regs_ok : forall regs mem sp can, ap1H regs mem sp can ->
    regs_ok (ENV (p1_vals regs sp can)) ap1_sr regs.
  Proof.
    intros regs mem sp can PH. destruct PH.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth ap1_sr allregs32 edenot].
    1: apply getr_zero.
    1: assumption.
    1: cbn [ev ENV]; assumption.
    9: assumption.
    all: rewrite p1_ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma p1_know_ok : forall regs mem sp can, ap1H regs mem sp can ->
    know_ok RSEGS (ENV (p1_vals regs sp can)) mem ap1_kn.
  Proof.
    intros regs mem sp can PH. destruct PH. pose proof (u64_range sp) as Hsp.
    assert (E0 : ev (ENV (p1_vals regs sp can)) 0 = sp) by reflexivity.
    assert (E1 : ev (ENV (p1_vals regs sp can)) 1 = Z_to_bv 64 can) by reflexivity.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
    pose proof (ap1_shx_denot (ENV (p1_vals regs sp can)) sp E0 QspLo0 QspHi0) as SHX.
    pose proof (ap1_shw_range (bv_unsigned sp) (conj QspLo0 QspHi0)) as (SR1 & SR2 & SR3).
    unfold ASP_LO, ASP_HI, ASH_LO, ASH_HI in *.
    unfold ap1_kn. apply (proj2 (know_ok_app RSEGS _ _ _ _)). split; [| apply cells_know; [vm_compute; reflexivity | assumption]].
    repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite E0. unfold ASP_LO, ASP_HI. lia.
    - apply (kwr_of_stk_ok RSEGS _ mem (EVar 0) sp 3400); [exact E0 | assumption | lia].
    - apply kimg_intro; [lia | lia | assumption].
    - apply kimg_intro; [lia | lia | assumption].
    - eapply (kword_intro RSEGS _ mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | exact E1 | lia | lia | rewrite Z0; lia
        | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; assumption].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
    - apply krange_intro. rewrite SHX. unfold ASH_LO, ASH_HI. lia.
    - eapply (kzero_intro RSEGS _ mem ap1_shx (edenot (ENV (p1_vals regs sp can)) ap1_shx) 0 (ELit 8) 8);
        [reflexivity | reflexivity | rewrite SHX; lia | lia | rewrite SHX; lia |].
      intros i Hi. rewrite SHX. apply Qsh1. lia.
  Qed.

  Theorem aprintf0_first : forall regs mem msF mo (sp : word) (can : Z) (K : TSet),
    ap1H regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0xe884c) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    K [] ->
    (forall regs' mem' msF' mo', ap1Post regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 0xe87a0) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo)
             (t_emit [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 48); WriteEv (Z_to_bv 64 1) (Z_to_bv 8 10)] K).
  Proof.
    intros regs mem msF mo sp can K PH OK RS Hfd1 HKnil HCONT.
    pose proof (p1_regs_ok regs mem sp can PH) as HR. pose proof (p1_know_ok regs mem sp can PH) as HK.
    destruct PH. pose proof (u64_range sp) as Hsp. unfold ASP_LO, ASP_HI in *.
    apply (ap1_sound sp L S Zr (p1_vals regs sp can) regs mem msF mo K);
      [ unfold p1_vals; rewrite length_app, junk_vals_length; reflexivity | reflexivity | exact HR | exact HK
      | exact Hfd1 | exact OK | exact RS | exact HKnil |].
    clear HR HK. intros Rj R' M' msF' mo' HR HK FM OK' SB' HS' RS'.
    set (vals' := p1_vals regs sp can ++ junk_vals Rj) in *.
    assert (P0 : vals_ev vals' 0 = sp) by reflexivity.
    assert (P1 : vals_ev vals' 1 = Z_to_bv 64 can) by reflexivity.
    assert (PJ : forall i, (2 <= i < 34)%nat -> vals_ev vals' i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2)))).
    { intros i Hi. subst vals'. rewrite vals_ev_app_l by (unfold p1_vals; rewrite length_app, junk_vals_length; cbn; lia).
      apply (p1_ev_junk regs sp can i Hi). }
    apply (HCONT R' M' msF' mo'); [| exact OK' | exact SB' | exact HS' | exact RS']. split.
    - regv HR (2 : reg). exact P0.
    - regv HR (1 : reg). reflexivity.
    - regv HR (10 : reg). reflexivity.
    - intros r Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
        lazymatch goal with |- getr R' ?rr = _ => regv HR rr end; cbn [edenot ev ENV]; rewrite PJ by lia; f_equal; apply bv_eq; reflexivity.
    - exact FM.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd HK 0x6e5898%Z 8%nat Hc. rewrite Hc. cbn [ev ENV]. rewrite P1. reflexivity.
    - intros a n Ha Hn. eapply frame_mod_store_ok; [exact FM|]. apply Qstk0; assumption.
  Qed.
End Plain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
