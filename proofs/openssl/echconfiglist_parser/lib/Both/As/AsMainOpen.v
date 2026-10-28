(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts
  MmapSim AllocSim FileSim AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame SymAux
  Spec RefNodes LibTail HeapCeil LazyRestrict LazySR LazyFdNodes
  MainDefs MainArith MainWalk_defs MainSegs MainOpen.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem MState Exec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0 RefExitBase AsDrvRun
  AsPrintfFirst AsDrvMem AsDrvDefs AsTRSegs AsMainWalk_defs AsMainSegs AsMainPre ECH_Iface.
Import ListNotations.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma acovA : log_covered regA (s_log (fst (fst rA))) = true. Proof. vm_compute. reflexivity. Qed.
Definition caA := Eval vm_compute in carryM rA kn_amain.
Lemma caA_knA : fst (fst caA) = knA. Proof. vm_compute. reflexivity. Qed.
Lemma rA_facts : s_pc (fst (fst rA)) = 0x56aabc%Z /\ snd (fst rA) = []. Proof. vm_compute. split; reflexivity. Qed.
Lemma rC_facts : s_pc (fst (fst rC)) = 0x1bf174%Z /\ snd (fst rC) = [] /\ s_log (fst (fst rC)) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
(* [comment removed for export] *)
Definition aregF : list sregion := [(SA (EVar 0) (-240), 16); (SA (ELit 0) 0xbe1bec, 4)]%Z.
Lemma acovF : log_covered aregF (s_log (fst (fst rF))) = true. Proof. vm_compute. reflexivity. Qed.
Definition caF := Eval vm_compute in carryM rF knF0.
Lemma caF_knF : fst (fst caF) = knF. Proof. vm_compute. reflexivity. Qed.
Lemma rF_facts : s_pc (fst (fst rF)) = 0x1eefb8%Z
  /\ snd (fst rF) = [SCBr false BC_LTU (EAluw ALU_ADD (EVar 40) (ELit 0)) (ELit 18446744073709547521)]%Z
  /\ snd (fst caF) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
(* [comment removed for export] *)
Lemma acovU : log_covered regU (s_log (fst (fst rU))) = true. Proof. vm_compute. reflexivity. Qed.
Definition caU := Eval vm_compute in carryM rU kn_amainU.
Lemma caU_knU : fst (fst caU) = knU. Proof. vm_compute. reflexivity. Qed.
Lemma rU_facts : s_pc (fst (fst rU)) = 0x1eeebc%Z /\ snd (fst rU) = [SCBr true BC_NE (EVar 16) (ELit 2)]%Z /\ snd (fst caU) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Definition AENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev []).
Definition avals0 (sp0 : word) (p0 pp tid can : Z) (regs : bvmap 5 word) : list word :=
  [sp0; Z_to_bv 64 p0; Z_to_bv 64 pp; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 tid] ++ junk_vals regs ++ [Z_to_bv 64 0; Z_to_bv 64 can].

Lemma avals0_length : forall sp0 p0 pp tid can regs, length (avals0 sp0 p0 pp tid can regs) = 40%nat.
Proof. intros. unfold avals0. rewrite !length_app, junk_vals_length. reflexivity. Qed.

Lemma a_ev_junk : forall sp0 p0 pp tid can regs i, (i < 32)%nat ->
  ev (AENV (avals0 sp0 p0 pp tid can regs)) (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
Proof.
  intros sp0 p0 pp tid can regs i Hi. unfold AENV, avals0. cbn [ev]. unfold vals_ev.
  change (6 + i)%nat with (length [sp0; Z_to_bv 64 p0; Z_to_bv 64 pp; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 tid] + i)%nat.
  rewrite app_nth2_plus, app_nth1 by (rewrite junk_vals_length; exact Hi). unfold junk_vals.
  rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
Qed.
Lemma a_ev0 : forall sp0 p0 pp tid can regs, ev (AENV (avals0 sp0 p0 pp tid can regs)) 0 = sp0. Proof. reflexivity. Qed.
Lemma a_ev1 : forall sp0 p0 pp tid can regs, ev (AENV (avals0 sp0 p0 pp tid can regs)) 1 = Z_to_bv 64 p0. Proof. reflexivity. Qed.
Lemma a_ev2 : forall sp0 p0 pp tid can regs, ev (AENV (avals0 sp0 p0 pp tid can regs)) 2 = Z_to_bv 64 pp. Proof. reflexivity. Qed.
Lemma a_ev39 : forall sp0 p0 pp tid can regs, ev (AENV (avals0 sp0 p0 pp tid can regs)) 39 = Z_to_bv 64 can.
Proof.
  intros. unfold AENV, avals0. cbn [ev]. unfold vals_ev.
  rewrite app_assoc, app_nth2; rewrite ?length_app, ?junk_vals_length; [reflexivity| cbn; lia].
Qed.

Section AOpen.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable L : alib.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.
  Variables (sp0 : word) (argv : list (list byte)) (s0 : as_St H) (msF0 : machine_state) (mo0 : Model)
            (regs0 : bvmap 5 word) (mem0 : word -> option byte) (B tid can : Z).
  Hypothesis Hva : valid_argv argv.
  Hypothesis PRE : AMpre H L sp0 argv s0 msF0 mo0 regs0 mem0 B tid can.

  Let rom := seg_rom asegs.
  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 (am_vsp _ _ _ _ _ _ _ _ _ _ _ _ PRE)). Qed.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 (am_vsp _ _ _ _ _ _ _ _ _ _ _ _ PRE))). Qed.
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 (am_vsp _ _ _ _ _ _ _ _ _ _ _ _ PRE))). Qed.

  (* [comment removed for export] *)
  Lemma am_stk_ok : forall K, (0 <= K <= 2048)%Z -> stk_ok RSEGS mem0 sp0 K.
  Proof.
    intros K HK. pose proof (am_ceil _ _ _ _ _ _ _ _ _ _ _ _ PRE). acb.
    eapply astk_stk_ok; [exact (am_stk _ _ _ _ _ _ _ _ _ _ _ _ PRE) | unfold AMLO, ATR_STACK; lia | lia | lia | lia].
  Qed.

  Lemma am_ro : aro_none mem0.
  Proof. exact (amem_inv_ro_none mem0 (am_inv _ _ _ _ _ _ _ _ _ _ _ _ PRE)). Qed.

  (* [comment removed for export] *)
  Section TwoArgs.
    Variables a0s path : list byte.
    Hypothesis Hargv : argv = [a0s; path].
    Variables (p0 pp : Z).
    Hypothesis Hp0 : rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned sp0 + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p0)) /\ astr_at mem0 sp0 p0 a0s.
    Hypothesis Hpp : rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned sp0 + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pp)) /\ astr_at mem0 sp0 pp path.

    Let E0 := AENV (avals0 sp0 p0 pp tid can regs0).

    Lemma amain_regs_ok : regs_ok E0 sr_amain regs0.
    Proof.
      pose proof PRE as P. destruct P as [_ _ R1 R2 R4 R10 R11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
      replace (Z.of_nat (length argv)) with 2%Z in R10 by (rewrite Hargv; reflexivity).
      subst E0. apply regs_ok_by_idx. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; cbn [nth sr_amain allregs32];
      first [ apply getr_zero
            | cbn [edenot]; assumption
            | unfold spx; cbn [edenot]; rewrite a_ev0, alu_add; match goal with R : getr regs0 ?r = _ |- getr regs0 ?r = _ => rewrite R end;
              unfold v_add; apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, ?Zplus_mod_idemp_r, ?Zplus_mod_idemp_l; f_equal; lia
            | change (edenot ?E (EVar ?n)) with (ev E n);
              lazymatch goal with |- _ = ev _ ?n => rewrite (a_ev_junk sp0 p0 pp tid can regs0 (n - 6)) by lia end;
              f_equal; apply bv_eq; reflexivity ].
    Qed.

    Lemma amain_know_ok : know_ok RSEGS E0 mem0 kn_amain.
    Proof.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SPal as Hal.
      destruct Hp0 as [RP0 (S0a & S0b & S0c & S0d & S0e)]. destruct Hpp as [RP1 (S1a & S1b & S1c & S1d & S1e)].
      destruct (am_can _ _ _ _ _ _ _ _ _ _ _ _ PRE) as [CAN CAN64]. destruct (am_errno _ _ _ _ _ _ _ _ _ _ _ _ PRE) as [e [[_ _] EW]].
      cbn [Cells.cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in EW. unfold AERRNO, ATP in EW.
      subst E0. unfold kn_amain, ESTK. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
      - apply kalign_intro; [lia|]. cbn [edenot]. rewrite a_ev0. exact Hal.
      - apply krange_intro. cbn [edenot]. rewrite a_ev0. lia.
      - apply (kwr_of_stk_ok RSEGS _ mem0 (EVar 0) sp0 2048); [apply a_ev0 | apply am_stk_ok; lia | lia].
      - eapply (kword_intro RSEGS _ mem0 (EVar 0) sp0 8 8 (EVar 1)); [apply a_ev0 | apply a_ev1 | lia | lia | lia | lia | exact RP0].
      - eapply (kword_intro RSEGS _ mem0 (EVar 0) sp0 16 8 (EVar 2)); [apply a_ev0 | apply a_ev2 | lia | lia | lia | lia | exact RP1].
      - eapply (kword_intro RSEGS _ mem0 (ELit 0%Z) (Z_to_bv 64 0) 0xc01cd0 8 (EVar 39));
          [reflexivity | apply a_ev39 | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; exact CAN].
      - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u_small by lia. split; [lia|].
        intros d m Hd Hm. replace (0 + 12458988 + d)%Z with (12459152 - 164 + d)%Z by lia.
        eapply (wr_at_store_ok asegs); [exact EW | lia | lia].
      - apply kimg_intro; [lia|lia|exact am_ro].
      - apply kimg_intro; [lia|lia|exact (am_relro _ _ _ _ _ _ _ _ _ _ _ _ PRE)].
    Qed.

    Definition regA_w : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp0 - 224), 176%Z)].

    (* [comment removed for export] *)
    Lemma aseg_A : forall T,
      (forall R M msF mo,
         as_VIS H s0 msF = mkst R (Z_to_bv 64 0x56aabc) M rom -> as_AKREL H s0 (mkCfg msF mo) -> same_but_materialized mo0 mo ->
         regs_ok E0 srA R -> know_ok RSEGS E0 M knA ->
         frame_mod mem0 M regA_w -> amframe sp0 M ->
         realizes asegs (mkCfg msF mo) T) ->
      realizes asegs (mkCfg msF0 mo0) T.
    Proof.
      intros T HA. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      pose proof amain_regs_ok as HR. pose proof amain_know_ok as HK.
      pose proof (am_vis _ _ _ _ _ _ _ _ _ _ _ _ PRE) as HV. pose proof (am_krel _ _ _ _ _ _ _ _ _ _ _ _ PRE) as HAK.
      eapply (drv_run_lf H DL s0 FUELM STOPSAM scrA 0x1eed1c%Z sr_amain kn_amain 40%nat (fst (fst rA)) (snd (fst rA)) (snd rA)
                (fst (fst caA)) (snd (fst caA)) (snd caA) E0 mem0 regs0 msF0 mo0);
        [ vm_cast_no_check (@eq_refl _ rA) | vm_cast_no_check (@eq_refl _ caA) | exact HR | exact HK
        | rewrite (proj2 rA_facts); apply Forall_nil | scs_nil | exact HV | exact HAK | ].
      intros R M msF mo HR' HK' EQM LF HV' HA' SB'. rewrite caA_knA in HK'.
      rewrite (proj1 rA_facts) in HV'. change (s_regs (fst (fst rA))) with srA in HR'.
      assert (RF : regions_flat E0 regA).
      { intros r Hr. unfold regA in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
        unfold flat, estart; cbn [fst snd a_base a_off edenot]. subst E0. rewrite a_ev0. lia. }
      pose proof (log_covered_frame E0 mem0 regA _ acovA RF LF) as FR. rewrite <- EQM in FR.
      unfold regA, rdenot, estart in FR. cbn [map fst snd a_base a_off edenot] in FR. subst E0. rewrite a_ev0 in FR.
      replace (bv_unsigned sp0 + -224)%Z with (bv_unsigned sp0 - 224)%Z in FR by lia.
      apply (HA R M msF mo HV' HA' SB' HR' HK' FR).
      (* [comment removed for export] *)
      split.
      - krdv HK' 0%nat (-56)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot]; rewrite ?a_ev0; lia|].
        unfold adenot, v_addi in Hrd. cbn [a_base a_off edenot] in Hrd. rewrite a_ev0 in Hrd.
        replace (bv_unsigned sp0 + -56)%Z with (bv_unsigned sp0 - 56)%Z in Hrd by lia. exact Hrd.
      - intros i Hi.
        destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [ .. | lia];
        lazymatch goal with |- exists w, rdn _ _ (Z_to_bv 64 (?b + 8 * Z.of_nat ?k)) 8 = _ =>
          let off := eval vm_compute in (-120 + 8 * Z.of_nat k)%Z in
          krdv HK' 0%nat off 8%nat Hrd; [apply flat_intro; cbn [edenot]; rewrite ?a_ev0; lia|];
          unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot] in Hrd; rewrite a_ev0 in Hrd;
          eexists; replace (b + 8 * Z.of_nat k)%Z with (bv_unsigned sp0 + off)%Z by (cbn; lia); exact Hrd
        end.
    Qed.

    (* [comment removed for export] *)
    Lemma aopenat_regs : forall R,
      regs_ok E0 srA R ->
      getr R 17 = Z_to_bv 64 56 /\ getr R 10 = AT_FDCWD /\ getr R 11 = Z_to_bv 64 pp
      /\ Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
    Proof.
      intros R HR. repeat split.
      - regv HR (17 : reg). reflexivity.
      - regv HR (10 : reg). apply bv_eq. reflexivity.
      - regv HR (11 : reg). subst E0. cbn [edenot]. apply a_ev2.
      - regv HR (12 : reg). vm_compute. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma above_A : forall M, frame_mod mem0 M regA_w -> forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x.
    Proof.
      intros M [FM _] x Hx. pose proof SPlo. apply FM. cbn [outside]. split; [|exact I]. unfold in_rng. unorm. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma apath_at_A : forall M R,
      frame_mod mem0 M regA_w -> regs_ok E0 srA R -> (length path <= 4095)%nat ->
      path_at_lazy asegs R M path.
    Proof.
      intros M R FM HR Hlen. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      destruct Hpp as [_ (S1a & S1b & S1c & S1d & S1e)].
      destruct (aopenat_regs R HR) as (_ & _ & H11 & _).
      split; [exact Hlen|]. split; [exact S1c|]. rewrite H11.
      rewrite <- S1d. apply rdn_agree. intros j Hj. apply (above_A M FM). unorm. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma aseg_C : forall R M msF mo T,
      as_VIS H s0 msF = mkst (regupd R 10 (Z_to_bv 64 3)) (Z_to_bv 64 0x56aac0) M rom -> as_AKREL H s0 (mkCfg msF mo) ->
      regs_ok E0 srA R -> know_ok RSEGS E0 M knA ->
      (forall R' msF' mo',
          as_VIS H s0 msF' = mkst R' (Z_to_bv 64 0x1bf174) M rom -> as_AKREL H s0 (mkCfg msF' mo') -> same_but_materialized mo mo' ->
          getr R' 1 = Z_to_bv 64 0x1eed74 -> getr R' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) ->
          getr R' 4 = Z_to_bv 64 0xbe1c90 -> getr R' 8 = Z_to_bv 64 2 -> getr R' 10 = Z_to_bv 64 0x10000 ->
          getr R' 18 = Z_to_bv 64 pp -> getr R' 20 = Z_to_bv 64 3 -> getr R' 21 = Z_to_bv 64 0x10000 ->
          realizes asegs (mkCfg msF' mo') T) ->
      realizes asegs (mkCfg msF mo) T.
    Proof.
      intros R M msF mo T HV HAK HR HK HC. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      pose proof (regs_set_a0 E0 srA R (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR3.
      change (sr_upd srA (ridx 10) (ELit 3)) with srC0 in HR3.
      eapply (drv_run_lf H DL s0 FUELM STOPSAM noscr 0x56aac0%Z srC0 knA 40%nat (fst (fst rC)) (snd (fst rC)) (snd rC)
                (fst (fst (carryM rC knA))) (snd (fst (carryM rC knA))) (snd (carryM rC knA)) E0 M _ msF mo);
        [ vm_cast_no_check (@eq_refl _ rC) | vm_cast_no_check (@eq_refl _ (carryM rC knA)) | exact HR3 | exact HK
        | rewrite (proj1 (proj2 rC_facts)); apply Forall_nil | scs_nil | exact HV | exact HAK | ].
      intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. destruct rC_facts as (Epc & _ & Elog).
      rewrite Epc in HV'. change (s_regs (fst (fst rC))) with srC in HR'.
      assert (EM : M' = M) by (rewrite EQM, Elog; reflexivity). rewrite EM in HV'.
      apply (HC R' msF' mo' HV' HA' SB');
        first [ regv HR' (1:reg); reflexivity | regv HR' (4:reg); reflexivity | regv HR' (8:reg); reflexivity
              | regv HR' (10:reg); reflexivity | regv HR' (20:reg); reflexivity | regv HR' (21:reg); reflexivity
              | regv HR' (18:reg); subst E0; cbn [edenot]; apply a_ev2
              | regv HR' (2:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; subst E0; rewrite a_ev0; f_equal; lia ].
    Qed.

    (* [comment removed for export] *)
    Definition aregF_w : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp0 - 240), 16%Z); (Z_to_bv 64 0xbe1bec, 4%Z)].

    Lemma aseg_F : forall (e : Z) R M msF mo T,
      as_VIS H s0 msF = mkst (regupd R 10 (errno_ret e)) (Z_to_bv 64 0x56aac0) M rom -> as_AKREL H s0 (mkCfg msF mo) ->
      (1 <= e <= 4095)%Z -> scF e ->
      regs_ok E0 srA R -> know_ok RSEGS E0 M knA ->
      (forall R' M' msF' mo',
          as_VIS H s0 msF' = mkst R' (Z_to_bv 64 0x1eefb8) M' rom -> as_AKREL H s0 (mkCfg msF' mo') -> same_but_materialized mo mo' ->
          getr R' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R' 4 = Z_to_bv 64 0xbe1c90 -> getr R' 8 = Z_to_bv 64 2 ->
          getr R' 18 = Z_to_bv 64 pp ->
          frame_mod M M' aregF_w ->
          realizes asegs (mkCfg msF' mo') T) ->
      realizes asegs (mkCfg msF mo) T.
    Proof.
      intros e R M msF mo T HV HAK He HSC HR HK HC. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      (* [comment removed for export] *)
      set (vals := avals0 sp0 p0 pp tid can regs0) in *.
      assert (HL : length vals = 40%nat) by (subst vals; apply avals0_length).
      pose proof (env_app_regs vals [errno_ret e] (blobs_ev []) srA R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
      pose proof (env_app_know RSEGS vals [errno_ret e] (blobs_ev []) M knA ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK1.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev [])) with (AENV (vals ++ [errno_ret e])) in HR1, HK1.
      assert (Q40 : vals_ev (vals ++ [errno_ret e]) 40 = errno_ret e).
      { rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
      assert (Q0 : vals_ev (vals ++ [errno_ret e]) 0 = sp0) by (rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
      assert (Q2 : vals_ev (vals ++ [errno_ret e]) 2 = Z_to_bv 64 pp) by (rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
      set (vals1 := vals ++ [errno_ret e]) in *. clearbody vals1.
      pose proof (regs_set_a0 (AENV vals1) srA R (errno_ret e) (EVar 40) HR1 ltac:(cbn [edenot ev AENV]; exact Q40)) as HR2.
      change (sr_upd srA (ridx 10) (EVar 40)) with srF0 in HR2.
      assert (HK2 : know_ok RSEGS (AENV vals1) M knF0).
      { unfold knF0. apply Forall_cons; [| exact HK1]. apply krange_intro. cbn [edenot ev AENV]. rewrite Q40.
        pose proof (MainOpen.errno_ret_range e He). pose proof (u64_range (errno_ret e)). lia. }
      eapply (drv_run_lf H DL s0 FUELM STOPSAM scrF 0x56aac0%Z srF0 knF0 41%nat (fst (fst rF)) (snd (fst rF)) (snd rF)
                (fst (fst caF)) (snd (fst caF)) (snd caF) (AENV vals1) M _ msF mo);
        [ vm_cast_no_check (@eq_refl _ rF) | vm_cast_no_check (@eq_refl _ caF) | exact HR2 | exact HK2
        | | rewrite (proj2 (proj2 rF_facts)); apply Forall_nil | exact HV | exact HAK | ].
      { rewrite (proj1 (proj2 rF_facts)). apply Forall_cons; [|apply Forall_nil].
        unfold sc_denot. cbn [edenot ev AENV]. rewrite Q40. exact HSC. }
      intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'.
      rewrite (proj1 rF_facts) in HV'. change (s_regs (fst (fst rF))) with srF in HR'.
      assert (RF : regions_flat (AENV vals1) aregF).
      { intros r Hr. unfold aregF in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]];
          unfold flat, estart; cbn [fst snd a_base a_off edenot ev AENV]; rewrite ?Q0, ?(u_small 0) by lia; lia. }
      pose proof (log_covered_frame (AENV vals1) M aregF _ acovF RF LF) as FR. rewrite <- EQM in FR.
      unfold aregF, rdenot, estart in FR. cbn [map fst snd a_base a_off edenot ev AENV] in FR. rewrite Q0, ?(u_small 0) in FR by lia.
      replace (bv_unsigned sp0 + -240)%Z with (bv_unsigned sp0 - 240)%Z in FR by lia.
      apply (HC R' M' msF' mo' HV' HA' SB').
      - regv HR' (2:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev AENV]. rewrite Q0. f_equal; lia.
      - regv HR' (4:reg). reflexivity.
      - regv HR' (8:reg). reflexivity.
      - regv HR' (18:reg). cbn [edenot ev AENV]. exact Q2.
      - exact FR.
    Qed.
  End TwoArgs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Usage.
    Hypothesis Hargc : length argv <> 2%nat.

    Let EU := AENV (avals0 sp0 0 0 tid can regs0).

    Lemma amain_regs_okU : regs_ok EU sr_amainN regs0.
    Proof.
      pose proof PRE as P. destruct P as [_ _ R1 R2 R4 R10 R11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. clear R10.
      subst EU. apply regs_ok_by_idx. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; cbn [nth sr_amainN allregs32];
      first [ apply getr_zero
            | cbn [edenot]; assumption
            | unfold spx; cbn [edenot]; rewrite a_ev0, alu_add; match goal with R : getr regs0 ?r = _ |- getr regs0 ?r = _ => rewrite R end;
              unfold v_add; apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, ?Zplus_mod_idemp_r, ?Zplus_mod_idemp_l; f_equal; lia
            | change (edenot ?E (EVar ?n)) with (ev E n);
              lazymatch goal with |- _ = ev _ ?n => rewrite (a_ev_junk sp0 0 0 tid can regs0 (n - 6)) by lia end;
              f_equal; apply bv_eq; reflexivity ].
    Qed.

    Lemma amain_know_okU : know_ok RSEGS EU mem0 kn_amainU.
    Proof.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SPal as Hal.
      subst EU. unfold kn_amainU, ESTK. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
      - apply kalign_intro; [lia|]. cbn [edenot]. rewrite a_ev0. exact Hal.
      - apply krange_intro. cbn [edenot]. rewrite a_ev0. lia.
      - apply (kwr_of_stk_ok RSEGS _ mem0 (EVar 0) sp0 2048); [apply a_ev0 | apply am_stk_ok; lia | lia].
      - apply kimg_intro; [lia|lia|exact am_ro].
      - apply kimg_intro; [lia|lia|exact (am_relro _ _ _ _ _ _ _ _ _ _ _ _ PRE)].
    Qed.

    Definition regU_w : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp0 - 128), 80%Z)].

    (* [comment removed for export] *)
    Lemma aseg_U : forall T,
      (forall R M msF mo,
         as_VIS H s0 msF = mkst R (Z_to_bv 64 0x1eeebc) M rom -> as_AKREL H s0 (mkCfg msF mo) -> same_but_materialized mo0 mo ->
         getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 4 = Z_to_bv 64 0xbe1c90 -> getr R 8 = Z_to_bv 64 2 ->
         getr R 10 = Z_to_bv 64 (Z.of_nat (length argv)) -> getr R 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
         frame_mod mem0 M regU_w -> amframe sp0 M ->
         realizes asegs (mkCfg msF mo) T) ->
      realizes asegs (mkCfg msF0 mo0) T.
    Proof.
      intros T HU. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      assert (Hlen : (1 <= length argv <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
      pose proof amain_regs_okU as HR. pose proof amain_know_okU as HK.
      pose proof (am_vis _ _ _ _ _ _ _ _ _ _ _ _ PRE) as HV. pose proof (am_krel _ _ _ _ _ _ _ _ _ _ _ _ PRE) as HAK.
      pose proof (am_a0 _ _ _ _ _ _ _ _ _ _ _ _ PRE) as R10.
      assert (Hac : ev EU 16 = getr regs0 10) by (subst EU; apply (a_ev_junk sp0 0 0 tid can regs0 10); lia).
      eapply (drv_run_lf H DL s0 FUELM STOPSAM scrU 0x1eed1c%Z sr_amainN kn_amainU 40%nat (fst (fst rU)) (snd (fst rU)) (snd rU)
                (fst (fst caU)) (snd (fst caU)) (snd caU) EU mem0 regs0 msF0 mo0);
        [ vm_cast_no_check (@eq_refl _ rU) | vm_cast_no_check (@eq_refl _ caU) | exact HR | exact HK
        | | rewrite (proj2 (proj2 rU_facts)); apply Forall_nil | exact HV | exact HAK | ].
      { (* [comment removed for export] *)
        rewrite (proj1 (proj2 rU_facts)). apply Forall_cons; [|apply Forall_nil]. unfold sc_denot. cbn [branch_taken edenot]. rewrite Hac, R10.
        unfold bv_eqb. rewrite u_small by lia. change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
        apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
      intros R M msF mo HR' HK' EQM LF HV' HA' SB'. rewrite caU_knU in HK'.
      rewrite (proj1 rU_facts) in HV'. change (s_regs (fst (fst rU))) with srU in HR'.
      assert (RF : regions_flat EU regU).
      { intros r Hr. unfold regU in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
        unfold flat, estart; cbn [fst snd a_base a_off edenot]. subst EU. rewrite a_ev0. lia. }
      pose proof (log_covered_frame EU mem0 regU _ acovU RF LF) as FR. rewrite <- EQM in FR.
      unfold regU, rdenot, estart in FR. cbn [map fst snd a_base a_off edenot] in FR. subst EU. rewrite a_ev0 in FR.
      replace (bv_unsigned sp0 + -128)%Z with (bv_unsigned sp0 - 128)%Z in FR by lia.
      apply (HU R M msF mo HV' HA' SB').
      - regv HR' (2:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite a_ev0. f_equal; try lia.
      - regv HR' (4:reg). reflexivity.
      - regv HR' (8:reg). reflexivity.
      - regv HR' (10:reg). change (edenot _ (EVar 16)) with (ev (AENV (avals0 sp0 0 0 tid can regs0)) 16). rewrite Hac. exact R10.
      - regv HR' (11:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite a_ev0. f_equal; try lia.
      - exact FR.
      - (* [comment removed for export] *)
        split.
        + krdv HK' 0%nat (-56)%Z 8%nat Hrd; [apply flat_intro; cbn [edenot]; rewrite ?a_ev0; lia|].
          unfold adenot, v_addi in Hrd. cbn [a_base a_off edenot] in Hrd. rewrite a_ev0 in Hrd.
          replace (bv_unsigned sp0 + -56)%Z with (bv_unsigned sp0 - 56)%Z in Hrd by lia. exact Hrd.
        + intros i Hi.
          destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [ .. | lia];
          lazymatch goal with |- exists w, rdn _ _ (Z_to_bv 64 (?b + 8 * Z.of_nat ?k)) 8 = _ =>
            let off := eval vm_compute in (-120 + 8 * Z.of_nat k)%Z in
            krdv HK' 0%nat off 8%nat Hrd; [apply flat_intro; cbn [edenot]; rewrite ?a_ev0; lia|];
            unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot] in Hrd; rewrite a_ev0 in Hrd;
            eexists; replace (b + 8 * Z.of_nat k)%Z with (bv_unsigned sp0 + off)%Z by (cbn; lia); exact Hrd
          end.
    Qed.
  End Usage.
End AOpen.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
