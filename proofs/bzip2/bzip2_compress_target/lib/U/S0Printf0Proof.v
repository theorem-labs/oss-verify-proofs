(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim ShapeAlg Spec AgentLib SymExec SymExec2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive SymDriveX SymDriveH4 SymAux RefMemcpyLib RefNodes U.S0StdioDefs U.S0LibStdioCall U.S0LibStdioCallF U.S0ExitBase U.S0PrintfBufBase U.S0Printf0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Frame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.AgentLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveH4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefNodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0StdioDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0LibStdioCall OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0LibStdioCallF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ExitBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0PrintfBufBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Printf0.
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition STOPS_P : list Z := [0x2b114; 0x1392c]%Z.
Definition ZL : list byte := [Z_to_bv 8 0x30; Z_to_bv 8 0x0a].

(* [comment removed for export] *)
Definition P0_FUEL : nat := 5000.
Definition p0_scr : scripts := SCR [] [] [].

Definition p_sr0 : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0 | 1 => ELit 0x1392c | 2 => EVar 0 | 11 => ELit 0
                          | _ => EVar (3 + i) end)%nat (seq 0 32)).

Definition p_kn0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x1000004b0 0x7fffffffffff;
   KWr (SA (EVar 0) (-1200)) 1200;
   KImg 0x10000 0x33000;
   KImg 0x33f90 0x34078;
   KWord (SA (ELit 0) 0x64450) 8 (EVar 1);
   KWr (SA (ELit 0) 0x33000) 0x33000].

Definition p_vals (regs : bvmap 5 word) (sp : word) (can : Z) : list word :=
  [sp; Z_to_bv 64 can; Z_to_bv 64 0] ++ junk_vals regs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rz_run_fr : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R model T,
  sym_exec RSEGS fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  scs_denot RSEGS M E scs -> scs_denot RSEGS M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok RSEGS E M' kn' ->
     M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
     realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
         Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
  cps_destruct (run_sound RSEGS fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply (Hcont R' _ HR'); [| reflexivity | exact Hlf].
  eapply carry_after; eassumption.
Qed.

Ltac run_blk_fr HR HK scr NX R' M' EQM LF :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs P0_FUEL true STOPS_P scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (rz_run_fr P0_FUEL STOPS_P scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | try reflexivity; try assumption
            | try reflexivity; try assumption
            | clear HR HK;
              intros R' M' HR HK EQM LF; cbn [s_pc s_regs s_log] in HR, EQM, LF |- * ]
          end
        end
      end
    end
  end.


(* [comment removed for export] *)
Lemma frame_mod_of_sw_post : forall m su f bufp bufsz m',
  sw_post m su f bufp bufsz m' -> 112 <= su -> su <= 2 ^ 64 -> 0 <= f -> f + 64 <= 2 ^ 64 ->
  frame_mod m m' [(Z_to_bv 64 (su - 112), 112); (Z_to_bv 64 (f + 32), 16); (Z_to_bv 64 (f + 56), 8)].
Proof.
  intros m su f bufp bufsz m' [AG GR _ _ _] H1 H2 H3 H4. split; [|exact GR].
  (intros a; cps_intros (N1 & N2 & N3 & _)). unfold in_rng in N1, N2, N3. rewrite !u64_lit in N1, N2, N3 by lia.
  apply AG; lia.
Qed.

(* [comment removed for export] *)
Definition p_regions : list sregion := [(SA (EVar 0) (-1200), 1200); (SA (ELit 0) 0x33f90, 232); (SA (ELit 0) 0x64cb8, 1024)]%Z.

Lemma fetch_ecall_21afc : exists w, fetch_word RSEGS (Z_to_bv 64 0x2bc74) = Some w /\ is_ecall w = true.
Proof. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section P.
  Variables (regs : bvmap 5 word) (mem : word -> option byte) (model : Model) (sp : word) (can : Z) (K : TSet).
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x1392c.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPLO : 4294967296 + PF0_FR <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp <= 0x7fffffffffff.
  Hypothesis STK : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - PF0_FR)) (Z.to_nat PF0_FR) = true.
  Hypothesis IMG : forall i, 0x10000 <= i < 0x33000 -> mem (Z_to_bv 64 i) = None.
  Hypothesis SOF : forall i, 0x33f90 <= i < 0x33f90 + FILE_SIZE -> mem (Z_to_bv 64 i) = None.
  Hypothesis CAN : cellZ PF0_S0 mem 0x64450 8 can.
  Hypothesis CANR : 0 <= can < 2 ^ 64.
  Hypothesis FD1 : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hl : m_vm_lazy model = [].
  Hypothesis K0 : K [].
  Hypothesis HK : forall regs' mem',
      keeps_cs regs regs' -> frame_mod mem mem' (pf0_fp PF0_S0 (bv_unsigned sp)) -> stdout_wmode PF0_S0 mem' (pf_buf PF0_S0) ->
      realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x1392c) mem' (seg_rom RSEGS)) model) K.

  Let vals0 := p_vals regs sp can.
  Let E := Env (vals_ev vals0) (blobs_ev []).

  Lemma vals0_len : length vals0 = 35%nat.
  Proof. reflexivity. Qed.
  Lemma ev0 : ev E 0 = sp. Proof. reflexivity. Qed.
  Lemma ev1 : ev E 1 = Z_to_bv 64 can. Proof. reflexivity. Qed.
  Lemma ev_junk : forall i, (3 <= i < 35)%nat -> ev E i = getr regs (Z_to_bv 5 (Z.of_nat (i - 3))).
  Proof.
    intros i Hi. unfold E, vals0, p_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 can; Z_to_bv 64 0] + (i - 3))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma p_regs_ok : regs_ok E p_sr0 regs.
  Proof.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth p_sr0 allregs32 edenot].
    1: apply getr_zero.
    1: exact R1.
    1: exact R2.
    9: exact R11.
    all: rewrite ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x33000) 208896 = true.
  Proof. exact S0ExitBase.ref_wseg_1c. Qed.

  Lemma data_store_ok : forall m a n,
    0x33000 <= a -> a + Z.of_nat n <= 0x66000 -> store_ok RSEGS m (Z_to_bv 64 a) n = true.
  Proof.
    intros m a n Ha Hn.
    eapply (store_ok_window RSEGS m (Z_to_bv 64 0x33000) (Z_to_bv 64 a) 208896 n 0x33000 0x66000);
      [ apply u64_lit; lia | vm_cast_no_check (@eq_refl Z 0x66000%Z) | cbn; lia | apply wseg_data
      | rewrite u64_lit by lia; lia | rewrite u64_lit by lia; lia ].
  Qed.

  Lemma p_know_ok : know_ok RSEGS E mem p_kn0.
  Proof.
    pose proof (u64_range sp) as Hsp. unfold PF0_FR in *.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    unfold p_kn0. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite ev0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite ev0. lia.
    - apply (kwr_of_stk_ok RSEGS E mem (EVar 0) sp 1200); [apply ev0 | | lia].
      change (Z.to_nat 1200) with 1200%nat in STK.
      intros a n H1 H2.
      eapply (store_ok_sub RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 1200)) a 1200 n); rewrite ?u64_lit by lia; [lia | exact STK | lia | lia].
    - apply kimg_intro; [lia | lia | exact IMG].
    - apply kimg_intro; [lia | lia |]. intros i Hi. apply SOF. unfold FILE_SIZE. lia.
    - eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply ev1 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact CAN].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
  Qed.

  Theorem printf0_main :
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x139d8) mem (seg_rom RSEGS)) model) (t_emit (W 1 ZL) K).
  Proof.
    pose proof p_regs_ok as HR. pose proof p_know_ok as HKN.
    pose proof (u64_range sp) as Hsp. unfold PF0_FR in *.
    (* [comment removed for export] *)
    run_blk_fr HR HKN p0_scr 35%nat R1x M1 EQM1 LF1.
    (* [comment removed for export] *)
    cps_destruct fetch_ecall_21afc as (w & FW & EW).
    eapply (rz_ioctl_winsz RSEGS R1x (Z_to_bv 64 0x2bc74) M1 model w (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)));
      [exact FW | exact EW | exact Hh | exact Hl | regv HR (17%bv : reg); reflexivity | regv HR (10%bv : reg); reflexivity
      | rewrite u64_lit by lia; lia | exact FD1 | exact I | regv HR (11%bv : reg); reflexivity |].
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_ok_set E sr R1x (10%bv : reg) (errno_ret ENOTTY) (ELit (two64 - 25)) HR ltac:(discriminate)
                    ltac:(cbn [edenot]; apply bv_eq; reflexivity)) as HR2 end.
    clear HR. rename HR2 into HR. cbn [ridx sr_upd] in HR || idtac.
    replace (v_addi (Z_to_bv 64 0x2bc74) 4) with (Z_to_bv 64 0x2bc78) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    run_blk_fr HR HKN p0_scr 35%nat R2x M2 EQM2 LF2.
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr ?Rc => lazymatch type of HKN with know_ok _ _ ?Mc ?kn =>
      let r := eval vm_compute in (stdio_call 35 sr kn) in
      lazymatch r with Some ?res =>
        change (t_emit (W 1 ZL) K) with (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) ([Z_to_bv 8 48] ++ [Z_to_bv 8 10])) K);
        eapply (stdio_call_sound_fr vals0 (blobs_ev []) sr kn Rc Mc model res [Z_to_bv 8 48] [Z_to_bv 8 10] K HR HKN);
        [ vm_cast_no_check (@eq_refl _ (Some res)) | .. ];
        cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn length Z.of_nat Pos.of_succ_nat Pos.succ]
      end end end.
    all: rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev eb vals_ev nth p_vals app vals0]; rewrite ?u64_lit by lia.
    all: try lia.
    - unfold Uaccess.rw_bytes_max. cbn. lia.
    - krd_solve HKN. 
    - krd_solve HKN.
    - exact FD1.
    - exact Hh.
    - exact Hl.
    - exact K0.
    - (* [comment removed for export] *)
      clear HR HKN. intros R3x M3 HR HKN SWP.
      cbn [sc_sr sc_kn sc_ret sc_f sc_bufp sc_bufsz sc_sp edenot] in HR, HKN, SWP |- *.
      set (vals1 := vals0 ++ junk_vals R3x) in *.
      set (E1 := Env (vals_ev vals1) (blobs_ev [])) in *.
      run_blk_fr HR HKN p0_scr 67%nat R4x M4 EQM4 LF4.
      (* [comment removed for export] *)
      assert (EV1 : ev E1 0 = sp).
      { subst E1 vals1. cbn [ev]. rewrite vals_ev_app_l by (rewrite vals0_len; lia). reflexivity. }
      assert (RF : forall E', ev E' 0 = sp -> regions_flat E' p_regions).
      { intros E' HE' r Hr. unfold p_regions in Hr. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[]]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot]; rewrite ?HE', ?u64_lit by lia; lia. }
      assert (RD : forall E', ev E' 0 = sp -> map (rdenot E') p_regions = pf0_fp PF0_S0 (bv_unsigned sp)).
      { intros E' HE'. unfold p_regions, pf0_fp, rdenot, estart. cbn [map fst snd a_base a_off edenot pf_file pf_buf PF0_S0].
        rewrite HE', u64_lit by lia. unfold PF0_FR, FILE_SIZE, BUF_SIZE. repeat f_equal; lia. }
      apply (HK R4x M4).
      + (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr _ =>
          apply (keeps_cs_of_same E1 p_sr0 sr regs R4x); [vm_compute; reflexivity | | exact HR] end.
        subst E1 vals1. apply env_app_regs; [reflexivity | exact p_regs_ok].
      + (* [comment removed for export] *)
        assert (F1 : frame_mod mem M1 (pf0_fp PF0_S0 (bv_unsigned sp))).
        { rewrite <- (RD E ev0), EQM1. lazymatch type of EQM1 with _ = mem_denot _ _ ?lg =>
            exact (log_covered_frame E mem p_regions lg ltac:(vm_compute; reflexivity) (RF E ev0) LF1) end. }
        assert (F2 : frame_mod M1 M2 (pf0_fp PF0_S0 (bv_unsigned sp))).
        { rewrite <- (RD E ev0), EQM2. lazymatch type of EQM2 with _ = mem_denot _ _ ?lg =>
            exact (log_covered_frame E M1 p_regions lg ltac:(vm_compute; reflexivity) (RF E ev0) LF2) end. }
        assert (F3 : frame_mod M2 M3 (pf0_fp PF0_S0 (bv_unsigned sp))).
        { eapply frame_mod_weaken; [| eapply frame_mod_of_sw_post; [exact SWP | lia | lia | lia | lia]].
          intros a Ho. unfold pf0_fp in Ho. cbn [outside pf_file pf_buf PF0_S0] in Ho |- *. unfold in_rng in *.
          unfold PF0_FR, FILE_SIZE, BUF_SIZE in Ho. rewrite !u64_lit in Ho |- * by lia. lia. }
        assert (F4 : frame_mod M3 M4 (pf0_fp PF0_S0 (bv_unsigned sp))).
        { rewrite <- (RD E1 EV1), EQM4. lazymatch type of EQM4 with _ = mem_denot _ _ ?lg =>
            exact (log_covered_frame E1 M3 p_regions lg ltac:(vm_compute; reflexivity) (RF E1 EV1) LF4) end. }
        eapply frame_mod_trans_same; [exact F1|]. eapply frame_mod_trans_same; [exact F2|].
        eapply frame_mod_trans_same; [exact F3| exact F4].
      + (* [comment removed for export] *)
        constructor; unfold cellZ; cbn [pf_file pf_buf pf_swrite pf_segs PF0_S0 BUF_SIZE]; krd_solve HKN.
  Qed.
End P.

Theorem printf0_first_s0 : printf0_first_stmt_s0.
Proof.
  intros regs mem model sp can K R1 R2 R11 SP16 SPLO SPHI STK IMG SOF CAN CANR FD1 Hh Hl K0 HK.
  eapply printf0_main; eassumption.
Qed.
