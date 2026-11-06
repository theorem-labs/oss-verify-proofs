(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux
  Hoare RefExitBase RefStdioDefs RefStdioWrite LibStdioCall RefNodes RefPrintfBufBase LibTail LibDiagKn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition P1_FR : Z := 1232%Z.
Definition STOPS1 : list Z := [0x272e44; 0xddca8]%Z.
Definition FUEL1 : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].

(* [comment removed for export] *)
Definition p1_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 1 => ELit 0xddca8%Z | 2 => EVar 0 | 11 => ELit 0%Z
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p1_cells : list (Z * nat * Z) := pf1_cells.

Definition p1_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x100000500 0x7fffffffffff;
   KWr (SA (EVar 0) (-1232)) 1232;
   KImg 0x10000 0x27e000;
   KWord (SA (ELit 0) 0x30f4b8) 8 (EVar 1);
   KWr (SA (ELit 0) 0x2dc000) 0x35000]%Z
  ++ kn_cells p1_cells.

(* [comment removed for export] *)
Definition p1_rA := Eval vm_compute in (sym_exec RSEGS FUEL1 true STOPS1 scr0 (SS 0xddd60 p1_sr [] p1_kn 34) []).
Definition p1_cA := Eval vm_compute in (carry (s_log (fst (fst p1_rA))) p1_kn []).
Definition p1_srA : list expr := Eval vm_compute in (s_regs (fst (fst p1_rA))).
Definition p1_knA : list kentry := Eval vm_compute in (fst (fst p1_cA)).
(* [comment removed for export] *)
Definition p1_srA' : list expr := Eval vm_compute in (sr_upd p1_srA (ridx 10) (ELit (2^64 - 25)%Z)).
(* [comment removed for export] *)
Definition p1_rB := Eval vm_compute in (sym_exec RSEGS FUEL1 true STOPS1 scr0 (SS 0x273954 p1_srA' [] p1_knA 34) []).
Definition p1_cB := Eval vm_compute in (carry (s_log (fst (fst p1_rB))) p1_knA []).
Definition p1_srB : list expr := Eval vm_compute in (s_regs (fst (fst p1_rB))).
Definition p1_knB : list kentry := Eval vm_compute in (fst (fst p1_cB)).
(* [comment removed for export] *)
Definition p1_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 p1_srB p1_knB with Some r => r
   | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end).
(* [comment removed for export] *)
Definition p1_rC := Eval vm_compute in (sym_exec RSEGS FUEL1 true STOPS1 scr0 (SS 0x273974 (sc_sr p1_sc) [] (sc_kn p1_sc) 66) []).
Definition p1_cC := Eval vm_compute in (carry (s_log (fst (fst p1_rC))) (sc_kn p1_sc) []).
Definition p1_srF : list expr := Eval vm_compute in (s_regs (fst (fst p1_rC))).
Definition p1_knF : list kentry := Eval vm_compute in (fst (fst p1_cC)).

(* [comment removed for export] *)
Lemma p1_itinerary :
  s_pc (fst (fst p1_rA)) = 0x273950%Z /\ snd (fst p1_rA) = [] /\ snd (fst p1_cA) = []
  /\ s_pc (fst (fst p1_rB)) = 0x272e44%Z /\ snd (fst p1_rB) = [] /\ snd (fst p1_cB) = []
  /\ stdio_call 34 p1_srB p1_knB = Some p1_sc
  /\ s_pc (fst (fst p1_rC)) = 0xddca8%Z /\ snd (fst p1_rC) = [] /\ snd (fst p1_cC) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem rz_run_lf : forall segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R model T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
     realizes segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
         Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply (Hcont R' _ HR'); [| reflexivity | exact Hlf].
  eapply carry_after; eassumption.
Qed.

(* [comment removed for export] *)
Definition p1_regions : list sregion :=
  [(SA (EVar 0) (-1232), 1232); (SA (ELit 0) 0x2dc7a0, 232); (SA (ELit 0) 0x30ff60, 1)]%Z.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section First.
  Variable sp0 : word.
  Variable model : Model.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd1 : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev []).

  (* [comment removed for export] *)
  Definition p1_regions_w : list (word * Z) :=
    [(Z_to_bv 64 (bv_unsigned sp0 - 1232), 1232%Z); (Z_to_bv 64 0x2dc7a0, 232%Z); (Z_to_bv 64 0x30ff60, 1%Z)].

  Lemma p1_regions_denot : forall vals, vals_ev vals 0 = sp0 ->
    (0x100000500 <= bv_unsigned sp0)%Z ->
    map (rdenot (ENV vals)) p1_regions = p1_regions_w.
  Proof.
    intros vals P0 Hlo. unfold p1_regions, p1_regions_w, rdenot, estart. cbn [map fst snd a_base a_off edenot ev ENV].
    rewrite P0. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    repeat f_equal; lia.
  Qed.

  Lemma p1_regions_flat : forall vals, vals_ev vals 0 = sp0 ->
    (0x100000500 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x7fffffffffff)%Z ->
    regions_flat (ENV vals) p1_regions.
  Proof.
    intros vals P0 Hlo Hhi r Hr. unfold p1_regions in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[]]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV];
      rewrite ?P0; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  Qed.

  Theorem p1_sound : forall vals R M (K : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) p1_sr R -> know_ok RSEGS (ENV vals) M p1_kn ->
    K [] ->
    (forall Rj R' M',
       regs_ok (ENV (vals ++ junk_vals Rj)) p1_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' p1_knF ->
       frame_mod M M' p1_regions_w ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0xddca8) M' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xddd60) M (seg_rom RSEGS)) model)
             (t_emit [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 48); WriteEv (Z_to_bv 64 1) (Z_to_bv 8 10)] K).
  Proof.
    intros vals R M K HL P0 HR HK HKnil HCONT.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ p1_kn 1%nat _ HK eq_refl) as Hrg. cbn [kentry_ok edenot ev ENV] in Hrg. rewrite P0 in Hrg.
    pose proof (p1_regions_flat vals P0 ltac:(lia) ltac:(lia)) as RF.
    pose proof (p1_regions_denot vals P0 ltac:(lia)) as RD.
    (* [comment removed for export] *)
    eapply (rz_run_lf RSEGS FUEL1 STOPS1 scr0 0xddd60 p1_sr p1_kn 34 (fst (fst p1_rA)) (snd (fst p1_rA)) (snd p1_rA)
              (fst (fst p1_cA)) (snd (fst p1_cA)) (snd p1_cA) (ENV vals) M (seg_rom RSEGS) R model);
      [ vm_cast_no_check (@eq_refl _ p1_rA) | vm_cast_no_check (@eq_refl _ p1_cA)
      | exact HR | exact HK | constructor | constructor | exact Hh | exact Hlazy | ].
    clear HR HK. intros RA MA HR HK EQA LFA.
    pose proof (log_covered_frame (ENV vals) M p1_regions _ p1_covA RF LFA) as FA. rewrite <- EQA, RD in FA.
    change (s_regs (fst (fst p1_rA))) with p1_srA in HR. change (fst (fst p1_cA)) with p1_knA in HK.
    change (s_pc (fst (fst p1_rA))) with 0x273950%Z.
    (* [comment removed for export] *)
    eapply (rz_ioctl_winsz RSEGS _ _ _ model ECALLW (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)));
      [ vm_compute; reflexivity | apply is_ecall_ECALLW | exact Hh | exact Hlazy
      | regv HR (17 : reg); reflexivity | regv HR (10 : reg); reflexivity
      | change (bv_unsigned (Z_to_bv 64 1)) with 1%Z; lia | exact Hfd1
      | regv HR (11 : reg); reflexivity | ].
    rewrite v_addi_pc4 by lia. change (0x273950 + 4)%Z with 0x273954%Z.
    pose proof (regs_set_a0 (ENV vals) _ _ (errno_ret ENOTTY) (ELit (2^64 - 25)%Z) HR
                  ltac:(cbn [edenot]; apply bv_eq; reflexivity)) as HR'.
    clear HR. change (sr_upd p1_srA (ridx 10) (ELit (2 ^ 64 - 25)%Z)) with p1_srA' in HR'.
    (* [comment removed for export] *)
    eapply (rz_run_lf RSEGS FUEL1 STOPS1 scr0 0x273954 p1_srA' p1_knA 34 (fst (fst p1_rB)) (snd (fst p1_rB)) (snd p1_rB)
              (fst (fst p1_cB)) (snd (fst p1_cB)) (snd p1_cB) (ENV vals) MA (seg_rom RSEGS) _ model);
      [ vm_cast_no_check (@eq_refl _ p1_rB) | vm_cast_no_check (@eq_refl _ p1_cB)
      | exact HR' | exact HK | constructor | constructor | exact Hh | exact Hlazy | ].
    clear HR' HK. intros RB MB HR HK EQB LFB.
    pose proof (log_covered_frame (ENV vals) MA p1_regions _ p1_covB RF LFB) as FB. rewrite <- EQB, RD in FB.
    change (s_regs (fst (fst p1_rB))) with p1_srB in HR. change (fst (fst p1_cB)) with p1_knB in HK.
    change (s_pc (fst (fst p1_rB))) with 0x272e44%Z.
    (* [comment removed for export] *)
    pose proof p1_itinerary as (_ & _ & _ & _ & _ & _ & SC & _).
    apply (stdio_call_sound_post vals (blobs_ev []) p1_srB p1_knB RB MB model p1_sc [Z_to_bv 8 48] [Z_to_bv 8 10] K
             HR HK (eq_trans (f_equal (fun n => stdio_call n p1_srB p1_knB) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn p1_sc length edenot ev ENV Z.of_nat Pos.of_succ_nat Pos.succ].
    - change (bv_unsigned (Z_to_bv 64 3211104)) with 3211104%Z. change (bv_unsigned (Z_to_bv 64 3211105)) with 3211105%Z. lia.
    - change (bv_unsigned (Z_to_bv 64 3211105)) with 3211105%Z. lia.
    - change (bv_unsigned (Z_to_bv 64 3211104)) with 3211104%Z. change (bv_unsigned (Z_to_bv 64 3211105)) with 3211105%Z. lia.
    - reflexivity.
    - lia.
    - left. change (bv_unsigned (Z_to_bv 64 3211105)) with 3211105%Z. rewrite P0, alu_add, vadd_wZ. unorm. lia.
    - left. change (bv_unsigned (Z_to_bv 64 103824)) with 103824%Z. change (bv_unsigned (Z_to_bv 64 1)) with 1%Z.
      rewrite P0, alu_add, vadd_wZ. unorm. lia.
    - change (bv_unsigned (Z_to_bv 64 103824)) with 103824%Z. change (bv_unsigned (Z_to_bv 64 1)) with 1%Z. lia.
    - (* [comment removed for export] *) change (bv_unsigned (Z_to_bv 64 3211104)) with 3211104%Z. krd_solve HK.
    - (* [comment removed for export] *) krd_solve HK.
    - exact Hfd1.
    - exact Hh.
    - exact Hlazy.
    - exact HKnil.
    - (* [comment removed for export] *)
      clear HR HK. intros Rj MC HR HK HPOST.
      assert (FC0 : frame_mod MB MC p1_regions_w).
      { eapply sw_post_frame_mod; [exact HPOST|]. intros x Hx. unfold p1_regions_w in Hx. cbn [outside] in Hx.
        unfold in_rng in Hx. rewrite P0, alu_add, vadd_wZ. revert Hx. unorm. intros (N1 & N2 & N3 & _). lia. }
      set (vals' := vals ++ junk_vals Rj) in *.
      assert (HL' : length vals' = 66%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      pose proof (p1_regions_flat vals' P0' ltac:(lia) ltac:(lia)) as RF'.
      pose proof (p1_regions_denot vals' P0' ltac:(lia)) as RD'.
      change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK.
      eapply (rz_run_lf RSEGS FUEL1 STOPS1 scr0 0x273974 (sc_sr p1_sc) (sc_kn p1_sc) 66 (fst (fst p1_rC)) (snd (fst p1_rC)) (snd p1_rC)
                (fst (fst p1_cC)) (snd (fst p1_cC)) (snd p1_cC) (ENV vals') MC (seg_rom RSEGS) _ model);
        [ vm_cast_no_check (@eq_refl _ p1_rC) | vm_cast_no_check (@eq_refl _ p1_cC)
        | exact HR | exact HK | constructor | constructor | exact Hh | exact Hlazy | ].
      clear HR HK. intros RC MF HR HK EQC LFC.
      pose proof (log_covered_frame (ENV vals') MC p1_regions _ p1_covC RF' LFC) as FC. rewrite <- EQC, RD' in FC.
      change (s_regs (fst (fst p1_rC))) with p1_srF in HR. change (fst (fst p1_cC)) with p1_knF in HK.
      change (s_pc (fst (fst p1_rC))) with 0xddca8%Z.
      apply (HCONT Rj RC MF HR HK).
      eapply frame_mod_trans_same; [exact FA|]. eapply frame_mod_trans_same; [exact FB|].
      eapply frame_mod_trans_same; [exact FC0 | exact FC].
  Qed.
End First.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Plain.
  Variable model : Model.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd1 : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).

  (* [comment removed for export] *)
  Record p1H (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z) : Prop := P1H {
    Q1  : getr regs 1 = Z_to_bv 64 0xddca8;
    Q2  : getr regs 2 = sp;
    Q11 : getr regs 11 = Z_to_bv 64 0;
    Qsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    QspLo : (0x100000500 <= bv_unsigned sp)%Z;
    QspHi : (bv_unsigned sp <= 0x7fffffffffff)%Z;
    Qstk  : stk_ok RSEGS mem sp 1232;
    Qimg  : forall i, (0x10000 <= i < 0x27e000)%Z -> mem (Z_to_bv 64 i) = None;
    Qcells : cells_ok mem p1_cells;
    Qcan  : rdn RSEGS mem (Z_to_bv 64 0x30f4b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Qcan64 : (0 <= can < 2 ^ 64)%Z }.

  (* [comment removed for export] *)
  Record p1Post (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := P1P {
    P_sp  : getr regs' 2 = sp;
    P_ra  : getr regs' 1 = Z_to_bv 64 0xddca8;
    P_a0  : getr regs' 10 = Z_to_bv 64 2;
    P_cs  : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    (* [comment removed for export] *)
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1232), 1232%Z); (Z_to_bv 64 0x2dc7a0, 232%Z); (Z_to_bv 64 0x30ff60, 1%Z)];
    (* [comment removed for export] *)
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0x2dc7a0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0x2dc7a8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0x2dc7b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wend  : rdn RSEGS mem' (Z_to_bv 64 0x2dc7c0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x310360));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0x2dc7c8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x30ff60));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0x2dc7d8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x30ff60));
    P_write : rdn RSEGS mem' (Z_to_bv 64 0x2dc7e8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x272e44));
    P_buf   : rdn RSEGS mem' (Z_to_bv 64 0x2dc7f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x30ff60));
    P_bsz   : rdn RSEGS mem' (Z_to_bv 64 0x2dc800) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
    P_fd    : rdn RSEGS mem' (Z_to_bv 64 0x2dc818) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
    P_mode  : rdn RSEGS mem' (Z_to_bv 64 0x2dc828) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0x2dc82c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lbf   : rdn RSEGS mem' (Z_to_bv 64 0x2dc830) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_can   : rdn RSEGS mem' (Z_to_bv 64 0x30f4b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    P_stk   : stk_ok RSEGS mem' sp 1232 }.

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

  Lemma p1_regs_ok : forall regs mem sp can, p1H regs mem sp can ->
    regs_ok (ENV (p1_vals regs sp can)) p1_sr regs.
  Proof.
    intros regs mem sp can PH. destruct PH.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth p1_sr allregs32 edenot].
    1: apply getr_zero.
    1: assumption.
    1: cbn [ev ENV]; assumption.
    9: assumption.
    all: rewrite p1_ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma p1_know_ok : forall regs mem sp can, p1H regs mem sp can ->
    know_ok RSEGS (ENV (p1_vals regs sp can)) mem p1_kn.
  Proof.
    intros regs mem sp can PH. destruct PH. pose proof (u64_range sp) as Hsp.
    assert (E0 : ev (ENV (p1_vals regs sp can)) 0 = sp) by reflexivity.
    assert (E1 : ev (ENV (p1_vals regs sp can)) 1 = Z_to_bv 64 can) by reflexivity.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
    unfold p1_kn. apply know_ok_app; [| apply cells_know; [vm_compute; reflexivity | assumption]].
    repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite E0. lia.
    - apply (kwr_of_stk_ok RSEGS _ mem (EVar 0) sp 1232); [exact E0 | assumption | lia].
    - apply kimg_intro; [lia | lia | assumption].
    - eapply (kword_intro RSEGS _ mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | exact E1 | lia | lia | rewrite Z0; lia
        | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; assumption].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
  Qed.

  Theorem printf0_first : forall regs mem (sp : word) (can : Z) (K : TSet),
    p1H regs mem sp can ->
    K [] ->
    (forall regs' mem', p1Post regs mem sp can regs' mem' ->
       realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xddca8) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xddd60) mem (seg_rom RSEGS)) model)
             (t_emit [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 48); WriteEv (Z_to_bv 64 1) (Z_to_bv 8 10)] K).
  Proof.
    intros regs mem sp can K PH HKnil HCONT.
    pose proof (p1_regs_ok regs mem sp can PH) as HR. pose proof (p1_know_ok regs mem sp can PH) as HK.
    destruct PH. pose proof (u64_range sp) as Hsp.
    apply (p1_sound sp model Hh Hlazy Hfd1 (p1_vals regs sp can) regs mem K);
      [ unfold p1_vals; rewrite length_app, junk_vals_length; reflexivity | reflexivity | exact HR | exact HK | exact HKnil |].
    clear HR HK. intros Rj R' M' HR HK FM.
    set (vals' := p1_vals regs sp can ++ junk_vals Rj) in *.
    assert (P0 : vals_ev vals' 0 = sp) by reflexivity.
    assert (P1 : vals_ev vals' 1 = Z_to_bv 64 can) by reflexivity.
    assert (PJ : forall i, (2 <= i < 34)%nat -> vals_ev vals' i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2)))).
    { intros i Hi. subst vals'. rewrite vals_ev_app_l by (unfold p1_vals; rewrite length_app, junk_vals_length; cbn; lia).
      apply (p1_ev_junk regs sp can i Hi). }
    apply HCONT. split.
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
    - krd HK 0x30f4b8%Z 8%nat Hc. rewrite Hc. cbn [ev ENV]. rewrite P1. reflexivity.
    - intros a n Ha Hn. eapply frame_mod_store_ok; [exact FM|]. apply Qstk0; assumption.
  Qed.
End Plain.
