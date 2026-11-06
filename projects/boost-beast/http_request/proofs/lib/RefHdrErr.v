(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux
  Hoare RefExitBase RefStdioDefs RefStdioWrite LibStdioCall RefPrintfBufBase RefPrintfFirst LibTail LibDiagKn Spec.
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
Definition HF_FR : Z := 256%Z.
Definition STOPSH : list Z := [0x6afc8; 0x2ae5c]%Z.
Definition FUELH : nat := 5000.

(* [comment removed for export] *)
Definition h_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0 | 4 => ELit 0x92650%Z
                          | _ => EVar (3 + i) end)%nat (seq 0 32)).

Definition h_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x100000500 0x7fffffffffff;
   KWr (SA (EVar 0) (- HF_FR)) HF_FR;
   KImg 0x10000 0x7a000;
   KWr (SA (ELit 0) 0x80000) 0x34000;
   KWord (SA (ELit 0) 0x925a8) 4 (EVar 1);
   KWord (SA (ELit 0) CANARY) 8 (EVar 2)]%Z
  ++ kn_cells diag_cells.

Definition sc_dummy : stdio_res := SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [].

(* [comment removed for export] *)
Definition hs_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x2ae20 h_sr [] h_kn 35) []).
Definition hs_cA := Eval vm_compute in (carry (s_log (fst (fst hs_rA))) h_kn []).
Definition hs_srA : list expr := Eval vm_compute in (s_regs (fst (fst hs_rA))).
Definition hs_knA : list kentry := Eval vm_compute in (fst (fst hs_cA)).
Definition hs_sc : stdio_res := Eval vm_compute in
  (match stdio_call 35 hs_srA hs_knA with Some r => r | None => sc_dummy end).
Definition hs_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x6aecc (sc_sr hs_sc) [] (sc_kn hs_sc) 67) []).
Definition hs_cC := Eval vm_compute in (carry (s_log (fst (fst hs_rC))) (sc_kn hs_sc) []).
Definition hs_srF : list expr := Eval vm_compute in (s_regs (fst (fst hs_rC))).
Definition hs_knF : list kentry := Eval vm_compute in (fst (fst hs_cC)).

Lemma hs_itinerary :
  s_pc (fst (fst hs_rA)) = 0x6afc8%Z /\ snd (fst hs_rA) = [] /\ snd (fst hs_cA) = []
  /\ stdio_call 35 hs_srA hs_knA = Some hs_sc
  /\ (sc_ret hs_sc, sc_f hs_sc, sc_fd hs_sc, sc_s hs_sc, sc_l hs_sc) = (0x6aecc%Z, 0x80a20%Z, 2%Z, ELit 0x14782%Z, ELit 31%Z)
  /\ s_pc (fst (fst hs_rC)) = 0x2ae5c%Z /\ snd (fst hs_rC) = [] /\ snd (fst hs_cC) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Definition ho_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x2ae3c h_sr [] h_kn 35) []).
Definition ho_cA := Eval vm_compute in (carry (s_log (fst (fst ho_rA))) h_kn []).
Definition ho_srA : list expr := Eval vm_compute in (s_regs (fst (fst ho_rA))).
Definition ho_knA : list kentry := Eval vm_compute in (fst (fst ho_cA)).
Definition ho_sc : stdio_res := Eval vm_compute in
  (match stdio_call 35 ho_srA ho_knA with Some r => r | None => sc_dummy end).
Definition ho_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x6aecc (sc_sr ho_sc) [] (sc_kn ho_sc) 67) []).
Definition ho_cC := Eval vm_compute in (carry (s_log (fst (fst ho_rC))) (sc_kn ho_sc) []).
Definition ho_srF : list expr := Eval vm_compute in (s_regs (fst (fst ho_rC))).
Definition ho_knF : list kentry := Eval vm_compute in (fst (fst ho_cC)).

Lemma ho_itinerary :
  s_pc (fst (fst ho_rA)) = 0x6afc8%Z /\ snd (fst ho_rA) = [] /\ snd (fst ho_cA) = []
  /\ stdio_call 35 ho_srA ho_knA = Some ho_sc
  /\ (sc_ret ho_sc, sc_f ho_sc, sc_fd ho_sc, sc_s ho_sc, sc_l ho_sc) = (0x6aecc%Z, 0x80a20%Z, 2%Z, ELit 0x11905%Z, ELit 31%Z)
  /\ s_pc (fst (fst ho_rC)) = 0x2ae5c%Z /\ snd (fst ho_rC) = [] /\ snd (fst ho_cC) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma hso_srF : ho_srF = hs_srF. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x14782) 31 = Some msg_short.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x11905) 31 = Some msg_overrun.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_short_len : length msg_short = 31%nat. Proof. reflexivity. Qed.
Lemma msg_overrun_len : length msg_overrun = 31%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_regions : list sregion :=
  [(SA (EVar 0) (- HF_FR), HF_FR); (SA (ELit 0) 0x80a20, 232)]%Z.

Lemma hs_covA : log_covered h_regions (s_log (fst (fst hs_rA))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hs_covC : log_covered h_regions (s_log (fst (fst hs_rC))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ho_covA : log_covered h_regions (s_log (fst (fst ho_rA))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ho_covC : log_covered h_regions (s_log (fst (fst ho_rC))) = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
  Variable sp0 : word.
  Variable model : Model.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev []).

  Definition h_regions_w : list (word * Z) :=
    [(Z_to_bv 64 (bv_unsigned sp0 - HF_FR), HF_FR); (Z_to_bv 64 0x80a20, 232%Z)].

  Lemma h_regions_denot : forall vals, vals_ev vals 0 = sp0 ->
    (0x100000500 <= bv_unsigned sp0)%Z ->
    map (rdenot (ENV vals)) h_regions = h_regions_w.
  Proof.
    intros vals P0 Hlo. unfold h_regions, h_regions_w, rdenot, estart, HF_FR. cbn [map fst snd a_base a_off edenot ev ENV].
    rewrite P0. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    repeat f_equal; lia.
  Qed.

  Lemma h_regions_flat : forall vals, vals_ev vals 0 = sp0 ->
    (0x100000500 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x7fffffffffff)%Z ->
    regions_flat (ENV vals) h_regions.
  Proof.
    intros vals P0 Hlo Hhi r Hr. unfold h_regions, HF_FR in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV];
      rewrite ?P0; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac scs_nil :=
    lazymatch goal with
    | |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l'
    | |- Forall _ ?l => let l' := eval vm_compute in l in change l with l'
    end; apply Forall_nil.

  (* [comment removed for export] *)
  Ltac hf_sound pcA rA cA srA knA sc rC cC srF knF ITIN COVA COVC MSG_IMG MSG_LEN msg :=
    intros vals R M K HL P0 HR HK HKnil HCONT;
    pose proof (know_nth RSEGS _ _ h_kn 1%nat _ HK eq_refl) as Hrg; cbn [kentry_ok edenot ev ENV] in Hrg; rewrite P0 in Hrg;
    pose proof (h_regions_flat vals P0 ltac:(lia) ltac:(lia)) as RF;
    pose proof (h_regions_denot vals P0 ltac:(lia)) as RD;
    (* [comment removed for export] *)
    eapply (rz_run_lf RSEGS FUELH STOPSH scr0 pcA h_sr h_kn 35 (fst (fst rA)) (snd (fst rA)) (snd rA)
              (fst (fst cA)) (snd (fst cA)) (snd cA) (ENV vals) M (seg_rom RSEGS) R model);
      [ vm_cast_no_check (@eq_refl _ rA) | vm_cast_no_check (@eq_refl _ cA)
      | exact HR | exact HK | scs_nil | scs_nil | exact Hh | exact Hlazy | ];
    clear HR HK; intros RA MA HR HK EQA LFA;
    pose proof (log_covered_frame (ENV vals) M h_regions _ COVA RF LFA) as FA; rewrite <- EQA, RD in FA;
    change (s_regs (fst (fst rA))) with srA in HR; change (fst (fst cA)) with knA in HK;
    change (s_pc (fst (fst rA))) with 0x6afc8%Z;
    (* [comment removed for export] *)
    pose proof ITIN as (_ & _ & _ & SC & _);
    apply (stdio_call_sound_post vals (blobs_ev []) srA knA RA MA model sc [] msg K
             HR HK (eq_trans (f_equal (fun n => stdio_call n srA knA) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn sc edenot ev ENV app];
      rewrite ?MSG_LEN; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
    [ unorm; lia
    | unorm; lia
    | unorm; lia
    | unorm; reflexivity
    | lia
    | left; rewrite P0, alu_add, vadd_wZ; unorm; lia
    | left; rewrite P0, alu_add, vadd_wZ; unorm; lia
    | unorm; lia
    | unorm; reflexivity
    | (* [comment removed for export] *)
      lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 31 = _ =>
        rewrite (kimg_rdn RSEGS (ENV vals) _ knA ltac:(let i := kidx knA (is_kimg_cov a 31) in exact i)
                   _ _ a 31 HK eq_refl) by (cbn; lia) end;
      apply MSG_IMG
    | exact Hfd2
    | exact Hh
    | exact Hlazy
    | exact HKnil
    | (* [comment removed for export] *)
      clear HR HK; intros Rj MC HR HK HPOST;
      assert (FC0 : frame_mod MA MC h_regions_w);
      [ eapply sw_post_frame_mod; [exact HPOST|]; intros x Hx; unfold h_regions_w, HF_FR in Hx; cbn [outside] in Hx;
        unfold in_rng in Hx; rewrite P0, alu_add, vadd_wZ; revert Hx; unorm; intros (N1 & N2 & _); lia |];
      set (vals' := vals ++ junk_vals Rj) in *;
      assert (HL' : length vals' = 67%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity);
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
      pose proof (h_regions_flat vals' P0' ltac:(lia) ltac:(lia)) as RF';
      pose proof (h_regions_denot vals' P0' ltac:(lia)) as RD';
      change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK;
      eapply (rz_run_lf RSEGS FUELH STOPSH scr0 0x6aecc (sc_sr sc) (sc_kn sc) 67 (fst (fst rC)) (snd (fst rC)) (snd rC)
                (fst (fst cC)) (snd (fst cC)) (snd cC) (ENV vals') MC (seg_rom RSEGS) _ model);
        [ vm_cast_no_check (@eq_refl _ rC) | vm_cast_no_check (@eq_refl _ cC)
        | exact HR | exact HK | scs_nil | scs_nil | exact Hh | exact Hlazy | ];
      clear HR HK; intros RC MF HR HK EQC LFC;
      pose proof (log_covered_frame (ENV vals') MC h_regions _ COVC RF' LFC) as FC; rewrite <- EQC, RD' in FC;
      change (s_regs (fst (fst rC))) with srF in HR; change (fst (fst cC)) with knF in HK;
      change (s_pc (fst (fst rC))) with 0x2ae5c%Z;
      apply (HCONT Rj RC MF HR HK);
      eapply frame_mod_trans_same; [exact FA|];
      eapply frame_mod_trans_same; [exact FC0 | exact FC] ].

  Theorem hs_sound : forall vals R M (K : TSet),
    length vals = 35%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) h_sr R -> know_ok RSEGS (ENV vals) M h_kn ->
    K [] ->
    (forall Rj R' M',
       regs_ok (ENV (vals ++ junk_vals Rj)) hs_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' hs_knF ->
       frame_mod M M' h_regions_w ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x2ae5c) M' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2ae20) M (seg_rom RSEGS)) model)
             (t_emit (W 2 msg_short) K).
  Proof.
    unfold W.
    hf_sound 0x2ae20%Z hs_rA hs_cA hs_srA hs_knA hs_sc hs_rC hs_cC hs_srF hs_knF
             hs_itinerary hs_covA hs_covC msg_short_img msg_short_len msg_short.
  Qed.

  Theorem ho_sound : forall vals R M (K : TSet),
    length vals = 35%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) h_sr R -> know_ok RSEGS (ENV vals) M h_kn ->
    K [] ->
    (forall Rj R' M',
       regs_ok (ENV (vals ++ junk_vals Rj)) ho_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' ho_knF ->
       frame_mod M M' h_regions_w ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x2ae5c) M' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2ae3c) M (seg_rom RSEGS)) model)
             (t_emit (W 2 msg_overrun) K).
  Proof.
    unfold W.
    hf_sound 0x2ae3c%Z ho_rA ho_cA ho_srA ho_knA ho_sc ho_rC ho_cC ho_srF ho_knF
             ho_itinerary ho_covA ho_covC msg_overrun_img msg_overrun_len msg_overrun.
  Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Plain.
  Variable model : Model.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  (* [comment removed for export] *)
  Record hfH (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (tid can : Z) : Prop := HFH {
    H2  : getr regs 2 = sp;
    H4  : getr regs 4 = Z_to_bv 64 0x92650;
    Hsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    HspLo : (0x100000500 <= bv_unsigned sp)%Z;
    HspHi : (bv_unsigned sp <= 0x7fffffffffff)%Z;
    Hstk  : stk_ok RSEGS mem sp HF_FR;
    Himg  : forall i, (0x10000 <= i < 0x7a000)%Z -> mem (Z_to_bv 64 i) = None;
    Hcells : cells_ok mem diag_cells;
    Htid  : rdn RSEGS mem (Z_to_bv 64 0x925a8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
    Htid32 : (0 <= tid < 2 ^ 32)%Z;
    Hcan  : canary_ok mem can }.

  (* [comment removed for export] *)
  Record hfPost (regs : bvmap 5 word) (mem : word -> option byte) (sp : word)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := HFP {
    P_sp  : getr regs' 2 = sp;
    P_tp  : getr regs' 4 = Z_to_bv 64 0x92650;
    P_a0  : getr regs' 10 = Z_to_bv 64 1;
    P_cs  : forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - HF_FR), HF_FR); (Z_to_bv 64 0x80a20, 232%Z)];
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0x80a20) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0x80a28) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0x80a30) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0x80a48) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb2d20));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0x80a58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb2d20));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0x80aac) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_stk   : stk_ok RSEGS mem' sp HF_FR }.

  Definition h_vals (regs : bvmap 5 word) (sp : word) (tid can : Z) : list word :=
    [sp; Z_to_bv 64 tid; Z_to_bv 64 can] ++ junk_vals regs.

  Lemma h_ev_junk : forall regs sp tid can i, (3 <= i < 35)%nat ->
    ev (ENV (h_vals regs sp tid can)) i = getr regs (Z_to_bv 5 (Z.of_nat (i - 3))).
  Proof.
    intros regs sp tid can i Hi. unfold ENV, h_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 tid; Z_to_bv 64 can] + (i - 3))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma h_regs_ok : forall regs mem sp tid can, hfH regs mem sp tid can ->
    regs_ok (ENV (h_vals regs sp tid can)) h_sr regs.
  Proof.
    intros regs mem sp tid can PH. destruct PH.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth h_sr allregs32 edenot].
    1: apply getr_zero.
    2: cbn [ev ENV]; assumption.
    3: assumption.
    all: rewrite h_ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma h_know_ok : forall regs mem sp tid can, hfH regs mem sp tid can ->
    know_ok RSEGS (ENV (h_vals regs sp tid can)) mem h_kn.
  Proof.
    intros regs mem sp tid can PH. destruct PH. pose proof (u64_range sp) as Hsp.
    assert (E0 : ev (ENV (h_vals regs sp tid can)) 0 = sp) by reflexivity.
    assert (E1 : ev (ENV (h_vals regs sp tid can)) 1 = Z_to_bv 64 tid) by reflexivity.
    assert (E2 : ev (ENV (h_vals regs sp tid can)) 2 = Z_to_bv 64 can) by reflexivity.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
    unfold h_kn. apply know_ok_app; [| apply diag_cells_know; assumption].
    repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite E0. lia.
    - apply (kwr_of_stk_ok RSEGS _ mem (EVar 0) sp HF_FR); [exact E0 | assumption | unfold HF_FR; lia].
    - apply kimg_intro; [lia | lia | assumption].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
    - eapply (kword_intro RSEGS _ mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | exact E1 | lia | lia | rewrite Z0; lia
        | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; assumption].
    - apply (canary_know _ mem 2 can E2). assumption.
  Qed.

  Ltac hf_plain SOUND :=
    intros regs mem sp tid can K PH HKnil HCONT;
    pose proof (h_regs_ok regs mem sp tid can PH) as HR; pose proof (h_know_ok regs mem sp tid can PH) as HK;
    destruct PH; pose proof (u64_range sp) as Hsp;
    apply (SOUND sp model Hh Hlazy Hfd2 (h_vals regs sp tid can) regs mem K);
      [ unfold h_vals; rewrite length_app, junk_vals_length; reflexivity | reflexivity | exact HR | exact HK | exact HKnil |];
    clear HR HK; intros Rj R' M' HR HK FM;
    try rewrite hso_srF in HR;
    set (vals' := h_vals regs sp tid can ++ junk_vals Rj) in *;
    assert (P0 : vals_ev vals' 0 = sp) by reflexivity;
    assert (PJ : forall i, (3 <= i < 35)%nat -> vals_ev vals' i = getr regs (Z_to_bv 5 (Z.of_nat (i - 3))));
    [ intros i Hi; subst vals'; rewrite vals_ev_app_l by (unfold h_vals; rewrite length_app, junk_vals_length; cbn; lia);
      apply (h_ev_junk regs sp tid can i Hi) |];
    apply HCONT; split;
    [ regv HR (2 : reg); exact P0
    | regv HR (4 : reg); reflexivity
    | regv HR (10 : reg); reflexivity
    | intros r Hr; cbn [In] in Hr;
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]];
        lazymatch goal with |- getr R' ?rr = _ => regv HR rr end; cbn [edenot ev ENV]; rewrite PJ by lia; f_equal; apply bv_eq; reflexivity
    | exact FM
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | intros a n Ha Hn; eapply frame_mod_store_ok; [exact FM|];
      match goal with Hs : stk_ok _ mem sp _ |- _ => apply Hs; assumption end ].

  Theorem hdr_short_fwrite : forall regs mem (sp : word) (tid can : Z) (K : TSet),
    hfH regs mem sp tid can ->
    K [] ->
    (forall regs' mem', hfPost regs mem sp regs' mem' ->
       realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2ae5c) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2ae20) mem (seg_rom RSEGS)) model)
             (t_emit (W 2 msg_short) K).
  Proof. hf_plain hs_sound. Qed.

  Theorem hdr_overrun_fwrite : forall regs mem (sp : word) (tid can : Z) (K : TSet),
    hfH regs mem sp tid can ->
    K [] ->
    (forall regs' mem', hfPost regs mem sp regs' mem' ->
       realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0x2ae5c) mem' (seg_rom RSEGS)) model) K) ->
    realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2ae3c) mem (seg_rom RSEGS)) model)
             (t_emit (W 2 msg_overrun) K).
  Proof. hf_plain ho_sound. Qed.
End Plain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
