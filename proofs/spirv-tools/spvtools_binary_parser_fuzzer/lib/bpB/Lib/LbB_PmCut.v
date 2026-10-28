(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_PmBase LbB_FSlots LbB_PmOwn.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition PM_RF_TOP : Z := 728.
Definition PM_RF_LO : Z := -4096.

Definition FSHB : expr := EAlu ALU_SRL (EVar WV_FF) (ELit 3).

Definition PM_OWN : list (expr * Z * Z) :=
  [(EVar WV_S1, PM_RF_LO, PM_RF_TOP); (EVar WV_FF, 24, 16376); (FSHB, SHBASE, SHBASE + PM_NSH);
   (EVar WV_P, O_WIDX, O_FLAGS + 2)].

Fixpoint xclosed (k : N) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => (32 <=? n)%N && (n <? k)%N
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => xclosed k a && xclosed k b
  | EExt _ _ _ a => xclosed k a
  | EBlob _ _ _ _ => false
  end.

Definition regs_tblX {HCEIL : HeapCeil} {H : asr} (w : pmwA H) (X : list word) (R : bvmap 5 word) (RT : list (reg * expr)) : Prop :=
  Forall (fun re => PropExec.getr R (fst re) = edenot (Eseed bvmap_empty (wenv_vals w ++ X)) (snd re)) RT.
Notation regs_tbl w R RT := (regs_tblX w [] R RT).

Definition xbound (X : list word) : N := (41 + N.of_nat (length X))%N.

Definition tbl_okX (k : N) (RT : list (reg * expr)) : bool :=
  forallb (fun re => (xclosed k (snd re) && negb (bv_eqb (fst re) 0%bv))%bool) RT.

Definition sr_tbl_checkX (k : N) (sr : list expr) (RT : list (reg * expr)) : bool :=
  forallb (fun re => (expr_eqb (sr_get sr (fst re)) (snd re) && xclosed k (snd re))%bool) RT.

Lemma wenv_vals_length {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H), length (wenv_vals w) = 9%nat.
Proof. intros w. reflexivity. Qed.

Lemma Eseed_wv {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) R R0 X n, (32 <= n <= WV_LAST)%N ->
  ev (Eseed R (wenv_vals w ++ X)) n = ev (Eseed R0 (wenv_vals w)) n.
Proof.
  intros w R R0 X n Hn. unfold WV_LAST in Hn. rewrite !Eseed_world by lia.
  rewrite app_nth1; [reflexivity|]. rewrite wenv_vals_length. lia.
Qed.

Lemma edenot_wv {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) R R0 X e, wclosed e = true ->
  edenot (Eseed R (wenv_vals w ++ X)) e = edenot (Eseed R0 (wenv_vals w)) e.
Proof. intros w R R0 X e Hc. apply edenot_wclosed; [exact Hc|]. intros n Hn. apply Eseed_wv. unfold WV_LAST. lia. Qed.

Lemma edenot_xclosed : forall R R0 vals k e, xclosed k e = true ->
  edenot (Eseed R vals) e = edenot (Eseed R0 vals) e.
Proof.
  intros R R0 vals k e. induction e; cbn [xclosed edenot]; intros Hc; try discriminate; try reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. apply N.leb_le in H1. rewrite !Eseed_world by lia. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
Qed.

Lemma regs_ok_of_tbl {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) R RT X k,
  regs_tblX w X R RT -> tbl_okX k RT = true -> regs_ok (Eseed R (wenv_vals w ++ X)) (srs sr_id RT) R.
Proof.
  intros w R RT X k HT Hok. apply regs_ok_srs; [apply regs_ok_seed|].
  unfold regs_tblX, tbl_okX in *. rewrite Forall_forall in *. intros [r e] Hin.
  pose proof (proj1 (forallb_forall _ _) Hok (r, e) Hin) as K. cbn [fst snd] in *.
  apply andb_true_iff in K as [Kc Kr]. split.
  - intros ->. discriminate Kr.
  - pose proof (HT (r, e) Hin) as HTe. cbn [fst snd] in HTe |- *. rewrite HTe. symmetry. apply (edenot_xclosed _ _ _ k). exact Kc.
Qed.

Lemma regs_tbl_of_run {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) R X sr R' RT k,
  regs_ok (Eseed R (wenv_vals w ++ X)) sr R' -> sr_tbl_checkX k sr RT = true -> regs_tblX w X R' RT.
Proof.
  intros w R X sr R' RT k HR Hc. unfold regs_tblX, sr_tbl_checkX in *. apply Forall_forall. intros [r e] Hin.
  pose proof (proj1 (forallb_forall _ _) Hc (r, e) Hin) as K. cbn [fst snd] in *.
  apply andb_true_iff in K as [Ke Kc]. apply expr_eqb_eq in Ke.
  rewrite (HR r), Ke. apply (edenot_xclosed _ _ _ k). exact Kc.
Qed.

Lemma regs_tbl_app {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X R RT1 RT2,
  regs_tblX w X R RT1 -> regs_tblX w X R RT2 -> regs_tblX w X R (RT1 ++ RT2).
Proof. intros w X R RT1 RT2 A B. apply Forall_app. split; assumption. Qed.

Lemma edenot_app_x : forall R vals more k e, xclosed k e = true -> (k <= 32 + N.of_nat (length vals))%N ->
  edenot (Eseed R vals) e = edenot (Eseed R (vals ++ more)) e.
Proof.
  intros R vals more k e. induction e; cbn [xclosed edenot]; intros Hc Hk; try discriminate; try reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. apply N.leb_le in H1. apply N.ltb_lt in H2.
    rewrite !Eseed_world by lia. rewrite app_nth1; [reflexivity|]. lia.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_true_iff in Hc as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
Qed.

Lemma regs_tbl_ext {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X X' R RT,
  regs_tblX w X R RT -> tbl_okX (xbound X) RT = true -> regs_tblX w (X ++ X') R RT.
Proof.
  intros w X X' R RT HT Hok. unfold regs_tblX, tbl_okX in *. rewrite Forall_forall in *. intros [r e] Hin.
  pose proof (proj1 (forallb_forall _ _) Hok (r, e) Hin) as K. cbn [fst snd] in *.
  apply andb_true_iff in K as [Kc _]. pose proof (HT (r, e) Hin) as HTe. cbn [fst snd] in HTe. rewrite HTe. rewrite app_assoc.
  apply (edenot_app_x _ _ _ (xbound X)); [exact Kc|]. unfold xbound. rewrite length_app, (wenv_vals_length w). lia.
Qed.

Lemma regs_tbl_restrict {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X X' R RT,
  regs_tblX w (X ++ X') R RT -> tbl_okX (xbound X) RT = true -> regs_tblX w X R RT.
Proof.
  intros w X X' R RT HT Hok. unfold regs_tblX, tbl_okX in *. rewrite Forall_forall in *. intros [r e] Hin.
  pose proof (proj1 (forallb_forall _ _) Hok (r, e) Hin) as K. cbn [fst snd] in *.
  apply andb_true_iff in K as [Kc _]. pose proof (HT (r, e) Hin) as HTe. cbn [fst snd] in HTe. rewrite HTe. rewrite app_assoc.
  symmetry. apply (edenot_app_x _ _ _ (xbound X)); [exact Kc|]. unfold xbound. rewrite length_app, (wenv_vals_length w). lia.
Qed.

Section Geom.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma pm_geom : forall (w : pmwA H), pmw_okA H w ->
    let ff := wa_ff w in let S1 := wa_s1 w in
    0 < ff /\ ff mod 64 = 0 /\ ff + 16384 <= aceil /\ AIMG_TOP + AFS_HDR <= ff
    /\ sh ff + 2048 <= aceil /\ (ff + 16384 <= sh ff \/ sh ff + 2048 <= ff)
    /\ aceil <= wa_lo w /\ wa_lo w + 32768 <= wa_sp0 w /\ wa_lo w + 4096 <= S1 /\ S1 + 832 <= wa_sp0 w
    /\ wa_sp0 w <= 2 ^ 47 /\ S1 mod 32 = 0 /\ sh ff = ff / 8 + SHBASE.
  Proof.
    intros w OK ff S1.
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack H w OK) as (S1a & S2 & S3 & S4 & S5 & S6).
    pose proof (wk_s1 H w OK) as (T1 & T2).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    change (fsz PM_FCLASS) with 16384 in *.
    fold ff S1 in F1, F2, F3, T1, T2 |- *.
    assert (SHf : sh ff = ff / 8 + SHBASE) by (unfold sh, ASHADOW_BASE, SHBASE; lia).
    assert (Happ : aapp ff 16384) by (eapply aapp_sub; [exact F8 | unfold AFS_HDR in *; lia | unfold AFS_HDR in *; lia]).
    unfold APM_STACK in S2. unfold AAPP_HI in S5.
    split; [unfold AIMG_TOP, AFS_HDR in F1; lia|]. split; [exact F3|]. split; [exact F2|]. split; [exact F1|].
    split.
    { rewrite SHf. unfold SHBASE. assert (aceil <= 2 ^ 47) by lia. Z.div_mod_to_equations. lia. }
    split.
    { rewrite SHf. unfold SHBASE. destruct Happ as [(L1 & L2)|(L1 & L2)]; unfold aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in *.
      - left. Z.div_mod_to_equations. lia.
      - right. Z.div_mod_to_equations. lia. }
    split; [exact S1a|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact T2|]. exact SHf.
  Qed.
End Geom.

Section After.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Definition env_world (w : pmwA H) (E : env) : Prop :=
    forall n, (32 <= n <= WV_LAST)%N -> ev E n = ev (Eseed bvmap_empty (wenv_vals w)) n.

  Lemma env_world_seed : forall w R X, env_world w (Eseed R (wenv_vals w ++ X)).
  Proof. intros w R X n Hn. apply Eseed_wv. exact Hn. Qed.

  Lemma ev_world : forall w E (k : nat) (z : Z), env_world w E -> (k < 9)%nat -> nth k (wenv_vals w) (Z_to_bv 64 0) = Z_to_bv 64 z ->
    0 <= z < 2 ^ 64 -> bv_unsigned (edenot E (EVar (32 + N.of_nat k))) = z.
  Proof.
    intros w E k z HE Hk Hn Hz. cbn [edenot]. rewrite HE by (unfold WV_LAST; lia).
    rewrite Eseed_world by lia. replace (N.to_nat (32 + N.of_nat k) - 32)%nat with k by lia. rewrite Hn. apply u64_of_Z. lia.
  Qed.

  Lemma ev_ff : forall w E, pmw_okA H w -> env_world w E -> bv_unsigned (edenot E (EVar WV_FF)) = wa_ff w.
  Proof.
    intros w E OK HE. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    apply (ev_world w E 1 (wa_ff w) HE ltac:(lia) eq_refl). lia.
  Qed.
  Lemma ev_s1 : forall w E, pmw_okA H w -> env_world w E -> bv_unsigned (edenot E (EVar WV_S1)) = wa_s1 w.
  Proof.
    intros w E OK HE. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    apply (ev_world w E 3 (wa_s1 w) HE ltac:(lia) eq_refl). pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). lia.
  Qed.
  Lemma ev_p : forall w E, pmw_okA H w -> env_world w E -> bv_unsigned (edenot E (EVar WV_P)) = wa_p w.
  Proof.
    intros w E OK HE. pose proof (p_range H w OK) as [P1 P2]. pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    apply (ev_world w E 0 (wa_p w) HE ltac:(lia) eq_refl). unfold AIMG_TOP, PARSER_SIZE in *. lia.
  Qed.
  Lemma ev_fshb : forall w E, pmw_okA H w -> env_world w E -> bv_unsigned (edenot E FSHB) = wa_ff w / 8.
  Proof.
    intros w E OK HE. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    unfold FSHB. apply srl3_val; [| lia]. rewrite <- (ev_ff w E OK HE). symmetry. apply Z_to_bv_bv_unsigned.
  Qed.

  Definition own_nwins (w : pmwA H) : list (Z * Z) :=
    [(wa_s1 w + PM_RF_LO, wa_s1 w + PM_RF_TOP); (wa_ff w + 24, wa_ff w + 16376);
     (sh (wa_ff w), sh (wa_ff w) + PM_NSH); (wa_p w + O_WIDX, wa_p w + (O_FLAGS + 2))].

  Lemma num_wins_own : forall w E, pmw_okA H w -> env_world w E -> num_wins E PM_OWN = own_nwins w.
  Proof.
    intros w E OK HE. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    unfold num_wins, PM_OWN, own_nwins. cbn [map]. rewrite (ev_s1 w E OK HE), (ev_ff w E OK HE), (ev_fshb w E OK HE), (ev_p w E OK HE).
    destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SHf). rewrite SHf, Z.add_assoc. reflexivity.
  Qed.

  Lemma own_wins_ok : forall w, pmw_okA H w ->
    Forall (own_ivl H w) (own_nwins w) /\ Forall (fun iv : Z * Z => fst iv <= snd iv) (own_nwins w).
  Proof.
    intros w OK. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    unfold own_nwins, own_ivl, PM_RF_TOP, PM_RF_LO, PM_NSH. change (fsz PM_FCLASS) with 16384. split.
    - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + left. lia.
      + right; left. lia.
      + right; right; left. unfold PM_NSH. lia.
      + right; right; right. unfold O_WIDX, O_FLAGS. lia.
    - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold O_WIDX, O_FLAGS; lia.
  Qed.

  Lemma sym_inside_num : forall w E se, pmw_okA H w -> env_world w E ->
    sym_inside PM_OWN se = true ->
    let a := estart E (e_addr se) in let n := Z.of_nat (e_width se) in
    (expr_eqb (a_base (e_addr se)) (EVar WV_S1) = true /\ wa_s1 w + PM_RF_LO <= a /\ a + n <= wa_s1 w + PM_RF_TOP)
    \/ (expr_eqb (a_base (e_addr se)) (EVar WV_FF) = true /\ wa_ff w + 24 <= a /\ a + n <= wa_ff w + 16376)
    \/ (expr_eqb (a_base (e_addr se)) FSHB = true /\ sh (wa_ff w) <= a /\ a + n <= sh (wa_ff w) + PM_NSH)
    \/ (expr_eqb (a_base (e_addr se)) (EVar WV_P) = true /\ wa_p w + O_WIDX <= a /\ a + n <= wa_p w + O_FLAGS + 2).
  Proof.
    intros w E se OK HE Hs a n.
    unfold PM_OWN in Hs. cbn [sym_inside] in Hs. rewrite orb_false_r in Hs.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    apply orb_true_iff in Hs as [Hs|Hs]; [| apply orb_true_iff in Hs as [Hs|Hs]; [| apply orb_true_iff in Hs as [Hs|Hs]]];
      unfold sym_in1 in Hs;
      apply andb_true_iff in Hs as [Hs H2]; apply andb_true_iff in Hs as [Hb H1];
      apply Z.leb_le in H1; apply Z.leb_le in H2; pose proof Hb as Hb'; apply expr_eqb_true in Hb'.
    - left. split; [exact Hb|]. subst a n. unfold estart. rewrite Hb', (ev_s1 w E OK HE). unfold PM_RF_TOP, PM_RF_LO in *. lia.
    - right; left. split; [exact Hb|]. subst a n. unfold estart. rewrite Hb', (ev_ff w E OK HE). lia.
    - right; right; left. split; [exact Hb|]. subst a n. unfold estart. rewrite Hb', (ev_fshb w E OK HE). rewrite G13.
      unfold PM_NSH in *. lia.
    - right; right; right. split; [exact Hb|]. subst a n. unfold estart. rewrite Hb', (ev_p w E OK HE).
      unfold O_WIDX, O_FLAGS in *. lia.
  Qed.
End After.

Lemma gran_of_length : forall sz b, 0 <= sz -> length (gran_of sz b) = Z.to_nat ((sz + 7) / 8).
Proof.
  intros sz b Hsz. unfold gran_of. destruct b.
  - rewrite length_app, repeat_length. destruct (Z.eqb_spec (sz mod 8) 0) as [E0|E0]; cbn [length].
    + pose proof (Z.div_mod sz 8 ltac:(lia)) as D. assert ((sz + 7) / 8 = sz / 8).
      { rewrite D at 1. rewrite E0. replace (8 * (sz / 8) + 0 + 7) with (7 + (sz / 8) * 8) by lia.
        rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
      rewrite H. lia.
    + pose proof (Z.div_mod sz 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as B.
      assert ((sz + 7) / 8 = sz / 8 + 1).
      { rewrite D at 1. replace (8 * (sz / 8) + sz mod 8 + 7) with ((sz mod 8 + 7) + (sz / 8) * 8) by lia.
        rewrite Z.div_add by lia. assert ((sz mod 8 + 7) / 8 = 1) by (symmetry; apply Z.div_unique with (sz mod 8 - 1); lia). lia. }
      rewrite H. assert (0 <= sz / 8) by (apply Z.div_pos; lia). lia.
  - apply repeat_length.
Qed.

Lemma fsh_objs_length : forall objs i ins ins' pos, Forall (fun o : Z * Z => 0 <= snd o) objs ->
  length (fsh_objs objs i ins pos) = length (fsh_objs objs i ins' pos).
Proof.
  induction objs as [|[off sz] rest IH]; intros i ins ins' pos Hp; cbn [fsh_objs]; [reflexivity|].
  inversion Hp as [|? ? H0 H1]; subst. cbn [snd] in H0.
  rewrite !length_app, !gran_of_length by exact H0. rewrite (IH _ ins ins' _ H1). reflexivity.
Qed.

Lemma pm_fsh_len : forall ins, length (fsh_pat PM_OBJS PM_NSH ins) = 1448%nat.
Proof.
  intros ins. unfold fsh_pat. rewrite !length_app, repeat_length, repeat_length.
  rewrite (fsh_objs_length PM_OBJS 0 ins [] 4) by (unfold PM_OBJS; repeat constructor; cbn; lia).
  vm_compute. reflexivity.
Qed.

Section AfterRun.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Definition keys_ok (ks : list Z) : bool := forallb (fun k => (PM_RF_LO <=? k) && (k + 8 <=? PM_RF_TOP))%bool ks.

  Definition fkeys_ok (ks : list Z) : bool := forallb (fun k => (24 <=? k) && (k + 8 <=? 16376))%bool ks.

  Definition scal_after (E : env) (LOG : list sentry) (c : pmc) : pmc :=
    set_scalA c (sval E LOG (EVar WV_P) O_WIDX 8 (c_widx c)) (sval E LOG (EVar WV_P) O_ICOUNT 8 (c_icount c))
                (sval E LOG (EVar WV_P) O_ENDIAN 4 (c_endian c)) (sval E LOG (EVar WV_P) O_FLAGS 1 (c_reqconv c)).
  Definition scal_ok (LOG : list sentry) : bool :=
    (field_ok LOG (EVar WV_P) O_WIDX 8 && field_ok LOG (EVar WV_P) O_ICOUNT 8 && field_ok LOG (EVar WV_P) O_ENDIAN 4
     && field_ok LOG (EVar WV_P) O_FLAGS 1 && field_ok LOG (EVar WV_P) (O_FLAGS + 1) 1)%bool.

  Definition scal_none (LOG : list sentry) : bool :=
    forallb (fun kw => match lfield LOG (EVar WV_P) (fst kw) (snd kw) with None => true | _ => false end)
      [(O_WIDX, 8%nat); (O_ICOUNT, 8%nat); (O_ENDIAN, 4%nat); (O_FLAGS, 1%nat); (O_FLAGS + 1, 1%nat)].

  Lemma scal_none_facts : forall E LOG c, scal_none LOG = true ->
    scal_ok LOG = true /\ scal_after E LOG c = c /\ sval E LOG (EVar WV_P) (O_FLAGS + 1) 1 0 = 0.
  Proof.
    intros E LOG c Hn. unfold scal_none in Hn. cbn [forallb fst snd] in Hn.
    destruct (lfield LOG (EVar WV_P) O_WIDX 8) eqn:E1; [destruct o; discriminate|].
    destruct (lfield LOG (EVar WV_P) O_ICOUNT 8) eqn:E2; [destruct o; discriminate|].
    destruct (lfield LOG (EVar WV_P) O_ENDIAN 4) eqn:E3; [destruct o; discriminate|].
    destruct (lfield LOG (EVar WV_P) O_FLAGS 1) eqn:E4; [destruct o; discriminate|].
    destruct (lfield LOG (EVar WV_P) (O_FLAGS + 1) 1) eqn:E5; [destruct o; discriminate|].
    unfold scal_ok, field_ok, scal_after. rewrite E1, E2, E3, E4, E5. split; [reflexivity|].
    rewrite !sval_none by assumption. split; [apply set_scalA_id | reflexivity].
  Qed.

  Lemma pm_after_run : forall w s LB LBs m mo c ins tbl ftbl TB spal E LOG ins' ks fks,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E ->
    log_flat E LOG -> mem_inv asegs (mem_denot E m LOG) ->
    forallb (sym_inside PM_OWN) LOG = true ->
    lbytes LOG FSHB SHBASE (fsh_pat PM_OBJS PM_NSH ins) = Some (fsh_pat PM_OBJS PM_NSH ins') ->
    keys_ok (map fst tbl ++ ks) = true -> fkeys_ok (map fst ftbl ++ fks) = true ->
    scal_ok LOG = true -> sval E LOG (EVar WV_P) (O_FLAGS + 1) 1 0 = 0 ->
    0 <= c_widx (scal_after E LOG c) <= wa_n w -> 0 <= c_icount (scal_after E LOG c) <= c_widx (scal_after E LOG c) ->
    0 <= c_endian (scal_after E LOG c) < 2 ^ 32 -> (c_reqconv (scal_after E LOG c) = 0 \/ c_reqconv (scal_after E LOG c) = 1) ->
    forall spal', 0 <= spal' <= PM_RESERVE -> pm_phi c + spal <= pm_phi (scal_after E LOG c) + spal' ->
    PMXAT H LINV w s LB LBs (mem_denot E m LOG) mo (scal_after E LOG c) ins' (upd_slots LOG (EVar WV_S1) tbl ++ add_slots LOG (EVar WV_S1) ks)
         (upd_slots LOG (EVar WV_FF) ftbl ++ add_slots LOG (EVar WV_FF) fks) TB spal'.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E LOG ins' ks fks OK X HE Hf MI Hown Hby Hks Hfks Hsok Hr0 B1 B2 B3 B4 spal' Bsp Bphi.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (own_wins_ok H w OK) as [OW1 OW2].
    assert (MU : munch (own_nwins H w) m (mem_denot E m LOG)).
    { rewrite <- (num_wins_own H w E OK HE). apply munch_sym; assumption. }
    assert (Hkr : forall k, In k (map fst tbl ++ ks) -> PM_RF_LO <= k /\ k + 8 <= PM_RF_TOP).
    { intros k Hk. pose proof (proj1 (forallb_forall _ _) Hks k Hk) as K. apply andb_true_iff in K as [K1 K2].
      apply Z.leb_le in K1. apply Z.leb_le in K2. lia. }
    assert (Hfkr : forall k, In k (map fst ftbl ++ fks) -> 24 <= k /\ k + 8 <= 16376).
    { intros k Hk. pose proof (proj1 (forallb_forall _ _) Hfks k Hk) as K. apply andb_true_iff in K as [K1 K2].
      apply Z.leb_le in K1. apply Z.leb_le in K2. lia. }
    pose proof (pm_fsh_len ins) as LEN. pose proof (pm_fsh_len ins') as LEN'.
    pose proof (ev_fshb H w E OK HE) as EF.
    pose proof (ev_p H w E OK HE) as EP.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (p_range H w OK) as (PR1 & PR2).
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    assert (SHP : sh (wa_ff w) + 2048 <= wa_p w \/ wa_p w + PARSER_SIZE <= sh (wa_ff w)).
    { pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE (wa_ff w) 16384 PA ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D.
      unfold nsh in D. change ((16384 + 7) / 8) with 2048 in D. exact D. }
    assert (FFP : wa_ff w + 16384 <= wa_p w + O_WIDX \/ wa_p w + O_FLAGS + 2 <= wa_ff w).
    { destruct (wk_pin H w OK) as (f & Hf0 & P1 & P2). destruct (wk_fresh H w OK) as (_ & _ & FR).
      destruct (FR f Hf0) as [D _]. change (fsz PM_FCLASS) with 16384 in D.
      unfold O_WIDX, O_FLAGS, PARSER_SIZE in *. destruct D as [D|D]; [left | right]; lia. }

    assert (OMP : forall k len, O_WIDX <= k -> k + len <= O_FLAGS + 2 -> 0 <= len ->
                    Forall (omiss E (EVar WV_P) (wa_p w + k) len) LOG).
    { intros k len Hk1 Hk2 Hl. apply Forall_forall. intros se Hse Hne.
      pose proof (sym_inside_num H w E se OK HE (proj1 (forallb_forall _ _) Hown se Hse)) as HS.
      destruct HS as [(_ & A1 & A2)|[(_ & A1 & A2)|[(_ & A1 & A2)|(EB & _)]]]; [| | | rewrite Hne in EB; discriminate].
      - right. unfold PM_RF_LO, O_WIDX, O_FLAGS, PARSER_SIZE in *. lia.
      - unfold O_WIDX, O_FLAGS in *. destruct FFP as [D|D]; [left | right]; lia.
      - unfold PM_NSH, O_WIDX, O_FLAGS, PARSER_SIZE in *. destruct SHP as [D|D]; [left | right]; lia. }
    assert (HFA : forall k (wd : nat) old, O_WIDX <= k -> k + Z.of_nat wd <= O_FLAGS + 2 -> field_ok LOG (EVar WV_P) k wd = true ->
                    fld ASEGS m (wa_p w + k) wd old -> fld ASEGS (mem_denot E m LOG) (wa_p w + k) wd (sval E LOG (EVar WV_P) k wd old)).
    { intros k wd old Hk1 Hk2 Hok F. apply (fld_field_after E m LOG (EVar WV_P) (wa_p w) k wd old Hf EP); [apply OMP; lia | exact Hok | | | exact F];
        unfold O_WIDX, O_FLAGS, PARSER_SIZE, AAPP_HI in *; lia. }
    unfold scal_ok in Hsok. apply andb_true_iff in Hsok as [Hsok S5]. apply andb_true_iff in Hsok as [Hsok S4].
    apply andb_true_iff in Hsok as [Hsok S3]. apply andb_true_iff in Hsok as [S1 S2].
    unfold scal_after in *. cbn [c_widx c_icount c_endian c_reqconv set_scalA] in B1, B2, B3, B4.
    eapply (pmxa_own H HH LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal (mem_denot E m LOG) _ ins' _ _ _ _ _ _ spal' OK X MU
              (LbB_Conv.wmono_mem_denot _ _ _) (mem_denot_defined E m LOG) MI
              (LbB_Conv.stk_mem_denot _ _ _ _ _ (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)) OW1 OW2).
    -
      pose proof (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (S0 & S8 & U).
      split; [exact S0|]. split; [exact S8|].
      unfold pm_fsh in *.
      replace (sh (wa_ff w)) with (bv_unsigned (edenot E FSHB) + SHBASE) in U |- * by (rewrite EF; lia).
      eapply (u8arr_mem_denot E m LOG FSHB SHBASE _ _ Hf); [| | | exact U | exact Hby].
      + intros i Hi. rewrite LEN in Hi. change (Z.of_nat 1448) with 1448 in Hi.
        apply Forall_forall. intros se Hse. unfold lmiss.
        pose proof (sym_inside_num H w E se OK HE (proj1 (forallb_forall _ _) Hown se Hse)) as HS.
        destruct (expr_eqb (a_base (e_addr se)) FSHB) eqn:EB; [left; reflexivity|]. right.
        rewrite EF. rewrite G13 in HS.
        destruct HS as [(_ & A1 & A2)|[(_ & A1 & A2)|[(EB' & _)|(_ & A1 & A2)]]]; [| | exfalso; unfold FSHB in *; congruence |].
        * right. pose proof G5 as G5'. rewrite G13 in G5'. unfold PM_NSH, SHBASE, PM_RF_LO in *. lia.
        * destruct G6 as [G6|G6]; unfold PM_NSH, SHBASE in *; rewrite G13 in G6; unfold SHBASE in G6; lia.
        * rewrite G13 in SHP. unfold PM_NSH, SHBASE, O_WIDX, O_FLAGS, PARSER_SIZE in *. destruct SHP as [D|D]; [right | left]; lia.
      + rewrite EF. unfold SHBASE. pose proof (Z.div_pos (wa_ff w) 8 ltac:(lia) ltac:(lia)). lia.
      + rewrite EF, LEN. change (Z.of_nat 1448) with 1448. rewrite G13 in G5. unfold SHBASE in *. lia.
    -
      eapply (slots_mem_denot H w m bvmap_empty tbl E LOG ks (xa_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) Hf (ev_s1 H w E OK HE) HE).
      + intros k Hk. apply Forall_forall. intros se Hse Hne. specialize (Hkr k Hk).
        pose proof (sym_inside_num H w E se OK HE (proj1 (forallb_forall _ _) Hown se Hse)) as HS.
        destruct HS as [(EB & _)|[(_ & A1 & A2)|[(_ & A1 & A2)|(_ & A1 & A2)]]]; [rewrite Hne in EB; discriminate | left; unfold PM_RF_LO in *; lia | left |].
        * unfold PM_NSH, PM_RF_LO in *. lia.
        * left. unfold PM_RF_LO, O_WIDX, O_FLAGS, PARSER_SIZE in *. lia.
      + intros k Hk. specialize (Hkr k Hk). unfold PM_RF_TOP, PM_RF_LO in *. lia.
      + intros k Hk. assert (Hk' : In k (map fst tbl ++ ks)) by (apply in_app_iff; right; exact Hk).
        specialize (Hkr k Hk'). pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (W1 & W2 & W3).
        split; [unfold PM_RF_LO in *; lia|]. split; [unfold PM_RF_TOP in *; lia|]. intros i Hi.
        exact (proj1 (W3 (wa_s1 w + k + i) ltac:(unfold PM_RF_TOP, PM_RF_LO in *; lia))).
    -
      eapply (bslots_mem_denot H w (EVar WV_FF) (wa_ff w) m bvmap_empty ftbl E LOG fks (xa_fslots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) Hf (ev_ff H w E OK HE) HE).
      + intros k Hk. apply Forall_forall. intros se Hse Hne. specialize (Hfkr k Hk).
        pose proof (sym_inside_num H w E se OK HE (proj1 (forallb_forall _ _) Hown se Hse)) as HS.
        destruct HS as [(_ & A1 & A2)|[(EB & _)|[(_ & A1 & A2)|(_ & A1 & A2)]]]; [right | rewrite Hne in EB; discriminate | |].
        * unfold PM_RF_LO in *. lia.
        * rewrite G13 in A1, A2. pose proof G6 as G6'. rewrite G13 in G6'. unfold PM_NSH in *. lia.
        * unfold O_WIDX, O_FLAGS in *. destruct FFP as [D|D]; [right | left]; lia.
      + intros k Hk. specialize (Hfkr k Hk). lia.
      + intros k Hk. assert (Hk' : In k (map fst ftbl ++ fks)) by (apply in_app_iff; right; exact Hk).
        specialize (Hfkr k Hk'). pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (W1 & W2 & W3).
        change (fsz PM_FCLASS) with 16384 in *.
        split; [lia|]. split; [lia|]. intros i Hi. rewrite <- Z.add_assoc. exact (W3 (k + i) ltac:(lia)).
    -
      apply HFA; [unfold O_WIDX, O_FLAGS; lia | unfold O_WIDX, O_FLAGS; lia | exact S1 | exact (xa_widx _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
    - apply HFA; [unfold O_ICOUNT, O_WIDX; lia | unfold O_ICOUNT, O_FLAGS; lia | exact S2 | exact (xa_icount _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
    - apply HFA; [unfold O_ENDIAN, O_WIDX; lia | unfold O_ENDIAN, O_FLAGS; lia | exact S3 | exact (xa_endian _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
    - apply HFA; [unfold O_FLAGS, O_WIDX; lia | unfold O_FLAGS; lia | exact S4 | exact (xa_flags _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
    - rewrite <- Z.add_assoc.
      assert (K : fld ASEGS (mem_denot E m LOG) (wa_p w + (O_FLAGS + 1)) 1 (sval E LOG (EVar WV_P) (O_FLAGS + 1) 1 0)).
      { apply HFA; [unfold O_FLAGS, O_WIDX; lia | unfold O_FLAGS; lia | exact S5 |].
        rewrite Z.add_assoc. exact (xa_retry _ _ _ _ _ _ _ _ _ _ _ _ _ _ X). }
      rewrite Hr0 in K. exact K.
    - exact B1.
    - exact B2.
    - exact B3.
    - exact B4.
    - exact Bsp.
    - exact Bphi.
  Qed.
End AfterRun.

Definition PM_KN_FIX : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
    KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit SHBASE);
    KRange (EVar WV_P) 1 (2 ^ 47); KAlign (EVar WV_P) 16;
    KRange (EVar WV_FF) (AIMG_TOP + AFS_HDR) (2 ^ 47); KAlign (EVar WV_FF) 64;
    KRange (EVar WV_SP0) (0x7fff7f800000 + 32768) (2 ^ 47); KAlign (EVar WV_SP0) 16;
    KRange (EVar WV_S1) (0x7fff7f800000 - PM_RF_LO) (2 ^ 47); KAlign (EVar WV_S1) 32;
    KRange (EVar WV_N) 0 (2 ^ 24);
    KRange (EVar WV_WORDS) 0 (2 ^ 47);
    KWr (SA (EVar WV_S1) PM_RF_LO) (ELit (PM_RF_TOP - PM_RF_LO));
    KWr (SA (EVar WV_FF) 24) (ELit 16352);
    KWr (SA FSHB SHBASE) (ELit PM_NSH);
    KDisj (SA FSHB SHBASE) (ELit PM_NSH) (SA (EVar WV_P) 0) (ELit 288);
    KDisj (SA FSHB SHBASE) (ELit PM_NSH) (SA (EVar WV_S1) PM_RF_LO) (ELit (832 - PM_RF_LO));
    KDisj (SA FSHB SHBASE) (ELit PM_NSH) (SA (EVar WV_FF) 0) (ELit 16384);
    KDisj (SA FSHB SHBASE) (ELit PM_NSH) (SA (EVar WV_CONS) 0) (ELit 48);
    KDisj (SA (EVar WV_P) 0) (ELit 288) (SA (EVar WV_S1) PM_RF_LO) (ELit (832 - PM_RF_LO));
    KDisj (SA (EVar WV_CONS) 0) (ELit 48) (SA (EVar WV_S1) PM_RF_LO) (ELit (832 - PM_RF_LO));
    KDisj (SA (EVar WV_P) 0) (ELit 288) (SA (EVar WV_FF) 0) (ELit 16384);
    KDisj (SA (EVar WV_CONS) 0) (ELit 48) (SA (EVar WV_FF) 0) (ELit 16384);
    KDisj (SA (EVar WV_FF) 0) (ELit 16384) (SA (EVar WV_S1) PM_RF_LO) (ELit (832 - PM_RF_LO));
    KWord (SA (EVar WV_P) 8) 8 (EVar WV_CONS);
    KWord (SA (EVar WV_P) 16) 8 (EVar WV_USER);
    KWord (SA (EVar WV_P) 24) 8 (ELit 0);
    KWord (SA (EVar WV_P) 32) 8 (ELit 0);
    KWord (SA (EVar WV_P) 48) 8 (EVar WV_WORDS);
    KWord (SA (EVar WV_P) 56) 8 (EVar WV_N);
    KWord (SA (EVar WV_P) 64) 8 (EVar WV_DIAG);
    KWord (SA (EVar WV_CONS) 32) 8 (ELit 0);
    KWr (SA (EVar WV_P) 0) (ELit 288) ].

Definition slot_kn (tbl : list (Z * expr)) : list kentry :=
  map (fun ke => KWord (SA (EVar WV_S1) (fst ke)) 8 (snd ke)) tbl.

Definition fslot_kn (tbl : list (Z * expr)) : list kentry :=
  map (fun ke => KWord (SA (EVar WV_FF) (fst ke)) 8 (snd ke)) tbl.

Definition pm_kn_base (tbl ftbl : list (Z * expr)) : list kentry := PM_KN_FIX ++ slot_kn tbl ++ fslot_kn ftbl.

Definition tbl_closed (tbl : list (Z * expr)) : bool := forallb (fun ke => wclosed (snd ke)) tbl.

Lemma kword_of_fld : forall E m a (k : nat) v (sa : saddr) (e : expr),
  fld ASEGS m a k v -> (1 <= k <= 8)%nat -> estart E sa = a -> 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  edenot E e = Z_to_bv 64 v -> kentry_ok ASEGS E m (KWord sa k e).
Proof.
  intros E m a k v sa e HF Hk Hs Ha Hak He. cbn [kentry_ok]. split; [lia|]. split.
  - unfold SymExec3Sound.SX2S.flat. rewrite Hs. lia.
  - assert (HA : adenot E sa = Z_to_bv 64 a).
    { unfold adenot, v_addi. unfold estart in Hs. rewrite <- Hs. reflexivity. }
    rewrite HA, He. exact HF.
Qed.

Lemma elit_u : forall E z, 0 <= z < 2 ^ 64 -> bv_unsigned (edenot E (ELit z)) = z.
Proof. intros E z Hz. cbn [edenot]. apply u64_of_Z. exact Hz. Qed.

Section Know.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma ev_wv : forall (w : pmwA H) E (n : N) (k : nat) (z : Z), env_world H w E -> n = (32 + N.of_nat k)%N -> (k < 9)%nat ->
    nth k (wenv_vals w) (Z_to_bv 64 0) = Z_to_bv 64 z -> edenot E (EVar n) = Z_to_bv 64 z.
  Proof.
    intros w E n k z HE -> Hk Hn. cbn [edenot]. rewrite HE by (unfold WV_LAST; lia).
    rewrite Eseed_world by lia. replace (N.to_nat (32 + N.of_nat k) - 32)%nat with k by lia. exact Hn.
  Qed.

  Lemma pm_kn_base_ok : forall w s LB LBs m mo c ins tbl ftbl TB spal E,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E ->
    tbl_closed tbl = true -> keys_ok (map fst tbl) = true ->
    tbl_closed ftbl = true -> fkeys_ok (map fst ftbl) = true ->
    know_ok ASEGS E m (pm_kn_base tbl ftbl).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E OK X HE Hc Hk Hfc Hfk.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_papp H w OK) as (P1 & P2 & P3).
    pose proof (wk_capp H w OK) as (C1 & C2 & C3).
    pose proof (wk_stack H w OK) as (S1a & S2 & S3 & S4 & S5 & S6).
    pose proof (wk_n H w OK) as N1.
    assert (P4 : wa_p w + PARSER_SIZE <= 2 ^ 47).
    { destruct P1 as [(Q1 & Q2)|(Q1 & Q2)]; unfold aapp_lo, aapp_hi, ALOWSH_LO, AAPP_HI in *; lia. }
    assert (C4 : wa_cons w + 48 <= 2 ^ 47).
    { destruct C1 as [(Q1 & Q2)|(Q1 & Q2)]; unfold aapp_lo, aapp_hi, ALOWSH_LO, AAPP_HI in *; lia. }
    assert (P5 : wa_p w + PARSER_SIZE <= aceil).
    { destruct P1 as [(Q1 & Q2)|(Q1 & Q2)]; [unfold ALOWSH_LO in Q2; lia | exact Q2]. }
    assert (C5 : wa_cons w + 48 <= aceil).
    { destruct C1 as [(Q1 & Q2)|(Q1 & Q2)]; [unfold ALOWSH_LO in Q2; lia | exact Q2]. }
    pose proof (own_apart_obj3 H HH w (wa_p w) PARSER_SIZE OK (wk_pobj H w OK) P1 ltac:(lia) ltac:(unfold PARSER_SIZE; lia) P5) as [AP _].
    pose proof (own_apart_obj3 H HH w (wa_cons w) 48 OK (wk_cobj H w OK) C1 ltac:(lia) ltac:(lia) C5) as [AC _].
    assert (FSHI : own_ivl3 H w (sh (wa_ff w), sh (wa_ff w) + PM_NSH)) by (right; right; cbn; lia).
    pose proof (AP _ FSHI) as APf. pose proof (AC _ FSHI) as ACf. cbn [fst snd] in APf, ACf.
    assert (EP : edenot E (EVar WV_P) = Z_to_bv 64 (wa_p w)) by (apply (ev_wv w E _ 0 _ HE eq_refl); [lia | reflexivity]).
    assert (EF : edenot E (EVar WV_FF) = Z_to_bv 64 (wa_ff w)) by (apply (ev_wv w E _ 1 _ HE eq_refl); [lia | reflexivity]).
    assert (ES0 : edenot E (EVar WV_SP0) = Z_to_bv 64 (wa_sp0 w)) by (apply (ev_wv w E _ 2 _ HE eq_refl); [lia | reflexivity]).
    assert (ES1 : edenot E (EVar WV_S1) = Z_to_bv 64 (wa_s1 w)) by (apply (ev_wv w E _ 3 _ HE eq_refl); [lia | reflexivity]).
    assert (EW : edenot E (EVar WV_WORDS) = Z_to_bv 64 (wa_words w)) by (apply (ev_wv w E _ 4 _ HE eq_refl); [lia | reflexivity]).
    assert (EN : edenot E (EVar WV_N) = Z_to_bv 64 (wa_n w)) by (apply (ev_wv w E _ 5 _ HE eq_refl); [lia | reflexivity]).
    assert (EC : edenot E (EVar WV_CONS) = Z_to_bv 64 (wa_cons w)) by (apply (ev_wv w E _ 6 _ HE eq_refl); [lia | reflexivity]).
    assert (EU : edenot E (EVar WV_USER) = Z_to_bv 64 (wa_user w)) by (apply (ev_wv w E _ 7 _ HE eq_refl); [lia | reflexivity]).
    assert (ED : edenot E (EVar WV_DIAG) = Z_to_bv 64 (wa_diag w)) by (apply (ev_wv w E _ 8 _ HE eq_refl); [lia | reflexivity]).
    assert (UP : bv_unsigned (edenot E (EVar WV_P)) = wa_p w) by (rewrite EP; apply u64_of_Z; unfold PARSER_SIZE in *; lia).
    assert (UF : bv_unsigned (edenot E (EVar WV_FF)) = wa_ff w) by (rewrite EF; apply u64_of_Z; lia).
    assert (US0 : bv_unsigned (edenot E (EVar WV_SP0)) = wa_sp0 w) by (rewrite ES0; apply u64_of_Z; lia).
    assert (US1 : bv_unsigned (edenot E (EVar WV_S1)) = wa_s1 w) by (rewrite ES1; apply u64_of_Z; lia).
    assert (UN : bv_unsigned (edenot E (EVar WV_N)) = wa_n w) by (rewrite EN; apply u64_of_Z; lia).
    assert (UW : bv_unsigned (edenot E (EVar WV_WORDS)) = wa_words w).
    { rewrite EW; apply u64_of_Z. destruct (wk_words H w OK) as [[E0 _]|(pw & k & _ & Rg & W0 & _ & Whi & _ & _)]; lia. }
    assert (UC : bv_unsigned (edenot E (EVar WV_CONS)) = wa_cons w) by (rewrite EC; apply u64_of_Z; lia).
    assert (UFS : bv_unsigned (edenot E FSHB) = wa_ff w / 8) by (exact (ev_fshb H w E OK HE)).
    pose proof (ACONST_shbase m (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)) as [CG CS].
    pose proof (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (_ & _ & _ & FSW).
    unfold pm_fsh in FSW. rewrite length_map, pm_fsh_len in FSW. change (Z.of_nat 1448) with 1448 in FSW.
    unfold pm_kn_base. apply Forall_app. split.
    - unfold PM_KN_FIX.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m AGOT_SHBASE _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; unfold AGOT_SHBASE; lia | cbn; unfold AGOT_SHBASE; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m ASHBASE_CELL _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; unfold ASHBASE_CELL; lia | cbn; unfold ASHBASE_CELL; lia | reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite UP. unfold PARSER_SIZE in *. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite UP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite UF. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite UF. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite US0. unfold APM_STACK in S2. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite US0. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite US1. unfold PM_RF_LO. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite US1. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite UN. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. rewrite UW. destruct (wk_words H w OK) as [[E0 _]|(pw & k & _ & Rg & W0 & _ & Whi & _ & _)]; lia. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | | | ]; unfold estart, elenZ; cbn [a_base a_off];
          rewrite ?US1, ?elit_u by (unfold PM_RF_TOP, PM_RF_LO; lia); unfold PM_RF_TOP, PM_RF_LO; lia. }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | | | ]; unfold estart, elenZ; cbn [a_base a_off];
          rewrite ?UF, ?elit_u by lia; change (fsz PM_FCLASS) with 16384; lia. }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact FSW | | | ]; unfold estart, elenZ; cbn [a_base a_off];
          rewrite ?UFS, ?elit_u by (unfold PM_NSH; lia); rewrite ?G13; unfold PM_NSH; lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite UFS, UP, !elit_u by (unfold PM_NSH; lia).
        rewrite G13 in APf. unfold PM_NSH, PARSER_SIZE in *. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite UFS, US1, !elit_u by (unfold PM_NSH; lia).
        rewrite G13 in G5. unfold PM_NSH, PM_RF_LO in *. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite UFS, UF, !elit_u by (unfold PM_NSH; lia).
        rewrite G13 in G6. unfold PM_NSH in *. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite UFS, UC, !elit_u by (unfold PM_NSH; lia).
        rewrite G13 in ACf. unfold PM_NSH in *. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite UP, US1, !elit_u by (unfold PM_RF_LO; lia).
        unfold PM_RF_LO, PARSER_SIZE in *. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite UC, US1, !elit_u by (unfold PM_RF_LO; lia).
        unfold PM_RF_LO in *. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite UP, UF, !elit_u by lia.
        assert (FFI : own_ivl3 H w (wa_ff w + 24, wa_ff w + 16376)) by (right; left; cbn; change (fsz PM_FCLASS) with 16384; lia).
        pose proof (AP _ FFI) as APff. cbn [fst snd] in APff.
        pose proof (fsobj_windows H HH _ _ _ _ _ _ (wa_m0 w) (wk_rfs0 H w OK) (wk_pobj H w OK) (wk_fresh H w OK) ltac:(lia) ltac:(unfold PARSER_SIZE; lia) ltac:(unfold AAPP_HI, PARSER_SIZE in *; lia)) as (D1 & _).
        change (fsz PM_FCLASS) with 16384 in D1. unfold PARSER_SIZE in *. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite UC, UF, !elit_u by lia.
        pose proof (fsobj_windows H HH _ _ _ _ _ _ (wa_m0 w) (wk_rfs0 H w OK) (wk_cobj H w OK) (wk_fresh H w OK) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia)) as (D1 & _).
        change (fsz PM_FCLASS) with 16384 in D1. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite UF, US1, !elit_u by (unfold PM_RF_LO; lia).
        unfold PM_RF_LO in *. lia. }
      apply Forall_cons.
      { eapply kword_of_fld; [exact (xa_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | unfold estart; cbn [a_base a_off]; rewrite UP; lia | lia | cbn; unfold PARSER_SIZE in *; lia | exact EC]. }
      apply Forall_cons.
      { eapply kword_of_fld; [exact (xa_user _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | unfold estart; cbn [a_base a_off]; rewrite UP; lia | lia | cbn; unfold PARSER_SIZE in *; lia | exact EU]. }
      apply Forall_cons.
      { eapply kword_of_fld; [exact (xa_hdrfn _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | unfold estart; cbn [a_base a_off]; rewrite UP; lia | lia | cbn; unfold PARSER_SIZE in *; lia | reflexivity]. }
      apply Forall_cons.
      { eapply kword_of_fld; [exact (xa_insfn _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | unfold estart; cbn [a_base a_off]; rewrite UP; lia | lia | cbn; unfold PARSER_SIZE in *; lia | reflexivity]. }
      apply Forall_cons.
      { eapply kword_of_fld; [exact (xa_words _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | unfold estart; cbn [a_base a_off]; rewrite UP; unfold O_WORDS; lia | unfold O_WORDS; lia | cbn; unfold O_WORDS, PARSER_SIZE in *; lia | exact EW]. }
      apply Forall_cons.
      { eapply kword_of_fld; [exact (xa_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | unfold estart; cbn [a_base a_off]; rewrite UP; unfold O_N; lia | unfold O_N; lia | cbn; unfold O_N, PARSER_SIZE in *; lia | exact EN]. }
      apply Forall_cons.
      { eapply kword_of_fld; [exact (xa_diag _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | unfold estart; cbn [a_base a_off]; rewrite UP; unfold O_DIAG; lia | unfold O_DIAG; lia | cbn; unfold O_DIAG, PARSER_SIZE in *; lia | exact ED]. }
      apply Forall_cons.
      { eapply kword_of_fld; [exact (xa_consf _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | unfold estart; cbn [a_base a_off]; rewrite UC; lia | lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { assert (WP : wr_at asegs m (wa_p w) 288).
        { split; [lia|]. split; [unfold PARSER_SIZE in *; lia|]. intros i Hi. unfold wview.
          pose proof (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X i ltac:(unfold PARSER_SIZE; lia)) as D.
          unfold wa. destruct (m (Z_to_bv 64 (wa_p w + i))); [discriminate | contradiction]. }
        eapply kwr_of_wr_at; [exact WP | | | ]; unfold estart, elenZ; cbn [a_base a_off];
          rewrite ?UP, ?elit_u by lia; unfold PARSER_SIZE in *; lia. }
      apply Forall_nil.
    - apply Forall_app. split.
      2:{ unfold fslot_kn. apply Forall_map. pose proof (xa_fslots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as SL. unfold fslots_ok in SL.
      apply Forall_forall. intros [k e] Hin. pose proof (proj1 (Forall_forall _ _) SL (k, e) Hin) as SLk. cbn [fst snd] in *.
      pose proof (proj1 (forallb_forall _ _) Hfc (k, e) Hin) as Hce. cbn [snd] in Hce.
      assert (Hkk : In k (map fst ftbl)) by (apply (in_map fst ftbl (k, e)); exact Hin).
      pose proof (proj1 (forallb_forall _ _) Hfk k Hkk) as K. apply andb_true_iff in K as [K1 K2].
      apply Z.leb_le in K1. apply Z.leb_le in K2.
      eapply (kword_of_rw_cells asegs E m (wa_ff w + k) _ 0%nat (C8 _)); [exact SLk | reflexivity | reflexivity | lia | | lia | cbn; lia |].
      + unfold estart. cbn [a_base a_off]. rewrite UF. lia.
      + cbn [cbytes]. unfold le8. f_equal. symmetry. apply edenot_wclosed; [exact Hce|]. intros n Hn. apply HE. unfold WV_LAST. lia. }
      unfold slot_kn. apply Forall_map. pose proof (xa_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as SL. unfold slots_ok in SL.
      apply Forall_forall. intros [k e] Hin. pose proof (proj1 (Forall_forall _ _) SL (k, e) Hin) as SLk. cbn [fst snd] in *.
      pose proof (proj1 (forallb_forall _ _) Hc (k, e) Hin) as Hce. cbn [snd] in Hce.
      assert (Hkk : In k (map fst tbl)) by (apply (in_map fst tbl (k, e)); exact Hin).
      pose proof (proj1 (forallb_forall _ _) Hk k Hkk) as K. apply andb_true_iff in K as [K1 K2].
      apply Z.leb_le in K1. apply Z.leb_le in K2.
      eapply (kword_of_rw_cells asegs E m (wa_s1 w + k) _ 0%nat (C8 _)); [exact SLk | reflexivity | reflexivity | lia | | unfold PM_RF_LO in *; lia | cbn; unfold PM_RF_TOP in *; lia |].
      + unfold estart. cbn [a_base a_off]. rewrite US1. lia.
      + cbn [cbytes]. unfold le8. f_equal. symmetry. apply edenot_wclosed; [exact Hce|]. intros n Hn. apply HE. unfold WV_LAST. lia.
  Qed.
End Know.

Section RunL.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma pmxa_mpres : forall w s LB LBs m mo mo' c ins tbl ftbl TB spal,
    PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> as_MPRES H mo mo' -> PMXAT H LINV w s LB LBs m mo' c ins tbl ftbl TB spal.
  Proof.
    intros w s LB LBs m mo mo' c ins tbl ftbl TB spal X MP. destruct X. constructor; try assumption.
    eapply (ah_mpres_trans H HH); eassumption.
  Qed.

  Lemma pm_runS : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (pc : Z) RT X kn fuel stops scr nx SSr scs scr'
                        ins' ks fks tbl' ftbl' RT' c' (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) ->
    as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) -> rfull R ->
    regs_tblX w X R RT -> tbl_okX (xbound X) RT = true ->
    sym_exec asegs fuel true stops scr (SS pc (srs sr_id RT) [] kn nx) [] = (SSr, scs, scr') ->
    know_ok asegs (Eseed R (wenv_vals w ++ X)) m kn ->
    scs_denot asegs m (Eseed R (wenv_vals w ++ X)) scs ->
    forallb (sym_inside PM_OWN) (s_log SSr) = true ->
    lbytes (s_log SSr) FSHB SHBASE (fsh_pat PM_OBJS PM_NSH ins) = Some (fsh_pat PM_OBJS PM_NSH ins') ->
    keys_ok (map fst tbl ++ ks) = true -> fkeys_ok (map fst ftbl ++ fks) = true ->
    upd_slots (s_log SSr) (EVar WV_S1) tbl ++ add_slots (s_log SSr) (EVar WV_S1) ks = tbl' ->
    upd_slots (s_log SSr) (EVar WV_FF) ftbl ++ add_slots (s_log SSr) (EVar WV_FF) fks = ftbl' ->
    sr_tbl_checkX (xbound X) (s_regs SSr) RT' = true ->
    scal_ok (s_log SSr) = true -> sval (Eseed R (wenv_vals w ++ X)) (s_log SSr) (EVar WV_P) (O_FLAGS + 1) 1 0 = 0 ->
    scal_after (Eseed R (wenv_vals w ++ X)) (s_log SSr) c = c' ->
    c_widx c <= c_widx c' <= wa_n w   -> 0 <= c_icount c' <= c_widx c' -> 0 <= c_endian c' < 2 ^ 32 -> (c_reqconv c' = 0 \/ c_reqconv c' = 1) ->
    (forall msF1 mo1 R1,
       as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 (s_pc SSr)) fc None (mem_denot (Eseed R (wenv_vals w ++ X)) m (s_log SSr)) (seg_rom asegs) ->
       rfull R1 ->
       PMXAT H LINV w s LB LBs (mem_denot (Eseed R (wenv_vals w ++ X)) m (s_log SSr)) mo1 c' ins' tbl' ftbl' TB spal ->
       regs_tblX w X R1 RT' ->
       regs_ok (Eseed R (wenv_vals w ++ X)) (s_regs SSr) R1 ->
       log_flat (Eseed R (wenv_vals w ++ X)) (s_log SSr) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc pc RT X kn fuel stops scr nx SSr scs scr' ins' ks fks tbl' ftbl' RT' c' Q
           OK X0 KR VIS RF HT Hok Hex HK Hsc Hown Hby Hks Hfks Ht1 Ht2 Htb Hso Hr0 Hc' B1 B2 B3 B4 K.
    subst tbl' ftbl' c'.
    pose proof (regs_ok_of_tbl w R RT X _ HT Hok) as HR.
    destruct (@SymRun3.run_sound (PropExec.mkFP F fc) asegs fuel stops scr pc (srs sr_id RT) kn nx SSr scs scr'
                (Eseed R (wenv_vals w ++ X)) m (seg_rom asegs) R Hex HR HK Hsc) as (R' & HR' & Hlf & Hms).
    rewrite !mkst_MS in Hms.
    pose proof (msteps_full asegs _ _ Hms RF) as RF'. cbn [ms_regs] in RF'.
    pose proof (msteps_mem_inv asegs _ _ Hms (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)) as MI'. cbn [ms_mem] in MI'.
    eapply (sr_blk H HH); [exact KR | exact VIS | exact RF | exact Hms |].
    intros msF' mo' KR' MP' VIS'.
    rewrite <- (rfull_eq R' RF') in VIS'.
    eapply K; [exact KR' | exact VIS' | exact RF' | | eapply regs_tbl_of_run; [exact HR' | exact Htb] | exact HR' | exact Hlf].
    apply pmxa_mpres with mo; [| exact MP'].
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (Bs1 & _).
    eapply (pm_after_run H HH LINV LINV_frame); [exact OK | exact X0 | apply env_world_seed | exact Hlf | exact MI' | exact Hown | exact Hby | exact Hks | exact Hfks
                                                 | exact Hso | exact Hr0 | lia | exact B2 | exact B3 | exact B4
                                                 | exact (proj2 (proj2 (proj2 (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)))) | ].
    pose proof (pm_progz_mono _ _ (proj1 B1)) as PMono. unfold pm_phi, pm_prog.
    replace (c_blocks (scal_after (Eseed R (wenv_vals w ++ X)) (s_log SSr) c)) with (c_blocks c) by reflexivity. lia.
  Qed.

  Lemma pm_runSX : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (pc : Z) RT X kn fuel stops scr nx SSr scs scr'
                        ins' ks fks tbl' ftbl' RT' c' (spal' : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) ->
    as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) -> rfull R ->
    regs_tblX w X R RT -> tbl_okX (xbound X) RT = true ->
    sym_exec asegs fuel true stops scr (SS pc (srs sr_id RT) [] kn nx) [] = (SSr, scs, scr') ->
    know_ok asegs (Eseed R (wenv_vals w ++ X)) m kn ->
    scs_denot asegs m (Eseed R (wenv_vals w ++ X)) scs ->
    forallb (sym_inside PM_OWN) (s_log SSr) = true ->
    lbytes (s_log SSr) FSHB SHBASE (fsh_pat PM_OBJS PM_NSH ins) = Some (fsh_pat PM_OBJS PM_NSH ins') ->
    keys_ok (map fst tbl ++ ks) = true -> fkeys_ok (map fst ftbl ++ fks) = true ->
    upd_slots (s_log SSr) (EVar WV_S1) tbl ++ add_slots (s_log SSr) (EVar WV_S1) ks = tbl' ->
    upd_slots (s_log SSr) (EVar WV_FF) ftbl ++ add_slots (s_log SSr) (EVar WV_FF) fks = ftbl' ->
    sr_tbl_checkX (xbound X) (s_regs SSr) RT' = true ->
    scal_ok (s_log SSr) = true -> sval (Eseed R (wenv_vals w ++ X)) (s_log SSr) (EVar WV_P) (O_FLAGS + 1) 1 0 = 0 ->
    scal_after (Eseed R (wenv_vals w ++ X)) (s_log SSr) c = c' ->
    0 <= c_widx c' <= wa_n w -> 0 <= c_icount c' <= c_widx c' -> 0 <= c_endian c' < 2 ^ 32 -> (c_reqconv c' = 0 \/ c_reqconv c' = 1) ->
    0 <= spal' <= PM_RESERVE -> pm_phi c + spal <= pm_phi c' + spal' ->
    (forall msF1 mo1 R1,
       as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 (s_pc SSr)) fc None (mem_denot (Eseed R (wenv_vals w ++ X)) m (s_log SSr)) (seg_rom asegs) ->
       rfull R1 ->
       PMXAT H LINV w s LB LBs (mem_denot (Eseed R (wenv_vals w ++ X)) m (s_log SSr)) mo1 c' ins' tbl' ftbl' TB spal' ->
       regs_tblX w X R1 RT' ->
       regs_ok (Eseed R (wenv_vals w ++ X)) (s_regs SSr) R1 ->
       log_flat (Eseed R (wenv_vals w ++ X)) (s_log SSr) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc pc RT X kn fuel stops scr nx SSr scs scr' ins' ks fks tbl' ftbl' RT' c' spal' Q
           OK X0 KR VIS RF HT Hok Hex HK Hsc Hown Hby Hks Hfks Ht1 Ht2 Htb Hso Hr0 Hc' B1 B2 B3 B4 Bsp Bphi K.
    subst tbl' ftbl' c'.
    pose proof (regs_ok_of_tbl w R RT X _ HT Hok) as HR.
    destruct (@SymRun3.run_sound (PropExec.mkFP F fc) asegs fuel stops scr pc (srs sr_id RT) kn nx SSr scs scr'
                (Eseed R (wenv_vals w ++ X)) m (seg_rom asegs) R Hex HR HK Hsc) as (R' & HR' & Hlf & Hms).
    rewrite !mkst_MS in Hms.
    pose proof (msteps_full asegs _ _ Hms RF) as RF'. cbn [ms_regs] in RF'.
    pose proof (msteps_mem_inv asegs _ _ Hms (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)) as MI'. cbn [ms_mem] in MI'.
    eapply (sr_blk H HH); [exact KR | exact VIS | exact RF | exact Hms |].
    intros msF' mo' KR' MP' VIS'.
    rewrite <- (rfull_eq R' RF') in VIS'.
    eapply K; [exact KR' | exact VIS' | exact RF' | | eapply regs_tbl_of_run; [exact HR' | exact Htb] | exact HR' | exact Hlf].
    apply pmxa_mpres with mo; [| exact MP'].
    eapply (pm_after_run H HH LINV LINV_frame); [exact OK | exact X0 | apply env_world_seed | exact Hlf | exact MI' | exact Hown | exact Hby | exact Hks | exact Hfks
                                                 | exact Hso | exact Hr0 | exact B1 | exact B2 | exact B3 | exact B4 | exact Bsp | exact Bphi].
  Qed.

  Lemma pm_run : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (pc : Z) RT X kn fuel stops scr nx SSr scs scr'
                        ins' ks fks tbl' ftbl' RT' (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) ->
    as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) -> rfull R ->
    regs_tblX w X R RT -> tbl_okX (xbound X) RT = true ->
    sym_exec asegs fuel true stops scr (SS pc (srs sr_id RT) [] kn nx) [] = (SSr, scs, scr') ->
    know_ok asegs (Eseed R (wenv_vals w ++ X)) m kn ->
    scs_denot asegs m (Eseed R (wenv_vals w ++ X)) scs ->
    forallb (sym_inside PM_OWN) (s_log SSr) = true ->
    lbytes (s_log SSr) FSHB SHBASE (fsh_pat PM_OBJS PM_NSH ins) = Some (fsh_pat PM_OBJS PM_NSH ins') ->
    keys_ok (map fst tbl ++ ks) = true -> fkeys_ok (map fst ftbl ++ fks) = true ->
    upd_slots (s_log SSr) (EVar WV_S1) tbl ++ add_slots (s_log SSr) (EVar WV_S1) ks = tbl' ->
    upd_slots (s_log SSr) (EVar WV_FF) ftbl ++ add_slots (s_log SSr) (EVar WV_FF) fks = ftbl' ->
    sr_tbl_checkX (xbound X) (s_regs SSr) RT' = true ->
    scal_none (s_log SSr) = true ->
    (forall msF1 mo1 R1,
       as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 (s_pc SSr)) fc None (mem_denot (Eseed R (wenv_vals w ++ X)) m (s_log SSr)) (seg_rom asegs) ->
       rfull R1 ->
       PMXAT H LINV w s LB LBs (mem_denot (Eseed R (wenv_vals w ++ X)) m (s_log SSr)) mo1 c ins' tbl' ftbl' TB spal ->
       regs_tblX w X R1 RT' ->
       regs_ok (Eseed R (wenv_vals w ++ X)) (s_regs SSr) R1 ->
       log_flat (Eseed R (wenv_vals w ++ X)) (s_log SSr) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc pc RT X kn fuel stops scr nx SSr scs scr' ins' ks fks tbl' ftbl' RT' Q
           OK X0 KR VIS RF HT Hok Hex HK Hsc Hown Hby Hks Hfks Ht1 Ht2 Htb Hsn K.
    destruct (scal_none_facts (Eseed R (wenv_vals w ++ X)) (s_log SSr) c Hsn) as (Hso & Hc & Hr0).
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    eapply (pm_runS w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc pc RT X kn fuel stops scr nx SSr scs scr' ins' ks fks tbl' ftbl' RT' c Q
              OK X0 KR VIS RF HT Hok Hex HK Hsc Hown Hby Hks Hfks Ht1 Ht2 Htb Hso Hr0 Hc (conj (Z.le_refl _) (proj2 B1)) B2 B3 B4 K).
  Qed.
End RunL.

Lemma shk_of_fsh : forall m ff ins (j : nat) v,
  SHAD m ff (pm_fsh ins) -> (j < 1448)%nat -> nth j (fsh_pat PM_OBJS PM_NSH ins) 0 = v -> 0 <= v < 256 ->
  shk m (ff + 8 * Z.of_nat j) v.
Proof.
  intros m ff ins j v (S0 & S8 & [B _]) Hj Hv Hvr. unfold shk.
  destruct B as (B0 & B1 & B2).
  assert (Hl : (j < length (pm_fsh ins))%nat) by (unfold pm_fsh; rewrite length_map, pm_fsh_len; exact Hj).
  pose proof (B2 j Hl) as Hm. unfold pm_fsh in Hm. rewrite nth_error_map in Hm.
  rewrite (nth_error_nth' _ 0) in Hm by (rewrite pm_fsh_len; exact Hj). cbn [option_map] in Hm. rewrite Hv in Hm.
  replace ((ff + 8 * Z.of_nat j) / 8 + SHBASE) with (sh ff + Z.of_nat j).
  2:{ unfold sh, ASHADOW_BASE, SHBASE. replace (ff + 8 * Z.of_nat j) with (Z.of_nat j * 8 + ff) by lia.
      rewrite Z.div_add_l by lia. lia. }
  exact (rdn1_of_mrd ASEGS m _ _ Hm).
Qed.

Definition fsh_at (ins : list nat) (k : Z) : Z := nth (Z.to_nat (k / 8)) (fsh_pat PM_OBJS PM_NSH ins) 0.

Definition ff_off (a : saddr) : option Z :=
  match a_base a with
  | EAlu ALU_SRL (EVar 33) (ELit 3) => Some 0
  | EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit k)) (ELit 3) => Some k
  | _ => None
  end.

Definition fix_of3 (ins : list nat) (s : sidecond) : option kentry :=
  match s with
  | SCReadBase a 1 _ _ =>
      if is_shadow_addr a then
        match ff_off a with
        | Some k => if ((0 <=? k) && (k <? 11584) && (k mod 8 =? 0))%bool then Some (KWord a 1 (ELit (fsh_at ins k))) else None
        | None => Some (KWord a 1 (ELit 0))
        end
      else None
  | SCDisj a1 n1 a2 n2 =>
      if (is_shadow_addr a1 && expr_eqb (a_base a2) FSHB)%bool then
        match ff_off a1 with None => Some (KDisj a1 (ELit 1) (SA FSHB SHBASE) (ELit PM_NSH)) | Some _ => None end
      else if (is_shadow_addr a2 && expr_eqb (a_base a1) FSHB)%bool then
        match ff_off a2 with None => Some (KDisj a2 (ELit 1) (SA FSHB SHBASE) (ELit PM_NSH)) | Some _ => None end
      else if (is_shadow_addr a1 && expr_eqb (a_base a2) (EVar WV_FF))%bool then
        Some (KDisj a1 (ELit 1) (SA (EVar WV_FF) 0) (ELit 16384))
      else if (is_shadow_addr a2 && expr_eqb (a_base a1) (EVar WV_FF))%bool then
        Some (KDisj a2 (ELit 1) (SA (EVar WV_FF) 0) (ELit 16384))
      else if (is_shadow_addr a1 && expr_eqb (a_base a2) (EVar WV_P))%bool then
        Some (KDisj a1 (ELit 1) (SA (EVar WV_P) 0) (ELit 288))
      else if (is_shadow_addr a2 && expr_eqb (a_base a1) (EVar WV_P))%bool then
        Some (KDisj a2 (ELit 1) (SA (EVar WV_P) 0) (ELit 288))
      else if (is_shadow_addr a1 && expr_eqb (a_base a2) (EVar WV_S1))%bool then
        Some (KDisj a1 (ELit 1) (SA (EVar WV_S1) PM_RF_LO) (ELit (832 - PM_RF_LO)))
      else if (is_shadow_addr a2 && expr_eqb (a_base a1) (EVar WV_S1))%bool then
        Some (KDisj a2 (ELit 1) (SA (EVar WV_S1) PM_RF_LO) (ELit (832 - PM_RF_LO)))
      else None
  | _ => None
  end.

Fixpoint add_fixes3 (ins : list nat) (scs : list sidecond) (acc : list kentry) : list kentry :=
  match scs with
  | [] => acc
  | s :: t =>
      match fix_of3 ins s with
      | Some K => if existsb (kentry_eqb K) acc then add_fixes3 ins t acc else add_fixes3 ins t (acc ++ [K])
      | None => add_fixes3 ins t acc
      end
  end.

Fixpoint kn_fix3 (fuel : nat) (xfuel : nat) (ins : list nat) (stops : list Z) (scr : scripts) (pc : Z) (sr : list expr)
         (kn : list kentry) (nx : N) : list kentry :=
  match fuel with
  | O => kn
  | Datatypes.S f =>
      let '(_, scs, _) := sym_exec ASEGS xfuel true stops scr (SS pc sr [] kn nx) [] in
      let kn' := add_fixes3 ins scs kn in
      if Nat.eqb (length kn') (length kn) then kn else kn_fix3 f xfuel ins stops scr pc sr kn' nx
  end.

Lemma Forall_repeat_Z : forall (P : Z -> Prop) x n, P x -> Forall P (repeat x n).
Proof. intros P x n Hx. induction n; cbn; constructor; assumption. Qed.

Lemma fsh_objs_bytes : forall objs i ins pos, Forall (fun z => 0 <= z < 256) (fsh_objs objs i ins pos).
Proof.
  induction objs as [|[off sz] rest IH]; intros i ins pos; cbn [fsh_objs]; [constructor|].
  apply Forall_app. split; [apply Forall_repeat_Z; lia|]. apply Forall_app. split; [|apply IH].
  unfold gran_of. destruct (existsb (Nat.eqb i) ins).
  - apply Forall_app. split; [apply Forall_repeat_Z; lia|]. destruct (sz mod 8 =? 0); [constructor|].
    constructor; [pose proof (Z.mod_pos_bound sz 8 ltac:(lia)); lia | constructor].
  - apply Forall_repeat_Z; lia.
Qed.

Lemma fsh_pat_byte_range : forall ins j, 0 <= nth j (fsh_pat PM_OBJS PM_NSH ins) 0 < 256.
Proof.
  intros ins j. assert (F : Forall (fun z => 0 <= z < 256) (fsh_pat PM_OBJS PM_NSH ins)).
  { unfold fsh_pat. apply Forall_app. split; [apply Forall_repeat_Z; lia|]. apply Forall_app. split; [apply fsh_objs_bytes | apply Forall_repeat_Z; lia]. }
  destruct (Nat.lt_ge_cases j (length (fsh_pat PM_OBJS PM_NSH ins))) as [Hj|Hj].
  - exact (proj1 (Forall_forall _ _) F _ (nth_In _ 0 Hj)).
  - rewrite nth_overflow by exact Hj. lia.
Qed.
