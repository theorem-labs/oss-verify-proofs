(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core StreamSim.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutL5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SP.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
Definition CSV1 : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma csv_in : forall r : reg, In (bv_unsigned r) callee_saved_idx -> In (ridx r) CSV1.
Proof. intros r H. unfold ridx. unfold callee_saved_idx in H. cbn [In] in H. repeat (destruct H as [H|H]; [rewrite <- H; cbn; tauto|]). destruct H. Qed.

(* [comment removed for export] *)
Definition reg_eqb (a b : SGP.region) : bool :=
  let '(ab, alo, alen) := a in let '(bb, blo, blen) := b in (expr_eqb ab bb && Z.eqb alo blo && expr_eqb alen blen)%bool.
Lemma reg_eqb_eq : forall a b, reg_eqb a b = true -> a = b.
Proof.
  intros [[ab alo] alen] [[bb blo] blen] H. unfold reg_eqb in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1, H3. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Definition F_sub (F F0 : list SGP.region) : bool := forallb (fun r => existsb (reg_eqb r) F0) F.
Lemma F_sub_in : forall F F0 r, F_sub F F0 = true -> In r F -> In r F0.
Proof.
  intros F F0 r H Hin. unfold F_sub in H. rewrite forallb_forall in H. specialize (H _ Hin). apply existsb_exists in H as (r0 & Hr0 & He).
  apply reg_eqb_eq in He. subst. exact Hr0.
Qed.

Definition cut_chk (NF : nat) (F0 : list SGP.region) (c : CC.cutpoint) : bool := (Nat.leb NF (CC.cp_nx c) && F_sub (CC.cp_F c) F0)%bool.
Definition exit_chk (ENDS : list Z) (ps : SR.post_spec) : bool := (CL.ps_at ps ENDS && CL.ps_keeps ps CSV1)%bool.

(* [comment removed for export] *)
Lemma frame_but_of_outside : forall (E0 : env) (F0 : list SGP.region) (FR : list L5.range) (M M' : mem),
  (forall rb rlo rlen, In (rb, rlo, rlen) F0 ->
     elenZ E0 rlen <= 0 \/ exists w, In w FR /\ fst w <= estart E0 (SA rb rlo) /\ estart E0 (SA rb rlo) + elenZ E0 rlen <= fst w + snd w) ->
  (forall a : word, SGP.outside E0 F0 a -> M' a = M a) -> L5.frame_but FR M M'.
Proof.
  intros E0 F0 FR M M' HF H x Hout. apply H. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  destruct (HF rb rlo rlen Hin) as [Hz | (w & Hw & H1 & H2)].
  - destruct (Z_lt_dec (bv_unsigned x) (estart E0 (SA rb rlo))); [left; assumption | right; lia].
  - specialize (Hout w Hw). unfold L5.in_rng in Hout.
    destruct (Z_lt_dec (bv_unsigned x) (estart E0 (SA rb rlo))); [left; assumption | right; lia].
Qed.

(* [comment removed for export] *)
Lemma writable_static : forall segs (M : mem) A (N : nat), StreamSim.wseg_ok segs (Z_to_bv 64 A) N = true -> 0 <= A < 2 ^ 64 -> A + Z.of_nat N <= 2 ^ 64 -> L5.writable segs M A (Z.of_nat N).
Proof.
  intros segs M A N H HA HN d k Hd Hk. destruct k as [|k]; [reflexivity|].
  apply (store_ok_sub segs M (Z_to_bv 64 A) (Z_to_bv 64 (A + d)) N (S k)); [rewrite u64_of_Z by lia; lia | apply store_ok_wseg; exact H | rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; lia].
Qed.
Lemma kwr_of_writable : forall segs E (M : mem) a n A N, estart E a = A -> elenZ E n = N -> 0 <= A < 2 ^ 64 -> A + N <= 2 ^ 64 -> L5.writable segs M A N -> kentry_ok segs E M (KWr a n).
Proof.
  intros segs E M a n A N Ha Hn H0 H1 Hw. cbn [kentry_ok]. rewrite Ha, Hn.
  split; [unfold flat; rewrite Ha; pose proof (u64_range (edenot E n)) as Hr; unfold elenZ in Hn; rewrite Hn in Hr; lia|]. intros d m Hd Hm. apply Hw; assumption.
Qed.
(* [comment removed for export] *)
Lemma u64_u32_low : forall segs (M : mem) a w, L5.u64_at segs M a w -> L5.u32_at segs M a w.
Proof.
  intros segs M a w H. unfold L5.u64_at, L5.u32_at in *.
  assert (EQ : forall x n, rdn segs M x (S n) = match (match M x with Some b => Some b | None => seg_rom segs x end) with
                 | Some b => match rdn segs M (x + 1)%bv n with Some rest => Some (b :: rest) | None => None end | None => None end) by reflexivity.
  set (x0 := Z_to_bv 64 a) in *.
  rewrite (EQ x0 7%nat) in H. rewrite (EQ x0 3%nat).
  destruct (match M x0 with Some b => Some b | None => seg_rom segs x0 end) as [b0|]; [|discriminate].
  rewrite (EQ (x0 + 1)%bv 6%nat) in H. rewrite (EQ (x0 + 1)%bv 2%nat).
  destruct (match M (x0 + 1)%bv with Some b => Some b | None => seg_rom segs (x0 + 1)%bv end) as [b1|]; [|discriminate].
  rewrite (EQ (x0 + 1 + 1)%bv 5%nat) in H. rewrite (EQ (x0 + 1 + 1)%bv 1%nat).
  destruct (match M (x0 + 1 + 1)%bv with Some b => Some b | None => seg_rom segs (x0 + 1 + 1)%bv end) as [b2|]; [|discriminate].
  rewrite (EQ (x0 + 1 + 1 + 1)%bv 4%nat) in H. rewrite (EQ (x0 + 1 + 1 + 1)%bv 0%nat).
  destruct (match M (x0 + 1 + 1 + 1)%bv with Some b => Some b | None => seg_rom segs (x0 + 1 + 1 + 1)%bv end) as [b3|]; [|discriminate].
  destruct (rdn segs M (x0 + 1 + 1 + 1 + 1)%bv 4) as [rest|]; [|discriminate]. cbn [rdn].
  unfold word_to_le_bytes in *. cbn [Z_to_le_bytes] in *. injection H as H0 H1 H2 H3 _. subst. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma outside_excl : forall E0 F0 (x : word) rb rlo rlen, SGP.outside E0 F0 x -> In (rb, rlo, rlen) F0 ->
  ~ (estart E0 (SA rb rlo) <= bv_unsigned x < estart E0 (SA rb rlo) + elenZ E0 rlen).
Proof. intros E0 F0 x rb rlo rlen H Hin. unfold SGP.outside in H. rewrite Forall_forall in H. specialize (H _ Hin). cbv beta iota zeta in H. intros X. destruct H as [H|H]; lia. Qed.

(* [comment removed for export] *)
Lemma reg_is_sound : forall segs c ps E' R' M M' (x : reg) q e,
  CC.leaf_facts segs c ps E' R' M M' -> CL.ps_reg_is ps q e = true -> q = ridx x -> getr R' x = edenot E' e.
Proof. intros segs c ps E' R' M M' x q e HLF H ->. rewrite <- (CC.reg_of_ridx x) at 1. exact (CL.ps_reg_is_sound segs _ _ _ _ _ _ _ _ HLF H). Qed.

(* [comment removed for export] *)
Definition reg_of (ps : SR.post_spec) (q : nat) : option expr :=
  match find (fun ie : nat * expr => Nat.eqb (fst ie) q) (SR.ps_regs ps) with Some ie => Some (snd ie) | None => None end.
Lemma reg_of_sound : forall segs c ps E' R' M M' (x : reg) q e,
  CC.leaf_facts segs c ps E' R' M M' -> reg_of ps q = Some e -> q = ridx x -> getr R' x = edenot E' e.
Proof.
  intros segs c ps E' R' M M' x q e HLF H ->. unfold reg_of in H. destruct (find _ (SR.ps_regs ps)) as [[i e']|] eqn:Hf; [|discriminate]. injection H as <-.
  apply find_some in Hf as [Hin Hi]. cbn [fst] in Hi. apply Nat.eqb_eq in Hi. subst i.
  rewrite <- (CC.reg_of_ridx x) at 1. exact (CL.leaf_reg segs _ _ _ _ _ _ _ _ HLF Hin).
Qed.
Definition lit_in (o : option expr) (zs : list Z) : bool := match o with Some (ELit z) => existsb (Z.eqb z) zs | _ => false end.
Lemma lit_in_sound : forall o zs, lit_in o zs = true -> exists z, o = Some (ELit z) /\ In z zs.
Proof.
  intros [e|] zs H; [|discriminate]. destruct e; try discriminate. cbn [lit_in] in H. apply existsb_exists in H as (z0 & Hin & He). apply Z.eqb_eq in He. subst.
  eexists. split; [reflexivity | exact Hin].
Qed.

Section PureLeaf.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Variable FPI : FPState -> Prop.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps segs (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom segs)) -> FPI fx -> FPI fx'.
Variables (CPS : list CC.cutpoint) (TAGS : list (list CC.tag)) (NF : nat) (F0 : list SGP.region) (ENDS : list Z).
Hypothesis F0vars : forallb (SGP.region_vars_lt NF) F0 = true.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis plans : forall i c, nth_error CPS i = Some c -> CC.plan_sound segs c.
Hypothesis tags_ok : CC.tags_chk CPS TAGS NF = true.
Hypothesis cut_facts : CC.cps_all CPS (fun _ c => cut_chk NF F0 c) = true.
Hypothesis rets : forall pc, In pc ENDS -> CL.is_ret_at segs pc.

(* [comment removed for export] *)
Variable CALLS : list Z.
Definition is_call (id : Z) : bool := existsb (Z.eqb id) CALLS.
Hypothesis exit_facts_c : CC.others_all CPS TAGS (fun _ ps id => if is_call id then true else exit_chk ENDS ps) = true.

Lemma NFle : forall i c, nth_error CPS i = Some c -> (NF <= CC.cp_nx c)%nat.
Proof. intros i c H. pose proof (CC.cps_all_sound _ _ cut_facts i c H) as X. apply andb_prop in X as [X _]. apply Nat.leb_le. exact X. Qed.
Lemma SUBF : forall E0 i c, nth_error CPS i = Some c -> CL.sub_F NF E0 F0 c.
Proof.
  intros E0 i c H. pose proof (CC.cps_all_sound _ _ cut_facts i c H) as X. apply andb_prop in X as [_ X].
  intros E a Hag Hout. pose proof (CL.outside_agree_F0 NF E0 F0 F0vars E a Hag Hout) as Ho.
  unfold SGP.outside in *. rewrite Forall_forall in *. intros rg Hin. apply Ho. exact (F_sub_in _ _ _ X Hin).
Qed.

Theorem pure_fun_sound : forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet) (E0 : env) (cp0 : CC.cutpoint) (r : Z),
  m_halted model = None -> m_vm_lazy model = [] -> FPI fx ->
  (forall x : reg, ev E0 (ridx x) = getr R x) ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
  nth_error CPS 0 = Some cp0 -> CC.At segs cp0 E0 R M ->
  (forall i c tags k ps id, nth_error CPS i = Some c -> nth_error TAGS i = Some tags -> nth_error (CC.cp_PSS c) k = Some ps -> nth_error tags k = Some (CC.TOther id) ->
      is_call id = true -> CC.leaf_ok segs CPS (CL.pure_amb NF E0 M model F0) K FPI i c ps) ->
  (forall (fx' : FPState) i c tags k ps id E' R' M1 M',
      nth_error CPS i = Some c -> nth_error TAGS i = Some tags -> nth_error (CC.cp_PSS c) k = Some ps -> nth_error tags k = Some (CC.TOther id) -> is_call id = false ->
      FPI fx' -> env_agree NF E0 E' -> CC.leaf_facts segs c ps E' R' M1 M' ->
      (forall a : word, SGP.outside E0 F0 a -> M' a = M a) -> mem_grows M M' -> regs_preserved R R' ->
      srealizes segs SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 r) M' (seg_rom segs)) model) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (CC.cp_pc cp0)) M (seg_rom segs)) model) K.
Proof.
  intros fx R M model K E0 cp0 r Hh Hl Hfp EV Hra Hraok Hcp0 HAt Hcalls Hcont.
  set (Amb := CL.pure_amb NF E0 M model F0).
  eapply (CC.cutcert_sound_tagged segs CPS TAGS NF Amb K FPI FPM plans tags_ok) with (i := 0%nat) (c := cp0) (E := E0).
  - intros i E M1 m1 H. eapply (CL.pure_amb_model NF E0 M model F0 i); eauto.
  - intros i c tags k ps j s Hc _ _ _. apply CL.pure_amb_goto; [exact (SUBF E0 i c Hc) | exact (NFle i c Hc)].
  - intros i c tags k ps id Hc Htags Hps Htag. destruct (is_call id) eqn:Hic; [exact (Hcalls i c tags k ps id Hc Htags Hps Htag Hic)|].
    intros fx' E R1 M1 m1 E' R' M' HAt1 HAmb HFP Hag HLF _.
    pose proof (CC.others_all_sound _ _ _ exit_facts_c i c tags k ps id Hc Htags Hps Htag) as X. cbv beta in X. rewrite Hic in X. apply andb_prop in X as [Xpc Xk].
    assert (HA' : Amb 0%nat E' M' m1).
    { eapply (CL.pure_amb_step segs NF E0 M model F0) with (c := c); [exact (SUBF E0 i c Hc) | exact (NFle i c Hc) | exact HAmb | exact Hag | exact HLF | apply CC.env_agree_refl]. }
    destruct HA' as (-> & HagE & Hfr & Hgr).
    assert (Hcs : forall x : reg, In (ridx x) CSV1 -> getr R' x = getr R x).
    { intros x Hx. assert (Hx32 : (ridx x < 32)%nat) by (unfold CSV1 in Hx; cbn in Hx; intuition lia).
      rewrite (CL.ps_keeps_sound segs c ps E0 E' R' M1 M' CSV1 NF x HLF Xk HagE Hx ltac:(lia)).
      apply EV. }
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (Hcs 1%bv ltac:(left; reflexivity)); exact Hra).
    eapply CL.ret_cps; [exact (rets _ (CL.ps_at_sound _ _ Xpc)) | exact Hh | exact Hl | |].
    + rewrite Hra'. destruct Hraok as (Hr1 & Hr2). apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact Hr2.
    + rewrite Hra'. eapply (Hcont fx' i c tags k ps id E' R' M1 M' Hc Htags Hps Htag Hic HFP HagE HLF Hfr Hgr).
      intros x Hx. exact (Hcs x (csv_in x Hx)).
  - exact Hcp0.
  - exact HAt.
  - split; [reflexivity|]. split; [apply CC.env_agree_refl|]. split; [reflexivity | apply mem_grows_refl].
  - exact Hfp.
  Unshelve. all: exact 0%nat.
Qed.
End PureLeaf.

(* [comment removed for export] *)
Theorem pure_leaf_sound : forall (segs : list Segment) {SCFG_P : ScfgP} (FPI : FPState -> Prop)
  (FPM : forall (fx fx' : FPState) R pc M R' pc' M',
     msteps segs (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom segs)) -> FPI fx -> FPI fx')
  (CPS : list CC.cutpoint) (TAGS : list (list CC.tag)) (NF : nat) (F0 : list SGP.region) (ENDS : list Z),
  forallb (SGP.region_vars_lt NF) F0 = true -> (32 <= NF)%nat ->
  (forall i c, nth_error CPS i = Some c -> CC.plan_sound segs c) -> CC.tags_chk CPS TAGS NF = true ->
  CC.cps_all CPS (fun _ c => cut_chk NF F0 c) = true -> CC.others_all CPS TAGS (fun _ ps _ => exit_chk ENDS ps) = true ->
  (forall pc, In pc ENDS -> CL.is_ret_at segs pc) ->
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet) (E0 : env) (cp0 : CC.cutpoint) (r : Z),
  m_halted model = None -> m_vm_lazy model = [] -> FPI fx ->
  (forall x : reg, ev E0 (ridx x) = getr R x) ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
  nth_error CPS 0 = Some cp0 -> CC.At segs cp0 E0 R M ->
  (forall (fx' : FPState) i c tags k ps id E' R' M1 M',
      nth_error CPS i = Some c -> nth_error TAGS i = Some tags -> nth_error (CC.cp_PSS c) k = Some ps -> nth_error tags k = Some (CC.TOther id) ->
      FPI fx' -> env_agree NF E0 E' -> CC.leaf_facts segs c ps E' R' M1 M' ->
      (forall a : word, SGP.outside E0 F0 a -> M' a = M a) -> mem_grows M M' -> regs_preserved R R' ->
      srealizes segs SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 r) M' (seg_rom segs)) model) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (CC.cp_pc cp0)) M (seg_rom segs)) model) K.
Proof.
  intros segs SCFG_P FPI FPM CPS TAGS NF F0 ENDS F0vars NF32 plans tags_ok cut_facts exit_facts rets fx R M model K E0 cp0 r Hh Hl Hfp EV Hra Hraok Hcp0 HAt Hcont.
  apply (pure_fun_sound segs FPI FPM CPS TAGS NF F0 ENDS F0vars NF32 plans tags_ok cut_facts rets [] exit_facts fx R M model K E0 cp0 r Hh Hl Hfp EV Hra Hraok Hcp0 HAt).
  - intros i c tags k ps id _ _ _ _ Hic. discriminate Hic.
  - intros fx' i c tags k ps id E' R' M1 M' Hc Htags Hps Htag _. exact (Hcont fx' i c tags k ps id E' R' M1 M' Hc Htags Hps Htag).
Qed.
End SP.

(* [comment removed for export] *)
Ltac sp_len := apply CL5.elen_lin; [lin_eval; rw_atoms; first [reflexivity | lia] | lia].
Ltac sp_start := unfold estart; cbn [a_base a_off edenot]; rw_atoms; rewrite ?(u64_of_Z 0) by lia; first [reflexivity | lia].
Ltac sp_startl v := rewrite (CL5.estart_lin _ _ _ v); [lia | lin_eval; rw_atoms; lia | lia].
Ltac sp_disj := eapply CL5.kdisj_intro; [sp_start | sp_len | sp_start | sp_len | lia].
Ltac sp_unk H := eapply CL5.kunk_intro; [sp_start | sp_len | lia | lia | lia | first [exact H | eapply (L5.defined_sub _ _ _ _ _ H); lia]].
Ltac sp_wr H := eapply CL5.kwr_intro; [sp_start | sp_len | lia | lia | lia | first [exact H | eapply (L5.defined_sub _ _ _ _ _ H); lia]].
Ltac sp_range := eapply CL5.krange_intro; [lin_eval; rw_atoms; reflexivity | lia | lia].
