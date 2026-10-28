(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module TK.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Section Stretch.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma stretch_cps : forall (c : CC.cutpoint) (fx : FPState) E R M model K,
  CC.plan_sound RSEGS c -> m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  regs_ok E (CC.cp_regs c) R -> know_ok RSEGS E M (CC.cp_know c) ->
  (forall (fx' : FPState) E' R' M' k ps, nth_error (CC.cp_PSS c) k = Some ps -> env_agree (CC.cp_nx c) E E' ->
       CC.leaf_facts RSEGS c ps E' R' M M' -> PML.fp_ok fx' ->
       srealizes RSEGS SCFG (@PML.cfg fx' R' (SR.ps_pc ps) M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R (CC.cp_pc c) M model) K.
Proof.
  intros c fx E R M model K PS Hh Hl Hfp HR HK Hcont.
  destruct (PS fx E R M HR HK) as (fx' & E' & R' & M' & k & ps & Hnth & Hag & Hms & HLF).
  unfold PML.cfg. eapply L5.cps_of_msteps; [exact Hh | exact Hl | exact Hms |].
  apply (Hcont fx' E' R' M' k ps Hnth Hag HLF). exact (FPM _ _ _ _ _ _ _ _ Hms Hfp).
Qed.
End Stretch.

Definition hvV (sp0 : Z) (R : bvmap 5 word) (gh : nat -> word) : nat -> word :=
  fun n => if Nat.ltb n 32 then (if Nat.eqb n 2 then Z_to_bv 64 sp0 else Z_to_bv 64 0)
           else if Nat.ltb n 64 then getr R (Z_to_bv 5 (Z.of_nat (n - 32))) else gh (n - 64)%nat.
Definition hvE (sp0 : Z) (R : bvmap 5 word) (gh : nat -> word) : env := Env (hvV sp0 R gh) (fun _ => []).

Definition hv_slot (off : Z) (pins : list (nat * Z)) (q : nat) : expr :=
  if Nat.eqb q 2 then EAlu ALU_ADD (EVar 2) (ELit off)
  else match List.find (fun p => Nat.eqb (fst p) q) pins with Some p => ELit (snd p) | None => EVar (32 + q) end.
Definition hv_shape (sr : list expr) (off : Z) (pins : list (nat * Z)) : bool :=
  forallb (fun q => expr_eqb (nth q sr (ELit 0)) (hv_slot off pins q)) (seq 1 31).

Lemma add_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= a + b < 2 ^ 64 -> alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b Ha Hab. change (alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b)) with (bv_add (Z_to_bv 64 a) (Z_to_bv 64 b)).
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma regs_ok_hv : forall sr off pins sp0 R gh,
  hv_shape sr off pins = true -> 0 <= sp0 < 2 ^ 64 -> 0 <= sp0 + off < 2 ^ 64 ->
  getr R 2%bv = Z_to_bv 64 (sp0 + off) ->
  (forall q z, In (q, z) pins -> getr R (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z) ->
  regs_ok (hvE sp0 R gh) sr R.
Proof.
  intros sr off pins sp0 R gh Hsh Hsp Hspo H2 Hpins. apply APSX.regs_ok_pointwise. intros r Hr0.
  assert (Hq : In (ridx r) (seq 1 31)).
  { apply in_seq. pose proof (ridx_range r). assert (ridx r <> 0%nat).
    { intros X. apply Hr0. rewrite <- (ridx_roundtrip r), X. apply bv_eq. reflexivity. } lia. }
  unfold hv_shape in Hsh. rewrite forallb_forall in Hsh. specialize (Hsh _ Hq). apply expr_eqb_eq in Hsh. rewrite Hsh.
  unfold hv_slot. destruct (Nat.eqb (ridx r) 2) eqn:E2.
  - apply Nat.eqb_eq in E2. assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r), E2; apply bv_eq; reflexivity). subst r.
    cbn [edenot ev hvE]. unfold hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite add_lit by lia. exact H2.
  - destruct (find (fun p => Nat.eqb (fst p) (ridx r)) pins) as [[q z]|] eqn:Hf.
    + apply find_some in Hf as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q. cbn [snd edenot].
      rewrite <- (Hpins _ _ Hin), ridx_roundtrip. reflexivity.
    + cbn [edenot ev hvE]. unfold hvV. pose proof (ridx_range r) as Hlt.
      replace (Nat.ltb (32 + ridx r) 32) with false by (symmetry; apply Nat.ltb_ge; lia).
      replace (Nat.ltb (32 + ridx r) 64) with true by (symmetry; apply Nat.ltb_lt; lia).
      replace (32 + ridx r - 32)%nat with (ridx r) by lia. rewrite ridx_roundtrip. reflexivity.
Qed.

Lemma hvE_sp : forall sp0 R gh, 0 <= sp0 < 2 ^ 64 -> bv_unsigned (ev (hvE sp0 R gh) 2) = sp0.
Proof. intros. cbn. apply u64_of_Z. assumption. Qed.
Lemma hvE_ghost : forall sp0 R gh k, ev (hvE sp0 R gh) (64 + k) = gh k.
Proof.
  intros. cbn [ev hvE]. unfold hvV.
  replace (Nat.ltb (64 + k) 32) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (Nat.ltb (64 + k) 64) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (64 + k - 64)%nat with k by lia. reflexivity.
Qed.
Lemma hvE_reg : forall sp0 R gh (r : reg), ev (hvE sp0 R gh) (32 + ridx r) = getr R r.
Proof.
  intros. cbn [ev hvE]. unfold hvV. pose proof (ridx_range r).
  replace (Nat.ltb (32 + ridx r) 32) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (Nat.ltb (32 + ridx r) 64) with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (32 + ridx r - 32)%nat with (ridx r) by lia. rewrite ridx_roundtrip. reflexivity.
Qed.

Lemma edenot_lin : forall E e v, lden E (lin_of e) = v -> 0 <= v < 2 ^ 64 -> edenot E e = Z_to_bv 64 v.
Proof. intros E e v H Hv. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E e)). f_equal. apply CL5.u_lin; assumption. Qed.

Definition ps_reg (ps : SR.post_spec) (q : nat) : option expr :=
  match List.find (fun ie : nat * expr => Nat.eqb (fst ie) q) (SR.ps_regs ps) with Some ie => Some (snd ie) | None => None end.
Lemma ps_reg_sound : forall c ps E' R' M M' q e,
  CC.leaf_facts RSEGS c ps E' R' M M' -> ps_reg ps q = Some e -> getr R' (Z_to_bv 5 (Z.of_nat q)) = edenot E' e.
Proof.
  intros c ps E' R' M M' q e HLF H. unfold ps_reg in H. destruct (find _ (SR.ps_regs ps)) as [[i e']|] eqn:Hf; [|discriminate].
  injection H as <-. apply find_some in Hf as [Hin Hq]. cbn [fst] in Hq. apply Nat.eqb_eq in Hq. subst i.
  exact (CL.leaf_reg RSEGS _ _ _ _ _ _ _ _ HLF Hin).
Qed.

Lemma ps_reg_r : forall c ps E' R' M M' (r : reg) e,
  CC.leaf_facts RSEGS c ps E' R' M M' -> ps_reg ps (ridx r) = Some e -> getr R' r = edenot E' e.
Proof. intros c ps E' R' M M' r e HLF H. rewrite <- (ridx_roundtrip r) at 1. exact (ps_reg_sound _ _ _ _ _ _ _ _ HLF H). Qed.
Lemma leaf_lin : forall c ps E' R' M M' (r : reg) e v,
  CC.leaf_facts RSEGS c ps E' R' M M' -> ps_reg ps (ridx r) = Some e -> lden E' (lin_of e) = v -> 0 <= v < 2 ^ 64 -> getr R' r = Z_to_bv 64 v.
Proof. intros c ps E' R' M M' r e v HLF H Hl Hv. rewrite (ps_reg_r _ _ _ _ _ _ _ _ HLF H). apply edenot_lin; assumption. Qed.

Definition keeps_hv (ps : SR.post_spec) (qs : list nat) : bool := forallb (fun q => CL.ps_reg_is ps q (EVar (32 + q))) qs.
Lemma keeps_hv_sound : forall c ps sp0 R gh E' R' M M' qs (r : reg),
  CC.leaf_facts RSEGS c ps E' R' M M' -> keeps_hv ps qs = true -> env_agree 64 (hvE sp0 R gh) E' -> In (ridx r) qs -> getr R' r = getr R r.
Proof.
  intros c ps sp0 R gh E' R' M M' qs r HLF H Hag Hin. unfold keeps_hv in H. rewrite forallb_forall in H.
  rewrite <- (ridx_roundtrip r) at 1. rewrite (CL.ps_reg_is_sound RSEGS _ _ _ _ _ _ _ _ HLF (H _ Hin)). cbn [edenot].
  rewrite <- (proj1 Hag) by (pose proof (ridx_range r); lia). apply hvE_reg.
Qed.

Lemma keeps_id_sound : forall c ps R rest ebs E' R' M M' qs (r : reg),
  CC.leaf_facts RSEGS c ps E' R' M M' -> CL.ps_keeps ps qs = true -> env_agree 32 (Env (reg_ev R rest) ebs) E' -> In (ridx r) qs -> getr R' r = getr R r.
Proof.
  intros c ps R rest ebs E' R' M M' qs r HLF H Hag Hin.
  rewrite (CL.ps_keeps_sound RSEGS c ps _ E' R' M M' qs 32 r HLF H Hag Hin (ridx_range r)). apply CL5.ev_reg.
Qed.

Definition KS : list nat := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition keepsR (qs : list nat) (R R' : bvmap 5 word) : Prop := forall r : reg, In (ridx r) qs -> getr R' r = getr R r.
Lemma keepsR_refl : forall qs R, keepsR qs R R. Proof. intros qs R r _. reflexivity. Qed.
Lemma keepsR_trans : forall qs R R' R'', keepsR qs R R' -> keepsR qs R' R'' -> keepsR qs R R''.
Proof. intros qs R R' R'' H1 H2 r Hr. rewrite (H2 r Hr). apply H1. exact Hr. Qed.
Lemma keepsR_preserved : forall qs R R', regs_preserved R R' -> (forall q, In q qs -> In (Z.of_nat q) callee_saved_idx) -> keepsR qs R R'.
Proof.
  intros qs R R' HP Hqs r Hr. apply HP. specialize (Hqs _ Hr). unfold ridx in Hqs. rewrite Z2Nat.id in Hqs by (pose proof (bv_unsigned_in_range _ r); lia). exact Hqs.
Qed.

Definition samem (K : Z -> Prop) (M M' : mem) : Prop := forall a, 0 <= a < 2 ^ 64 -> K a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Lemma samem_weaken : forall (K K' : Z -> Prop) M M', samem K M M' -> (forall a, K' a -> K a) -> samem K' M M'.
Proof. intros K K' M M' H HK a Ha Hk. apply H; [exact Ha | apply HK; exact Hk]. Qed.
Lemma samem_trans : forall (K : Z -> Prop) M M' M'', samem K M M' -> samem K M' M'' -> samem K M M''.
Proof. intros K M M' M'' H1 H2 a Ha Hk. rewrite (H2 a Ha Hk). apply H1; assumption. Qed.
Lemma samem_refl : forall K M, samem K M M. Proof. intros K M a _ _. reflexivity. Qed.

Lemma frame_nil : forall c ps E' R' (M M' : mem), CC.leaf_facts RSEGS c ps E' R' M M' -> CC.cp_F c = [] -> M' = M.
Proof.
  intros c ps E' R' M M' HLF HF. apply FunctionalExtensionality.functional_extensionality. intros a.
  apply (CC.lf_frame _ _ _ _ _ _ _ HLF a). rewrite HF. constructor.
Qed.

Lemma frame_samem : forall c ps E' R' (M M' : mem) (K : Z -> Prop), CC.leaf_facts RSEGS c ps E' R' M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> K a -> SGP.outside E' (CC.cp_F c) (Z_to_bv 64 a)) -> samem K M M'.
Proof. intros c ps E' R' M M' K HLF H a Ha Hk. apply (CC.lf_frame _ _ _ _ _ _ _ HLF). apply H; assumption. Qed.

Lemma rdn_samem : forall (K : Z -> Prop) M M' a (n : nat), samem K M M' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat n -> K i) ->
  rdn RSEGS M' (Z_to_bv 64 a) n = rdn RSEGS M (Z_to_bv 64 a) n.
Proof. intros K M M' a n H Ha Hn HK. apply (L5C.rdn_agree RSEGS M M' n a Ha Hn). intros i Hi. apply H; [lia | apply HK; exact Hi]. Qed.
Lemma u8_samem : forall (K : Z -> Prop) M M' a v, samem K M M' -> 0 <= a < 2 ^ 63 -> K a -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v.
Proof. intros K M M' a v H Ha HK Hu. unfold L5.u8_at in *. rewrite (rdn_samem K M M' a 1 H) by (try (cbn; lia); intros i Hi; replace i with a by (cbn in Hi; lia); exact HK). exact Hu. Qed.
Lemma u32_samem : forall (K : Z -> Prop) M M' a v, samem K M M' -> 0 <= a < 2 ^ 63 -> (forall i, a <= i < a + 4 -> K i) -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof. intros K M M' a v H Ha HK Hu. unfold L5.u32_at in *. rewrite (rdn_samem K M M' a 4 H) by (first [cbn; lia | intros i Hi; apply HK; cbn in Hi; lia]). exact Hu. Qed.
Lemma u64_samem : forall (K : Z -> Prop) M M' a v, samem K M M' -> 0 <= a < 2 ^ 63 -> (forall i, a <= i < a + 8 -> K i) -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v.
Proof. intros K M M' a v H Ha HK Hu. unfold L5.u64_at in *. rewrite (rdn_samem K M M' a 8 H) by (first [cbn; lia | intros i Hi; apply HK; cbn in Hi; lia]). exact Hu. Qed.
Lemma bytes_samem : forall (K : Z -> Prop) M M' p bs, samem K M M' -> 0 <= p -> p + Z.of_nat (length bs) < 2 ^ 63 -> (forall i, p <= i < p + Z.of_nat (length bs) -> K i) ->
  L5.bytes_at RSEGS M p bs -> L5.bytes_at RSEGS M' p bs.
Proof. intros K M M' p bs H Hp Hn HK Hb i Hi. apply (u8_samem K M M' _ _ H); [lia | apply HK; lia | apply Hb; exact Hi]. Qed.
Lemma defined_samem : forall (K : Z -> Prop) M M' a n, samem K M M' -> 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> K i) -> L5.defined M a n -> L5.defined M' a n.
Proof. intros K M M' a n H Ha Hn HK Hd i Hi. rewrite (H (a + i)) by (first [lia | apply HK; lia]). apply Hd. exact Hi. Qed.
Lemma img_clear_samem : forall (K : Z -> Prop) M M' lo hi, samem K M M' -> 0 <= lo -> hi <= 2 ^ 64 -> (forall i, lo <= i < hi -> K i) -> L5.img_clear M lo hi -> L5.img_clear M' lo hi.
Proof. intros K M M' lo hi H Hlo Hhi HK Hc i Hi. rewrite (H i) by (first [lia | apply HK; lia]). apply Hc. exact Hi. Qed.

Lemma kword8_intro : forall E (M : mem) a v A z, estart E a = A -> 0 <= A -> A + 1 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  L5.u8_at RSEGS M A z -> kentry_ok RSEGS E M (KWord a 1 v).
Proof.
  intros E M a v A z Ha H0 H1 Hv Hz Hu. cbn [kentry_ok]. assert (Hfl : flat E a (Z.of_nat 1)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv.
  change (word_to_le_bytes 1 (Z_to_bv 64 z)) with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))]. rewrite u64_of_Z by exact Hz. exact Hu.
Qed.
Lemma kword32_elim : forall E (M : mem) a v A z, kentry_ok RSEGS E M (KWord a 4 v) -> estart E a = A -> bv_unsigned (edenot E v) = z -> L5.u32_at RSEGS M A z.
Proof.
  intros E M a v A z (_ & Hfl & Hr) Ha Hz. unfold L5.u32_at. rewrite <- Ha, <- (CL5.adenot_start E a _ Hfl), Hr. rewrite <- Hz, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma and1_val : forall (w : word) b, bv_unsigned w = b -> bv_unsigned (alu64 ALU_AND w (Z_to_bv 64 1)) = Z.land b 1.
Proof.
  intros w b <-. change (alu64 ALU_AND w (Z_to_bv 64 1)) with (bv_and w (Z_to_bv 64 1)). rewrite bv_and_unsigned. reflexivity.
Qed.
End TK.

Ltac tk_kimg RO := cbn [kentry_ok]; split; [lia|]; split; [lia|]; intros i Hi; apply RO; unfold PML.IMG_RO_HI; lia.
Ltac tk_outside := repeat (apply Forall_cons; [unfold estart, elenZ; cbn [a_base a_off edenot]; rw_atoms; rewrite ?u64_of_Z by lia; lia|]); apply Forall_nil.

Ltac tk_reg HLF r :=
  lazymatch type of HLF with
  | CC.leaf_facts _ _ ?ps _ _ _ _ =>
      let o := eval vm_compute in (TK.ps_reg ps (ridx r)) in
      lazymatch o with Some ?e => rewrite (TK.ps_reg_r _ _ _ _ _ _ r e HLF ltac:(vm_compute; reflexivity)); cbn [edenot] end
  end.
Ltac tk_lin HLF r :=
  lazymatch type of HLF with
  | CC.leaf_facts _ _ ?ps _ _ _ _ =>
      let o := eval vm_compute in (TK.ps_reg ps (ridx r)) in
      lazymatch o with Some ?e => apply (TK.leaf_lin _ _ _ _ _ _ r e _ HLF ltac:(vm_compute; reflexivity)); [lin_eval; rw_atoms; rewrite ?u64_of_Z by lia; lia | lia] end
  end.
