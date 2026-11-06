(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StoreOk ShapeSet RealizesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxImg.

Module FxGrow.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Sem Decode DecodeC.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import StoreOk FxStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Grow.
Variable segs : list Segment.

#[using="Type"] Lemma interp_eff_accesses_grows : forall t m r, interp_eff_accesses segs t m = MachineOk r -> mem_grows m (snd (access_value _ r)).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r H; cbn [interp_eff_accesses] in H; try discriminate.
  - injection H as <-. apply mem_grows_refl.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| |] eqn:Hk; try discriminate.
    injection H as <-. cbn [access_value]. exact (IH _ m rep Hk).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [rep| |] eqn:Hk;
      try discriminate.
    injection H as <-. cbn [access_value]. eapply mem_grows_trans; [apply write_to_mem_grows | exact (IH _ rep Hk)].
Qed.

#[using="Type"] Lemma decode_exec_accesses_grows : forall st w rep, decode_exec_accesses segs st w = MachineOk rep ->
  mem_grows (ms_mem st) (ms_mem (access_value _ rep)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros st w rep H. unfold decode_exec_accesses in H. destruct (is_ecall w).
  - injection H as <-. apply mem_grows_refl.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    destruct (interp_eff_accesses _ _) as [r| |] eqn:Hi; try discriminate.
    destruct (access_value _ r) as [c m'] eqn:Hv. injection H as <-. cbn [access_value ms_mem].
    pose proof (interp_eff_accesses_grows _ _ r Hi) as Hg. rewrite Hv in Hg. exact Hg.
Qed.

#[using="Type"] Lemma step_grows : forall st st', RiscvSemantics.step segs st = MachineOk st' -> mem_grows (ms_mem st) (ms_mem st').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros st st' H. unfold RiscvSemantics.step, drop_access_report in H.
  destruct (step_accesses segs st) as [rep| |] eqn:Hs; try discriminate. injection H as <-.
  unfold step_accesses in Hs.
  destruct (fetch_word segs (ms_pc st)); [exact (decode_exec_accesses_grows _ _ _ Hs)|].
  destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)); [exact (decode_exec_accesses_grows _ _ _ Hs)|].
  destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)); [exact (decode_exec_accesses_grows _ _ _ Hs)|].
  unfold fetch_failure in Hs. destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

#[using="Type"] Theorem isteps_grows : forall ms ms', isteps segs ms ms' -> mem_grows (ms_mem ms) (ms_mem ms').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' H. induction H as [ms|ms ms1 ms2 _ Hs _ IH]; [apply mem_grows_refl|].
  eapply mem_grows_trans; [exact (step_grows _ _ Hs) | exact IH].
Qed.
End Grow.
End FxGrow.

Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Drv.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

#[using="Type"] Lemma isteps_of_fx : forall ms ms', FxStep.isteps segs ms ms' -> RealizesCfg.isteps segs ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hst _ IH];
    [apply RealizesCfg.ist_refl | eapply RealizesCfg.ist_step; eassumption].
Qed.

#[using="Type"] Lemma step_rom : forall ms ms', RiscvSemantics.step segs ms = MachineOk ms' -> ms_rom ms' = ms_rom ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' H. unfold RiscvSemantics.step, RiscvSemantics.step_accesses in H.
  assert (Hd : forall w, drop_access_report (decode_exec_accesses segs ms w) = MachineOk ms' -> ms_rom ms' = ms_rom ms).
  { intros w Hw. unfold decode_exec_accesses in Hw. destruct (is_ecall w).
    - cbn in Hw. injection Hw as <-. reflexivity.
    - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
      destruct (interp_eff_accesses _ _) as [report| |]; try discriminate.
      destruct report as [[c m'] acc]. cbn in Hw. injection Hw as <-. reflexivity. }
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (Hd w H)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hd w H)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hd w H)|].
  unfold fetch_failure in H.
  destruct (negb _); [discriminate|]. destruct (_ || _ || _)%bool; discriminate.
Qed.

#[using="Type"] Lemma fx_rom : forall ms ms', FxStep.isteps segs ms ms' -> ms_rom ms' = ms_rom ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hst _ IH]; [reflexivity|].
  rewrite IH. exact (step_rom _ _ Hst).
Qed.

#[using="Type"] Theorem rzc_fx_explore : forall t img fuel stops (S : sst) (LEAVES : list sst) E ms model T,
  tbl_ok segs t -> img_ok segs img ->
  fx_explore t img fuel stops S [] = LEAVES ->
  sden segs E S ms -> m_halted model = None -> m_vm_lazy model = [] ->
  (forall L E' ms', In L LEAVES -> sden segs E' L ms' -> agree (s_next S) E E' -> ms_rom ms' = ms_rom ms ->
      realizes_cfg segs cfg (mkCfg ms' model) T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel stops S LEAVES E ms model T Ht Himg HL Hden Hh Hl Hk.
  destruct (explore_sound segs t img fuel stops S [] E ms Ht Himg Hden) as (L & ms' & E' & HIn & Hst & Hd' & Ha).
  rewrite HL in HIn.
  eapply rzc_isteps; [exact Hh | exact Hl | apply isteps_of_fx; exact Hst |].
  apply (Hk L E' ms' HIn Hd' Ha (fx_rom _ _ Hst)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem rzc_fx_explore_frame : forall t img fuel stops (S : sst) (LEAVES : list sst) E ms model T,
  tbl_ok segs t -> img_ok segs img ->
  fx_explore t img fuel stops S [] = LEAVES ->
  sden segs E S ms -> bases_wf (s_next S) (s_rgs S) = true -> m_halted model = None -> m_vm_lazy model = [] ->
  (forall L E' ms', In L LEAVES -> sden segs E' L ms' -> agree (s_next S) E E' -> ms_rom ms' = ms_rom ms ->
      (forall x, outside E (s_rgs S) x -> ms_mem ms' x = ms_mem ms x) ->
      realizes_cfg segs cfg (mkCfg ms' model) T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel stops S LEAVES E ms model T Ht Himg HL Hden Hwf Hh Hl Hk.
  destruct (explore_frame segs t img fuel stops S [] E ms Ht Himg Hden Hwf) as (L & ms' & E' & HIn & Hst & Hd' & Ha & Hfr & _).
  rewrite HL in HIn.
  eapply rzc_isteps; [exact Hh | exact Hl | apply isteps_of_fx; exact Hst |].
  apply (Hk L E' ms' HIn Hd' Ha (fx_rom _ _ Hst) Hfr).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem rzc_fx_explore_fg : forall t img fuel stops (S : sst) (LEAVES : list sst) E ms model T,
  tbl_ok segs t -> img_ok segs img ->
  fx_explore t img fuel stops S [] = LEAVES ->
  sden segs E S ms -> bases_wf (s_next S) (s_rgs S) = true -> m_halted model = None -> m_vm_lazy model = [] ->
  (forall L E' ms', In L LEAVES -> sden segs E' L ms' -> agree (s_next S) E E' -> ms_rom ms' = ms_rom ms ->
      (forall x, outside E (s_rgs S) x -> ms_mem ms' x = ms_mem ms x) -> mem_grows (ms_mem ms) (ms_mem ms') ->
      realizes_cfg segs cfg (mkCfg ms' model) T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel stops S LEAVES E ms model T Ht Himg HL Hden Hwf Hh Hl Hk.
  destruct (explore_frame segs t img fuel stops S [] E ms Ht Himg Hden Hwf) as (L & ms' & E' & HIn & Hst & Hd' & Ha & Hfr & _).
  rewrite HL in HIn.
  eapply rzc_isteps; [exact Hh | exact Hl | apply isteps_of_fx; exact Hst |].
  apply (Hk L E' ms' HIn Hd' Ha (fx_rom _ _ Hst) Hfr (isteps_grows segs _ _ Hst)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem rzc_fx_seg : forall t img fuel stops (S : sst) (LEAVES : list sst) (P : sst) E0 mem0 E ms model T,
  tbl_ok segs t -> img_ok segs img ->
  fx_explore t img fuel stops S [] = LEAVES ->
  sden segs E S ms -> bases_wf (s_next S) (s_rgs S) = true ->
  shape (s_rgs S) = shape (s_rgs P) -> bases_wf (s_next P) (s_rgs P) = true -> agree (s_next P) E0 E ->
  (forall x, outside E0 (s_rgs P) x -> ms_mem ms x = mem0 x) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (forall L E' ms', In L LEAVES -> sden segs E' L ms' -> agree (s_next S) E E' -> ms_rom ms' = ms_rom ms ->
      (forall x, outside E0 (s_rgs P) x -> ms_mem ms' x = mem0 x) ->
      realizes_cfg segs cfg (mkCfg ms' model) T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel stops S LEAVES P E0 mem0 E ms model T Ht Himg HL Hden Hwf Hsh HwfP Ha0 Hmf Hh Hl Hk.
  apply (rzc_fx_explore_frame t img fuel stops S LEAVES E ms model T Ht Himg HL Hden Hwf Hh Hl).
  intros L E' ms' HIn Hd' Ha' Hrom Hfr. apply (Hk L E' ms' HIn Hd' Ha' Hrom).
  intros x Hx. rewrite Hfr; [exact (Hmf x Hx)|].
  apply (outside_shape E (s_rgs P) (s_rgs S) x Hsh). apply (outside_agree (s_next P) E0 E (s_rgs P) x HwfP Ha0). exact Hx.
Qed.

#[using="Type"] Theorem rzc_fx_check : forall t img ins depth p (S : sst) finals E ms model T,
  tbl_ok segs t -> img_ok segs img ->
  check t img ins depth p S = Some finals ->
  sden segs E S ms -> m_halted model = None -> m_vm_lazy model = [] ->
  (forall L E' ms', In L finals -> sden segs E' L ms' -> (forall x, In x ins -> E' x = E x) -> ms_rom ms' = ms_rom ms ->
      realizes_cfg segs cfg (mkCfg ms' model) T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ins depth p S finals E ms model T Ht Himg Hck Hden Hh Hl Hk.
  destruct (check_sound segs t img ins depth p S finals Ht Himg Hck E ms Hden) as (L & ms' & E' & HIn & Hst & Hd' & Hi).
  eapply rzc_isteps; [exact Hh | exact Hl | apply isteps_of_fx; exact Hst |].
  apply (Hk L E' ms' HIn Hd' Hi (fx_rom _ _ Hst)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma sden_getr : forall E L ms, sden segs E L ms ->
  forall r, getr (ms_regs ms) r = lden E (rget (s_regs L) (rkey r)).
Proof. LiaFast.lf_pins LiaFast.u0. intros E L ms H. destruct (sden_0 _ _ _ _ H) as (_ & _ & _ & HR & _). exact HR. Qed.

#[using="Type"] Lemma sden_pc : forall E L ms, sden segs E L ms -> ms_pc_val ms = Z_to_bv 64 (s_pc L).
Proof. LiaFast.lf_pins LiaFast.u0. intros E L ms H. destruct (sden_0 _ _ _ _ H) as (Hpc & _). exact Hpc. Qed.

#[using="Type"] Lemma sden_svc : forall E L ms, sden segs E L ms -> ms_svc_pending ms = None.
Proof. LiaFast.lf_pins LiaFast.u0. intros E L ms H. destruct (sden_0 _ _ _ _ H) as (_ & Hs & _). exact Hs. Qed.

#[using="Type"] Lemma sden_resv : forall E L ms, sden segs E L ms -> s_resv L = RNone -> ms_resv ms = None.
Proof. LiaFast.lf_pins LiaFast.u0. intros E L ms H Hr. destruct (sden_0 _ _ _ _ H) as (_ & _ & Hrv & _). rewrite Hr in Hrv. exact Hrv. Qed.

#[using="Type"] Lemma sden_frm : forall E L ms, sden segs E L ms -> frm_zero (ms_fcsr ms).
Proof. LiaFast.lf_pins LiaFast.u0. intros E L ms H. destruct (sden_0 _ _ _ _ H) as (_ & _ & _ & _ & _ & _ & _ & Hf). exact Hf. Qed.

#[using="Type"] Lemma sden_rg : forall E L ms i R, sden segs E L ms -> nth_error (s_rgs L) i = Some R -> rg_ok segs E (ms_mem ms) R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L ms i R H Hi. destruct (sden_0 _ _ _ _ H) as (_ & _ & _ & _ & Hrg & _).
  rewrite Forall_nth' in Hrg. exact (Hrg i R Hi).
Qed.

#[using="Type"] Lemma sden_fact : forall E L ms f, sden segs E L ms -> In f (s_facts L) -> fact_ok E f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L ms f H Hf. destruct (sden_0 _ _ _ _ H) as (_ & _ & _ & _ & _ & _ & Hfs & _).
  rewrite Forall_forall in Hfs. exact (Hfs f Hf).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sden_mkst : forall E L ms, sden segs E L ms -> s_resv L = RNone ->
  ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (Z_to_bv 64 (s_pc L)) (ms_mem ms) (ms_rom ms).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L ms H Hr. rewrite <- (sden_pc _ _ _ H). pose proof (sden_svc _ _ _ H) as Hs.
  pose proof (sden_resv _ _ _ H Hr) as Hv.
  destruct ms as [r f p sv rv fc m ro]; cbn in *. subst. reflexivity.
Qed.

End Drv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint regs_havoc (R : tree lin) (keep : list positive) (nx : positive) (k : nat) (acc : tree lin) : tree lin :=
  match k with
  | O => acc
  | S k' =>
      let key := Pos.of_succ_nat k in
      regs_havoc R keep nx k'
        (rset acc key (if existsb (Pos.eqb key) keep then rget R key else lvar (nx + Pos.of_nat k)))
  end.

(* [comment removed for export] *)
Definition fpr : Type := (nat * Z * Z)%type.

Definition fp_targets (fp : list fpr) (i : nat) : bool := existsb (fun f : fpr => let '(j, _, _) := f in Nat.eqb i j) fp.

Definition havoc_cont (fp : list fpr) (i : nat) (t : tree bval) : tree bval :=
  fold_left (fun acc '(j, o, n) => if Nat.eqb i j then havoc_range acc o (o + n) else acc) fp t.

Definition havoc_rg_i (fp : list fpr) (i : nat) (R : region) : region :=
  if fp_targets fp i then RG (rg_base R) (rg_size R) RW (havoc_cont fp i (rg_cont R)) else R.

Fixpoint map_i {A B} (f : nat -> A -> B) (i : nat) (l : list A) : list B :=
  match l with [] => [] | x :: r => f i x :: map_i f (S i) r end.

(* [comment removed for export] *)
Definition set_a0 (R : tree lin) (res : option lin) : tree lin :=
  match res with None => R | Some l => rset R 11%positive l end.

(* [comment removed for export] *)
Definition havoc_call (L : sst) (ret : Z) (keep : list positive) (fp : list fpr) (res : option lin) : sst :=
  SST ret (set_a0 (regs_havoc (s_regs L) keep (s_next L) 31 TEmpty) res) (map_i (havoc_rg_i fp) 0 (s_rgs L)) (s_facts L)
      (s_next L + 32) RNone.

(* [comment removed for export] *)
Definition wkind (k : rkind) : bool := match k with RO | RT => false | _ => true end.

Definition fp_in_rw (rgs : list region) (f : fpr) : bool :=
  let '(j, o, n) := f in
  match nth_error rgs j with
  | Some R => (wkind (rg_kind R) && Z.leb 0 o && Z.leb 0 n && Z.leb (o + n) (size_lo [] R))%bool
  | None => false
  end.

Definition havoc_ok (L : sst) (fp : list fpr) (res : option lin) : bool :=
  (state_wf L && forallb (fp_in_rw (s_rgs L)) fp && match res with None => true | Some l => lwf (s_next L) l end)%bool.

(* [comment removed for export] *)
Definition in_fp (E : valu) (rgs : list region) (fp : list fpr) (x : word) : Prop :=
  exists j o n R, In (j, o, n) fp /\ nth_error rgs j = Some R /\
    bv_unsigned (lden E (rg_base R)) + o <= bv_unsigned x < bv_unsigned (lden E (rg_base R)) + o + n.

(* [comment removed for export] *)
Definition in_rg (E : valu) (R : region) (x : word) : Prop :=
  bv_unsigned (lden E (rg_base R)) <= bv_unsigned x < bv_unsigned (lden E (rg_base R)) + rsz E R.

Lemma nth_map_i : forall {A B} (f : nat -> A -> B) l i k x, nth_error l k = Some x -> nth_error (map_i f i l) k = Some (f (i + k)%nat x).
Proof.
  intros A B f l. induction l as [|y l IH]; intros i k x H; [destruct k; discriminate|].
  destruct k as [|k]; cbn [nth_error map_i] in *.
  - injection H as <-. rewrite Nat.add_0_r. reflexivity.
  - rewrite (IH (S i) k x H). f_equal. f_equal. lia.
Qed.

Lemma nth_map_i_inv : forall {A B} (f : nat -> A -> B) l i k y, nth_error (map_i f i l) k = Some y ->
  exists x, nth_error l k = Some x /\ y = f (i + k)%nat x.
Proof.
  intros A B f l. induction l as [|x l IH]; intros i k y H; [destruct k; discriminate|].
  destruct k as [|k]; cbn [nth_error map_i] in *.
  - injection H as <-. exists x. rewrite Nat.add_0_r. auto.
  - destruct (IH (S i) k y H) as (x' & Hx & ->). exists x'. split; [exact Hx|]. f_equal. lia.
Qed.

Lemma length_map_i : forall {A B} (f : nat -> A -> B) l i, length (map_i f i l) = length l.
Proof. intros A B f l. induction l as [|x l IH]; intros i; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma rget_nonxH : forall t key, key <> xH -> rget t key = match tget key t with Some l => l | None => lc0 end.
Proof. intros t key H. unfold rget. destruct key; [reflexivity | reflexivity | congruence]. Qed.

Lemma succ_nat_nonxH : forall j, (1 <= j)%nat -> Pos.of_succ_nat j <> xH.
Proof. intros j Hj Hc. destruct j; [lia|]. cbn in Hc. destruct (Pos.of_succ_nat j); discriminate. Qed.

Lemma regs_havoc_spec : forall R keep nx k acc key,
  (forall j, (k < j <= 31)%nat -> tget (Pos.of_succ_nat j) acc =
     Some (if existsb (Pos.eqb (Pos.of_succ_nat j)) keep then rget R (Pos.of_succ_nat j) else lvar (nx + Pos.of_nat j))) ->
  (k <= 31)%nat ->
  forall j, (1 <= j <= 31)%nat -> key = Pos.of_succ_nat j ->
  rget (regs_havoc R keep nx k acc) key
  = if existsb (Pos.eqb key) keep then rget R key else lvar (nx + Pos.of_nat j).
Proof.
  intros R keep nx k. induction k as [|k IH]; intros acc key Hacc Hk j Hj Hkey; cbn [regs_havoc].
  - subst key. rewrite rget_nonxH by (apply succ_nat_nonxH; lia). rewrite (Hacc j ltac:(lia)). reflexivity.
  - apply IH; [| lia | exact Hj | exact Hkey].
    intros j' Hj'. unfold rset.
    assert (Hnx : Pos.of_succ_nat (S k) <> xH) by (apply succ_nat_nonxH; lia).
    destruct (Pos.of_succ_nat (S k)) eqn:E; [| | exfalso; exact (Hnx eq_refl)];
    rewrite <- E; destruct (Nat.eq_dec j' (S k)) as [->|Hne];
      [ rewrite tget_tset_same; reflexivity
      | rewrite tget_tset_other; [apply Hacc; lia|]; intros Hc; apply SuccNat2Pos.inj in Hc; lia
      | rewrite tget_tset_same; reflexivity
      | rewrite tget_tset_other; [apply Hacc; lia|]; intros Hc; apply SuccNat2Pos.inj in Hc; lia ].
Qed.

Lemma regs_havoc_get : forall R keep nx j, (1 <= j <= 31)%nat ->
  rget (regs_havoc R keep nx 31 TEmpty) (Pos.of_succ_nat j)
  = if existsb (Pos.eqb (Pos.of_succ_nat j)) keep then rget R (Pos.of_succ_nat j) else lvar (nx + Pos.of_nat j).
Proof.
  intros R keep nx j Hj. apply (regs_havoc_spec R keep nx 31 TEmpty); [| lia | exact Hj | reflexivity].
  intros j' Hj'. lia.
Qed.

Lemma rget_set_a0_other : forall R res key, key <> 11%positive -> rget (set_a0 R res) key = rget R key.
Proof.
  intros R [l|] key Hk; [|reflexivity]. cbn [set_a0]. unfold rget, rset.
  destruct key as [k|k|]; [| |reflexivity]; rewrite tget_tset_other by (intros Hc; apply Hk; rewrite Hc; reflexivity); reflexivity.
Qed.

Lemma rget_set_a0_same : forall R l, rget (set_a0 R (Some l)) 11%positive = l.
Proof. intros R l. cbn [set_a0]. unfold rget, rset. rewrite tget_tset_same. reflexivity. Qed.

Lemma rkey_a0 : forall r : reg, rkey r = 11%positive -> r = Z_to_bv 5 10.
Proof.
  intros r H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold rkey, bv_key in H.
  pose proof (bv_unsigned_in_range _ r) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 5) with 32 in R.
  apply (f_equal Zpos) in H. rewrite Z2Pos.id in H by lia. change (bv_wrap 5 10) with 10. lia.
Qed.

Lemma rsz_RG_eq : forall E R k c, rsz E (RG (rg_base R) (rg_size R) k c) = rsz E R.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rsz_LIN : forall E b n k c, 0 <= n < two64 -> rsz E (RG b (LIN n []) k c) = n.
Proof. intros E b n k c Hn. unfold rsz, lden, lz. cbn [rg_size l_c l_t tsum]. rewrite Z.add_0_r. apply u_small64. exact Hn. Qed.
Ltac rsz_simpl := repeat first [ rewrite rsz_RGz by (unfold two64; lia) | rewrite rsz_lconst by (unfold two64; lia)
                               | rewrite rsz_LIN by (unfold two64; lia) ].
Ltac rsz_simpl_in H := repeat first [ rewrite rsz_RGz in H by (unfold two64; lia) | rewrite rsz_lconst in H by (unfold two64; lia)
                                    | rewrite rsz_LIN in H by (unfold two64; lia) ].

(* [comment removed for export] *)
Definition csz (R : region) : Z := match is_const (rg_size R) with Some c => c | None => -1 end.
Lemma csz_rsz : forall E R, 0 <= csz R -> rsz E R = csz R.
Proof.
  intros E R H. unfold csz in *. destruct (is_const (rg_size R)) as [c|] eqn:Hc; [|lia].
  unfold rsz. exact (is_const_u E _ c Hc).
Qed.
Lemma rsz_c : forall E R n, csz R = n -> 0 <= n -> rsz E R = n.
Proof. intros E R n H Hn. subst n. exact (csz_rsz E R Hn). Qed.
(* [comment removed for export] *)
Ltac rszv := repeat match goal with
  | |- context [rsz ?E ?R] => let n := eval vm_compute in (csz R) in
       match n with
       | Zpos _ => rewrite (rsz_c E R n ltac:(vm_compute; reflexivity) ltac:(lia))
       | Z0 => rewrite (rsz_c E R n ltac:(vm_compute; reflexivity) ltac:(lia))
       end
  end.
Ltac rszv_in H := repeat match type of H with
  | context [rsz ?E ?R] => let n := eval vm_compute in (csz R) in
       match n with
       | Zpos _ => rewrite (rsz_c E R n ltac:(vm_compute; reflexivity) ltac:(lia)) in H
       | Z0 => rewrite (rsz_c E R n ltac:(vm_compute; reflexivity) ltac:(lia)) in H
       end
  end.

Section Havoc.
Variable segs : list Segment.

#[using="Type"] Lemma fold_havoc_sub : forall fp i t p v,
  tget p (havoc_cont fp i t) = Some v ->
  tget p t = Some v /\ (forall j o n, In (j, o, n) fp -> i = j -> ~ (o <= Zpos p - 1 < o + n)).
Proof. LiaFast.lf_pins LiaFast.u0.
  unfold havoc_cont. intros fp. induction fp as [|[[j o] n] fp IH]; intros i t p v H; cbn [fold_left] in H.
  - split; [exact H | intros j o n []].
  - destruct (IH i _ p v H) as [H1 H2]. destruct (Nat.eqb i j) eqn:Eij.
    + unfold havoc_range in H1. rewrite tget_tfilter in H1.
      destruct (tget p t) as [v'|] eqn:Ht; [|discriminate].
      destruct (negb _) eqn:Hn; [|discriminate]. injection H1 as <-. split; [reflexivity|].
      intros j' o' n' [Heq|HIn] Hi.
      * injection Heq as <- <- <-. apply negb_true_iff in Hn. intros [A B].
        rewrite (proj2 (Z.leb_le _ _) A), (proj2 (Z.ltb_lt _ _) B) in Hn. discriminate.
      * exact (H2 j' o' n' HIn Hi).
    + split; [exact H1|]. intros j' o' n' [Heq|HIn] Hi.
      * injection Heq as <- <- <-. subst i. rewrite Nat.eqb_refl in Eij. discriminate.
      * exact (H2 j' o' n' HIn Hi).
Qed.

#[using="Type"] Lemma fp_targets_in : forall fp i, fp_targets fp i = true -> exists o n, In (i, o, n) fp.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fp i H. unfold fp_targets in H. apply existsb_exists in H as ([[j o] n] & HIn & Hj).
  apply Nat.eqb_eq in Hj. subst j. exists o, n. exact HIn.
Qed.

#[using="Type"] Lemma fp_targets_notin : forall fp i j o n, fp_targets fp i = false -> In (j, o, n) fp -> j <> i.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fp i j o n H HIn Hji. subst j. unfold fp_targets in H.
  assert (Hc : existsb (fun f : fpr => let '(j, _, _) := f in Nat.eqb i j) fp = true).
  { apply existsb_exists. exists (i, o, n). split; [exact HIn | apply Nat.eqb_refl]. }
  congruence.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_rw_byte : forall E m R, rg_ok segs E m R -> wkind (rg_kind R) = true ->
  forall i, 0 <= i < rsz E R ->
    rd1 segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None /\
    wview segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R (_ & _ & Hall & _) Hk i Hi. specialize (Hall i Hi).
  destruct (rg_kind R); [exact Hall | discriminate | exact (proj1 Hall) | exact (proj1 Hall) | discriminate].
Qed.

#[using="Type"] Theorem havoc_call_sound : forall E L ms ms' (ret : Z) (keep : list positive) (fp : list fpr) (res : option lin),
  havoc_ok L fp res = true ->
  sden segs E L ms ->
  ms_pc_val ms' = Z_to_bv 64 ret -> ms_svc_pending ms' = None -> ms_resv ms' = None -> frm_zero (ms_fcsr ms') ->
  (forall r : reg, existsb (Pos.eqb (rkey r)) keep = true -> rkey r <> 11%positive \/ res = None ->
     getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  (forall l, res = Some l -> getr (ms_regs ms') (Z_to_bv 5 10) = lden E l) ->
  (forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) fp x -> ms_mem ms' x = ms_mem ms x) ->
  (forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ms_mem ms x <> None -> ms_mem ms' x <> None) ->
  exists E', agree (s_next L) E E' /\ sden segs E' (havoc_call L ret keep fp res) ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L ms ms' ret keep fp res Hok Hden Hpc Hsvc Hrv Hfrm Hkeep Hres Hmem Hgrow.
  unfold havoc_ok in Hok. apply andb_prop in Hok as [Hok Hresw]. apply andb_prop in Hok as [Hwf Hfp].
  rewrite forallb_forall in Hfp.
  set (nx := s_next L).
  set (E' := fun x : positive =>
    if (Pos.ltb nx x && Pos.ltb x (nx + 32))%bool then getr (ms_regs ms') (Z_to_bv 5 (Zpos x - Zpos nx)) else E x).
  assert (HaE : agree nx E E').
  { intros x Hx. unfold E'. rewrite (proj2 (Pos.ltb_ge _ _)) by lia. reflexivity. }
  exists E'. split; [exact HaE|].
  intros E'' Ha''. cbn [s_next havoc_call] in Ha''.
  assert (Ha0 : agree nx E E'') by (intros x Hx; rewrite (HaE x Hx); apply Ha''; lia).
  pose proof (Hden E'' Ha0) as (Hpc0 & Hsvc0 & Hrv0 & HR0 & Hrg0 & Hdj0 & Hf0 & Hfrm0).
  assert (Hfresh : forall j, (1 <= j <= 31)%nat -> E'' (nx + Pos.of_nat j)%positive = getr (ms_regs ms') (Z_to_bv 5 (Z.of_nat j))).
  { intros j Hj. rewrite <- (Ha'' (nx + Pos.of_nat j)%positive) by lia. unfold E'.
    rewrite (proj2 (Pos.ltb_lt _ _)) by lia. rewrite (proj2 (Pos.ltb_lt _ _)) by lia. cbn [andb].
    f_equal. f_equal. lia. }
  (* [comment removed for export] *)
  assert (Hbs : forall i R, nth_error (s_rgs L) i = Some R -> lden E (rg_base R) = lden E'' (rg_base R) /\ rsz E R = rsz E'' R).
  { intros i R Hi. unfold state_wf in Hwf. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [Hwf _].
    apply andb_prop in Hwf as [_ Hrw]. rewrite forallb_forall in Hrw.
    pose proof (Hrw R (nth_error_In _ _ Hi)) as HR. unfold rwf in HR. apply andb_prop in HR as [HR _]. apply andb_prop in HR as [HR HS].
    split; [exact (lden_agree nx E E'' (rg_base R) HR Ha0) | unfold rsz; rewrite (lden_agree nx E E'' (rg_size R) HS Ha0); reflexivity]. }
  assert (Hbase : forall i R, nth_error (s_rgs L) i = Some R -> lden E (rg_base R) = lden E'' (rg_base R)) by (intros i R Hi; exact (proj1 (Hbs i R Hi))).
  assert (Hsize : forall i R, nth_error (s_rgs L) i = Some R -> rsz E R = rsz E'' R) by (intros i R Hi; exact (proj2 (Hbs i R Hi))).
  (* [comment removed for export] *)
  assert (Hnofp : forall k R x, nth_error (s_rgs L) k = Some R -> in_rg E'' R x ->
             (forall j o n, In (j, o, n) fp -> j = k -> ~ (o <= bv_unsigned x - bv_unsigned (lden E'' (rg_base R)) < o + n)) ->
             ~ in_fp E (s_rgs L) fp x).
  { intros k R x Hk Hin Hno (j & o' & n & R2 & HIn & Hj & Hinj). rewrite (Hbase j R2 Hj) in Hinj.
    pose proof (Hfp _ HIn) as Hf. unfold fp_in_rw in Hf. rewrite Hj in Hf.
    apply andb_prop in Hf as [Hf Hn2]. apply andb_prop in Hf as [Hf Hn1]. apply andb_prop in Hf as [_ Ho1].
    apply Z.leb_le in Hn2. apply Z.leb_le in Hn1. apply Z.leb_le in Ho1.
    destruct (Nat.eq_dec j k) as [->|Hne].
    - rewrite Hk in Hj. injection Hj as <-. apply (Hno k o' n HIn eq_refl). lia.
    - pose proof (rgs_disj_nth E'' (s_rgs L) k j R R2 Hdj0 (fun H => Hne (eq_sym H)) Hk Hj) as Hd.
      pose proof (size_lo_sound E'' [] R2 (Forall_nil _)) as Hsl.
      unfold rg_disj, in_rg in *. lia. }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - exact Hpc.
  - exact Hsvc.
  - cbn [s_resv havoc_call rsv_ok]. exact Hrv.
  - (* [comment removed for export] *)
    intros r. cbn [s_regs havoc_call]. fold nx.
    destruct (decide (r = 0%bv)) as [->|Hr0].
    + change (rkey 0%bv) with xH. unfold rget. reflexivity.
    + destruct (Pos.eq_dec (rkey r) 11%positive) as [Ha0k|Ha0k].
      * destruct res as [l|].
        -- rewrite Ha0k, rget_set_a0_same. rewrite (rkey_a0 r Ha0k). rewrite (Hres l eq_refl).
           apply (lden_agree nx E E'' l); [exact Hresw | exact Ha0].
        -- cbn [set_a0]. destruct (rkey_succ r Hr0) as (j & Hj & Hkey). rewrite Hkey.
           rewrite (regs_havoc_get (s_regs L) keep nx j Hj).
           destruct (existsb (Pos.eqb (Pos.of_succ_nat j)) keep) eqn:Hk.
           ++ rewrite <- Hkey in Hk |- *. rewrite (Hkeep r Hk (or_intror eq_refl)). apply HR0.
           ++ cbn [lden]. unfold lvar, lden, lz. cbn [l_c l_t tsum]. unfold vz.
              rewrite Hfresh by exact Hj.
              assert (Hrj : Z_to_bv 5 (Z.of_nat j) = r).
              { pose proof (bv_unsigned_in_range _ r) as Rr. unfold bv_modulus in Rr. change (2 ^ Z.of_N 5) with 32 in Rr.
                assert (Hu : bv_unsigned r = Z.of_nat j).
                { apply (f_equal Zpos) in Hkey. unfold rkey, bv_key in Hkey. rewrite Z2Pos.id in Hkey by lia.
                  rewrite Zpos_P_of_succ_nat in Hkey. lia. }
                apply bv_eq. rewrite Z_to_bv_unsigned, <- Hu. apply bv_wrap_small. unfold bv_modulus. lia. }
              rewrite Hrj. rewrite Z.add_0_l, Z.mul_1_l, Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
      * rewrite (rget_set_a0_other _ res _ Ha0k).
        destruct (rkey_succ r Hr0) as (j & Hj & Hkey). rewrite Hkey.
        rewrite (regs_havoc_get (s_regs L) keep nx j Hj).
        destruct (existsb (Pos.eqb (Pos.of_succ_nat j)) keep) eqn:Hk.
        -- rewrite <- Hkey in Hk |- *. rewrite (Hkeep r Hk (or_introl Ha0k)). apply HR0.
        -- cbn [lden]. unfold lvar, lden, lz. cbn [l_c l_t tsum]. unfold vz.
           rewrite Hfresh by exact Hj.
           assert (Hrj : Z_to_bv 5 (Z.of_nat j) = r).
           { pose proof (bv_unsigned_in_range _ r) as Rr. unfold bv_modulus in Rr. change (2 ^ Z.of_N 5) with 32 in Rr.
             assert (Hu : bv_unsigned r = Z.of_nat j).
             { apply (f_equal Zpos) in Hkey. unfold rkey, bv_key in Hkey. rewrite Z2Pos.id in Hkey by lia.
               rewrite Zpos_P_of_succ_nat in Hkey. lia. }
             apply bv_eq. rewrite Z_to_bv_unsigned, <- Hu. apply bv_wrap_small. unfold bv_modulus. lia. }
           rewrite Hrj. rewrite Z.add_0_l, Z.mul_1_l, Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  - (* [comment removed for export] *)
    cbn [s_rgs havoc_call]. rewrite Forall_nth'. intros k R' Hk.
    destruct (nth_map_i_inv (havoc_rg_i fp) (s_rgs L) 0 k R' Hk) as (R & HkR & ->).
    rewrite Forall_nth' in Hrg0. pose proof (Hrg0 k R HkR) as HokR.
    pose proof HokR as (Hsz & Hflat & Hall & Hcont).
    pose proof (bv_unsigned_in_range _ (lden E'' (rg_base R))) as RA. unfold bv_modulus in RA.
    change (2 ^ Z.of_N 64) with two64 in RA.
    unfold havoc_rg_i. cbn [Nat.add]. destruct (fp_targets fp k) eqn:Htg.
    + (* [comment removed for export] *)
      destruct (fp_targets_in fp k Htg) as (o0 & n0 & HIn0).
      assert (Hwk : wkind (rg_kind R) = true).
      { pose proof (Hfp _ HIn0) as Hf. unfold fp_in_rw in Hf. rewrite HkR in Hf.
        apply andb_prop in Hf as [Hf _]. apply andb_prop in Hf as [Hf _]. apply andb_prop in Hf as [Hf _]. exact Hf. }
      unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont]. rewrite ?rsz_RG_eq.
      refine (conj Hsz (conj Hflat (conj _ _))).
      * intros o Ho. destruct (rg_ok_rw_byte E'' _ R HokR Hwk o Ho) as [Hr Hw].
        assert (Hx : in_rg E R (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + o))).
        { unfold in_rg. rewrite (Hbase k R HkR), (Hsize k R HkR). rewrite u_small64 by lia. lia. }
        pose proof (Hgrow k R _ HkR Hx) as Hg.
        unfold rd1, wview in *.
        set (x := Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + o)) in *.
        split.
        -- destruct (ms_mem ms' x) eqn:Hm'; [congruence|].
           destruct (ms_mem ms x) eqn:Hm; [|exact Hr].
           exfalso. apply (Hg ltac:(congruence)); first [exact Hm' | reflexivity].
        -- destruct (ms_mem ms' x) eqn:Hm'; [congruence|].
           destruct (ms_mem ms x) eqn:Hm; [|exact Hw].
           exfalso. apply (Hg ltac:(congruence)); first [exact Hm' | reflexivity].
      * intros p v Hp. destruct (fold_havoc_sub fp k (rg_cont R) p v Hp) as [Hp0 Hno].
        destruct (Hcont p v Hp0) as [Hp1 Hp2]. split; [exact Hp1|].
        pose proof (Pos2Z.is_pos p) as Hpos.
        unfold rd1 in *. rewrite (Hmem k R); [exact Hp2 | exact HkR | |].
        -- unfold in_rg. rewrite (Hbase k R HkR), (Hsize k R HkR). rewrite u_small64 by lia. lia.
        -- apply (Hnofp k R); [exact HkR | unfold in_rg; rewrite u_small64 by lia; lia |].
           intros j o n HIn Hj. rewrite u_small64 by lia. intros Hc. apply (Hno j o n HIn (eq_sym Hj)). lia.
    + (* [comment removed for export] *)
      apply (rg_ok_frame segs E'' (ms_mem ms) (ms_mem ms') R HokR).
      intros x Hx. apply (Hmem k R x HkR); [unfold in_rg; rewrite (Hbase k R HkR), (Hsize k R HkR); exact Hx |].
      apply (Hnofp k R x HkR Hx). intros j o n HIn Hj. exfalso. exact (fp_targets_notin fp k j o n Htg HIn Hj).
  - (* [comment removed for export] *)
    cbn [s_rgs havoc_call].
    assert (Hgen : forall i l, rgs_disj E'' l -> rgs_disj E'' (map_i (havoc_rg_i fp) i l)).
    { intros i l. revert i. induction l as [|R l IH]; intros i Hl; [exact I|].
      cbn [map_i rgs_disj] in *. destruct Hl as [Hh Hl]. split; [|apply IH; exact Hl].
      rewrite Forall_nth' in Hh |- *. intros k R2 Hk.
      destruct (nth_map_i_inv (havoc_rg_i fp) l (S i) k R2 Hk) as (R3 & Hk3 & ->).
      pose proof (Hh k R3 Hk3) as Hd. unfold rg_disj, havoc_rg_i in *.
      destruct (fp_targets fp i); destruct (fp_targets fp (S i + k)); cbn [rg_base rg_size]; exact Hd. }
    apply Hgen. exact Hdj0.
  - cbn [s_facts havoc_call]. exact Hf0.
  - exact Hfrm.
Qed.

#[using="Type"] Theorem havoc_call_sound2 : forall E L ms ms' (ret : Z) (keep : list positive) (fp : list fpr) (res : option lin),
  havoc_ok L fp res = true ->
  sden segs E L ms ->
  ms_pc_val ms' = Z_to_bv 64 ret -> ms_svc_pending ms' = None -> ms_resv ms' = None -> frm_zero (ms_fcsr ms') ->
  (forall r : reg, existsb (Pos.eqb (rkey r)) keep = true -> rkey r <> 11%positive \/ res = None ->
     getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  (forall l, res = Some l -> getr (ms_regs ms') (Z_to_bv 5 10) = lden E l) ->
  (forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) fp x -> ms_mem ms' x = ms_mem ms x) ->
  (forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x ->
     (rd1 segs (ms_mem ms) x <> None -> rd1 segs (ms_mem ms') x <> None) /\ (wview segs (ms_mem ms) x <> None -> wview segs (ms_mem ms') x <> None)) ->
  exists E', agree (s_next L) E E' /\ sden segs E' (havoc_call L ret keep fp res) ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E L ms ms' ret keep fp res Hok Hden Hpc Hsvc Hrv Hfrm Hkeep Hres Hmem Hgrow.
  unfold havoc_ok in Hok. apply andb_prop in Hok as [Hok Hresw]. apply andb_prop in Hok as [Hwf Hfp].
  rewrite forallb_forall in Hfp.
  set (nx := s_next L).
  set (E' := fun x : positive =>
    if (Pos.ltb nx x && Pos.ltb x (nx + 32))%bool then getr (ms_regs ms') (Z_to_bv 5 (Zpos x - Zpos nx)) else E x).
  assert (HaE : agree nx E E').
  { intros x Hx. unfold E'. rewrite (proj2 (Pos.ltb_ge _ _)) by lia. reflexivity. }
  exists E'. split; [exact HaE|].
  intros E'' Ha''. cbn [s_next havoc_call] in Ha''.
  assert (Ha0 : agree nx E E'') by (intros x Hx; rewrite (HaE x Hx); apply Ha''; lia).
  pose proof (Hden E'' Ha0) as (Hpc0 & Hsvc0 & Hrv0 & HR0 & Hrg0 & Hdj0 & Hf0 & Hfrm0).
  assert (Hfresh : forall j, (1 <= j <= 31)%nat -> E'' (nx + Pos.of_nat j)%positive = getr (ms_regs ms') (Z_to_bv 5 (Z.of_nat j))).
  { intros j Hj. rewrite <- (Ha'' (nx + Pos.of_nat j)%positive) by lia. unfold E'.
    rewrite (proj2 (Pos.ltb_lt _ _)) by lia. rewrite (proj2 (Pos.ltb_lt _ _)) by lia. cbn [andb].
    f_equal. f_equal. lia. }
  (* [comment removed for export] *)
  assert (Hbs : forall i R, nth_error (s_rgs L) i = Some R -> lden E (rg_base R) = lden E'' (rg_base R) /\ rsz E R = rsz E'' R).
  { intros i R Hi. unfold state_wf in Hwf. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [Hwf _].
    apply andb_prop in Hwf as [_ Hrw]. rewrite forallb_forall in Hrw.
    pose proof (Hrw R (nth_error_In _ _ Hi)) as HR. unfold rwf in HR. apply andb_prop in HR as [HR _]. apply andb_prop in HR as [HR HS].
    split; [exact (lden_agree nx E E'' (rg_base R) HR Ha0) | unfold rsz; rewrite (lden_agree nx E E'' (rg_size R) HS Ha0); reflexivity]. }
  assert (Hbase : forall i R, nth_error (s_rgs L) i = Some R -> lden E (rg_base R) = lden E'' (rg_base R)) by (intros i R Hi; exact (proj1 (Hbs i R Hi))).
  assert (Hsize : forall i R, nth_error (s_rgs L) i = Some R -> rsz E R = rsz E'' R) by (intros i R Hi; exact (proj2 (Hbs i R Hi))).
  (* [comment removed for export] *)
  assert (Hnofp : forall k R x, nth_error (s_rgs L) k = Some R -> in_rg E'' R x ->
             (forall j o n, In (j, o, n) fp -> j = k -> ~ (o <= bv_unsigned x - bv_unsigned (lden E'' (rg_base R)) < o + n)) ->
             ~ in_fp E (s_rgs L) fp x).
  { intros k R x Hk Hin Hno (j & o' & n & R2 & HIn & Hj & Hinj). rewrite (Hbase j R2 Hj) in Hinj.
    pose proof (Hfp _ HIn) as Hf. unfold fp_in_rw in Hf. rewrite Hj in Hf.
    apply andb_prop in Hf as [Hf Hn2]. apply andb_prop in Hf as [Hf Hn1]. apply andb_prop in Hf as [_ Ho1].
    apply Z.leb_le in Hn2. apply Z.leb_le in Hn1. apply Z.leb_le in Ho1.
    destruct (Nat.eq_dec j k) as [->|Hne].
    - rewrite Hk in Hj. injection Hj as <-. apply (Hno k o' n HIn eq_refl). lia.
    - pose proof (rgs_disj_nth E'' (s_rgs L) k j R R2 Hdj0 (fun H => Hne (eq_sym H)) Hk Hj) as Hd.
      pose proof (size_lo_sound E'' [] R2 (Forall_nil _)) as Hsl.
      unfold rg_disj, in_rg in *. lia. }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - exact Hpc.
  - exact Hsvc.
  - cbn [s_resv havoc_call rsv_ok]. exact Hrv.
  - (* [comment removed for export] *)
    intros r. cbn [s_regs havoc_call]. fold nx.
    destruct (decide (r = 0%bv)) as [->|Hr0].
    + change (rkey 0%bv) with xH. unfold rget. reflexivity.
    + destruct (Pos.eq_dec (rkey r) 11%positive) as [Ha0k|Ha0k].
      * destruct res as [l|].
        -- rewrite Ha0k, rget_set_a0_same. rewrite (rkey_a0 r Ha0k). rewrite (Hres l eq_refl).
           apply (lden_agree nx E E'' l); [exact Hresw | exact Ha0].
        -- cbn [set_a0]. destruct (rkey_succ r Hr0) as (j & Hj & Hkey). rewrite Hkey.
           rewrite (regs_havoc_get (s_regs L) keep nx j Hj).
           destruct (existsb (Pos.eqb (Pos.of_succ_nat j)) keep) eqn:Hk.
           ++ rewrite <- Hkey in Hk |- *. rewrite (Hkeep r Hk (or_intror eq_refl)). apply HR0.
           ++ cbn [lden]. unfold lvar, lden, lz. cbn [l_c l_t tsum]. unfold vz.
              rewrite Hfresh by exact Hj.
              assert (Hrj : Z_to_bv 5 (Z.of_nat j) = r).
              { pose proof (bv_unsigned_in_range _ r) as Rr. unfold bv_modulus in Rr. change (2 ^ Z.of_N 5) with 32 in Rr.
                assert (Hu : bv_unsigned r = Z.of_nat j).
                { apply (f_equal Zpos) in Hkey. unfold rkey, bv_key in Hkey. rewrite Z2Pos.id in Hkey by lia.
                  rewrite Zpos_P_of_succ_nat in Hkey. lia. }
                apply bv_eq. rewrite Z_to_bv_unsigned, <- Hu. apply bv_wrap_small. unfold bv_modulus. lia. }
              rewrite Hrj. rewrite Z.add_0_l, Z.mul_1_l, Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
      * rewrite (rget_set_a0_other _ res _ Ha0k).
        destruct (rkey_succ r Hr0) as (j & Hj & Hkey). rewrite Hkey.
        rewrite (regs_havoc_get (s_regs L) keep nx j Hj).
        destruct (existsb (Pos.eqb (Pos.of_succ_nat j)) keep) eqn:Hk.
        -- rewrite <- Hkey in Hk |- *. rewrite (Hkeep r Hk (or_introl Ha0k)). apply HR0.
        -- cbn [lden]. unfold lvar, lden, lz. cbn [l_c l_t tsum]. unfold vz.
           rewrite Hfresh by exact Hj.
           assert (Hrj : Z_to_bv 5 (Z.of_nat j) = r).
           { pose proof (bv_unsigned_in_range _ r) as Rr. unfold bv_modulus in Rr. change (2 ^ Z.of_N 5) with 32 in Rr.
             assert (Hu : bv_unsigned r = Z.of_nat j).
             { apply (f_equal Zpos) in Hkey. unfold rkey, bv_key in Hkey. rewrite Z2Pos.id in Hkey by lia.
               rewrite Zpos_P_of_succ_nat in Hkey. lia. }
             apply bv_eq. rewrite Z_to_bv_unsigned, <- Hu. apply bv_wrap_small. unfold bv_modulus. lia. }
           rewrite Hrj. rewrite Z.add_0_l, Z.mul_1_l, Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  - (* [comment removed for export] *)
    cbn [s_rgs havoc_call]. rewrite Forall_nth'. intros k R' Hk.
    destruct (nth_map_i_inv (havoc_rg_i fp) (s_rgs L) 0 k R' Hk) as (R & HkR & ->).
    rewrite Forall_nth' in Hrg0. pose proof (Hrg0 k R HkR) as HokR.
    pose proof HokR as (Hsz & Hflat & Hall & Hcont).
    pose proof (bv_unsigned_in_range _ (lden E'' (rg_base R))) as RA. unfold bv_modulus in RA.
    change (2 ^ Z.of_N 64) with two64 in RA.
    unfold havoc_rg_i. cbn [Nat.add]. destruct (fp_targets fp k) eqn:Htg.
    + (* [comment removed for export] *)
      destruct (fp_targets_in fp k Htg) as (o0 & n0 & HIn0).
      assert (Hwk : wkind (rg_kind R) = true).
      { pose proof (Hfp _ HIn0) as Hf. unfold fp_in_rw in Hf. rewrite HkR in Hf.
        apply andb_prop in Hf as [Hf _]. apply andb_prop in Hf as [Hf _]. apply andb_prop in Hf as [Hf _]. exact Hf. }
      unfold rg_ok. cbn [rg_base rg_size rg_kind rg_cont]. rewrite ?rsz_RG_eq.
      refine (conj Hsz (conj Hflat (conj _ _))).
      * intros o Ho. destruct (rg_ok_rw_byte E'' _ R HokR Hwk o Ho) as [Hr Hw].
        assert (Hx : in_rg E R (Z_to_bv 64 (bv_unsigned (lden E'' (rg_base R)) + o))).
        { unfold in_rg. rewrite (Hbase k R HkR), (Hsize k R HkR). rewrite u_small64 by lia. lia. }
        destruct (Hgrow k R _ HkR Hx) as [Hg1 Hg2]. split; [exact (Hg1 Hr) | exact (Hg2 Hw)].
      * intros p v Hp. destruct (fold_havoc_sub fp k (rg_cont R) p v Hp) as [Hp0 Hno].
        destruct (Hcont p v Hp0) as [Hp1 Hp2]. split; [exact Hp1|].
        pose proof (Pos2Z.is_pos p) as Hpos.
        unfold rd1 in *. rewrite (Hmem k R); [exact Hp2 | exact HkR | |].
        -- unfold in_rg. rewrite (Hbase k R HkR), (Hsize k R HkR). rewrite u_small64 by lia. lia.
        -- apply (Hnofp k R); [exact HkR | unfold in_rg; rewrite u_small64 by lia; lia |].
           intros j o n HIn Hj. rewrite u_small64 by lia. intros Hc. apply (Hno j o n HIn (eq_sym Hj)). lia.
    + (* [comment removed for export] *)
      apply (rg_ok_frame segs E'' (ms_mem ms) (ms_mem ms') R HokR).
      intros x Hx. apply (Hmem k R x HkR); [unfold in_rg; rewrite (Hbase k R HkR), (Hsize k R HkR); exact Hx |].
      apply (Hnofp k R x HkR Hx). intros j o n HIn Hj. exfalso. exact (fp_targets_notin fp k j o n Htg HIn Hj).
  - (* [comment removed for export] *)
    cbn [s_rgs havoc_call].
    assert (Hgen : forall i l, rgs_disj E'' l -> rgs_disj E'' (map_i (havoc_rg_i fp) i l)).
    { intros i l. revert i. induction l as [|R l IH]; intros i Hl; [exact I|].
      cbn [map_i rgs_disj] in *. destruct Hl as [Hh Hl]. split; [|apply IH; exact Hl].
      rewrite Forall_nth' in Hh |- *. intros k R2 Hk.
      destruct (nth_map_i_inv (havoc_rg_i fp) l (S i) k R2 Hk) as (R3 & Hk3 & ->).
      pose proof (Hh k R3 Hk3) as Hd. unfold rg_disj, havoc_rg_i in *.
      destruct (fp_targets fp i); destruct (fp_targets fp (S i + k)); cbn [rg_base rg_size]; exact Hd. }
    apply Hgen. exact Hdj0.
  - cbn [s_facts havoc_call]. exact Hf0.
  - exact Hfrm.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma grow_val : forall m m' x, (m x <> None -> m' x <> None) ->
  (rd1 segs m x <> None -> rd1 segs m' x <> None) /\ (wview segs m x <> None -> wview segs m' x <> None).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m m' x H. unfold rd1, wview. split.
  - destruct (m' x) eqn:Hm'; [congruence|]. destruct (m x) eqn:Hm; [|tauto]. exfalso. apply H; [congruence | reflexivity].
  - destruct (m' x) eqn:Hm'; [congruence|]. destruct (m x) eqn:Hm; [|tauto]. exfalso. apply H; [congruence | reflexivity].
Qed.


(* [comment removed for export] *)
Definition add_fact (s : sst) (f : fact) : sst := SST (s_pc s) (s_regs s) (s_rgs s) (f :: s_facts s) (s_next s) (s_resv s).

#[using="Type"] Lemma fx_add_fact : forall E s ms f, sden segs E s ms -> fwf (s_next s) f = true ->
  fact_ok E f -> sden segs E (add_fact s f) ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E s ms f H Hw Hf E' Ha. destruct (H E' Ha) as (A & B & C & D & F & G & Hfs & I).
  refine (conj A (conj B (conj C (conj D (conj F (conj G (conj _ I))))))).
  cbn [s_facts add_fact]. constructor; [|exact Hfs]. exact (fact_ok_agree _ E E' f Hw Ha Hf).
Qed.

(* [comment removed for export] *)
Definition add_var (s : sst) : sst := SST (s_pc s) (s_regs s) (s_rgs s) (s_facts s) (s_next s + 1) (s_resv s).

#[using="Type"] Lemma fx_add_var : forall E s ms (v : word), sden segs E s ms ->
  exists E', agree (s_next s) E E' /\ E' (s_next s) = v /\ sden segs E' (add_var s) ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E s ms v Hd. exists (upd E (s_next s) v). split; [apply agree_upd|]. split; [unfold upd; rewrite Pos.eqb_refl; reflexivity|].
  intros E'' Ha. cbn [s_next add_var] in Ha. apply (Hd E''). intros x Hx. rewrite <- (Ha x) by lia.
  unfold upd. destruct (Pos.eqb_spec x (s_next s)); [lia | reflexivity].
Qed.

End Havoc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Rgs.
Variable segs : list Segment.

#[using="Type"] Lemma zbv_add1 : forall x : Z, (Z_to_bv 64 x + 1)%bv = Z_to_bv 64 (x + 1).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1%bv : bv 64)) with 1. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_rdn : forall E m R o bvs,
  rg_ok segs E m R -> 0 <= o ->
  (forall j v, nth_error bvs j = Some v -> tget (okey (o + Z.of_nat j)) (rg_cont R) = Some v) ->
  rdn segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (length bvs) = Some (map (bden E) bvs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o bvs HR. revert o. induction bvs as [|v bvs IH]; intros o Ho Hb; [reflexivity|].
  cbn [length rdn map].
  destruct HR as (_ & _ & _ & Hcont).
  destruct (Hcont (okey o) v) as [_ Hrd]; [rewrite <- (Z.add_0_r o) at 1; exact (Hb O v eq_refl)|].
  rewrite okey_pos in Hrd by exact Ho. unfold rd1 in Hrd. rewrite Hrd.
  rewrite zbv_add1, <- Z.add_assoc.
  rewrite (IH (o + 1)); [reflexivity | lia |].
  intros j w Hj. replace (o + 1 + Z.of_nat j) with (o + Z.of_nat (S j)) by lia. exact (Hb (S j) w Hj).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_rdn_gb : forall E m R o n bvs,
  rg_ok segs E m R -> 0 <= o -> get_bytes (rg_cont R) o n = Some bvs ->
  rdn segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) n = Some (map (bden E) bvs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o n bvs HR Ho Hg. destruct (get_bytes_spec _ _ _ _ Hg) as [Hl Hn]. subst n.
  apply rg_rdn; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_rdn_img : forall E m R o n,
  rg_ok segs E m R -> (rg_kind R = RO \/ rg_kind R = RI) -> 0 <= o -> o + Z.of_nat n <= rsz E R ->
  (forall j, (j < n)%nat -> tget (okey (o + Z.of_nat j)) (rg_cont R) = None) ->
  rdn segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) n
  = rdn segs (fun _ => None) (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o n HR Hk. revert o. induction n as [|n IH]; intros o Ho Hn Hu; [reflexivity|].
  cbn [rdn]. pose proof HR as (_ & _ & Hall & _).
  specialize (Hall o ltac:(lia)).
  assert (He : (match m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) with Some b => Some b
                | None => seg_rom segs (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) end)
               = seg_rom segs (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o))).
  { destruct Hk as [Hk|Hk]; rewrite Hk in Hall.
    - destruct Hall as [Hm _]. rewrite Hm. reflexivity.
    - destruct Hall as [_ Hd]. specialize (Hd ltac:(rewrite <- (Z.add_0_r o) at 1; exact (Hu O ltac:(lia)))).
      unfold rd1 in Hd. exact Hd. }
  rewrite He. rewrite zbv_add1, <- Z.add_assoc.
  rewrite (IH (o + 1)); [reflexivity | lia | lia |].
  intros j Hj. replace (o + 1 + Z.of_nat j) with (o + Z.of_nat (S j)) by lia. apply Hu. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_store_ok : forall E m R o n,
  rg_ok segs E m R -> wkind (rg_kind R) = true -> 0 <= o -> o + Z.of_nat n <= rsz E R ->
  RiscvSemantics.store_ok segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) n = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o n HR Hk. revert o. induction n as [|n IH]; intros o Ho Hn; [reflexivity|].
  cbn [RiscvSemantics.store_ok].
  destruct (rg_ok_rw_byte segs E m R HR Hk o ltac:(lia)) as [_ Hw].
  destruct (RiscvSemantics.wview segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o))) eqn:Hv; [|exfalso; exact (Hw eq_refl)].
  rewrite zbv_add1, <- Z.add_assoc. apply IH; lia.
Qed.

(* [comment removed for export] *)
Definition add_rg (s : sst) (R : region) : sst := SST (s_pc s) (s_regs s) (s_rgs s ++ [R]) (s_facts s) (s_next s) (s_resv s).

#[using="Type"] Lemma rgs_disj_app1 : forall E l R, rgs_disj E l -> Forall (fun R' => rg_disj E R' R) l -> rgs_disj E (l ++ [R]).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E l R. induction l as [|x l IH]; intros Hd Hf; cbn [app rgs_disj].
  - split; [constructor | exact I].
  - destruct Hd as [Hx Hl]. apply Forall_cons_iff in Hf as [Hxr Hf]. split.
    + apply Forall_app. split; [exact Hx | constructor; [exact Hxr | constructor]].
    + exact (IH Hl Hf).
Qed.

#[using="Type"] Lemma fx_add_rg : forall E s ms R,
  sden segs E s ms -> state_wf (add_rg s R) = true ->
  rg_ok segs E (ms_mem ms) R -> Forall (fun R' => rg_disj E R' R) (s_rgs s) ->
  sden segs E (add_rg s R) ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E s ms R Hd Hw HR Hdj. apply sden0_sden; [exact Hw|].
  destruct (sden_0 _ _ _ _ Hd) as (A & B & C & D & F & G & I & J).
  refine (conj A (conj B (conj C (conj D (conj _ (conj _ (conj I J))))))); cbn [s_rgs add_rg].
  - apply Forall_app. split; [exact F | constructor; [exact HR | constructor]].
  - apply rgs_disj_app1; assumption.
Qed.

(* [comment removed for export] *)
Definition track (R : region) (o : Z) (bvs : list bval) : region :=
  RG (rg_base R) (rg_size R) (rg_kind R) (put_bytes (rg_cont R) o bvs).

#[using="Type"] Lemma rg_track : forall E m R o bvs,
  rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (length bvs) <= rsz E R ->
  (forall j v, nth_error bvs j = Some v ->
     rd1 segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + (o + Z.of_nat j))) = Some (bden E v)) ->
  rg_ok segs E m (track R o bvs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o bvs (Hsz & Hflat & Hall & Hcont) Ho Hn Hb.
  unfold rg_ok, track. cbn [rg_base rg_size rg_kind rg_cont]. rewrite ?rsz_RG_eq.
  refine (conj Hsz (conj Hflat (conj _ _))).
  - intros i Hi. specialize (Hall i Hi). destruct (rg_kind R); try exact Hall;
      (destruct Hall as [Hrw Hd]; split; [exact Hrw|]; intros Hu; apply Hd;
       rewrite put_bytes_spec in Hu by exact Ho; rewrite okey_pos in Hu by lia;
       destruct (Z.leb o i && Z.ltb i (o + Z.of_nat (length bvs)))%bool eqn:E1; [|exact Hu];
       apply andb_prop in E1 as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2;
       destruct (nth_error bvs (Z.to_nat (i - o))) eqn:Hx; [discriminate|]; apply nth_error_None in Hx; lia).
  - intros p v Hp. rewrite put_bytes_spec in Hp by exact Ho.
    destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length bvs)))%bool eqn:E1.
    + apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. split; [lia|].
      pose proof (Hb _ _ Hp) as Hx. rewrite Z2Nat.id in Hx by lia. replace (o + (Zpos p - 1 - o)) with (Zpos p - 1) in Hx by lia.
      exact Hx.
    + exact (Hcont p v Hp).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_rd1 : forall m (a : Z) n bs, 0 <= a -> a + Z.of_nat n <= two64 ->
  rdn segs m (Z_to_bv 64 a) n = Some bs ->
  forall j b, nth_error bs j = Some b -> rd1 segs m (Z_to_bv 64 (a + Z.of_nat j)) = Some b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n. revert a. induction n as [|n IH]; intros a bs Ha Hn H j b Hj; cbn [rdn] in H.
  - injection H as <-. destruct j; discriminate.
  - unfold rd1. destruct (m (Z_to_bv 64 a)) as [b0|] eqn:Hm.
    + rewrite zbv_add1 in H. destruct (rdn segs m (Z_to_bv 64 (a + 1)) n) as [r|] eqn:Hr; [|discriminate].
      injection H as <-. destruct j as [|j]; cbn [nth_error] in Hj.
      * injection Hj as <-. rewrite Z.add_0_r, Hm. reflexivity.
      * pose proof (IH (a + 1) r ltac:(lia) ltac:(lia) Hr j b Hj) as Hx. unfold rd1 in Hx.
        replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia. exact Hx.
    + destruct (seg_rom segs (Z_to_bv 64 a)) as [b0|] eqn:Hs; [|discriminate].
      rewrite zbv_add1 in H. destruct (rdn segs m (Z_to_bv 64 (a + 1)) n) as [r|] eqn:Hr; [|discriminate].
      injection H as <-. destruct j as [|j]; cbn [nth_error] in Hj.
      * injection Hj as <-. rewrite Z.add_0_r, Hm. exact Hs.
      * pose proof (IH (a + 1) r ltac:(lia) ltac:(lia) Hr j b Hj) as Hx. unfold rd1 in Hx.
        replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia. exact Hx.
Qed.

#[using="Type"] Lemma rg_track_rdn : forall E m R o bvs,
  rg_ok segs E m R -> 0 <= o -> o + Z.of_nat (length bvs) <= rsz E R ->
  rdn segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (length bvs) = Some (map (bden E) bvs) ->
  rg_ok segs E m (track R o bvs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R o bvs HR Ho Hn Hrd. apply rg_track; [exact HR | exact Ho | exact Hn |].
  pose proof HR as (_ & Hflat & _). pose proof (u_range E (rg_base R)) as RA.
  intros j v Hj. rewrite Z.add_assoc.
  apply (rdn_rd1 m _ (length bvs) (map (bden E) bvs)); [lia | lia | exact Hrd |].
  rewrite nth_error_map, Hj. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rg_sub_ok (R R' : region) (o : Z) : bool :=
  (lin_eqb (rg_base R') (laddc (rg_base R) o) && Z.leb 0 o && (Z.leb 0 (csz R') && Z.ltb o (size_lo [] R)) && Z.leb (o + csz R') (size_lo [] R) &&
   match rg_kind R, rg_kind R' with
   | RO, RO => true
   | RW, RW | RZ, RW | RI, RW => true
   | RW, RT | RZ, RT | RI, RT | RO, RT | RT, RT => true     (* [comment removed for export] *)
   | RZ, RZ | RI, RI =>
       tforall (fun p v => if (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + csz R'))%bool
                           then match tget (Z.to_pos (Zpos p - o)) (rg_cont R') with Some v' => bval_eqb v' v | None => false end
                           else true) (rg_cont R)
   | _, _ => false
   end &&
   tforall (fun p v => Z.ltb (Zpos p - 1) (csz R') &&
                       match tget (Z.to_pos (o + Zpos p)) (rg_cont R) with Some v' => bval_eqb v v' | None => false end) (rg_cont R'))%bool.

Fixpoint wk_pairs_ok (ws : list (nat * Z * Z)) : bool :=
  match ws with
  | [] => true
  | (i, o, n) :: ws' =>
      (forallb (fun '(i', o', n') => negb (Nat.eqb i i') || Z.leb (o + n) o' || Z.leb (o' + n') o) ws' && wk_pairs_ok ws')%bool
  end.

Fixpoint wk_rgs_ok (rgs rgs' : list region) (ws : list (nat * Z)) : bool :=
  match rgs', ws with
  | [], [] => true
  | R' :: rs', (i, o) :: ws' =>
      (match nth_error rgs i with Some R => rg_sub_ok R R' o | None => false end && wk_rgs_ok rgs rs' ws')%bool
  | _, _ => false
  end.

Definition weaken_ok (rgs rgs' : list region) (ws : list (nat * Z)) : bool :=
  (wk_rgs_ok rgs rgs' ws && wk_pairs_ok (List.combine ws (List.map csz rgs')))%bool.

Definition with_rgs (s : sst) (rgs : list region) : sst := SST (s_pc s) (s_regs s) rgs (s_facts s) (s_next s) (s_resv s).

#[using="Type"] Lemma rg_sub_sound : forall E m R R' o, rg_ok segs E m R -> rg_sub_ok R R' o = true ->
  rg_ok segs E m R' /\ bv_unsigned (lden E (rg_base R')) = bv_unsigned (lden E (rg_base R)) + o /\ 0 <= o /\ 0 <= rsz E R' /\ o + rsz E R' <= rsz E R
  /\ rsz E R' = csz R'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R R' o HR H. unfold rg_sub_ok in H.
  apply andb_prop in H as [H Hc']. apply andb_prop in H as [H Hk]. apply andb_prop in H as [H Hs2]. apply andb_prop in H as [H Hs1].
  apply andb_prop in H as [Hb Ho]. apply lin_eqb_eq in Hb. apply Z.leb_le in Ho. apply andb_prop in Hs1 as [Hs1 Hs1']. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs1'. apply Z.leb_le in Hs2.
  pose proof (csz_rsz E R' ltac:(lia)) as HcR'. pose proof (size_lo_sound E [] R (Forall_nil _)) as HsR.
  pose proof HR as HR0. unfold rg_ok in HR0. cbv zeta in HR0.
  destruct HR0 as (Hsz & Hflat & Hall & Hcont). pose proof (u_range E (rg_base R)) as RA.
  assert (HA : bv_unsigned (lden E (rg_base R')) = bv_unsigned (lden E (rg_base R)) + o).
  { rewrite Hb, lden_laddc. apply u_small64. lia. }
  assert (Hz : 0 <= rsz E R') by lia. assert (Hfl : bv_unsigned (lden E (rg_base R)) + o + rsz E R' <= two64) by lia.
  assert (Hle : o + rsz E R' <= rsz E R) by lia.
  refine (conj _ (conj HA (conj Ho (conj Hz (conj Hle HcR'))))).
  unfold rg_ok. cbv zeta. rewrite HA. refine (conj Hz (conj Hfl (conj _ _))).
  all: cbv zeta.
  - intros i Hi. specialize (Hall (o + i) ltac:(lia)). rewrite Z.add_assoc in Hall.
    destruct (rg_kind R) eqn:Hk0; destruct (rg_kind R') eqn:Hk1; try discriminate; try exact Hall;
      try exact (proj1 Hall); try exact (proj1 (proj1 Hall));
      try (destruct Hall as [Hm Hr]; unfold rd1; rewrite Hm; exact Hr);
      (destruct Hall as [Hrw Hd]; split; [exact Hrw|]; intros Hu; apply Hd;
       destruct (tget (okey (o + i)) (rg_cont R)) as [v|] eqn:Hv; [|reflexivity];
       pose proof (tforall_spec _ _ Hk (okey (o + i)) v Hv) as Hx; cbv beta in Hx;
       rewrite okey_pos in Hx by lia;
       replace (Z.leb o (o + i) && Z.ltb (o + i) (o + csz R'))%bool with true in Hx
         by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia);
       replace (Z.to_pos (Zpos (okey (o + i)) - o)) with (okey i) in Hx by (unfold okey; rewrite Z2Pos.id by lia; f_equal; lia);
       rewrite Hu in Hx; discriminate).
  - intros p v Hp. pose proof (tforall_spec _ _ Hc' p v Hp) as Hx. cbv beta in Hx.
    apply andb_prop in Hx as [Hlt Hx]. apply Z.ltb_lt in Hlt.
    destruct (tget (Z.to_pos (o + Zpos p)) (rg_cont R)) as [v'|] eqn:Hv'; [|discriminate].
    apply bval_eqb_eq in Hx. subst v'.
    destruct (Hcont _ _ Hv') as [Hp1 Hp2]. rewrite Z2Pos.id in Hp1, Hp2 by lia.
    split; [lia|]. rewrite <- Z.add_assoc. replace (o + (Zpos p - 1)) with (o + Zpos p - 1) by lia. exact Hp2.
Qed.

#[using="Type"] Lemma wk_rgs_nth : forall rgs rgs' ws, wk_rgs_ok rgs rgs' ws = true ->
  length ws = length rgs' /\ forall k R' i o, nth_error rgs' k = Some R' -> nth_error ws k = Some (i, o) ->
    exists R, nth_error rgs i = Some R /\ rg_sub_ok R R' o = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rgs rgs'. induction rgs' as [|R' rs IH]; intros [|[i o] ws] H; cbn [wk_rgs_ok] in H; try discriminate.
  - split; [reflexivity|]. intros [|k]; discriminate.
  - apply andb_prop in H as [H1 H2]. destruct (IH ws H2) as [Hl Hn]. split; [cbn; lia|].
    intros [|k] R0 i0 o0 Hk Hw; cbn [nth_error] in Hk, Hw.
    + injection Hk as <-. injection Hw as <- <-. destruct (nth_error rgs i) as [R|]; [|discriminate]. exists R. split; [reflexivity | exact H1].
    + exact (Hn k R0 i0 o0 Hk Hw).
Qed.

#[using="Type"] Lemma wk_pairs_nth : forall ws, wk_pairs_ok ws = true ->
  forall k k' i o n i' o' n', (k < k')%nat -> nth_error ws k = Some (i, o, n) -> nth_error ws k' = Some (i', o', n') ->
  i <> i' \/ o + n <= o' \/ o' + n' <= o.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction ws as [|[[i0 o0] n0] ws IH]; intros H k k' i o n i' o' n' Hkk Hk Hk'; [destruct k; discriminate|].
  cbn [wk_pairs_ok] in H. apply andb_prop in H as [H1 H2].
  destruct k as [|k]; destruct k' as [|k']; try lia; cbn [nth_error] in Hk, Hk'.
  - injection Hk as -> -> ->. rewrite forallb_forall in H1. pose proof (H1 _ (nth_error_In _ _ Hk')) as Hx. cbn beta iota in Hx.
    destruct (Nat.eqb i i') eqn:Hii; [| apply Nat.eqb_neq in Hii; left; exact Hii].
    cbn [negb orb] in Hx. apply orb_prop in Hx as [Hx|Hx]; apply Z.leb_le in Hx; right; [left|right]; exact Hx.
  - exact (IH H2 k k' i o n i' o' n' ltac:(lia) Hk Hk').
Qed.

#[using="Type"] Lemma rgs_disj_nth_inv : forall E rgs, (forall k k' R R', (k < k')%nat -> nth_error rgs k = Some R -> nth_error rgs k' = Some R' -> rg_disj E R R') ->
  rgs_disj E rgs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E rgs. induction rgs as [|R rs IH]; intros H; [exact I|]. cbn [rgs_disj]. split.
  - apply Forall_nth'. intros k R' Hk. exact (H O (S k) R R' ltac:(lia) eq_refl Hk).
  - apply IH. intros k k' R1 R2 Hkk H1 H2. exact (H (S k) (S k') R1 R2 ltac:(lia) H1 H2).
Qed.

#[using="Type"] Lemma nth_error_combine' : forall {A B} (l : list A) (l' : list B) k,
  nth_error (List.combine l l') k = match nth_error l k, nth_error l' k with Some a, Some b => Some (a, b) | _, _ => None end.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros A B l. induction l as [|a l IH]; intros [|b l'] [|k]; cbn; try reflexivity.
  - destruct (nth_error l k); reflexivity.
  - apply IH.
Qed.

#[using="Type"] Lemma fx_weaken : forall E s ms rgs' ws,
  sden segs E s ms -> weaken_ok (s_rgs s) rgs' ws = true -> state_wf (with_rgs s rgs') = true ->
  sden segs E (with_rgs s rgs') ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E s ms rgs' ws Hd Hw Hwf. apply sden0_sden; [exact Hwf|].
  destruct (sden_0 _ _ _ _ Hd) as (A & B & C & D & F & G & I & J).
  unfold weaken_ok in Hw. apply andb_prop in Hw as [Hr Hp].
  destruct (wk_rgs_nth _ _ _ Hr) as [Hl Hn].
  refine (conj A (conj B (conj C (conj D (conj _ (conj _ (conj I J))))))); cbn [s_rgs with_rgs].
  - apply Forall_nth'. intros k R' Hk.
    destruct (nth_error ws k) as [[i o]|] eqn:Hwk; [|apply nth_error_None in Hwk; pose proof (nth_error_Some rgs' k) as Hs; rewrite Hk in Hs; specialize (proj1 Hs ltac:(discriminate)); lia].
    destruct (Hn k R' i o Hk Hwk) as (R & HR & Hsub).
    rewrite Forall_nth' in F. exact (proj1 (rg_sub_sound E _ R R' o (F i R HR) Hsub)).
  - apply rgs_disj_nth_inv. intros k k' R1 R2 Hkk H1 H2.
    destruct (nth_error ws k) as [[i o]|] eqn:Hw1; [|apply nth_error_None in Hw1; pose proof (nth_error_Some rgs' k) as Hs; rewrite H1 in Hs; specialize (proj1 Hs ltac:(discriminate)); lia].
    destruct (nth_error ws k') as [[i' o']|] eqn:Hw2; [|apply nth_error_None in Hw2; pose proof (nth_error_Some rgs' k') as Hs; rewrite H2 in Hs; specialize (proj1 Hs ltac:(discriminate)); lia].
    destruct (Hn k R1 i o H1 Hw1) as (P1 & HP1 & Hs1). destruct (Hn k' R2 i' o' H2 Hw2) as (P2 & HP2 & Hs2).
    rewrite Forall_nth' in F.
    destruct (rg_sub_sound E _ P1 R1 o (F i P1 HP1) Hs1) as (_ & HA1 & Ho1 & Hz1 & Hn1 & Hq1).
    destruct (rg_sub_sound E _ P2 R2 o' (F i' P2 HP2) Hs2) as (_ & HA2 & Ho2 & Hz2 & Hn2 & Hq2).
    assert (Hc1 : nth_error (List.combine ws (List.map csz rgs')) k = Some (i, o, csz R1)).
    { rewrite nth_error_combine', Hw1, nth_error_map, H1. reflexivity. }
    assert (Hc2 : nth_error (List.combine ws (List.map csz rgs')) k' = Some (i', o', csz R2)).
    { rewrite nth_error_combine', Hw2, nth_error_map, H2. reflexivity. }
    destruct (wk_pairs_nth _ Hp k k' i o (csz R1) i' o' (csz R2) Hkk Hc1 Hc2) as [Hii|Hoo].
    + pose proof (rgs_disj_nth E (s_rgs s) i i' P1 P2 G Hii HP1 HP2) as Hd12. unfold rg_disj in *. rewrite HA1, HA2. lia.
    + destruct (Nat.eq_dec i i') as [->|Hne].
      * rewrite HP1 in HP2. injection HP2 as <-. unfold rg_disj. rewrite HA1, HA2. lia.
      * pose proof (rgs_disj_nth E (s_rgs s) i i' P1 P2 G Hne HP1 HP2) as Hd12. unfold rg_disj in *. rewrite HA1, HA2. lia.
Qed.

(* [comment removed for export] *)
Definition upd_rg (s : sst) (i : nat) (R : region) : sst := SST (s_pc s) (s_regs s) (upd_nth (s_rgs s) i R) (s_facts s) (s_next s) (s_resv s).

#[using="Type"] Lemma fx_upd_rg : forall E s ms i R R',
  sden segs E s ms -> nth_error (s_rgs s) i = Some R -> rg_base R' = rg_base R -> rg_size R' = rg_size R ->
  rg_ok segs E (ms_mem ms) R' -> state_wf (upd_rg s i R') = true -> sden segs E (upd_rg s i R') ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E s ms i R R' Hd Hi Hb Hs HR Hw. apply sden0_sden; [exact Hw|].
  destruct (sden_0 _ _ _ _ Hd) as (A & B & C & D & F & G & I & J).
  refine (conj A (conj B (conj C (conj D (conj _ (conj _ (conj I J))))))); cbn [s_rgs upd_rg].
  - rewrite Forall_nth' in F |- *. intros k R0 Hk. destruct (Nat.eq_dec k i) as [->|Hne].
    + rewrite (nth_upd_same _ i R' R Hi) in Hk. injection Hk as <-. exact HR.
    + rewrite nth_upd_other in Hk by lia. exact (F k R0 Hk).
  - eapply rgs_disj_upd; [exact Hi | exact Hb | exact Hs | exact G].
Qed.

End Rgs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rk_find (known : list (nat * lin)) (j : nat) : option lin :=
  match List.find (fun kl : nat * lin => Nat.eqb (fst kl) j) known with Some (_, l) => Some l | None => None end.

Definition rpat_ok (R : tree lin) (known : list (nat * lin)) (base : positive) : bool :=
  forallb (fun j => lin_eqb (rget R (Pos.of_succ_nat j))
                            (match rk_find known j with Some l => l | None => lvar (base + Pos.of_nat j) end)) (seq 1 31).

Lemma regs_ok_pat : forall E R regs known base, rpat_ok R known base = true ->
  (forall j, (1 <= j <= 31)%nat -> rk_find known j = None -> E (base + Pos.of_nat j)%positive = getr regs (Z_to_bv 5 (Z.of_nat j))) ->
  (forall j l, (1 <= j <= 31)%nat -> rk_find known j = Some l -> getr regs (Z_to_bv 5 (Z.of_nat j)) = lden E l) ->
  regs_ok E R regs.
Proof.
  intros E R regs known base Hok Hu Hk r.
  destruct (decide (r = 0%bv)) as [->|Hr0].
  - change (rkey 0%bv) with xH. unfold rget. unfold getr. rewrite bv_eqb_refl. reflexivity.
  - destruct (rkey_succ r Hr0) as (j & Hj & Hkey). rewrite Hkey.
    unfold rpat_ok in Hok. rewrite forallb_forall in Hok.
    pose proof (Hok j ltac:(apply in_seq; lia)) as Hx. apply lin_eqb_eq in Hx. rewrite Hx.
    assert (Hrj : r = Z_to_bv 5 (Z.of_nat j)).
    { pose proof (bv_unsigned_in_range _ r) as Rr. unfold bv_modulus in Rr. change (2 ^ Z.of_N 5) with 32 in Rr.
      assert (Hu0 : bv_unsigned r = Z.of_nat j).
      { apply (f_equal Zpos) in Hkey. unfold rkey, bv_key in Hkey. rewrite Z2Pos.id in Hkey by lia.
        rewrite Zpos_P_of_succ_nat in Hkey. lia. }
      apply bv_eq. rewrite Z_to_bv_unsigned, <- Hu0. symmetry. apply bv_wrap_small. unfold bv_modulus. lia. }
    rewrite Hrj. destruct (rk_find known j) as [l|] eqn:Hf.
    + exact (Hk j l Hj Hf).
    + unfold lvar, lden, lz. cbn [l_c l_t tsum]. unfold vz. rewrite (Hu j Hj Hf).
      rewrite Z.add_0_l, Z.mul_1_l, Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bvs_of (v : lin) (n : nat) : list bval := List.map (fun j => BV v (Z.of_nat j)) (seq 0 n).

Lemma shiftr_Z_to_le : forall n z j, (j < n)%nat ->
  nth_error (Z_to_le_bytes n z) j = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat j))).
Proof.
  induction n as [|n IH]; intros z j Hj; [lia|]. destruct j as [|j]; cbn [Z_to_le_bytes nth_error].
  - rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - rewrite (IH (Z.shiftr z 8) j ltac:(lia)). rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma bvs_of_den_lin : forall E l n,
  List.map (bden E) (bvs_of l n) = Z_to_le_bytes n (bv_unsigned (lden E l)).
Proof.
  intros E l n. apply nth_error_ext. intros j.
  destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
  - rewrite (shiftr_Z_to_le n _ j Hj). unfold bvs_of. rewrite nth_error_map, nth_error_map.
    rewrite nth_error_seq. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj).
    cbn [option_map bden]. reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite length_map; unfold bvs_of; rewrite length_map, length_seq; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite length_Z_to_le_bytes; lia). reflexivity.
Qed.

Lemma bvs_of_den : forall E x n, (n <= 8)%nat ->
  List.map (bden E) (bvs_of (lvar x) n) = Z_to_le_bytes n (bv_unsigned (E x)).
Proof.
  intros E x n Hn. apply nth_error_ext. intros j.
  destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
  - rewrite (shiftr_Z_to_le n _ j Hj). unfold bvs_of. rewrite nth_error_map, nth_error_map.
    rewrite nth_error_seq. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj).
    cbn [option_map bden]. rewrite lden_lvar. reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite length_map; unfold bvs_of; rewrite length_map, length_seq; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite length_Z_to_le_bytes; lia). reflexivity.
Qed.

Section Hand.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_rw_empty_ok : forall E m base size,
  0 <= size -> bv_unsigned (lden E base) + size < two64 ->
  (forall i, 0 <= i < size -> m (Z_to_bv 64 (bv_unsigned (lden E base) + i)) <> None) ->
  rg_ok segs E m (RGz base size RW TEmpty).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m base size Hs Hf Hm. pose proof (u_range E base) as RB.
  unfold rg_ok. rewrite (rsz_RGz E base size RW TEmpty ltac:(lia)). cbv zeta. cbn [RGz rg_base rg_size rg_kind rg_cont].
  assert (Hf' : bv_unsigned (lden E base) + size <= two64) by lia.
  refine (conj Hs (conj Hf' (conj _ _))).
  - intros i Hi. specialize (Hm i Hi). unfold rd1, RiscvSemantics.wview.
    destruct (m (Z_to_bv 64 (bv_unsigned (lden E base) + i))); [split; discriminate | exfalso; exact (Hm eq_refl)].
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

(* [comment removed for export] *)
Definition img_ro_ok (lo : Z) (n : nat) : bool :=
  forallb (fun i => match seg_rom segs (Z_to_bv 64 (lo + Z.of_nat i)) with Some _ => true | None => false end) (seq 0 n).
Definition img_rw_ok (lo : Z) (n : nat) : bool :=
  forallb (fun i => match seg_rom segs (Z_to_bv 64 (lo + Z.of_nat i)) with Some _ => true | None => false end &&
                    match RiscvSemantics.wview segs (fun _ => None) (Z_to_bv 64 (lo + Z.of_nat i)) with Some _ => true | None => false end)%bool
          (seq 0 n).

#[using="Type"] Lemma rg_img_ro : forall E m lo n,
  0 <= lo < two64 -> lo + Z.of_nat n < two64 -> img_ro_ok lo n = true ->
  (forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (lo + i)) = None) ->
  rg_ok segs E m (RGz (lconst lo) (Z.of_nat n) RO TEmpty).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m lo n Hlo Hhi Hc Hm. unfold rg_ok. rewrite (rsz_RGz E (lconst lo) (Z.of_nat n) RO TEmpty ltac:(lia)).
  cbv zeta. cbn [RGz rg_base rg_size rg_kind rg_cont].
  assert (HA : bv_unsigned (lden E (lconst lo)) = lo).
  { unfold lconst, lden, lz. cbn [l_c l_t tsum]. rewrite Z.add_0_r, w64_mod, Z.mod_small by lia.
    apply u_small64. lia. }
  rewrite HA. assert (Hz : 0 <= Z.of_nat n) by lia. assert (Hhi' : lo + Z.of_nat n <= two64) by lia. refine (conj Hz (conj Hhi' (conj _ _))).
  - intros i Hi. split; [exact (Hm i Hi)|].
    unfold img_ro_ok in Hc. rewrite forallb_forall in Hc. pose proof (Hc (Z.to_nat i) ltac:(apply in_seq; lia)) as Hx.
    rewrite Z2Nat.id in Hx by lia. destruct (seg_rom segs _); [discriminate | discriminate].
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

#[using="Type"] Lemma wview_none : forall m x, m x = None -> RiscvSemantics.wview segs m x = RiscvSemantics.wview segs (fun _ => None) x.
Proof. LiaFast.lf_pins LiaFast.u0. intros m x H. unfold RiscvSemantics.wview. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma rg_img_ri : forall E m lo n t,
  0 <= lo < two64 -> lo + Z.of_nat n < two64 -> img_rw_ok lo n = true ->
  (forall i, 0 <= i < Z.of_nat n -> tget (okey i) t = None -> m (Z_to_bv 64 (lo + i)) = None) ->
  (forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (lo + i)) <> None \/ m (Z_to_bv 64 (lo + i)) = None) ->
  (forall p v, tget p t = Some v -> Zpos p - 1 < Z.of_nat n /\ rd1 segs m (Z_to_bv 64 (lo + (Zpos p - 1))) = Some (bden E v)) ->
  rg_ok segs E m (RGz (lconst lo) (Z.of_nat n) RI t).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m lo n t Hlo Hhi Hc Hm _ Ht. unfold rg_ok. rewrite (rsz_RGz E (lconst lo) (Z.of_nat n) RI t ltac:(lia)).
  cbv zeta. cbn [RGz rg_base rg_size rg_kind rg_cont].
  assert (HA : bv_unsigned (lden E (lconst lo)) = lo).
  { unfold lconst, lden, lz. cbn [l_c l_t tsum]. rewrite Z.add_0_r, w64_mod, Z.mod_small by lia.
    apply u_small64. lia. }
  rewrite HA. assert (Hz : 0 <= Z.of_nat n) by lia. assert (Hhi' : lo + Z.of_nat n <= two64) by lia. refine (conj Hz (conj Hhi' (conj _ Ht))).
  intros i Hi.
  unfold img_rw_ok in Hc. rewrite forallb_forall in Hc. pose proof (Hc (Z.to_nat i) ltac:(apply in_seq; lia)) as Hx.
  rewrite Z2Nat.id in Hx by lia. apply andb_prop in Hx as [Hr Hw].
  destruct (tget (okey i) t) as [v|] eqn:Hv.
  - destruct (Ht (okey i) v Hv) as [_ Hrd]. rewrite okey_pos in Hrd by lia.
    split; [split|].
    + rewrite Hrd. discriminate.
    + destruct (m (Z_to_bv 64 (lo + i))) eqn:Hmx.
      * unfold RiscvSemantics.wview. rewrite Hmx. discriminate.
      * rewrite (wview_none m _ Hmx). destruct (RiscvSemantics.wview segs (fun _ => None) _); [discriminate | discriminate Hw].
    + intros Hc0. discriminate.
  - pose proof (Hm i Hi Hv) as Hm0. unfold rd1. rewrite Hm0.
    split; [split|].
    + destruct (seg_rom segs _); [discriminate | discriminate].
    + rewrite (wview_none m _ Hm0). destruct (RiscvSemantics.wview segs (fun _ => None) _); [discriminate | discriminate Hw].
    + intros _. reflexivity.
Qed.

End Hand.

(* [comment removed for export] *)
Lemma find_segment_above : forall segs L a n,
  forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) L) segs = true -> L <= a -> 0 < n ->
  find_segment segs a n = None.
Proof.
  induction segs as [|seg rest IH]; intros L a n H Ha Hn; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  cbn [find_segment]. rewrite (proj2 (andb_false_iff _ _)); [exact (IH L a n H2 Ha Hn)|].
  right. apply Z.leb_gt. lia.
Qed.

Lemma seg_rom_above : forall segs L (a : word),
  forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) L) segs = true -> L <= bv_unsigned a ->
  seg_rom segs a = None.
Proof.
  intros segs L a H Ha. unfold seg_rom, memory_read. rewrite (find_segment_above segs L _ _ H Ha) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_overlay : forall segs L m (a : Z) n bs,
  forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) L) segs = true -> 0 <= L <= a -> a + Z.of_nat n <= two64 ->
  rdn segs m (Z_to_bv 64 a) n = Some bs ->
  forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (a + i)) = nth_error bs (Z.to_nat i).
Proof.
  intros segs L m a n bs HL Ha Hn Hr i Hi.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hb.
  - pose proof (rdn_rd1 segs m a n bs ltac:(lia) Hn Hr (Z.to_nat i) b Hb) as H. rewrite Z2Nat.id in H by lia.
    unfold rd1 in H. destruct (m (Z_to_bv 64 (a + i))) as [b'|] eqn:Hm; [exact H|].
    rewrite (seg_rom_above segs L _ HL) in H; [discriminate|]. rewrite u_small64 by lia. lia.
  - exfalso. apply nth_error_None in Hb.
    assert (Hl : length bs = n).
    { clear -Hr. revert a bs Hr. induction n as [|n IH]; intros a bs Hr; cbn [rdn] in Hr; [injection Hr as <-; reflexivity|].
      destruct (match m (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end); [|discriminate].
      rewrite zbv_add1 in Hr. destruct (rdn segs m (Z_to_bv 64 (a + 1)) n) as [r|] eqn:Hr'; [|discriminate].
      injection Hr as <-. cbn [length]. f_equal. exact (IH (a + 1) r Hr'). }
    lia.
Qed.

Lemma rdn_app_some : forall segs m (a : Z) n1 n2 bs1 bs2, 0 <= a -> a + Z.of_nat n1 <= two64 ->
  rdn segs m (Z_to_bv 64 a) n1 = Some bs1 -> rdn segs m (Z_to_bv 64 (a + Z.of_nat n1)) n2 = Some bs2 ->
  rdn segs m (Z_to_bv 64 a) (n1 + n2) = Some (bs1 ++ bs2).
Proof.
  intros segs m a n1. revert a. induction n1 as [|n1 IH]; intros a n2 bs1 bs2 Ha Hn H1 H2.
  - cbn [rdn] in H1. injection H1 as <-. rewrite Z.add_0_r in H2. exact H2.
  - cbn [rdn Nat.add] in *. destruct (match m (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) as [b|]; [|discriminate].
    rewrite zbv_add1 in *. destruct (rdn segs m (Z_to_bv 64 (a + 1)) n1) as [r|] eqn:Hr; [|discriminate].
    injection H1 as <-. rewrite (IH (a + 1) n2 r bs2 ltac:(lia) ltac:(lia) Hr ltac:(replace (a + 1 + Z.of_nat n1) with (a + Z.of_nat (S n1)) by lia; exact H2)).
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rg_rw_img : forall segs E m lo n,
  0 <= lo < two64 -> lo + Z.of_nat n < two64 -> img_rw_ok segs lo n = true ->
  rg_ok segs E m (RGz (lconst lo) (Z.of_nat n) RW TEmpty).
Proof.
  intros segs E m lo n Hlo Hhi Hc. unfold rg_ok. rewrite (rsz_RGz E (lconst lo) (Z.of_nat n) RW TEmpty ltac:(lia)).
  cbv zeta. cbn [RGz rg_base rg_size rg_kind rg_cont].
  assert (HA : bv_unsigned (lden E (lconst lo)) = lo).
  { unfold lconst, lden, lz. cbn [l_c l_t tsum]. rewrite Z.add_0_r, w64_mod, Z.mod_small by lia.
    apply u_small64. lia. }
  rewrite HA. assert (Hz : 0 <= Z.of_nat n) by lia. assert (Hhi' : lo + Z.of_nat n <= two64) by lia. refine (conj Hz (conj Hhi' (conj _ _))).
  - intros i Hi. unfold img_rw_ok in Hc. rewrite forallb_forall in Hc. pose proof (Hc (Z.to_nat i) ltac:(apply in_seq; lia)) as Hx.
    rewrite Z2Nat.id in Hx by lia. apply andb_prop in Hx as [Hr Hw]. unfold rd1.
    destruct (m (Z_to_bv 64 (lo + i))) eqn:Hm.
    + split; [discriminate|]. unfold RiscvSemantics.wview. rewrite Hm. discriminate.
    + split; [destruct (seg_rom segs _); [discriminate | discriminate Hr]|].
      rewrite (wview_none segs m _ Hm). destruct (RiscvSemantics.wview segs (fun _ => None) _); [discriminate | discriminate Hw].
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

(* [comment removed for export] *)
Lemma rgs_disj_app_sep : forall E l1 l2 M, rgs_disj E l1 -> rgs_disj E l2 ->
  Forall (fun R => M <= bv_unsigned (lden E (rg_base R))) l1 ->
  Forall (fun R => bv_unsigned (lden E (rg_base R)) + rsz E R <= M) l2 -> rgs_disj E (l1 ++ l2).
Proof.
  intros E l1 l2 M. induction l1 as [|R l1 IH]; intros H1 H2 F1 F2; [exact H2|].
  cbn [app rgs_disj] in *. destruct H1 as [HR H1]. apply Forall_cons_iff in F1 as [FR F1]. split.
  - apply Forall_app. split; [exact HR|]. rewrite Forall_forall in F2 |- *. intros R' HR'. specialize (F2 R' HR').
    unfold rg_disj. lia.
  - exact (IH H1 H2 F1 F2).
Qed.

(* [comment removed for export] *)
Definition cbase (R : region) : option Z := match rg_base R with LIN c [] => Some c | _ => None end.
Fixpoint cdisj_ok (rgs : list region) : bool :=
  match rgs with
  | [] => true
  | R :: rs => (match cbase R with
                | Some a => (Z.leb 0 (csz R) && forallb (fun R' => match cbase R' with Some a' => (Z.leb 0 (csz R') && (Z.leb (a + csz R) a' || Z.leb (a' + csz R') a))%bool | None => false end) rs)%bool
                | None => false end && cdisj_ok rs)%bool
  end.

Lemma cbase_den : forall E R a, cbase R = Some a -> 0 <= a < two64 -> bv_unsigned (lden E (rg_base R)) = a.
Proof.
  intros E [[c t] sz k cont] a H Ha. cbn [cbase rg_base] in *. destruct t; [|discriminate]. injection H as <-.
  unfold lden, lz. cbn [l_c l_t tsum]. rewrite Z.add_0_r. apply u_small64. exact Ha.
Qed.

Lemma cdisj_sound : forall E rgs, cdisj_ok rgs = true -> Forall (fun R => exists a, cbase R = Some a /\ 0 <= a < two64) rgs ->
  rgs_disj E rgs.
Proof.
  intros E rgs. induction rgs as [|R rs IH]; intros H F; [exact I|].
  cbn [cdisj_ok rgs_disj] in *. apply andb_prop in H as [H1 H2]. apply Forall_cons_iff in F as [(a & Ha & Ra) F].
  split; [|exact (IH H2 F)]. rewrite Ha in H1. apply andb_prop in H1 as [H0 H1]. apply Z.leb_le in H0.
  rewrite forallb_forall in H1. rewrite Forall_forall in F |- *.
  intros R' HR'. specialize (H1 R' HR'). destruct (F R' HR') as (a' & Ha' & Ra'). rewrite Ha' in H1.
  apply andb_prop in H1 as [H0' H1]. apply Z.leb_le in H0'.
  unfold rg_disj. rewrite (cbase_den E R a Ha Ra), (cbase_den E R' a' Ha' Ra'), (csz_rsz E R H0), (csz_rsz E R' H0').
  apply orb_prop in H1 as [H1|H1]; apply Z.leb_le in H1; lia.
Qed.

(* [comment removed for export] *)
Lemma getr_leaf : forall segs E L ms (r : reg) l, sden segs E L ms -> rget (s_regs L) (rkey r) = l -> getr (ms_regs ms) r = lden E l.
Proof. intros segs E L ms r l H Hl. rewrite (sden_getr segs E L ms H r), Hl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_ext_rd1 : forall segs m1 m2 (a : Z) n, 0 <= a -> a + Z.of_nat n <= two64 ->
  (forall i, 0 <= i < Z.of_nat n -> rd1 segs m1 (Z_to_bv 64 (a + i)) = rd1 segs m2 (Z_to_bv 64 (a + i))) ->
  rdn segs m1 (Z_to_bv 64 a) n = rdn segs m2 (Z_to_bv 64 a) n.
Proof.
  intros segs m1 m2 a n. revert a. induction n as [|n IH]; intros a Ha Hn H; [reflexivity|].
  cbn [rdn]. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rd1 in H0. rewrite H0.
  rewrite zbv_add1, (IH (a + 1)); [reflexivity | lia | lia |].
  intros i Hi. rewrite <- Z.add_assoc. apply H. lia.
Qed.

Lemma lden_lconst : forall E c, lden E (lconst c) = Z_to_bv 64 c.
Proof.
  intros E c. apply bv_eq. unfold lconst, lden, lz. cbn [l_c l_t tsum]. rewrite Z.add_0_r, w64_mod.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, two64. change (2 ^ Z.of_N 64) with 18446744073709551616.
  apply Z.mod_mod. lia.
Qed.

Lemma getr_leaf_c : forall segs E L ms (r : reg) c, sden segs E L ms -> rget (s_regs L) (rkey r) = lconst c ->
  getr (ms_regs ms) r = Z_to_bv 64 c.
Proof. intros segs E L ms r c H Hl. rewrite (getr_leaf segs E L ms r _ H Hl). apply lden_lconst. Qed.

Lemma sden_tracked : forall segs E L ms i R o v, sden segs E L ms -> nth_error (s_rgs L) i = Some R -> 0 <= o ->
  tget (okey o) (rg_cont R) = Some v -> rd1 segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) = Some (bden E v).
Proof.
  intros segs E L ms i R o v H Hi Ho Ht. pose proof (sden_rg segs E L ms i R H Hi) as (_ & _ & _ & Hc).
  destruct (Hc _ _ Ht) as [_ Hr]. rewrite okey_pos in Hr by exact Ho. exact Hr.
Qed.

(* [comment removed for export] *)
Fixpoint rekey_acc (t : tree bval) (o : Z) (k : nat) (acc : tree bval) : tree bval :=
  match k with
  | O => acc
  | S k' => rekey_acc t o k' (match tget (okey (o + Z.of_nat k')) t with Some v => tset (okey (Z.of_nat k')) v acc | None => acc end)
  end.
Definition below_cont (t : tree bval) (n : Z) : tree bval := tfilter (fun p => Z.ltb (Zpos p - 1) n) t.
(* [comment removed for export] *)
Definition split_rgs (rgs : list region) (i : nat) (o1 o2 : Z) : list region :=
  match nth_error rgs i with
  | Some R => upd_nth rgs i (RGz (rg_base R) o1 RW (below_cont (rg_cont R) o1)) ++
              [RGz (laddc (rg_base R) o2) (csz R - o2) RW (rekey_acc (rg_cont R) o2 (Z.to_nat (csz R - o2)) TEmpty)]
  | None => rgs
  end.
Definition split_ws (n : nat) (i : nat) (o2 : Z) : list (nat * Z) := List.map (fun k => (k, 0)) (seq 0 n) ++ [(i, o2)].

Lemma u_lconst : forall E0 c, 0 <= c < 2^64 -> bv_unsigned (lden E0 (lconst c)) = c.
Proof.
  intros E0 c Hc. unfold lconst, lden, lz. cbn [l_c l_t tsum]. rewrite Z.add_0_r, w64_mod, Z.mod_small by (unfold two64; lia).
  apply u_small64. unfold two64; lia.
Qed.

(* [comment removed for export] *)
Lemma t_emit_app : forall (l1 l2 : list event) (T : TSet),
  t_eq (t_emit l1 (t_emit l2 T)) (t_emit (l1 ++ l2) T).
Proof.
  intros l1 l2 T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. split; [apply app_assoc | exact HT].
  - intros [Hp | (tr' & -> & HT)].
    + destruct (is_prefix_app_split l1 l2 tr Hp) as [Hp1 | (b' & -> & Hp2)]; [left; exact Hp1|].
      right. exists b'. split; [reflexivity | left; exact Hp2].
    + right. exists (l2 ++ tr'). split; [symmetry; apply app_assoc|]. right. exists tr'. split; [reflexivity | exact HT].
Qed.

Lemma outside_nth : forall E rgs x i R, outside E rgs x -> nth_error rgs i = Some R ->
  bv_unsigned x < bv_unsigned (lden E (rg_base R)) \/ bv_unsigned (lden E (rg_base R)) + rsz E R <= bv_unsigned x.
Proof.
  intros E rgs x i R H Hi. unfold outside in H. rewrite Forall_forall in H. apply H. eapply nth_error_In. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma outside_nth_c : forall E rgs x i b n k c, outside E rgs x -> nth_error rgs i = Some (RGz b n k c) -> 0 <= n < two64 ->
  bv_unsigned x < bv_unsigned (lden E b) \/ bv_unsigned (lden E b) + n <= bv_unsigned x.
Proof.
  intros E rgs x i b n k c H Hi Hn. pose proof (outside_nth E rgs x i _ H Hi) as X. rewrite (rsz_RGz E b n k c Hn) in X. exact X.
Qed.


(* [comment removed for export] *)
Lemma u_lin0 : forall E c, 0 <= c < 2^64 -> bv_unsigned (lden E (LIN c [])) = c.
Proof. intros E c Hc. unfold lden, lz. cbn [l_c l_t tsum]. rewrite Z.add_0_r. apply u_small64. unfold two64; lia. Qed.

Lemma u_lin1 : forall E c x, bv_unsigned (lden E (LIN c [(x, 1)])) = (c + bv_unsigned (E x)) mod 2^64.
Proof.
  intros E c x. unfold lden, lz. cbn [l_c l_t tsum]. unfold vz. rewrite Z.mul_1_l, Z.add_0_r, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma u_lin2 : forall E c x y, bv_unsigned (lden E (LIN c [(x, 1); (y, 1)])) = (c + bv_unsigned (E x) + bv_unsigned (E y)) mod 2^64.
Proof.
  intros E c x y. unfold lden, lz. cbn [l_c l_t tsum]. unfold vz. rewrite !Z.mul_1_l, Z.add_0_r, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma rg_ok_refresh : forall segs E m m' R o bvs,
  rg_ok segs E m R -> wkind (rg_kind R) = true -> 0 <= o -> o + Z.of_nat (length bvs) <= rsz E R ->
  (forall i, 0 <= i < rsz E R -> ~ (o <= i < o + Z.of_nat (length bvs)) ->
     m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i))) ->
  (forall i, 0 <= i < rsz E R -> m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None ->
     m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None) ->
  rdn segs m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o)) (length bvs) = Some (List.map (bden E) bvs) ->
  rg_ok segs E m' (track R o bvs).
Proof.
  intros segs E m m' R o bvs HR Hk Ho Hn Hun Hgr Hrd.
  pose proof HR as HR0. unfold rg_ok in HR0. cbv zeta in HR0. destruct HR0 as (Hsz & Hflat & Hall & Hcont).
  pose proof (u_range E (rg_base R)) as RA.
  unfold rg_ok, track. cbv zeta. cbn [rg_base rg_size rg_kind rg_cont]. rewrite ?rsz_RG_eq.
  refine (conj Hsz (conj Hflat (conj _ _))).
  - intros i Hi. specialize (Hall i Hi).
    assert (RW' : rd1 segs m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None /\
                  RiscvSemantics.wview segs m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) <> None).
    { destruct (rg_ok_rw_byte segs E m R HR Hk i Hi) as [Hr Hw]. pose proof (Hgr i Hi) as G.
      unfold rd1, RiscvSemantics.wview in *.
      destruct (m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i))) eqn:Hm'; [split; discriminate|].
      destruct (m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i))) eqn:Hm; [exfalso; apply G; [discriminate | reflexivity]|].
      exact (conj Hr Hw). }
    destruct (rg_kind R) eqn:Hkd; [exact RW' | discriminate | | | discriminate ];
      (split; [exact RW'|]; intros Hu; rewrite put_bytes_spec in Hu by exact Ho; rewrite okey_pos in Hu by lia;
       destruct (Z.leb o i && Z.ltb i (o + Z.of_nat (length bvs)))%bool eqn:Hin;
       [ apply andb_prop in Hin as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2;
         destruct (nth_error bvs (Z.to_nat (i - o))) eqn:Hx; [discriminate|]; apply nth_error_None in Hx; lia
       | apply andb_false_iff in Hin; unfold rd1; rewrite Hun; [ | lia | destruct Hin as [Hin|Hin]; [apply Z.leb_gt in Hin | apply Z.ltb_ge in Hin]; lia];
         destruct Hall as [_ Hd]; unfold rd1 in Hd; exact (Hd Hu) ]).
  - intros p v Hp. rewrite put_bytes_spec in Hp by exact Ho.
    destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length bvs)))%bool eqn:Hin.
    + apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. split; [lia|].
      assert (Hb : nth_error (List.map (bden E) bvs) (Z.to_nat (Zpos p - 1 - o)) = Some (bden E v)) by (rewrite nth_error_map, Hp; reflexivity).
      pose proof (rdn_rd1 segs m' (bv_unsigned (lden E (rg_base R)) + o) (length bvs) _ ltac:(lia) ltac:(lia) Hrd _ _ Hb) as X.
      rewrite Z2Nat.id in X by lia. replace (bv_unsigned (lden E (rg_base R)) + o + (Zpos p - 1 - o)) with (bv_unsigned (lden E (rg_base R)) + (Zpos p - 1)) in X by lia.
      exact X.
    + destruct (Hcont p v Hp) as [Hp1 Hp2]. split; [exact Hp1|]. unfold rd1 in *. rewrite Hun; [exact Hp2 | pose proof (Pos2Z.is_pos p); lia |].
      apply andb_false_iff in Hin. destruct Hin as [Hin|Hin]; [apply Z.leb_gt in Hin | apply Z.ltb_ge in Hin]; lia.
Qed.

Lemma t_emit_cong : forall (l : list event) (T T' : TSet), t_eq T T' -> t_eq (t_emit l T) (t_emit l T').
Proof.
  intros l T T' H tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
  - intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
Qed.

(* [comment removed for export] *)
Lemma t_emit_exit_tail : forall (l : list event) (c : word) fs,
  t_eq (t_emit (l ++ []) (t_emit [] (t_exit c fs))) (t_emit l (t_exit c fs)).
Proof.
  intros l c fs. rewrite app_nil_r. apply t_emit_cong. apply t_emit_nil_eq. apply t_emit_has_nil.
Qed.
