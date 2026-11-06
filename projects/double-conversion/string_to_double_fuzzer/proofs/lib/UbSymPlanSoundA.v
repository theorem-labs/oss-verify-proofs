(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes
  MmapSim AllocSim FileSim AgentLib ShapeLaws Spec LibWritev RefNodes.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan UbSymSlots.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIface MemSplit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module SPSA.
Import SX2. Import SX2S. Import SP. Import SSL.

#[local] Abbreviation RSEGS := ImgU.M.loaded_segments.
Section FPW_1. Context {fx : PropExec.FPState}.


Section NX0.
Variable nx0 : nat.
(* [comment removed for export] *)
Variable IT : itab.
Hypothesis IT_ok : itab_sound RSEGS IT.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Wz (fd : Z) (bs : list Z) : list event := map (fun z => WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 z)) bs.

Fixpoint sd (E : env) (fs : Fs.Fs) (s : shape) : TSet :=
  match s with
  | SNil => t_nil
  | SExit c => t_exit (Z_to_bv 64 c) fs
  | SEmit fd bs s' => t_emit (Wz fd bs) (sd E fs s')
  | SAlt2 a b => t_alt2 (sd E fs a) (sd E fs b)
  | SCase e mid s1 s2 => if (bv_unsigned (edenot E e) <=? mid)%Z then sd E fs s1 else sd E fs s2
  end.

Lemma sd_has_nil : forall E fs s, sd E fs s [].
Proof.
  intros E fs s. induction s; cbn [sd].
  - reflexivity.
  - apply t_exit_has_nil.
  - apply t_emit_has_nil.
  - apply t_alt2_has_nil_l. exact IHs1.
  - destruct (_ <=? _)%Z; assumption.
Qed.

Lemma salt2_sound : forall E fs a b,
  t_eq (t_alt2 (sd E fs a) (sd E fs b)) (sd E fs (salt2 a b)).
Proof.
  intros E fs a b. unfold salt2.
  destruct a; [cbn [sd]; apply t_alt2_nil_l; apply sd_has_nil|..];
  (destruct b; [cbn [sd]; apply t_alt2_nil_r; first [apply t_exit_has_nil | apply t_emit_has_nil
                  | apply t_alt2_has_nil_l; apply sd_has_nil | cbn [sd]; destruct (_ <=? _)%Z; apply sd_has_nil] | apply t_eq_refl ..]).
Qed.

(* [comment removed for export] *)
Fixpoint shape_vars_lt (b : nat) (s : shape) : bool :=
  match s with
  | SNil | SExit _ => true
  | SEmit _ _ s' => shape_vars_lt b s'
  | SAlt2 x y => shape_vars_lt b x && shape_vars_lt b y
  | SCase e _ x y => expr_vars_lt b e && shape_vars_lt b x && shape_vars_lt b y
  end.

(* [comment removed for export] *)
Lemma expr_vars_lt_eq : forall b e, SP.expr_vars_lt b e = SymRun3.expr_vars_lt b e.
Proof. intros b e. induction e; cbn; try rewrite IHe1, IHe2; try rewrite IHe; reflexivity. Qed.

Lemma sd_agree : forall b E E' fs s,
  env_agree b E E' -> shape_vars_lt b s = true -> sd E fs s = sd E' fs s.
Proof.
  intros b E E' fs s Hag. induction s; cbn [shape_vars_lt sd]; intros H; try reflexivity.
  - rewrite IHs by exact H. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    rewrite IHs1, IHs2 by assumption.
    rewrite (edenot_agree b E E' e Hag) by (rewrite <- expr_vars_lt_eq; exact H1). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
   (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

(* [comment removed for export] *)
Definition iv_disjoint (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).

Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).

Definition smap_ok (E : env) (maps : list (word * word)) (m : smap) : Prop :=
  let a := bv_unsigned (edenot E (sm_base m)) in
  let L := bv_unsigned (edenot E (sm_len m)) in
  0 < L < 2 ^ 64 /\ a + L <= 2 ^ 64 /\
  if sm_exact m then In (edenot E (sm_base m), edenot E (sm_len m)) maps
  else exists lo sz, In (lo, sz) maps /\ bv_unsigned lo <= a /\ a + L <= bv_unsigned lo + bv_unsigned sz.

Record vm_ok (E : env) (ms : list smap) (nmaps live : Z) (VM : VmMaps) : Prop := VM_OK {
  vo_res   : vm_reserved VM = segments_reserved RSEGS;
  vo_maps  : Forall (smap_ok E (vm_maps VM)) ms;
  vo_len   : Z.of_nat (length (vm_maps VM)) <= nmaps;
  vo_live  : vm_live_bytes VM <= live;
  vo_small : Forall (fun p => 0 < bv_unsigned (snd p) <= 2 ^ 30) (vm_maps VM);
  vo_nw    : Forall (fun p => bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64) (vm_maps VM);
  vo_seps  : seps (vm_maps VM);
  vo_limit : 2 ^ 34 <= vm_limit VM;
  (* [comment removed for export] *)
  vo_sp0   : vm_init_sp VM = ev E SP.SP0V;
  vo_sp0w  : sp_window_lo <= bv_unsigned (vm_init_sp VM) <= sp_window_hi;
  vo_top   : Forall (fun p => bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (vm_init_sp VM) - SP.STKWIN) (vm_maps VM)
}.

(* [comment removed for export] *)
Definition HULL_LO : Z := t_hull_lo U0.
Definition HULL_HI : Z := t_hull_hi U0.
Definition lib_ok (M : word -> option byte) : Prop := lib_statics LIBR_HULL_U LIBR_U SNAP_U M.

Lemma HULL_eq : LIBR_HULL_U = (HULL_LO, HULL_HI). Proof. reflexivity. Qed.

Lemma LIBR_in_hull : forall a, in_ranges a LIBR_U -> HULL_LO <= a < HULL_HI.
Proof.
  intros a (r & Hin & Hr).
  assert (HB : forallb (fun r => (HULL_LO <=? fst r) && (snd r <=? HULL_HI))%bool LIBR_U = true) by (vm_compute; reflexivity).
  apply (proj1 (forallb_forall _ _)) with (x := r) in HB; [|exact Hin]. apply andb_prop in HB as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma SNAP_in_LIBR : forall a b, In (a, b) SNAP_U -> in_ranges a LIBR_U.
Proof.
  intros a b Hin.
  assert (HB : forallb (fun c => in_rangesb (fst c) LIBR_U) SNAP_U = true) by (vm_compute; reflexivity).
  apply (proj1 (forallb_forall _ _)) with (x := (a, b)) in HB; [|exact Hin]. cbn [fst] in HB. apply in_rangesb_spec. exact HB.
Qed.

Lemma lib_ok_frame : forall M M',
  (forall a, HULL_LO <= a < HULL_HI -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  lib_ok M -> lib_ok M'.
Proof.
  intros M M' Hag [HS HP]. unfold lib_ok, lib_statics. rewrite HULL_eq in *. cbn [fst snd] in *. split.
  - destruct HS as [Hpr|Hsn].
    + left. intros a Ha. rewrite Hag by (apply LIBR_in_hull; exact Ha). apply Hpr. exact Ha.
    + right. intros a b Hin. rewrite Hag by (apply LIBR_in_hull; eapply SNAP_in_LIBR; exact Hin). apply Hsn. exact Hin.
  - intros a Ha Hn. rewrite Hag by exact Ha. apply HP; assumption.
Qed.

Record cs_ok (E : env) (cs : cstate) (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop := CS_OK {
  co_regs : regs_ok E (s_regs (c_ss cs)) R;
  co_know : know_ok RSEGS E M (s_know (c_ss cs));
  co_log  : s_log (c_ss cs) = [];
  co_halt : m_halted model = None;
  co_lazy : m_vm_lazy model = [];
  co_mat  : m_vm_materialized model = [];
  co_fds  : m_fds model = fds_std;
  co_vm   : vm_ok E (c_maps cs) (c_nmaps cs) (c_live cs) (m_vmmaps model);
  co_slots : slots_ok E M (c_slots cs);                      (* [comment removed for export] *)
  co_lib  : lib_ok M                                         (* [comment removed for export] *)
}.

Definition cfg_of (R : bvmap 5 word) (p : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (mkst R (Z_to_bv 64 p) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
Record std_model (VM : VmMaps) (model : Model) : Prop := STD_MODEL {
  stdm_fds  : m_fds model = fds_std;
  stdm_vm   : m_vmmaps model = VM;
  stdm_halt : m_halted model = None;
  stdm_lazy : m_vm_lazy model = [];
  stdm_mat  : m_vm_materialized model = []
}.

Lemma std_model_mk : forall VM stdin0 fs0 tid rlim,
  std_model VM (mkModelA fds_std VM stdin0 fs0 None tid rlim).
Proof. intros. constructor; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma scs_denot_nil : forall base E, scs_denot RSEGS base E [].
Proof. intros. constructor. Qed.

(* [comment removed for export] *)
Lemma log_hull_ok_sound : forall E M k log,
  know_ok RSEGS E M k -> log_flat E log -> log_hull_ok U0 k log = true ->
  forall a, HULL_LO <= a < HULL_HI -> mem_denot E M log (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros E M k log HK Hlf H a Ha. unfold log_hull_ok in H.
  induction log as [|[[b o] w v] rest IH]; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. cbn [log_flat] in Hlf. destruct Hlf as (Hw & Hfl & Hlf).
  cbn [mem_denot]. rewrite MemSplit.wbytes_outside.
  - apply IH; assumption.
  - rewrite length_N_to_le_bytes. rewrite (flat_u E _ _ Hfl). destruct Hfl as (F1 & F2 & F3 & F4). lia.
  - rewrite length_N_to_le_bytes. rewrite (flat_u E _ _ Hfl).
    pose proof (ranges_apart_x_sound RSEGS E M k b o (ELit (Z.of_nat w)) (ELit 0) HULL_LO (ELit (HULL_HI - HULL_LO)) HK H1) as D.
    unfold estart, elenZ in D. cbn [a_base a_off edenot] in D.
    assert (E0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity. rewrite E0 in D.
    assert (EW : bv_unsigned (Z_to_bv 64 (Z.of_nat w)) = Z.of_nat w) by (apply u64_lit; lia).
    assert (EH : bv_unsigned (Z_to_bv 64 (HULL_HI - HULL_LO)) = HULL_HI - HULL_LO) by (vm_compute; reflexivity).
    rewrite EW, EH in D. unfold estart. cbn [a_base a_off].
    rewrite u64_lit by (unfold HULL_LO, HULL_HI in Ha; cbn in Ha; lia). lia.
Qed.

Lemma run_block_sound : forall bfuel stops cs cs' E R M model,
  run_block RSEGS IT U0 bfuel stops cs = Some cs' -> cs_ok E cs R M model ->
  exists R' M',
    msteps RSEGS (mkst R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS)) (mkst R' (Z_to_bv 64 (pc cs')) M' (seg_rom RSEGS))
    /\ cs_ok E cs' R' M' model
    /\ c_maps cs' = c_maps cs.
Proof.
  intros bfuel stops cs cs' E R M model Hrb HC.
  destruct HC as [HR HK HL Hh Hlz Hmt Hf HV HS HLIB]. unfold run_block in Hrb. rewrite sym_execT'_eq in Hrb. (* [comment removed for export] *)
  set (ss' := sym_execT RSEGS IT bfuel true stops (c_ss cs)) in Hrb.
  destruct (log_hull_ok U0 (s_know (c_ss cs)) (s_log ss')) eqn:Hhull; [|discriminate].
  destruct (carry (s_log ss') (s_know ss') []) as [[kn' scs] hs] eqn:Hc.
  destruct scs; [|discriminate]. injection Hrb as <-.
  destruct (c_ss cs) as [p sr log k nx] eqn:Hss. cbn [s_log] in HL. subst log.
  pose proof (sym_execT_ex RSEGS IT bfuel true stops (SS p sr [] k nx) E M (seg_rom RSEGS)
                (mkst R (Z_to_bv 64 p) M (seg_rom RSEGS)) IT_ok
                (st_ok_entry RSEGS E M (seg_rom RSEGS) p sr k nx R HR HK)) as HX.
  cbn zeta in HX. fold ss' in HX. destruct HX as (R' & HR' & Hlf & HK' & Hms).
  exists R', (mem_denot E M (s_log ss')).
  unfold pc. rewrite Hss. cbn [c_ss s_pc].
  split; [exact Hms|]. split; [|reflexivity].
  assert (HKc : know_ok RSEGS E (mem_denot E M (s_log ss')) kn').
  { eapply (carry_sound RSEGS E M); [exact Hc | exact Hlf | exact HK' | apply scs_denot_nil]. }
  constructor; cbn [c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity.
  - eapply slots_carry_sound; [exact HKc | exact Hlf | exact HS].
  - eapply lib_ok_frame; [|exact HLIB]. cbn [s_know] in Hhull.
    exact (log_hull_ok_sound E M k (s_log ss') HK Hlf Hhull).
Qed.


(* [comment removed for export] *)

Lemma cs_gc_ok : forall E cs R M model, cs_ok E cs R M model -> cs_ok E (cs_gc cs) R M model.
Proof.
  intros E cs R M model [HR HK HL Hh Hlz Hmt Hf HV HS HLIB]. unfold cs_gc.
  destruct (split_lit (reg cs 2)) as [spb spk].
  constructor; cbn [set_kn c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity.
  unfold know_ok in *. apply Forall_forall. intros K Hin. apply filter_In in Hin as [Hin _].
  exact (proj1 (Forall_forall _ _) HK K Hin).
Qed.

Lemma pc_cs_gc : forall cs, pc (cs_gc cs) = pc cs.
Proof. intros cs. unfold cs_gc. destruct (split_lit (reg cs 2)); reflexivity. Qed.

Lemma c_maps_cs_gc : forall cs, c_maps (cs_gc cs) = c_maps cs.
Proof. intros cs. unfold cs_gc. destruct (split_lit (reg cs 2)); reflexivity. Qed.

Lemma run_block_gc_sound : forall bfuel stops cs cs' E R M model,
  run_block_gc RSEGS IT U0 bfuel stops cs = Some cs' -> cs_ok E cs R M model ->
  exists R' M',
    msteps RSEGS (mkst R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS)) (mkst R' (Z_to_bv 64 (pc cs')) M' (seg_rom RSEGS))
    /\ cs_ok E cs' R' M' model
    /\ c_maps cs' = c_maps cs.
Proof.
  intros bfuel stops cs cs' E R M model H HC. unfold run_block_gc in H.
  destruct (run_block RSEGS IT U0 bfuel stops cs) as [cs1|] eqn:Hrb; [|discriminate]. injection H as <-.
  destruct (run_block_sound bfuel stops cs cs1 E R M model Hrb HC) as (R' & M' & Hms & HC1 & Hmaps).
  exists R', M'. rewrite pc_cs_gc, c_maps_cs_gc. split; [exact Hms|]. split; [apply cs_gc_ok; exact HC1 | exact Hmaps].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ext1 (E : env) (v : nat) (a : word) : env :=
  Env (fun n => if Nat.eqb n v then a else ev E n) (eb E).

Lemma ext1_agree : forall E v a, env_agree v E (ext1 E v a).
Proof.
  intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
  destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.

Lemma ext1_at : forall E v a, ev (ext1 E v a) v = a.
Proof. intros. cbn [ext1 ev]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma env_agree_le : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [H1 H2] Hle. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma ridx_lit : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
  intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma reg_sound : forall E cs R M model n,
  cs_ok E cs R M model -> (0 < n < 32)%nat ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof.
  intros E cs R M model n HC Hn. rewrite (co_regs _ _ _ _ _ HC). unfold sr_get, reg.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz. rewrite ridx_lit by lia. reflexivity.
Qed.

Lemma lit_of_sound : forall E e z, lit_of e = Some z -> edenot E e = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E e z H. destruct e; try discriminate. cbn [lit_of] in H. injection H as <-.
  split; [| unfold two64; apply Z.mod_pos_bound; lia].
  cbn [edenot]. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma reg_lit_sound : forall E cs R M model n z,
  cs_ok E cs R M model -> (0 < n < 32)%nat -> reg_lit cs n = Some z ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E cs R M model n z HC Hn H. unfold reg_lit in H.
  destruct (lit_of_sound E (reg cs n) z H) as [He Hz]. rewrite (reg_sound E cs R M model n HC Hn), He. auto.
Qed.

Lemma is_ecall_at_sound : forall cs, is_ecall_at RSEGS cs = true ->
  exists w, fetch_word RSEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true
            /\ (0 <= pc cs)%Z /\ (pc cs + 4 < 2 ^ 64)%Z.
Proof.
  intros cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4].
  apply Z.leb_le in H0. apply Z.ltb_lt in H4. unfold two64 in H4.
  destruct (fetch_word RSEGS (Z_to_bv 64 (pc cs))) as [w|]; [|discriminate].
  exists w. auto.
Qed.

(* [comment removed for export] *)
Lemma cs_ok_set_reg_pc : forall E cs R M model n e v p,
  cs_ok E cs R M model -> (0 < n < 32)%nat -> edenot E e = v ->
  cs_ok E (set_pc (set_reg cs n e) p) (regupd R (Z_to_bv 5 (Z.of_nat n)) v) M model.
Proof.
  intros E cs R M model n e v p HC Hn He. destruct HC as [HR HK HL Hh Hlz Hmt Hf HV HS HLIB].
  constructor; cbn [set_pc set_reg c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity.
  replace (sr_upd (s_regs (c_ss cs)) n e) with (sr_upd (s_regs (c_ss cs)) (ridx (Z_to_bv 5 (Z.of_nat n))) e)
    by (rewrite ridx_lit by lia; reflexivity).
  apply regs_ok_set; [exact HR | | exact He].
  intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
  change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
  replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia.
Qed.

Lemma pc_set_pc : forall cs n e p, pc (set_pc (set_reg cs n e) p) = p.
Proof. reflexivity. Qed.

Lemma v_addi_pc : forall p, (0 <= p)%Z -> (p + 4 < 2 ^ 64)%Z -> v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof. intros. apply v_addi_pc4; assumption. Qed.

Lemma m_fs_mmap_model : forall a n m, m_fs (mmap_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma m_fs_munmap_model : forall a n m, m_fs (munmap_model a n m) = m_fs m.
Proof. reflexivity. Qed.

Lemma split_sound : forall cs e mid lo hi E R M model,
  cs_ok E cs R M model -> erange (kn cs) e = Some (lo, hi) ->
  (bv_unsigned (edenot E e) <= mid -> cs_ok E (set_kn cs (KRange e lo mid :: kn cs)) R M model)
  /\ (mid < bv_unsigned (edenot E e) -> cs_ok E (set_kn cs (KRange e (mid + 1) hi :: kn cs)) R M model).
Proof.
  intros cs e mid lo hi E R M model HC Hr.
  destruct HC as [HR HK HL Hh Hlz Hmt Hf HV HS HLIB].
  pose proof (erange_sound RSEGS E M (kn cs) e lo hi HK Hr) as Hb.
  split; intros Hm; constructor; cbn [set_kn c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots]; try assumption; try reflexivity;
    (constructor; [cbn [kentry_ok]; lia | exact HK]).
Qed.


End NX0.
End FPW_1.

End SPSA.
