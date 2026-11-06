(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState LxMem LxStep LxCheck LxSem LxWf LxSoundVal LxSoundAlu LxSoundMem LxSoundMem2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LXS LXM LXI LXC LXSEM LXWF LXSV LXSA LXSM LXSM2.
Open Scope Z_scope.

Module LXSS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition core_of (ms : machine_state) : core :=
  {| c_regs := ms_regs ms; c_fregs := ms_fregs ms; c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms; c_resv := ms_resv ms |}.
Definition ms_of (ms : machine_state) (c : core) (m : word -> option byte) : machine_state :=
  {| ms_regs := c_regs c; ms_fregs := c_fregs c; ms_pc_val := c_pc c; ms_svc_pending := None;
     ms_resv := c_resv c; ms_fcsr := c_fcsr c; ms_mem := m; ms_rom := ms_rom ms |}.

Lemma ms_of_core : forall ms, ms_svc_pending ms = None -> ms_of ms (core_of ms) (ms_mem ms) = ms.
Proof. intros [] H; cbn in *; subst; reflexivity. Qed.

Section S.
  Variable segs : list Segment.

  Lemma step_via : forall ms w i sz c' m',
    fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, sz) ->
    interp_eff segs (exec (Z_to_bv 64 sz) i (core_of ms)) (ms_mem ms) = MachineOk (c', m') ->
    RiscvSemantics.step segs ms = MachineOk (ms_of ms c' m').
  Proof.
    intros ms w i sz c' m' Hf He Hd Hi.
    unfold RiscvSemantics.step, step_accesses. unfold ms_pc. rewrite Hf.
    unfold drop_access_report, decode_exec_accesses. rewrite He, Hd.
    unfold interp_eff, drop_access_report in Hi. unfold core_of in Hi.
    match type of Hi with context [interp_eff_accesses ?a ?b ?c] => destruct (interp_eff_accesses a b c) as [rep| |] end;
      try discriminate.
    destruct rep as [[c m] acc]. cbn in Hi. injection Hi; intros <- <-. reflexivity.
  Qed.

  Lemma interp_done : forall c m, interp_eff segs (EDone c) m = MachineOk (c, m).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma bv_extract_full : forall (v : word), bv_extract 0 64 v = v.
  Proof. intros v. apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

  Lemma ldval_small : forall (n : N) (w : Z) (sgn : bool) (bs : list byte),
    0 < w -> w < 8 -> Z.of_nat (length bs) = w -> n = Z.to_N (8 * w) ->
    (if sgn then sext 64 (bv_extract 0 n (le_bytes_to_word bs))
     else zext 64 (bv_extract 0 n (le_bytes_to_word bs))) = ldval w sgn bs.
  Proof.
    intros n w sgn bs Hw0 Hw8 Hlen Hn. unfold ldval.
    destruct (Z.eqb_spec w 8); [lia|].
    pose proof (bytes_le_to_Z_bound bs) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
    rewrite Hlen in Hb.
    assert (HnZ : Z.of_N n = 8 * w) by lia.
    assert (Hpow : 2 ^ (8 * w) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
    assert (Hz : bv_unsigned (bv_extract 0 n (le_bytes_to_word bs)) = bytes_le_to_Z bs).
    { rewrite bv_extract_unsigned, Z.shiftr_0_r. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
      rewrite (bv_wrap_small 64) by (change (bv_modulus 64) with (2 ^ 64); lia).
      apply bv_wrap_small. unfold bv_modulus. rewrite HnZ. lia. }
    set (z := bytes_le_to_Z bs) in *.
    assert (Hhalf : 2 ^ (8 * w) = 2 * 2 ^ (8 * w - 1)).
    { replace (8 * w) with (Z.succ (8 * w - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
    destruct sgn; apply bv_eq.
    - unfold sext. rewrite bv_sign_extend_unsigned. unfold w64. rewrite Z_to_bv_unsigned. f_equal.
      unfold bv_signed, bv_swrap. rewrite Hz. unfold bv_half_modulus, bv_wrap, bv_modulus. rewrite HnZ.
      replace (2 ^ (8 * w) `div` 2) with (2 ^ (8 * w - 1)) by (rewrite Hhalf; symmetry; rewrite Z.mul_comm; apply Z.div_mul; lia).
      destruct (Z.leb_spec (2 ^ (8 * w - 1)) z).
      + rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
      + rewrite Z.mod_small by lia. lia.
    - unfold zext. rewrite bv_zero_extend_unsigned'. unfold w64. rewrite Z_to_bv_unsigned. f_equal.
      rewrite Hz. reflexivity.
  Qed.

  Lemma interp_load_val : forall sz sgn a k m bs,
    rdn segs m a (Z.to_nat (msize_w sz)) = Some bs ->
    interp_eff segs (load_val sz sgn a k) m = interp_eff segs (k (ldval (msize_w sz) sgn bs)) m.
  Proof.
    intros sz sgn a k m bs Hrd.
    pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
    unfold interp_eff. destruct sz; cbn [msize_w] in *;
      [ change (Z.to_nat 1) with 1%nat in * | change (Z.to_nat 2) with 2%nat in * | change (Z.to_nat 4) with 4%nat in * | change (Z.to_nat 8) with 8%nat in * ];
      cbn [load_val interp_eff_accesses width_bytes]; rewrite ov_rdn;
      change (Pos.to_nat 1) with 1%nat; change (Pos.to_nat 2) with 2%nat; change (Pos.to_nat 4) with 4%nat; change (Pos.to_nat 8) with 8%nat;
      rewrite Hrd.
    - rewrite (ldval_small 8 1 sgn bs) by (try lia; try rewrite Hlen; reflexivity).
      destruct (interp_eff_accesses segs (k _) m) as [[]| |]; reflexivity.
    - rewrite (ldval_small 16 2 sgn bs) by (try lia; try rewrite Hlen; reflexivity).
      destruct (interp_eff_accesses segs (k _) m) as [[]| |]; reflexivity.
    - rewrite (ldval_small 32 4 sgn bs) by (try lia; try rewrite Hlen; reflexivity).
      destruct (interp_eff_accesses segs (k _) m) as [[]| |]; reflexivity.
    - rewrite bv_extract_full. replace (le_bytes_to_word bs) with (ldval 8 sgn bs) by reflexivity.
      destruct (interp_eff_accesses segs (k _) m) as [[]| |]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma interp_eload : forall (n : N) nb a k m bs,
    (n = 32%N /\ nb = 4%nat \/ n = 64%N /\ nb = 8%nat) ->
    rdn segs m a nb = Some bs ->
    interp_eff segs (ELoad n a k) m = interp_eff segs (k (bv_extract 0 n (le_bytes_to_word bs))) m.
  Proof.
    intros n nb a k m bs Hn Hrd. unfold interp_eff. cbn [interp_eff_accesses]. rewrite ov_rdn.
    destruct Hn as [[-> ->]|[-> ->]]; cbn [width_bytes]; change (Pos.to_nat 4) with 4%nat; change (Pos.to_nat 8) with 8%nat;
      rewrite Hrd; destruct (interp_eff_accesses segs (k _) m) as [[]| |]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma interp_estore : forall (n : N) nb a (v : bv n) k m,
    (n = 8%N /\ nb = 1%nat \/ n = 16%N /\ nb = 2%nat \/ n = 32%N /\ nb = 4%nat \/ n = 64%N /\ nb = 8%nat) ->
    store_ok segs m a nb = true ->
    interp_eff segs (EStore n a v k) m = interp_eff segs k (write_to_mem m a (Z_to_le_bytes nb (bv_unsigned v))).
  Proof.
    intros n nb a v k m Hn Hst. unfold interp_eff. cbn [interp_eff_accesses].
    destruct Hn as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; cbn [width_bytes];
      change (Pos.to_nat 1) with 1%nat; change (Pos.to_nat 2) with 2%nat; change (Pos.to_nat 4) with 4%nat; change (Pos.to_nat 8) with 8%nat;
      rewrite Hst; destruct (interp_eff_accesses segs k _) as [[]| |]; reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sext_w64 : forall {n} (i : bv n), sext 64 i = w64 (bv_signed i).
Proof. intros n i. apply bv_eq. unfold sext, w64. rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned. reflexivity. Qed.
Lemma zext_w64 : forall {n} (i : bv n), zext 64 i = w64 (bv_unsigned i).
Proof. intros n i. apply bv_eq. unfold zext, w64. rewrite bv_zero_extend_unsigned', Z_to_bv_unsigned. reflexivity. Qed.
Lemma w64_add : forall a b, w64 (a + b) = (w64 a + w64 b)%bv.
Proof. intros. change ((w64 a + w64 b)%bv) with (alu64 ALU_ADD (w64 a) (w64 b)). rewrite add_w64. reflexivity. Qed.
Lemma lui_w64 : forall imm : bv 20, sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = w64 (bv_signed imm * 4096).
Proof. intros. rewrite b_lui. unfold v_lui, w64. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma with_pc_rset : forall r v p c, with_pc p (rset r v c) = rset r v (with_pc p c).
Proof. intros. unfold rset. destruct (is_x0 r); reflexivity. Qed.
Lemma land_clear0_mod : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 ->
  (Z.land x (-2)) mod 2 ^ 64 = (Z.land (y mod 2 ^ 64) (2 ^ 64 - 2)) mod 2 ^ 64.
Proof.
  intros x y H. apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 64) as [L|G].
  - rewrite !Z.mod_pow2_bits_low, !Z.land_spec by lia.
    rewrite <- (Z.mod_pow2_bits_low x 64 i), H, Z.mod_pow2_bits_low by lia.
    f_equal. change (-2) with (Z.lnot 1). rewrite Z.lnot_spec by lia.
    replace (2 ^ 64 - 2) with (Z.lnot 1 mod 2 ^ 64) by reflexivity. rewrite Z.mod_pow2_bits_low, Z.lnot_spec by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma jalr_tgt_w64 : forall (a : word) (imm : bv 12) z, a = w64 z ->
  bv_and (a + sext 64 imm)%bv (bv_not (Z_to_bv 64 1)) = w64 (Z.land ((z + bv_signed imm) mod two64) (two64 - 2)).
Proof.
  intros a imm z ->. rewrite b_jalr. unfold jalr_tgt, jalr_tgtZ. fold (w64 z). rewrite w64_unsigned. change two64 with (2 ^ 64).
  apply w64_eq_mod. apply land_clear0_mod. rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fflags_bits_range : forall fl, 0 <= fflags_bits fl < 32.
Proof. intros [[] [] [] [] []]; unfold fflags_bits; cbn -[Z.shiftl]; rewrite ?Z.shiftl_1_l; cbn; lia. Qed.
Lemma frm_ok_accrue : forall (f : bv 32) fl, frm_ok f -> frm_ok (Z_to_bv 32 (Z.lor (bv_unsigned f) (fflags_bits fl))).
Proof.
  intros f fl H. unfold frm_ok in *. rewrite Z_to_bv_unsigned.
  pose proof (fflags_bits_range fl) as Hfl. pose proof (bv_unsigned_in_range _ f) as Hf. change (bv_modulus 32) with (2 ^ 32) in Hf.
  assert (Hlor : 0 <= Z.lor (bv_unsigned f) (fflags_bits fl) < 2 ^ 32).
  { split; [apply Z.lor_nonneg; lia|]. enough (Z.lor (bv_unsigned f) (fflags_bits fl) <= 2 ^ 32 - 1) by lia. apply lor_below_pow2; lia. }
  rewrite bv_wrap_small by (change (bv_modulus 32) with (2 ^ 32); lia).
  apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
  apply (f_equal (fun z => Z.testbit z i)) in H. rewrite Z.bits_0 in H.
  rewrite Z.land_spec, Z.shiftr_spec in * by lia. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i 3) as [L|G].
  - assert (T : Z.testbit (fflags_bits fl) (i + 5) = false).
    { destruct (Z.eq_dec (fflags_bits fl) 0) as [->|NE]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      assert (Z.log2 (fflags_bits fl) < 5) by (apply Z.log2_lt_pow2; cbn; lia). lia. }
    rewrite T, Bool.orb_false_r. exact H.
  - assert (T7 : Z.testbit 7 i = false) by (apply Z.bits_above_log2; cbn; lia). rewrite T7, !Bool.andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithU.
  Variable U : uenv.
  Variable G : sym -> Z.
  Variable M0 : word -> option byte.
  Hypothesis UOK : uenv_ok U.
  Hypothesis SCOK : scells_ok U G M0.   (* [comment removed for export] *)
  Let segs := ue_segs U.

  Definition cstep (ms ms' : machine_state) : Prop := RiscvSemantics.step segs ms = MachineOk ms'.

  (* [comment removed for export] *)
  Definition sound_res (rho : valuation) (n : nat) (ms : machine_state) (r : sres) : Prop :=
    match r with
    | SNext st' => exists ms' rho', cstep ms ms' /\ R U G M0 rho' st' ms' /\ (agree n rho rho' /\ (n <= s_next st')%nat)
    | SFork st1 st2 =>
        (exists rho', (R U G M0 rho' st1 ms \/ R U G M0 rho' st2 ms) /\ (agree n rho rho' /\ (n <= s_next st1)%nat /\ (n <= s_next st2)%nat))
        \/ (exists ms' rho', cstep ms ms' /\ (R U G M0 rho' st1 ms' \/ R U G M0 rho' st2 ms') /\ (agree n rho rho' /\ (n <= s_next st1)%nat /\ (n <= s_next st2)%nat))
    | SExit st' => exists ms', cstep ms ms' /\ R U G M0 rho (set_pc st' (rho SYM_RA)) ms' /\ (n <= s_next st')%nat
    | SFail _ _ => True
    end.

  Lemma list_get_set : forall (l : list aval) n m v d,
    list_get (list_set l n v) m d = if (Nat.eqb m n &&& Nat.ltb n (length l))%bool then v else list_get l m d.
  Proof.
    induction l as [|x r IH]; intros n m v d; cbn.
    - destruct (Nat.eqb m n); destruct m; reflexivity.
    - destruct n as [|n]; destruct m as [|m]; cbn; try reflexivity.
      rewrite IH. destruct (Nat.eqb m n); cbn; reflexivity.
  Qed.

  Lemma regn_range : forall r : reg, (regn r < 32)%nat.
  Proof. intros r. unfold regn. pose proof (u5_range r). lia. Qed.

  Lemma regn_bv : forall r : reg, Z_to_bv 5 (Z.of_nat (regn r)) = r.
  Proof. intros r. unfold regn. rewrite Z2Nat.id by (pose proof (u5_range r); lia). apply Z_to_bv_bv_unsigned. Qed.

  Lemma regn_zero : forall r : reg, (regn r = 0)%nat <-> is_x0 r = true.
  Proof.
    intros r. unfold regn, is_x0. rewrite Z.eqb_eq. pose proof (u5_range r) as HR5. split; intros HH; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma getreg_sound : forall rho st ms r,
    R U G M0 rho st ms -> val_ok rho (getreg st (regn r)) (rget (core_of ms) r).
  Proof.
    intros rho st ms r HR. unfold getreg, rget. cbn [c_regs core_of].
    destruct (Nat.eqb_spec (regn r) 0) as [E|E].
    - rewrite (proj1 (regn_zero r) E). cbn. rewrite lconst_sound. reflexivity.
    - assert (Hx : is_x0 r = false) by (destruct (is_x0 r) eqn:X; [exfalso; apply E; apply regn_zero; exact X|reflexivity]).
      rewrite Hx. pose proof (r_regs _ _ _ _ _ _ HR (regn r) ltac:(pose proof (regn_range r); lia)) as H.
      rewrite regn_bv in H. exact H.
  Qed.

  Lemma getreg_below : forall st r, wf_state st = true -> aval_below (getreg st r) (s_next st) = true.
  Proof.
    intros st r Hwf. destruct (wf_parts st Hwf) as (W & _). unfold getreg. destruct (Nat.eqb r 0); [reflexivity|].
    rewrite forallb_forall in W. revert r. induction (s_regs st) as [|v l IH]; intros r; [destruct r; reflexivity|].
    destruct r; cbn; [apply W; left; reflexivity|]. apply IH. intros x Hx. apply W. right; exact Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma setreg_sound : forall rho st ms r v wv,
    R U G M0 rho st ms -> val_ok rho v wv ->
    R U G M0 rho (setreg st (regn r) v) (ms_of ms (rset r wv (core_of ms)) (ms_mem ms)).
  Proof.
    intros rho st ms r v wv HR Hv.
    unfold setreg, rset. destruct (Nat.eqb_spec (regn r) 0) as [E|E].
    - rewrite (proj1 (regn_zero r) E). destruct HR; constructor; cbn; try assumption; try reflexivity.
    - assert (Hx : is_x0 r = false) by (destruct (is_x0 r) eqn:X; [exfalso; apply E; apply regn_zero; exact X|reflexivity]).
      rewrite Hx.
      destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata].
      constructor; cbn; try assumption; try reflexivity.
      intros r' Hr'. unfold reg_get. cbn [c_regs core_of with_regs].
      rewrite list_get_set.
      destruct (Nat.eqb_spec r' (regn r)) as [->|Hne].
      + rewrite regn_bv, bvmap_get_set_same. destruct (Nat.ltb (regn r) (length (s_regs st))) eqn:L; [exact Hv|].
        cbn. replace (list_get (s_regs st) (regn r) Top) with Top; [exact I|].
        apply Nat.ltb_ge in L. clear -L. revert L. generalize (regn r) as n. induction (s_regs st) as [|x l IH]; intros n L; [destruct n; reflexivity|].
        destruct n; cbn in *; [lia|]. apply IH. lia.
      + cbn. rewrite bvmap_get_set_other; [apply (Rregs r' Hr')|].
        intros Heq. apply Hne. apply (f_equal (fun x : bv 5 => Z.to_nat (bv_unsigned x))) in Heq.
        rewrite Z_to_bv_small in Heq by (change (bv_modulus 5) with 32; lia). rewrite Nat2Z.id in Heq. unfold regn in Heq |- *. lia.
  Qed.

  Lemma wr_sound : forall rho st ms r v wv,
    R U G M0 rho st ms -> val_ok rho v wv ->
    R U G M0 rho (wr st (regn r) v) (ms_of ms (rset r wv (core_of ms)) (ms_mem ms)).
  Proof.
    intros rho st ms r v wv HR Hv. unfold wr.
    pose proof (setreg_sound rho st ms r v wv HR Hv) as H1.
    destruct (Nat.eqb (regn r) 2); [|exact H1].
    destruct (sp_off st) as [k0|]; [|exact H1]. destruct (sp_off (setreg st (regn r) v)) as [k1|]; [|exact H1].
    destruct (Z.ltb k0 k1); [|exact H1]. unshelve eapply drop_below_sound; try exact UOK; exact H1.
  Qed.

  Lemma s_next_setreg : forall st r v, s_next (setreg st r v) = s_next st.
  Proof. intros. unfold setreg. destruct (Nat.eqb r 0); reflexivity. Qed.
  Lemma s_next_drop_below : forall st k, s_next (drop_below st k) = s_next st.
  Proof. reflexivity. Qed.
  Lemma s_next_wr : forall st r v, s_next (wr st r v) = s_next st.
  Proof.
    intros. unfold wr. destruct (Nat.eqb r 2); [|apply s_next_setreg].
    destruct (sp_off st); [destruct (sp_off (setreg st r v)); [destruct (Z.ltb _ _)|]|]; rewrite ?s_next_drop_below, ?s_next_setreg; reflexivity.
  Qed.
  Lemma s_next_learn : forall st l, s_next (learn st l) = s_next st.
  Proof. reflexivity. Qed.
  Lemma s_next_learn_eq : forall st l, s_next (learn_eq st l) = s_next st.
  Proof. reflexivity. Qed.
  Lemma s_next_learn_base : forall st k x y b, s_next (learn_base st k x y b) = s_next st.
  Proof.
    intros. unfold learn_base. destruct k, b; try reflexivity.
    - destruct (in_range _ _ _ _); reflexivity.
    - destruct (entails _ _ _); [reflexivity|]. destruct (entails _ _ _); reflexivity.
  Qed.
  Lemma s_next_learn_cond : forall st c b, s_next (learn_cond st c b) = s_next st.
  Proof. intros st [[[n k] x] y] b. unfold learn_cond. apply s_next_learn_base. Qed.

  Ltac nxt := cbn [s_next set_pc set_resv]; rewrite ?s_next_wr, ?s_next_setreg, ?s_next_learn, ?s_next_learn_cond; cbn [s_next set_pc set_resv];
              repeat match goal with H : s_next ?a = s_next ?b |- context [s_next ?a] => rewrite H end; cbn [s_next set_pc set_resv]; try lia.

  (* [comment removed for export] *)
  Lemma R_core_upd : forall rho st ms st' c,
    R U G M0 rho st ms ->
    s_ctx st' = s_ctx st -> s_next st' = s_next st -> s_stk st' = s_stk st -> s_arrs st' = s_arrs st ->
    s_abs st' = s_abs st -> s_pcache st' = s_pcache st -> s_pay st' = s_pay st ->
    c_pc c = w64 (s_pc st') -> regs_ok rho (s_regs st') (c_regs c) -> resv_ok (s_resv st') (c_resv c) -> frm_ok (c_fcsr c) ->
    R U G M0 rho st' (ms_of ms c (ms_mem ms)).
  Proof.
    intros rho st ms st' c HR E1 E2 E3 E4 E5 E6 E7 Hpc Hregs Hresv Hfrm.
    destruct HR; constructor; cbn; try rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7; try assumption; try reflexivity.
  Qed.

  Lemma set_pc_sound : forall rho st ms c m p,
    R U G M0 rho st (ms_of ms c m) -> R U G M0 rho (set_pc st p) (ms_of ms (with_pc (w64 p) c) m).
  Proof. intros rho st ms c m p HR. destruct HR; constructor; cbn in *; try assumption. reflexivity. Qed.

  Lemma R_ms_of : forall rho st ms, R U G M0 rho st ms -> R U G M0 rho st (ms_of ms (core_of ms) (ms_mem ms)).
  Proof. intros rho st ms HR. rewrite ms_of_core by exact (r_svc _ _ _ _ _ _ HR). exact HR. Qed.

  Lemma ms_of_idem : forall ms c m c' m', ms_of (ms_of ms c m) c' m' = ms_of ms c' m'.
  Proof. reflexivity. Qed.
  Lemma core_of_ms_of : forall ms c m, core_of (ms_of ms c m) = c.
  Proof. intros ms [] m; reflexivity. Qed.

  Definition can_exec (ms : machine_state) (i : instr) (sz : Z) : Prop :=
    forall c' m', interp_eff segs (exec (Z_to_bv 64 sz) i (core_of ms)) (ms_mem ms) = MachineOk (c', m') ->
                  cstep ms (ms_of ms c' m').

  Lemma npc_eq : forall rho st ms sz, R U G M0 rho st ms -> (c_pc (core_of ms) + Z_to_bv 64 sz)%bv = w64 (s_pc st + sz).
  Proof. intros rho st ms sz HR. cbn [c_pc core_of]. rewrite (r_pc _ _ _ _ _ _ HR), w64_add. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma wf_next2 : forall st, wf_state st = true -> (2 <= s_next st)%nat.
  Proof. intros st H. destruct (wf_parts st H) as (_ & _ & _ & _ & _ & _ & _ & H18 & _). lia. Qed.
  Lemma R_galign : forall rho st ms, R U G M0 rho st ms -> galign rho.
  Proof. intros rho st ms HR. exact (r_align _ _ _ _ _ _ HR). Qed.
  Lemma R_VS : forall rho st ms, R U G M0 rho st ms -> VS rho st.
  Proof. intros rho st ms HR. exact (r_vs _ _ _ _ _ _ HR). Qed.

  (* [comment removed for export] *)
  Lemma setreg_same_sound : forall rho st ms r v,
    (1 <= r < 32)%nat -> R U G M0 rho st ms -> val_ok rho v (reg_get (ms_regs ms) (Z_to_bv 5 (Z.of_nat r))) ->
    R U G M0 rho (setreg st r v) ms.
  Proof.
    intros rho st ms r v Hr HR Hv. unfold setreg. destruct (Nat.eqb_spec r 0) as [E|E]; [lia|].
    destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata].
    constructor; cbn; try assumption.
    intros r' Hr'. rewrite list_get_set.
    destruct (Nat.eqb_spec r' r) as [->|Hne].
    - destruct (Nat.ltb r (length (s_regs st))) eqn:L; [exact Hv|].
      replace (list_get (s_regs st) r Top) with Top; [exact I|].
      apply Nat.ltb_ge in L. clear -L. revert L. generalize r as n. induction (s_regs st) as [|x l IH]; intros n L; [destruct n; reflexivity|].
      destruct n; cbn in *; [lia|]. apply IH. lia.
    - exact (Rregs r' Hr').
  Qed.

  Lemma degrade_reg_sound : forall rho st ms r,
    (1 <= r < 32)%nat -> wf_state st = true -> R U G M0 rho st ms ->
    exists rho', R U G M0 rho' (degrade_reg st r) ms /\ agree (s_next st) rho rho' /\ (s_next st <= s_next (degrade_reg st r))%nat.
  Proof.
    intros rho st ms r Hr Hwf HR. unfold degrade_reg.
    assert (GEN : forall v, getreg st r = v ->
      exists rho', R U G M0 rho' (let (v', st1) := degrade st v in setreg st1 r v') ms
                   /\ agree (s_next st) rho rho' /\ (s_next st <= s_next (let (v', st1) := degrade st v in setreg st1 r v'))%nat).
    { intros v Hv.
      pose proof (r_regs _ _ _ _ _ _ HR r Hr) as Hval. unfold getreg in Hv. destruct (Nat.eqb_spec r 0); [lia|]. rewrite Hv in Hval.
      destruct (LXSV.degrade_sound rho st v _ (R_VS _ _ _ HR) Hval ltac:(rewrite <- Hv; pose proof (getreg_below st r Hwf) as B; unfold getreg in B; destruct (Nat.eqb_spec r 0); [lia|exact B]))
        as (rho' & Hext & HVS' & Hval' & Hbel').
      destruct (degrade st v) as [v' st1]. cbn [fst snd] in Hext, HVS', Hval', Hbel'.
      exists rho'. split; [|split; [exact (proj1 Hext) | unfold setreg; destruct (Nat.eqb r 0); cbn; exact (proj1 (proj2 Hext))]].
      apply setreg_same_sound; [exact Hr | eapply LXSM.R_vext; eauto | exact Hval']. }
    destruct (getreg st r) eqn:Hg; try (apply GEN; reflexivity).
    all: exists rho; split; [exact HR | split; [apply agree_refl | lia]].
  Qed.

  Lemma degrade_regs_ref_sound : forall rs rho st ms st',
    Forall (fun r => (1 <= r < 32)%nat) rs -> wf_state st = true -> R U G M0 rho st ms -> degrade_regs_ref st rs = Some st' ->
    exists rho', R U G M0 rho' st' ms /\ agree (s_next st) rho rho' /\ (s_next st <= s_next st')%nat /\ wf_state st' = true.
  Proof.
    induction rs as [|r rs IH]; intros rho st ms st' Hrs Hwf HR H; cbn in H.
    - injection H; intros <-. exists rho. split; [exact HR|]. split; [apply agree_refl|]. split; [lia | exact Hwf].
    - apply Forall_cons_iff in Hrs as [Hr Hrs].
      destruct (wf_state (degrade_reg st r)) eqn:Hwf1; [|discriminate].
      destruct (degrade_reg_sound rho st ms r Hr Hwf HR) as (rho1 & HR1 & Hag1 & Hn1).
      destruct (IH rho1 _ ms st' Hrs Hwf1 HR1 H) as (rho' & HR' & Hag' & Hn' & Hwf').
      exists rho'. split; [exact HR'|]. split; [eapply agree_trans; [exact Hn1 | exact Hag1 | exact Hag']|]. split; [lia | exact Hwf'].
  Qed.
  Lemma degrade_regs_sound : forall rs rho st ms st',
    Forall (fun r => (1 <= r < 32)%nat) rs -> wf_state st = true -> R U G M0 rho st ms -> degrade_regs st rs = Some st' ->
    exists rho', R U G M0 rho' st' ms /\ agree (s_next st) rho rho' /\ (s_next st <= s_next st')%nat /\ wf_state st' = true.
  Proof. intros rs rho st ms st' Hrs Hwf HR H. rewrite degrade_regs_eq in H. exact (degrade_regs_ref_sound rs rho st ms st' Hrs Hwf HR H). Qed.
  Lemma all_xregs_range : Forall (fun r => (1 <= r < 32)%nat) all_xregs.
  Proof. unfold all_xregs. apply Forall_forall. intros r Hr. apply in_seq in Hr. lia. Qed.

  (* [comment removed for export] *)
  Lemma sound_valop : forall rho st ms rd sz (p : aval * astate) (wv : word),
    wf_state st = true -> R U G M0 rho st ms ->
    (exists rho', VOK rho st p rho' wv) ->
    cstep ms (ms_of ms (rset rd wv (with_pc (c_pc (core_of ms) + Z_to_bv 64 sz)%bv (core_of ms))) (ms_mem ms)) ->
    sound_res rho (s_next st) ms (let (r, st1) := p in SNext (set_pc (wr st1 (regn rd) r) (s_pc st + sz))).
  Proof.
    intros rho st ms rd sz [r st1] wv Hwf HR (rho' & A & B & C & D) Hstep. cbn [fst snd] in *.
    cbn [sound_res]. eexists _, rho'. split; [exact Hstep|]. split; [|split; [exact (proj1 A) | nxt; exact (proj1 (proj2 A))]].
    rewrite <- with_pc_rset, (npc_eq rho st ms sz HR).
    assert (Epc : s_pc st = s_pc st1) by (destruct A as (_ & _ & E & _); symmetry; exact E).
    rewrite Epc. apply set_pc_sound. apply wr_sound; [|exact C].
    eapply R_vext; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma sound_split : forall rho st ms l,
    wf_state st = true -> R U G M0 rho st ms -> lin_below l (s_next st) = true ->
    sound_res rho (s_next st) ms (split_on st l).
  Proof.
    intros rho st ms l Hwf HR Hl. cbn [sound_res split_on]. left. exists rho. split; [|split; [apply agree_refl | nxt]].
    pose proof (R_VS _ _ _ HR) as HVS.
    destruct (Z.le_gt_cases 0 (evl rho l)) as [Hp|Hn].
    - left. destruct (learn_sound rho st l HVS Hl Hp) as [E V]. eapply R_vext; eauto.
    - right. assert (Hl' : lin_below (laddc (lneg l) (-1)) (s_next st) = true) by (apply laddc_below; apply lneg_below; exact Hl).
      destruct (learn_sound rho st _ HVS Hl' ltac:(rewrite laddc_sound, lneg_sound; lia)) as [E V]. eapply R_vext; eauto.
  Qed.

  Lemma and_split_below : forall C x p l n, and_split C x p = Some l -> lin_below x n = true -> lin_below l n = true.
  Proof.
    intros C x p l n H Bx. unfold and_split in H.
    destruct (lrange C x) as [[lo|] [hi|]]; try discriminate.
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
    injection H; intros <-. apply laddc_below; exact Bx.
  Qed.
  Lemma or_split_below : forall C x m l n, or_split C x m = Some l -> lin_below x n = true -> lin_below l n = true.
  Proof.
    intros C x m l n H Bx. unfold or_split in H.
    destruct (Z.ltb 0 m &&& Z.eqb m (2 ^ Z.log2 m) &&& Z.ltb (Z.log2 m) 63)%bool; [|discriminate].
    destruct (lrange C x) as [[lo|] [hi|]]; try discriminate.
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
    injection H; intros <-. apply laddc_below; exact Bx.
  Qed.

  Lemma alu_split_below : forall st op a b l n,
    alu_split st op a b = Some l -> aval_below a n = true -> aval_below b n = true -> lin_below l n = true.
  Proof.
    intros st op a b l n H Ba Bb. unfold alu_split in H.
    destruct (aval_litC (s_ctx st) a); [destruct (aval_litC (s_ctx st) b); [discriminate|]|];
    (destruct op; try discriminate; destruct a as [|x| |]; try discriminate; destruct b as [|y| |]; try discriminate;
     cbn [aval_below] in Ba, Bb;
     repeat match type of H with
       | context [match ?c with _ => _ end] => destruct c eqn:?; try discriminate
       | _ => idtac
       end; try (injection H; intros <-; first [exact Ba | exact Bb]);
     try (eapply or_split_below; [exact H | first [exact Ba | exact Bb]]);
     try (eapply and_split_below; [exact H | first [exact Ba | exact Bb]])).
  Qed.

  Lemma sound_lui : forall rho st ms rd imm sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Lui rd imm) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Lui rd imm) sz).
  Proof.
    intros rho st ms rd imm sz Hwf HR Hcan. cbn [exec_instr sound_res].
    eexists _, rho. split; [|split; [|split; [apply agree_refl | nxt]]].
    - apply Hcan. cbn [exec]. rewrite interp_done. reflexivity.
    - rewrite lui_w64, <- with_pc_rset, (npc_eq rho st ms sz HR). apply set_pc_sound. apply wr_sound; [exact HR | apply alit_ok].
  Qed.

  (* [comment removed for export] *)
  Lemma sltu_1 : forall a : word, alu64 ALU_SLTU a (w64 1) = (if Z.ltb (bv_unsigned a) 1 then Z_to_bv 64 1 else Z_to_bv 64 0).
  Proof. intros a. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite w64_unsigned. reflexivity. Qed.
  Lemma sltu_x0 : forall a : word, alu64 ALU_SLTU (w64 0) a = (if Z.ltb 0 (bv_unsigned a) then Z_to_bv 64 1 else Z_to_bv 64 0).
  Proof. intros a. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite w64_unsigned. reflexivity. Qed.
  Lemma xor_cv_1 : forall rho n k x y w,
    val_ok rho (CV n k x y) w -> val_ok rho (CV (negb n) k x y) (alu64 ALU_XOR w (w64 1)).
  Proof.
    intros rho n k x y w Hv. cbn [val_ok] in Hv |- *. rewrite Hv. apply bv_eq. rewrite xor_w64_unsigned, !w64_unsigned.
    destruct n, (cmp_holds rho k x y); reflexivity.
  Qed.

  Ltac side_tac Hwf HR :=
    first [ assumption | eapply R_galign; exact HR | apply wf_next2; exact Hwf | apply alit_ok | apply alit_below
          | rewrite sext_w64; apply alit_ok | rewrite zext_w64; apply alit_ok ].

  Lemma sound_opimm : forall rho st ms op rd rs1 imm sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (OpImm op rd rs1 imm) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (OpImm op rd rs1 imm) sz).
  Proof.
    intros rho st ms op rd rs1 imm sz Hwf HR Hcan. cbn [exec_instr].
    pose proof (getreg_sound rho st ms rs1 HR) as Hv1. pose proof (getreg_below st (regn rs1) Hwf) as Bv1.
    pose proof (R_VS _ _ _ HR) as HVS.
    assert (STEP : cstep ms (ms_of ms (rset rd (alu64 op (rget (core_of ms) rs1) (sext 64 imm))
                                       (with_pc (c_pc (core_of ms) + Z_to_bv 64 sz)%bv (core_of ms))) (ms_mem ms))).
    { apply Hcan. cbn [exec]. rewrite interp_done. reflexivity. }
    assert (GEN : sound_res rho (s_next st) ms
              match alu_split st op (getreg st (regn rs1)) (alit (immz imm)) with
              | Some l => split_on st l
              | None => let (r, st1) := aalu st op (getreg st (regn rs1)) (alit (immz imm)) in
                        SNext (set_pc (wr st1 (regn rd) r) (s_pc st + sz))
              end).
    { destruct (alu_split st _ _ _) as [l0|] eqn:Es.
      - apply sound_split; [exact Hwf | exact HR | eapply alu_split_below; [exact Es | exact Bv1 | apply alit_below]].
      - eapply sound_valop; [exact Hwf | exact HR | | exact STEP].
        apply aalu_sound; side_tac Hwf HR. }
    unfold opimm_special. destruct (Z.eqb_spec (immz imm) 1) as [E1|NE]; [|exact GEN].
    assert (Himm : sext 64 imm = w64 1) by (rewrite sext_w64; unfold immz in E1; rewrite E1; reflexivity).
    rewrite Himm in STEP.
    destruct op; try exact GEN.
    - (* [comment removed for export] *) eapply sound_valop; [exact Hwf | exact HR | | exact STEP].
      rewrite sltu_1. apply is_zero_cond_sound; assumption.
    - (* [comment removed for export] *)
      destruct (getreg st (regn rs1)) as [|l|n k x y|x y] eqn:Ev; try exact GEN.
      eapply (sound_valop rho st ms rd sz (_, st)); [exact Hwf | exact HR | | exact STEP].
      exists rho. unfold VOK; cbn [fst snd]. split; [apply vext_refl|]. split; [exact HVS|]. split; [apply xor_cv_1; exact Hv1 | exact Bv1].
  Qed.

  Lemma sound_shiftimm : forall rho st ms op rd rs1 shamt sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (ShiftImm op rd rs1 shamt) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (ShiftImm op rd rs1 shamt) sz).
  Proof.
    intros rho st ms op rd rs1 shamt sz Hwf HR Hcan. cbn [exec_instr].
    pose proof (getreg_sound rho st ms rs1 HR) as Hv1. pose proof (getreg_below st (regn rs1) Hwf) as Bv1.
    pose proof (R_VS _ _ _ HR) as HVS.
    assert (STEP : cstep ms (ms_of ms (rset rd (alu64 op (rget (core_of ms) rs1) (zext 64 shamt))
                                       (with_pc (c_pc (core_of ms) + Z_to_bv 64 sz)%bv (core_of ms))) (ms_mem ms))).
    { apply Hcan. cbn [exec]. rewrite interp_done. reflexivity. }
    destruct (alu_split st _ _ _) as [l0|] eqn:Es.
    - apply sound_split; [exact Hwf | exact HR | eapply alu_split_below; [exact Es | exact Bv1 | apply alit_below]].
    - eapply sound_valop; [exact Hwf | exact HR | | exact STEP]. apply aalu_sound; side_tac Hwf HR.
  Qed.

  Lemma sound_op : forall rho st ms op rd rs1 rs2 sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Op op rd rs1 rs2) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Op op rd rs1 rs2) sz).
  Proof.
    intros rho st ms op rd rs1 rs2 sz Hwf HR Hcan. cbn [exec_instr].
    pose proof (getreg_sound rho st ms rs1 HR) as Hv1. pose proof (getreg_below st (regn rs1) Hwf) as Bv1.
    pose proof (getreg_sound rho st ms rs2 HR) as Hv2. pose proof (getreg_below st (regn rs2) Hwf) as Bv2.
    pose proof (R_VS _ _ _ HR) as HVS.
    assert (STEP : cstep ms (ms_of ms (rset rd (alu64 op (rget (core_of ms) rs1) (rget (core_of ms) rs2))
                                       (with_pc (c_pc (core_of ms) + Z_to_bv 64 sz)%bv (core_of ms))) (ms_mem ms))).
    { apply Hcan. cbn [exec]. rewrite interp_done. reflexivity. }
    assert (GEN : sound_res rho (s_next st) ms
              match alu_split st op (getreg st (regn rs1)) (getreg st (regn rs2)) with
              | Some l => split_on st l
              | None => let (r, st1) := aalu st op (getreg st (regn rs1)) (getreg st (regn rs2)) in
                        SNext (set_pc (wr st1 (regn rd) r) (s_pc st + sz))
              end).
    { destruct (alu_split st _ _ _) as [l0|] eqn:Es.
      - apply sound_split; [exact Hwf | exact HR | eapply alu_split_below; [exact Es | exact Bv1 | exact Bv2]].
      - eapply sound_valop; [exact Hwf | exact HR | | exact STEP]. apply aalu_sound; side_tac Hwf HR. }
    unfold op_special. destruct op; try exact GEN. destruct (regn rs1) as [|n1] eqn:E0; [|exact GEN].
    (* [comment removed for export] *)
    eapply sound_valop; [exact Hwf | exact HR | | exact STEP].
    assert (Hx0 : rget (core_of ms) rs1 = w64 0).
    { unfold rget. rewrite (proj1 (regn_zero rs1) E0). reflexivity. }
    rewrite Hx0, sltu_x0. apply is_nonzero_cond_sound; assumption.
  Qed.

  Lemma low32_sext32 : forall (imm : bv 12), sext 32 imm = low32 (w64 (bv_signed imm)).
  Proof.
    intros imm. apply bv_eq. unfold low32, w64, sext. rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned, bv_sign_extend_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 32 * 2 ^ 32). change (bv_modulus 32) with (2 ^ 32).
    rewrite Zaux.Zmod_mod_mult by lia. reflexivity.
  Qed.
  Lemma low32_zext32 : forall {n} (s : bv n), zext 32 s = low32 (w64 (bv_unsigned s)).
  Proof.
    intros n s. apply bv_eq. unfold low32, w64, zext. rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned, bv_zero_extend_unsigned'.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 32 * 2 ^ 32). change (bv_modulus 32) with (2 ^ 32).
    rewrite Zaux.Zmod_mod_mult by lia. reflexivity.
  Qed.

  Lemma sound_opimm32 : forall rho st ms rd rs1 imm sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (OpImm32 rd rs1 imm) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (OpImm32 rd rs1 imm) sz).
  Proof.
    intros rho st ms rd rs1 imm sz Hwf HR Hcan. cbn [exec_instr].
    pose proof (getreg_sound rho st ms rs1 HR) as Hv1. pose proof (getreg_below st (regn rs1) Hwf) as Bv1.
    pose proof (R_VS _ _ _ HR) as HVS.
    eapply sound_valop; [exact Hwf | exact HR | | apply Hcan; cbn [exec]; rewrite interp_done; reflexivity].
    rewrite low32_sext32. apply aaluw_sound; side_tac Hwf HR.
  Qed.

  Lemma sound_shiftimm32 : forall rho st ms op rd rs1 shamt sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (ShiftImm32 op rd rs1 shamt) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (ShiftImm32 op rd rs1 shamt) sz).
  Proof.
    intros rho st ms op rd rs1 shamt sz Hwf HR Hcan. cbn [exec_instr].
    pose proof (getreg_sound rho st ms rs1 HR) as Hv1. pose proof (getreg_below st (regn rs1) Hwf) as Bv1.
    pose proof (R_VS _ _ _ HR) as HVS.
    eapply sound_valop; [exact Hwf | exact HR | | apply Hcan; cbn [exec]; rewrite interp_done; reflexivity].
    rewrite low32_zext32. apply aaluw_sound; side_tac Hwf HR.
  Qed.

  Lemma sound_op32 : forall rho st ms op rd rs1 rs2 sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Op32 op rd rs1 rs2) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Op32 op rd rs1 rs2) sz).
  Proof.
    intros rho st ms op rd rs1 rs2 sz Hwf HR Hcan. cbn [exec_instr].
    pose proof (getreg_sound rho st ms rs1 HR) as Hv1. pose proof (getreg_below st (regn rs1) Hwf) as Bv1.
    pose proof (getreg_sound rho st ms rs2 HR) as Hv2. pose proof (getreg_below st (regn rs2) Hwf) as Bv2.
    pose proof (R_VS _ _ _ HR) as HVS.
    eapply sound_valop; [exact Hwf | exact HR | | apply Hcan; cbn [exec]; rewrite interp_done; reflexivity].
    apply aaluw_sound; side_tac Hwf HR.
  Qed.

  Lemma sound_mul : forall rho st ms op rd rs1 rs2 sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Mul op rd rs1 rs2) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Mul op rd rs1 rs2) sz).
  Proof.
    intros rho st ms op rd rs1 rs2 sz Hwf HR Hcan. cbn [exec_instr].
    pose proof (getreg_sound rho st ms rs1 HR) as Hv1. pose proof (getreg_below st (regn rs1) Hwf) as Bv1.
    pose proof (getreg_sound rho st ms rs2 HR) as Hv2. pose proof (getreg_below st (regn rs2) Hwf) as Bv2.
    pose proof (R_VS _ _ _ HR) as HVS.
    eapply sound_valop; [exact Hwf | exact HR | | apply Hcan; cbn [exec]; rewrite interp_done; reflexivity].
    apply amuldiv_sound; side_tac Hwf HR.
  Qed.

  Lemma sound_mul32 : forall rho st ms op rd rs1 rs2 sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Mul32 op rd rs1 rs2) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Mul32 op rd rs1 rs2) sz).
  Proof.
    intros rho st ms op rd rs1 rs2 sz Hwf HR Hcan. cbn [exec_instr].
    pose proof (getreg_sound rho st ms rs1 HR) as Hv1. pose proof (getreg_below st (regn rs1) Hwf) as Bv1.
    pose proof (getreg_sound rho st ms rs2 HR) as Hv2. pose proof (getreg_below st (regn rs2) Hwf) as Bv2.
    pose proof (R_VS _ _ _ HR) as HVS.
    eapply sound_valop; [exact Hwf | exact HR | | apply Hcan; cbn [exec]; rewrite interp_done; reflexivity].
    apply amuldivw_sound; side_tac Hwf HR.
  Qed.

  Lemma sound_auipc : forall rho st ms rd imm sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Auipc rd imm) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Auipc rd imm) sz).
  Proof.
    intros rho st ms rd imm sz Hwf HR Hcan. cbn [exec_instr sound_res].
    eexists _, rho. split; [|split; [|split; [apply agree_refl | nxt]]].
    - apply Hcan. cbn [exec]. rewrite interp_done. reflexivity.
    - rewrite lui_w64, <- with_pc_rset, (npc_eq rho st ms sz HR). apply set_pc_sound. apply wr_sound; [exact HR |].
      apply alit_ok'. cbn [c_pc core_of]. rewrite (r_pc _ _ _ _ _ _ HR), <- w64_add. reflexivity.
  Qed.

  Lemma sound_jal : forall rho st ms rd imm sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Jal rd imm) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Jal rd imm) sz).
  Proof.
    intros rho st ms rd imm sz Hwf HR Hcan. cbn [exec_instr sound_res].
    eexists _, rho. split; [|split; [|split; [apply agree_refl | nxt]]].
    - apply Hcan. cbn [exec]. rewrite interp_done. reflexivity.
    - rewrite <- with_pc_rset. cbn [c_pc core_of]. rewrite (r_pc _ _ _ _ _ _ HR), sext_w64, <- w64_add.
      apply set_pc_sound. apply wr_sound; [exact HR |]. apply alit_ok'. rewrite w64_add. reflexivity.
  Qed.

  Lemma sound_fence : forall rho st ms a b c d e sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Fence a b c d e) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Fence a b c d e) sz).
  Proof.
    intros rho st ms a b c d e sz Hwf HR Hcan. cbn [exec_instr sound_res].
    eexists _, rho. split; [|split; [|split; [apply agree_refl | nxt]]].
    - apply Hcan. cbn [exec]. rewrite interp_done. reflexivity.
    - rewrite (npc_eq rho st ms sz HR). apply set_pc_sound. apply R_ms_of. exact HR.
  Qed.
  Lemma sound_fencei : forall rho st ms a b c sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (FenceI a b c) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (FenceI a b c) sz).
  Proof.
    intros rho st ms a b c sz Hwf HR Hcan. cbn [exec_instr sound_res].
    eexists _, rho. split; [|split; [|split; [apply agree_refl | nxt]]].
    - apply Hcan. cbn [exec]. rewrite interp_done. reflexivity.
    - rewrite (npc_eq rho st ms sz HR). apply set_pc_sound. apply R_ms_of. exact HR.
  Qed.

  Lemma even_land_clear0 : forall r, 0 <= r < 2 ^ 64 -> r mod 4 = 0 ->
    (Z.land (r mod 2 ^ 64) (2 ^ 64 - 2)) mod 2 ^ 64 = r mod 2 ^ 64.
  Proof.
    intros r Hr Hm. rewrite <- (land_clear0_mod r r) by reflexivity.
    f_equal. change (-2) with (- 2 ^ 1). rewrite <- (Z.mod_small r (2 ^ 64)) at 1 by lia.
    replace (Z.land (r mod 2 ^ 64) (- 2 ^ 1)) with (Z.land r (2 ^ 64 - 2 ^ 1)).
    - rewrite land_clear_low by lia. change (2 ^ 1) with 2.
      pose proof (Z.div_mod r 4 ltac:(lia)) as Hd. rewrite Hm, Z.add_0_r in Hd.
      rewrite Hd at 1. replace (4 * (r / 4)) with ((r / 4 * 2) * 2) by lia. rewrite Z.div_mul by lia. lia.
    - rewrite Z.mod_small by lia. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
      destruct (Z.lt_ge_cases i 64) as [L|Ge].
      + f_equal. replace (2 ^ 64 - 2 ^ 1) with ((- 2 ^ 1) mod 2 ^ 64) by reflexivity. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
      + assert (T : Z.testbit r i = false).
        { destruct (Z.eq_dec r 0) as [->|NE]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
          assert (Hl : Z.log2 r < 64) by (apply Z.log2_lt_pow2; lia). lia. }
        rewrite T. reflexivity.
  Qed.

  Lemma sound_jalr : forall rho st ms rd rs1 imm sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Jalr rd rs1 imm) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Jalr rd rs1 imm) sz).
  Proof.
    intros rho st ms rd rs1 imm sz Hwf HR Hcan. cbn [exec_instr].
    pose proof (getreg_sound rho st ms rs1 HR) as Hv1.
    assert (STEP : cstep ms (ms_of ms (rset rd (c_pc (core_of ms) + Z_to_bv 64 sz)%bv
                       (with_pc (bv_and (rget (core_of ms) rs1 + sext 64 imm)%bv (bv_not w1)) (core_of ms))) (ms_mem ms))).
    { apply Hcan. cbn [exec]. rewrite interp_done. reflexivity. }
    destruct (getreg st (regn rs1)) as [|l| |] eqn:Ev; try exact I.
    cbn in Hv1.
    destruct (is_const l) as [c|] eqn:Kl.
    - cbn [sound_res]. eexists _, rho. split; [exact STEP|]. split; [|split; [apply agree_refl | nxt]].
      rewrite <- with_pc_rset. unfold w1. rewrite (jalr_tgt_w64 _ imm c) by (rewrite Hv1, (is_const_sound rho l c Kl); reflexivity).
      apply set_pc_sound. apply wr_sound; [exact HR|]. apply alit_ok'. apply (npc_eq rho st ms sz HR).
    - destruct (is_var l) as [x|] eqn:Vl; [|exact I].
      destruct ((Nat.eqb x SYM_RA &&& Z.eqb (immz imm) 0) &&& Nat.eqb (regn rd) 0)%bool eqn:E; [|exact I].
      apply andb_prop in E as [E Erd]. apply andb_prop in E as [Ex Ei].
      apply Nat.eqb_eq in Ex. apply Z.eqb_eq in Ei. apply Nat.eqb_eq in Erd. subst x.
      cbn [sound_res]. eexists _. split; [exact STEP|]. split; [|nxt].
      unfold rset. rewrite (proj1 (regn_zero rd) Erd).
      rewrite (is_var_sound rho l SYM_RA Vl) in Hv1.
      pose proof (r_ra _ _ _ _ _ _ HR) as [Rr Rm].
      replace (bv_and (rget (core_of ms) rs1 + sext 64 imm) (bv_not w1)) with (w64 (rho SYM_RA)).
      2:{ unfold w1. rewrite (jalr_tgt_w64 _ imm (rho SYM_RA)) by exact Hv1. unfold immz in Ei. rewrite Ei, Z.add_0_r.
          apply w64_eq_mod. symmetry. change two64 with (2 ^ 64). apply even_land_clear0; assumption. }
      apply set_pc_sound. apply R_ms_of. exact HR.
  Qed.

  Lemma with_pc_with_pc : forall p q c, with_pc p (with_pc q c) = with_pc p c.
  Proof. reflexivity. Qed.
  Lemma with_pc_self : forall c p, c_pc c = p -> with_pc p c = c.
  Proof. intros [] p H; cbn in *; subst; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma sound_valop_core : forall rho st ms rd sz (p : aval * astate) (wv : word) (cb : core),
    wf_state st = true -> R U G M0 rho st ms ->
    (exists rho', VOK rho st p rho' wv) ->
    c_regs cb = ms_regs ms -> c_pc cb = w64 (s_pc st + sz) -> c_resv cb = ms_resv ms -> frm_ok (c_fcsr cb) ->
    cstep ms (ms_of ms (rset rd wv cb) (ms_mem ms)) ->
    sound_res rho (s_next st) ms (let (r, st1) := p in SNext (set_pc (wr st1 (regn rd) r) (s_pc st + sz))).
  Proof.
    intros rho st ms rd sz [r st1] wv cb Hwf HR (rho' & A & B & C & D) Hregs Hpc Hresv Hfrm Hstep. cbn [fst snd] in *.
    cbn [sound_res]. exists (ms_of ms (rset rd wv cb) (ms_mem ms)), rho'. split; [exact Hstep|]. split; [|split; [exact (proj1 A) | nxt; exact (proj1 (proj2 A))]].
    assert (Epc : s_pc st1 = s_pc st) by (destruct A as (_ & _ & E & _); exact E).
    assert (HR1 : R U G M0 rho' st1 ms) by (eapply R_vext; eauto).
    assert (HR2 : R U G M0 rho' st1 (ms_of ms (with_pc (ms_pc_val ms) cb) (ms_mem ms))).
    { eapply R_core_upd; try reflexivity; try exact HR1.
      - cbn. rewrite (r_pc _ _ _ _ _ _ HR1). reflexivity.
      - cbn. rewrite Hregs. exact (r_regs _ _ _ _ _ _ HR1).
      - cbn. rewrite Hresv. exact (r_resv _ _ _ _ _ _ HR1).
      - cbn. exact Hfrm. }
    pose proof (wr_sound rho' st1 (ms_of ms (with_pc (ms_pc_val ms) cb) (ms_mem ms)) rd r wv HR2 C) as HR3.
    rewrite core_of_ms_of in HR3. cbn [ms_mem ms_of] in HR3. rewrite ms_of_idem in HR3.
    pose proof (set_pc_sound rho' _ ms _ _ (s_pc st + sz) HR3) as HR4.
    rewrite with_pc_rset, with_pc_with_pc, (with_pc_self cb) in HR4 by (rewrite Hpc; reflexivity).
    exact HR4.
  Qed.

  (* [comment removed for export] *)
  Lemma sound_coreop : forall rho st ms sz (cb : core),
    R U G M0 rho st ms ->
    c_regs cb = ms_regs ms -> c_pc cb = w64 (s_pc st + sz) -> c_resv cb = ms_resv ms -> frm_ok (c_fcsr cb) ->
    cstep ms (ms_of ms cb (ms_mem ms)) ->
    sound_res rho (s_next st) ms (SNext (set_pc st (s_pc st + sz))).
  Proof.
    intros rho st ms sz cb HR Hregs Hpc Hresv Hfrm Hstep.
    cbn [sound_res]. eexists _, rho. split; [exact Hstep|]. split; [|split; [apply agree_refl | nxt]].
    apply (R_core_upd rho st ms); try reflexivity; try exact HR.
    - exact Hpc.
    - cbn. rewrite Hregs. exact (r_regs _ _ _ _ _ _ HR).
    - cbn. rewrite Hresv. exact (r_resv _ _ _ _ _ _ HR).
    - exact Hfrm.
  Qed.

  Lemma resolve_rm_some : forall rm c, rm_ok rm = true -> frm_ok (c_fcsr c) -> exists md, resolve_rm rm c = Some md.
  Proof.
    intros rm c Hok Hfrm. unfold resolve_rm, rmode_of_field, frm_of. unfold frm_ok in Hfrm. rewrite Hfrm.
    unfold rm_ok in Hok. pose proof (bv_unsigned_in_range _ rm) as Hr. change (bv_modulus 3) with 8 in Hr.
    destruct (Z.eqb_spec (bv_unsigned rm) 7) as [E|NE]; [eexists; reflexivity|].
    unfold rmode_of_Z. assert (Hle : bv_unsigned rm <= 4) by (destruct (Z.leb_spec (bv_unsigned rm) 4); [lia | discriminate]).
    destruct (Z.eqb_spec (bv_unsigned rm) 0); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 1); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 2); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 3); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 4); [eexists; reflexivity|]. lia.
  Qed.

  Lemma frm_ok_accrue_c : forall fl c, frm_ok (c_fcsr c) -> frm_ok (c_fcsr (accrue fl c)).
  Proof. intros fl c H. unfold accrue. cbn. apply frm_ok_accrue. exact H. Qed.

  Lemma c_regs_fwrite : forall fmt rd v c, c_regs (fwrite fmt rd v c) = c_regs c.
  Proof. intros [] rd v c; reflexivity. Qed.
  Lemma c_pc_fwrite : forall fmt rd v c, c_pc (fwrite fmt rd v c) = c_pc c.
  Proof. intros [] rd v c; reflexivity. Qed.
  Lemma c_resv_fwrite : forall fmt rd v c, c_resv (fwrite fmt rd v c) = c_resv c.
  Proof. intros [] rd v c; reflexivity. Qed.
  Lemma c_fcsr_fwrite : forall fmt rd v c, c_fcsr (fwrite fmt rd v c) = c_fcsr c.
  Proof. intros [] rd v c; reflexivity. Qed.

  Ltac coreop_tac HR Hcan :=
    eapply sound_coreop; [exact HR | | | | | apply Hcan];
    rewrite ?c_regs_fwrite, ?c_pc_fwrite, ?c_resv_fwrite, ?c_fcsr_fwrite; cbn [c_regs c_pc c_resv c_fcsr accrue with_fcsr with_pc fset with_fregs core_of];
    try reflexivity.

  Lemma sound_fari : forall rho st ms op fmt rd rs1 rs2 rm sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Fari op fmt rd rs1 rs2 rm) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Fari op fmt rd rs1 rs2 rm) sz).
  Proof.
    intros rho st ms op fmt rd rs1 rs2 rm sz Hwf HR Hcan. cbn [exec_instr].
    destruct (rm_ok rm) eqn:Hrm; [|exact I].
    destruct (resolve_rm_some rm (with_pc (c_pc (core_of ms) + Z_to_bv 64 sz)%bv (core_of ms)) Hrm (r_frm _ _ _ _ _ _ HR)) as [md Hmd].
    unfold can_exec in Hcan. cbn [exec] in Hcan. rewrite Hmd in Hcan.
    destruct (match op with F_ADD => fp_add (fp_format fmt) md (fread (core_of ms) fmt rs1) (fread (core_of ms) fmt rs2)
                          | F_SUB => fp_sub (fp_format fmt) md (fread (core_of ms) fmt rs1) (fread (core_of ms) fmt rs2)
                          | F_MUL => fp_mul (fp_format fmt) md (fread (core_of ms) fmt rs1) (fread (core_of ms) fmt rs2)
                          | F_DIV => fp_div (fp_format fmt) md (fread (core_of ms) fmt rs1) (fread (core_of ms) fmt rs2) end) as [v fl] eqn:Eop.
    eapply sound_coreop; [exact HR | | | | | apply Hcan; rewrite interp_done; reflexivity].
    - rewrite c_regs_fwrite. reflexivity.
    - rewrite c_pc_fwrite. cbn [c_pc accrue with_fcsr with_pc]. apply (npc_eq rho st ms sz HR).
    - rewrite c_resv_fwrite. reflexivity.
    - rewrite c_fcsr_fwrite. apply frm_ok_accrue_c. cbn. exact (r_frm _ _ _ _ _ _ HR).
  Qed.

  Ltac fin_coreop rho st ms sz HR :=
    first [ rewrite ?c_regs_fwrite; reflexivity
          | rewrite ?c_resv_fwrite; reflexivity
          | rewrite ?c_pc_fwrite; cbn [c_pc accrue with_fcsr with_pc fset with_fregs rset with_regs]; apply (npc_eq rho st ms sz HR)
          | rewrite ?c_fcsr_fwrite; try apply frm_ok_accrue_c; cbn; exact (r_frm _ _ _ _ _ _ HR) ].

  Lemma sound_fsqrt : forall rho st ms fmt rd rs1 rm sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Fsqrt fmt rd rs1 rm) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Fsqrt fmt rd rs1 rm) sz).
  Proof.
    intros rho st ms fmt rd rs1 rm sz Hwf HR Hcan. cbn [exec_instr].
    destruct (rm_ok rm) eqn:Hrm; [|exact I].
    destruct (resolve_rm_some rm (with_pc (c_pc (core_of ms) + Z_to_bv 64 sz)%bv (core_of ms)) Hrm (r_frm _ _ _ _ _ _ HR)) as [md Hmd].
    unfold can_exec in Hcan. cbn [exec] in Hcan. rewrite Hmd in Hcan.
    destruct (fp_sqrt (fp_format fmt) md (fread (core_of ms) fmt rs1)) as [v fl] eqn:Eop.
    eapply sound_coreop; [exact HR | | | | | apply Hcan; rewrite interp_done; reflexivity]; fin_coreop rho st ms sz HR.
  Qed.

  Lemma sound_fma : forall rho st ms op fmt rd rs1 rs2 rs3 rm sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Fma op fmt rd rs1 rs2 rs3 rm) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Fma op fmt rd rs1 rs2 rs3 rm) sz).
  Proof.
    intros rho st ms op fmt rd rs1 rs2 rs3 rm sz Hwf HR Hcan. cbn [exec_instr].
    destruct (rm_ok rm) eqn:Hrm; [|exact I].
    destruct (resolve_rm_some rm (with_pc (c_pc (core_of ms) + Z_to_bv 64 sz)%bv (core_of ms)) Hrm (r_frm _ _ _ _ _ _ HR)) as [md Hmd].
    unfold can_exec in Hcan. cbn [exec] in Hcan. rewrite Hmd in Hcan.
    match type of Hcan with context [let '(a', z') := ?p in _] => destruct p as [a' z'] end.
    match type of Hcan with context [let '(v, fl) := ?p in _] => destruct p as [v fl] end.
    eapply sound_coreop; [exact HR | | | | | apply Hcan; rewrite interp_done; reflexivity]; fin_coreop rho st ms sz HR.
  Qed.

  Lemma sound_fsgnj : forall rho st ms op fmt rd rs1 rs2 sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Fsgnj op fmt rd rs1 rs2) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Fsgnj op fmt rd rs1 rs2) sz).
  Proof.
    intros rho st ms op fmt rd rs1 rs2 sz Hwf HR Hcan. cbn [exec_instr].
    unfold can_exec in Hcan. cbn [exec] in Hcan.
    destruct fmt; (eapply sound_coreop; [exact HR | | | | | apply Hcan; rewrite interp_done; reflexivity]; fin_coreop rho st ms sz HR).
  Qed.

  Lemma sound_fminmax : forall rho st ms op fmt rd rs1 rs2 sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Fminmax op fmt rd rs1 rs2) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Fminmax op fmt rd rs1 rs2) sz).
  Proof.
    intros rho st ms op fmt rd rs1 rs2 sz Hwf HR Hcan. cbn [exec_instr].
    unfold can_exec in Hcan. cbn [exec] in Hcan.
    match type of Hcan with context [let '(v, fl) := ?p in _] => destruct p as [v fl] end.
    eapply sound_coreop; [exact HR | | | | | apply Hcan; rewrite interp_done; reflexivity]; fin_coreop rho st ms sz HR.
  Qed.

  Lemma sound_fp_int : forall rho st ms rd sz i (wv : word) (z : Z) (cb : core),
    wf_state st = true -> R U G M0 rho st ms ->
    wv = w64 z -> in_itv z i ->
    c_regs cb = ms_regs ms -> c_pc cb = w64 (s_pc st + sz) -> c_resv cb = ms_resv ms -> frm_ok (c_fcsr cb) ->
    cstep ms (ms_of ms (rset rd wv cb) (ms_mem ms)) ->
    sound_res rho (s_next st) ms (fp_int_result st (regn rd) i (s_pc st + sz)).
  Proof.
    intros rho st ms rd sz i wv z cb Hwf HR Hw Hi Hregs Hpc Hresv Hfrm Hstep. unfold fp_int_result.
    eapply (sound_valop_core rho st ms rd sz (fresh_val st i) wv cb); try assumption.
    apply VOK_fresh with (v := z); [exact (R_VS _ _ _ HR) | exact Hi | exact Hw].
  Qed.

  Lemma sound_fcmp : forall rho st ms op fmt rd rs1 rs2 sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Fcmp op fmt rd rs1 rs2) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Fcmp op fmt rd rs1 rs2) sz).
  Proof.
    intros rho st ms op fmt rd rs1 rs2 sz Hwf HR Hcan. cbn [exec_instr].
    unfold can_exec in Hcan. cbn [exec] in Hcan.
    match type of Hcan with context [let '(v, fl) := ?p in _] => destruct p as [v fl] end.
    eapply (sound_fp_int rho st ms rd sz itv01 (if v then w1 else w0) (if v then 1 else 0));
      [exact Hwf | exact HR | destruct v; reflexivity | unfold itv01, in_itv; cbn; destruct v; lia | | | | | apply Hcan; rewrite interp_done; reflexivity];
      fin_coreop rho st ms sz HR.
  Qed.

  Lemma fp_class_range : forall f a, 0 <= fp_class f a <= 1023.
  Proof.
    intros f a. unfold fp_class.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; rewrite ?Z.shiftl_1_l; cbn; lia.
  Qed.

  Lemma sound_fclass : forall rho st ms fmt rd rs1 sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Fclass fmt rd rs1) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Fclass fmt rd rs1) sz).
  Proof.
    intros rho st ms fmt rd rs1 sz Hwf HR Hcan. cbn [exec_instr].
    unfold can_exec in Hcan. cbn [exec] in Hcan.
    eapply (sound_fp_int rho st ms rd sz _ _ (fp_class (fp_format fmt) (fread (core_of ms) fmt rs1)));
      [exact Hwf | exact HR | reflexivity | pose proof (fp_class_range (fp_format fmt) (fread (core_of ms) fmt rs1)); unfold in_itv; cbn; lia
      | | | | | apply Hcan; rewrite interp_done; reflexivity];
      fin_coreop rho st ms sz HR.
  Qed.

  Lemma sound_fmv : forall rho st ms dir fmt rd rs1 sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Fmv dir fmt rd rs1) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Fmv dir fmt rd rs1) sz).
  Proof.
    intros rho st ms dir fmt rd rs1 sz Hwf HR Hcan. cbn [exec_instr].
    unfold can_exec in Hcan. cbn [exec] in Hcan.
    destruct dir, fmt.
    - destruct (sext32_is_w64 (low32 (fget (core_of ms) rs1))) as (z & Hz & Rz).
      eapply (sound_fp_int rho st ms rd sz _ _ z);
        [exact Hwf | exact HR | exact Hz | unfold itv_s32, in_itv; cbn [ilo ihi]; unfold LXI.two31; rewrite two31_eq; lia
        | | | | | apply Hcan; rewrite interp_done; reflexivity]; fin_coreop rho st ms sz HR.
    - eapply (sound_fp_int rho st ms rd sz _ _ (bv_unsigned (fget (core_of ms) rs1)));
        [exact Hwf | exact HR | symmetry; apply w64_of_unsigned
        | pose proof (u64_range (fget (core_of ms) rs1)); unfold itv_u64, in_itv; cbn [ilo ihi]; unfold LXI.two64; rewrite two64_eq; lia
        | | | | | apply Hcan; rewrite interp_done; reflexivity]; fin_coreop rho st ms sz HR.
    - eapply sound_coreop; [exact HR | | | | | apply Hcan; rewrite interp_done; reflexivity]; fin_coreop rho st ms sz HR.
    - eapply sound_coreop; [exact HR | | | | | apply Hcan; rewrite interp_done; reflexivity]; fin_coreop rho st ms sz HR.
  Qed.

  Lemma sound_fcvt : forall rho st ms dst src rd rs1 rm sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Fcvt dst src rd rs1 rm) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Fcvt dst src rd rs1 rm) sz).
  Proof.
    intros rho st ms dst src rd rs1 rm sz Hwf HR Hcan. cbn [exec_instr].
    destruct (rm_ok rm) eqn:Hrm; [|exact I]. cbn [negb].
    destruct (resolve_rm_some rm (with_pc (c_pc (core_of ms) + Z_to_bv 64 sz)%bv (core_of ms)) Hrm (r_frm _ _ _ _ _ _ HR)) as [md Hmd].
    unfold can_exec in Hcan. cbn [exec] in Hcan. rewrite Hmd in Hcan.
    destruct dst, src; cbn iota in Hcan |- *; try exact I;
      try match type of Hcan with context [let '(v, fl) := ?p in _] => destruct p as [v fl] end;
      first
        [ eapply sound_coreop; [exact HR | | | | | apply Hcan; rewrite interp_done; reflexivity]; fin_coreop rho st ms sz HR
        | destruct (sext32_is_w64 (Z_to_bv 32 v)) as (z & Hz & Rz);
          eapply (sound_fp_int rho st ms rd sz _ _ z);
            [exact Hwf | exact HR | exact Hz | unfold itv_s32, in_itv; cbn [ilo ihi]; unfold LXI.two31; rewrite two31_eq; lia
            | | | | | apply Hcan; rewrite interp_done; reflexivity]; fin_coreop rho st ms sz HR
        | eapply (sound_fp_int rho st ms rd sz _ _ v);
            [exact Hwf | exact HR | reflexivity | apply itop_sound
            | | | | | apply Hcan; rewrite interp_done; reflexivity]; fin_coreop rho st ms sz HR ].
  Qed.

  (* [comment removed for export] *)
  Lemma signed_neg_iff : forall w : word, (bv_signed w <? 0) = (2 ^ 63 - 1 <? bv_unsigned w).
  Proof.
    intros w. pose proof (bv_unsigned_in_range _ w) as R. unfold bv_modulus in R.
    rewrite <- (w64_of_unsigned w) at 1. unfold w64. rewrite Z_to_bv_signed.
    unfold bv_swrap. rewrite bv_wrap64_mod. change (bv_half_modulus 64) with (2 ^ 63).
    change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
    destruct (Z.ltb_spec (2 ^ 63 - 1) (bv_unsigned w)).
    - replace (bv_unsigned w + 2 ^ 63) with ((bv_unsigned w - 2 ^ 63) + 1 * 2 ^ 64) by lia.
      rewrite Z_mod_plus_full, Z.mod_small by lia. apply Z.ltb_lt. lia.
    - rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
  Qed.

  Lemma sign_test_sound : forall rho C x x2 n cc wa wb,
    ctx_ok rho C -> wa = w64 (evl rho x) -> wb = w64 (evl rho x2) -> sign_test C x x2 n = Some cc ->
    let '(n', k, x0, y0) := cc in (bv_signed wa <? bv_signed wb) = xorb n (xorb n' (cmp_holds rho k x0 y0)).
  Proof.
    intros rho C x x2 n cc wa wb HC Ha Hb Hs. unfold sign_test in Hs.
    destruct (is_const x2) as [[|p|p]|] eqn:K; try discriminate.
    destruct (uview C x) as [x'|] eqn:U1; [|discriminate]. injection Hs; intros <-.
    cbn [cmp_holds]. rewrite lconst_sound, <- (uview_unsigned rho _ x x' wa HC U1 Ha).
    rewrite Hb, (is_const_sound rho x2 0 K). replace (bv_signed (w64 0)) with 0 by (vm_compute; reflexivity).
    rewrite signed_neg_iff. replace (two63 - 1) with (2 ^ 63 - 1) by reflexivity.
    destruct n; destruct (2 ^ 63 - 1 <? bv_unsigned wa); reflexivity.
  Qed.

  Lemma cond_of_branch_sound : forall rho st bc a b wa wb c,
    VS rho st -> val_ok rho a wa -> val_ok rho b wb ->
    cond_of_branch st bc a b = Some c ->
    let '(n, k, x, y) := c in branch_taken bc wa wb = xorb n (cmp_holds rho k x y).
  Proof.
    intros rho st bc a b wa wb c HVS Ha Hb H. pose proof (proj1 HVS) as HC.
    unfold cond_of_branch in H.
    assert (EQW : forall x y (u v : word), u = w64 (evl rho x) -> v = w64 (evl rho y) ->
              bv_eqb u v = cmp_holds rho CK_EQ x y).
    { intros x y u v -> ->. cbn [cmp_holds]. rewrite two64z_eq. unfold bv_eqb. rewrite !w64_unsigned. reflexivity. }
    assert (CVW : forall n k x y (u v : word) z, val_ok rho (CV n k x y) u -> v = w64 z -> z = 0 ->
              bv_eqb u v = negb (xorb n (cmp_holds rho k x y)) /\ bv_eqb v u = negb (xorb n (cmp_holds rho k x y))).
    { intros n k x y u v z Hu -> ->. cbn in Hu. rewrite Hu. unfold bv_eqb. rewrite !w64_unsigned.
      destruct (xorb n (cmp_holds rho k x y)); split; reflexivity. }
    assert (XVW : forall x y (u v : word) z, val_ok rho (XV x y) u -> v = w64 z -> z = 0 ->
              bv_eqb u v = cmp_holds rho CK_EQ x y /\ bv_eqb v u = cmp_holds rho CK_EQ x y).
    { intros x y u v z Hu -> ->. cbn in Hu. cbn [cmp_holds]. rewrite two64z_eq. subst u. unfold bv_eqb.
      rewrite bv_xor_unsigned, !w64_unsigned, Z.mod_0_l by lia.
      pose proof (Z.mod_pos_bound (evl rho x) (2 ^ 64) ltac:(lia)). pose proof (Z.mod_pos_bound (evl rho y) (2 ^ 64) ltac:(lia)).
      assert (L : (Z.lxor (evl rho x mod 2 ^ 64) (evl rho y mod 2 ^ 64) =? 0) = (evl rho x mod 2 ^ 64 =? evl rho y mod 2 ^ 64)).
      { destruct (Z.eqb_spec (evl rho x mod 2 ^ 64) (evl rho y mod 2 ^ 64)) as [E|NE].
        - rewrite E, Z.lxor_nilpotent. reflexivity.
        - destruct (Z.eqb_spec (Z.lxor (evl rho x mod 2 ^ 64) (evl rho y mod 2 ^ 64)) 0) as [E0|]; [|reflexivity].
          exfalso. apply NE. apply Z.lxor_eq_0_iff. exact E0. }
      split.
      - exact L.
      - rewrite (Z.eqb_sym 0), L. reflexivity. }
    destruct bc; destruct a as [|x|n k x y|x y]; try discriminate; destruct b as [|x2|n2 k2 x2 y2|x2 y2]; try discriminate;
      cbn [branch_taken].
    all: try (injection H; intros <-; cbn in Ha, Hb; rewrite (EQW _ _ wa wb Ha Hb); reflexivity).
    all: try (cbn in Hb; destruct (is_const x2) as [[|p|p]|] eqn:K; try discriminate; injection H; intros <-;
              pose proof (is_const_sound rho x2 0 K) as K0;
              first [ destruct (CVW _ _ _ _ wa wb _ Ha Hb K0) as [-> _] | destruct (XVW _ _ wa wb _ Ha Hb K0) as [-> _] ];
              destruct (cmp_holds rho _ _ _); try destruct n; try destruct n2; reflexivity).
    all: try (cbn in Ha; destruct (is_const x) as [[|p|p]|] eqn:K; try discriminate; injection H; intros <-;
              pose proof (is_const_sound rho x 0 K) as K0;
              first [ destruct (CVW _ _ _ _ wb wa _ Hb Ha K0) as [_ ->] | destruct (XVW _ _ wb wa _ Hb Ha K0) as [_ ->] ];
              destruct (cmp_holds rho _ _ _); try destruct n; try destruct n2; reflexivity).
    (* [comment removed for export] *)
    all: cbn in Ha, Hb.
    - destruct (sexact (s_ctx st) x &&& sexact (s_ctx st) x2)%bool eqn:E.
      + apply andb_prop in E as [E1 E2].
        injection H; intros <-. cbn [cmp_holds xorb]. unfold bv_lts.
        rewrite (sexact_signed rho _ x wa HC E1 Ha), (sexact_signed rho _ x2 wb HC E2 Hb). reflexivity.
      + pose proof (sign_test_sound rho _ x x2 false c wa wb HC Ha Hb H) as GS. destruct c as [[[nq kq] x0] y0]. unfold bv_lts. rewrite GS. reflexivity.
    - destruct (sexact (s_ctx st) x &&& sexact (s_ctx st) x2)%bool eqn:E.
      + apply andb_prop in E as [E1 E2].
        injection H; intros <-. cbn [cmp_holds xorb]. unfold bv_lts.
        rewrite (sexact_signed rho _ x wa HC E1 Ha), (sexact_signed rho _ x2 wb HC E2 Hb). reflexivity.
      + pose proof (sign_test_sound rho _ x x2 true c wa wb HC Ha Hb H) as GS. destruct c as [[[nq kq] x0] y0]. cbn [branch_taken]. unfold bv_lts. rewrite GS.
        destruct (xorb nq (cmp_holds rho kq x0 y0)); reflexivity.
    - destruct (uview (s_ctx st) x) as [x'|] eqn:U1; [|discriminate]. destruct (uview (s_ctx st) x2) as [x2'|] eqn:U2; [|discriminate].
      injection H; intros <-. cbn [cmp_holds xorb]. unfold bv_ltu.
      rewrite (uview_unsigned rho _ x x' wa HC U1 Ha), (uview_unsigned rho _ x2 x2' wb HC U2 Hb). reflexivity.
    - destruct (uview (s_ctx st) x) as [x'|] eqn:U1; [|discriminate]. destruct (uview (s_ctx st) x2) as [x2'|] eqn:U2; [|discriminate].
      injection H; intros <-. cbn [cmp_holds xorb]. unfold bv_ltu.
      rewrite (uview_unsigned rho _ x x' wa HC U1 Ha), (uview_unsigned rho _ x2 x2' wb HC U2 Hb). reflexivity.
  Qed.

  Lemma learn_base_sound : forall rho st k x y b,
    VS rho st -> lin_below x (s_next st) = true -> lin_below y (s_next st) = true ->
    cmp_holds rho k x y = b ->
    vext rho st rho (learn_base st k x y b) /\ VS rho (learn_base st k x y b).
  Proof.
    intros rho st k x y b HVS Bx By Hc. pose proof (proj1 HVS) as HC.
    assert (NOP : vext rho st rho st /\ VS rho st) by (split; [apply vext_refl | exact HVS]).
    unfold learn_base. destruct k; cbn [cmp_holds] in Hc.
    - destruct b.
      + apply learn_sound; [exact HVS | apply laddc_below; apply lsub_below; assumption |].
        rewrite laddc_sound, lsub_sound. destruct (Z.ltb_spec (evl rho x) (evl rho y)); [lia | discriminate].
      + apply learn_sound; [exact HVS | apply lsub_below; assumption |].
        rewrite lsub_sound. destruct (Z.ltb_spec (evl rho x) (evl rho y)); [discriminate | lia].
    - destruct b.
      + apply learn_sound; [exact HVS | apply laddc_below; apply lsub_below; assumption |].
        rewrite laddc_sound, lsub_sound. destruct (Z.ltb_spec (evl rho x) (evl rho y)); [lia | discriminate].
      + apply learn_sound; [exact HVS | apply lsub_below; assumption |].
        rewrite lsub_sound. destruct (Z.ltb_spec (evl rho x) (evl rho y)); [discriminate | lia].
    - rewrite two64z_eq in Hc. pose proof (lsub_sound rho x y) as Hd.
      assert (Bd : lin_below (lsub x y) (s_next st) = true) by (apply lsub_below; assumption).
      destruct b.
      + destruct (in_range (s_ctx st) (lsub x y) (1 - LXI.two64) LXI.two64) eqn:Hr; [|exact NOP].
        pose proof (in_range_sound rho _ _ _ _ HC Hr) as R0. rewrite two64I_eq in R0.
        apply learn_eq_sound; [exact HVS | exact Bd |].
        apply Z.eqb_eq in Hc. rewrite Hd.
        rewrite eqb_mod_sub' in Hc || idtac.
        assert (Hm : (evl rho x - evl rho y) mod 2 ^ 64 = 0).
        { rewrite Zminus_mod, Hc, Z.sub_diag. reflexivity. }
        apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. rewrite Hd in R0.
        assert (q = 0) by nia. subst q. lia.
      + apply Z.eqb_neq in Hc.
        assert (Hne : evl rho x - evl rho y <> 0).
        { intros E. apply Hc. replace (evl rho x) with (evl rho y) by lia. reflexivity. }
        destruct (entails (s_ctx st) (lsub x y) None) eqn:E1.
        * pose proof (entails_sound rho _ _ None HC E1) as P. rewrite Hd in P.
          apply learn_sound; [exact HVS | apply laddc_below; exact Bd |]. rewrite laddc_sound, Hd. lia.
        * destruct (entails (s_ctx st) (lneg (lsub x y)) None) eqn:E2; [|exact NOP].
          pose proof (entails_sound rho _ _ None HC E2) as P. rewrite lneg_sound, Hd in P.
          apply learn_sound; [exact HVS | apply laddc_below; apply lneg_below; exact Bd |]. rewrite laddc_sound, lneg_sound, Hd. lia.
  Qed.

  Lemma learn_cond_sound : forall rho st c taken,
    VS rho st -> (let '(n, k, x, y) := c in lin_below x (s_next st) = true /\ lin_below y (s_next st) = true /\
                  xorb n (cmp_holds rho k x y) = taken) ->
    vext rho st rho (learn_cond st c taken) /\ VS rho (learn_cond st c taken).
  Proof.
    intros rho st [[[n k] x] y] taken HVS (Bx & By & Ht). unfold learn_cond.
    apply learn_base_sound; try assumption. destruct n, (cmp_holds rho k x y), taken; cbn in Ht |- *; congruence.
  Qed.

  Lemma cond_of_branch_below : forall st bc a b c n,
    cond_of_branch st bc a b = Some c -> aval_below a n = true -> aval_below b n = true ->
    let '(_, _, x, y) := c in lin_below x n = true /\ lin_below y n = true.
  Proof.
    intros st bc a b c n H Ba Bb. unfold cond_of_branch in H.
    destruct bc; destruct a as [|x|nn k x y|x y]; try discriminate; destruct b as [|x2|n2 k2 x2 y2|x2 y2]; try discriminate;
      cbn [aval_below] in Ba, Bb; try (apply andb_prop in Ba as [Ba1 Ba2]); try (apply andb_prop in Bb as [Bb1 Bb2]);
      repeat match type of H with
        | context [match ?cc with _ => _ end] => destruct cc eqn:?; try discriminate
        end;
      try (injection H; intros <-; split; first [assumption | eapply uview_below; eauto]);
      (unfold sign_test in H;
       repeat match type of H with
        | context [match ?cc with _ => _ end] => destruct cc eqn:?; try discriminate
        end; injection H; intros <-; split; first [apply lconst_below | eapply uview_below; eauto]).
  Qed.

  Lemma branch_split_below : forall st bc a b l n,
    branch_split st bc a b = Some l -> aval_below a n = true -> aval_below b n = true -> lin_below l n = true.
  Proof.
    intros st bc a b l n H Ba Bb. unfold branch_split in H.
    destruct bc; try discriminate; destruct a as [|x| |]; try discriminate; destruct b as [|y| |]; try discriminate;
      cbn [aval_below] in Ba, Bb;
      repeat match type of H with
        | context [match ?cc with _ => _ end] => destruct cc eqn:?; try discriminate
        | context [if ?cc then _ else _] => destruct cc eqn:?; try discriminate
        end; injection H; intros <-; assumption.
  Qed.

  Lemma sound_branch : forall rho st ms bc rs1 rs2 imm sz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Branch bc rs1 rs2 imm) sz ->
    sound_res rho (s_next st) ms (exec_instr U st (Branch bc rs1 rs2 imm) sz).
  Proof.
    intros rho st ms bc rs1 rs2 imm sz Hwf HR Hcan. cbn [exec_instr].
    pose proof (R_VS _ _ _ HR) as HVS. pose proof (proj1 HVS) as HC.
    pose proof (cv_lit_sound rho (s_ctx st) _ _ HC (getreg_sound rho st ms rs1 HR)) as Ha.
    pose proof (cv_lit_sound rho (s_ctx st) _ _ HC (getreg_sound rho st ms rs2 HR)) as Hb.
    pose proof (cv_lit_below (s_ctx st) _ _ (getreg_below st (regn rs1) Hwf)) as Ba.
    pose proof (cv_lit_below (s_ctx st) _ _ (getreg_below st (regn rs2) Hwf)) as Bb.
    set (a := cv_lit (s_ctx st) (getreg st (regn rs1))) in *. set (b := cv_lit (s_ctx st) (getreg st (regn rs2))) in *.
    set (taken := branch_taken bc (rget (core_of ms) rs1) (rget (core_of ms) rs2)).
    assert (STEP : cstep ms (ms_of ms (with_pc (if taken then w64 (s_pc st + immz imm) else w64 (s_pc st + sz)) (core_of ms)) (ms_mem ms))).
    { apply Hcan. cbn [exec]. rewrite interp_done. subst taken.
      rewrite sext_w64, <- (npc_eq rho st ms sz HR). cbn [c_pc core_of]. rewrite (r_pc _ _ _ _ _ _ HR), <- w64_add.
      destruct (branch_taken _ _ _); reflexivity. }
    assert (GO : forall p, (if taken then w64 (s_pc st + immz imm) else w64 (s_pc st + sz)) = w64 p ->
                 sound_res rho (s_next st) ms (SNext (set_pc st p))).
    { intros p Hp. cbn [sound_res]. eexists _, rho. split; [exact STEP|]. split; [|split; [apply agree_refl | nxt]]. rewrite Hp. apply set_pc_sound. apply R_ms_of. exact HR. }
    destruct (aval_litC (s_ctx st) a) as [x0|] eqn:La; [destruct (aval_litC (s_ctx st) b) as [y0|] eqn:Lb|].
    - (* [comment removed for export] *)
      apply GO. subst taken. change (LXI.w64 x0) with (w64 x0). change (LXI.w64 y0) with (w64 y0).
      rewrite <- (aval_litC_sound rho _ a x0 _ HC La Ha), <- (aval_litC_sound rho _ b y0 _ HC Lb Hb).
      destruct (branch_taken _ _ _); reflexivity.
    - destruct (branch_split st bc a b) as [l|] eqn:Es.
      { apply sound_split; [exact Hwf | exact HR | eapply branch_split_below; eauto]. }
      destruct (cond_of_branch st bc a b) as [c|] eqn:Ec.
      + pose proof (cond_of_branch_sound rho st bc a b _ _ c HVS Ha Hb Ec) as Htk.
        pose proof (cond_of_branch_below st bc a b c (s_next st) Ec Ba Bb) as Bc.
        destruct c as [[[n k] x] y]. fold taken in Htk. destruct Bc as [Bx By].
        destruct (decide_cond (s_ctx st) (n, k, x, y)) as [bb|] eqn:Ed.
        * unfold decide_cond in Ed. destruct (decide_base (s_ctx st) k x y) as [b0|] eqn:Ed0; [|discriminate].
          cbn in Ed. injection Ed; intros <-. rewrite (decide_base_sound rho _ k x y b0 HC Ed0) in Htk.
          rewrite <- Htk. destruct taken; apply GO; reflexivity.
        * cbn [sound_res]. right. eexists _, rho. split; [exact STEP|]. split; [|split; [apply agree_refl | nxt]].
          destruct taken.
          -- left. apply set_pc_sound. apply R_ms_of.
             destruct (learn_cond_sound rho st (n, k, x, y) true HVS ltac:(split; [exact Bx|split; [exact By|exact (eq_sym Htk)]])) as [E V].
             eapply R_vext; eauto.
          -- right. apply set_pc_sound. apply R_ms_of.
             destruct (learn_cond_sound rho st (n, k, x, y) false HVS ltac:(split; [exact Bx|split; [exact By|exact (eq_sym Htk)]])) as [E V].
             eapply R_vext; eauto.
      + cbn [sound_res]. right. eexists _, rho. split; [exact STEP|]. split; [|split; [apply agree_refl | nxt]].
        destruct taken; [left|right]; apply set_pc_sound; apply R_ms_of; exact HR.
    - destruct (branch_split st bc a b) as [l|] eqn:Es.
      { apply sound_split; [exact Hwf | exact HR | eapply branch_split_below; eauto]. }
      destruct (cond_of_branch st bc a b) as [c|] eqn:Ec.
      + pose proof (cond_of_branch_sound rho st bc a b _ _ c HVS Ha Hb Ec) as Htk.
        pose proof (cond_of_branch_below st bc a b c (s_next st) Ec Ba Bb) as Bc.
        destruct c as [[[n k] x] y]. fold taken in Htk. destruct Bc as [Bx By].
        destruct (decide_cond (s_ctx st) (n, k, x, y)) as [bb|] eqn:Ed.
        * unfold decide_cond in Ed. destruct (decide_base (s_ctx st) k x y) as [b0|] eqn:Ed0; [|discriminate].
          cbn in Ed. injection Ed; intros <-. rewrite (decide_base_sound rho _ k x y b0 HC Ed0) in Htk.
          rewrite <- Htk. destruct taken; apply GO; reflexivity.
        * cbn [sound_res]. right. eexists _, rho. split; [exact STEP|]. split; [|split; [apply agree_refl | nxt]].
          destruct taken.
          -- left. apply set_pc_sound. apply R_ms_of.
             destruct (learn_cond_sound rho st (n, k, x, y) true HVS ltac:(split; [exact Bx|split; [exact By|exact (eq_sym Htk)]])) as [E V].
             eapply R_vext; eauto.
          -- right. apply set_pc_sound. apply R_ms_of.
             destruct (learn_cond_sound rho st (n, k, x, y) false HVS ltac:(split; [exact Bx|split; [exact By|exact (eq_sym Htk)]])) as [E V].
             eapply R_vext; eauto.
      + cbn [sound_res]. right. eexists _, rho. split; [exact STEP|]. split; [|split; [apply agree_refl | nxt]].
        destruct taken; [left|right]; apply set_pc_sound; apply R_ms_of; exact HR.
  Qed.

  (* [comment removed for export] *)
  Lemma forallb_aval_mono : forall (l : list aval) n m, (n <= m)%nat ->
    forallb (fun v => aval_below v n) l = true -> forallb (fun v => aval_below v m) l = true.
  Proof.
    intros l n m Hnm H. rewrite forallb_forall in H |- *. intros x Hx. eapply aval_below_mono; [exact Hnm | apply H; exact Hx].
  Qed.

  Lemma wf_vext : forall rho st rho' st', wf_state st = true -> vext rho st rho' st' -> VS rho' st' -> wf_state st' = true.
  Proof.
    intros rho st rho' st' Hwf (A & N & P & Rg & S & Ar & Ab & Rv & D & Pc & Py) [HC HB].
    destruct (wf_parts st Hwf) as (Wregs & Wctx & Wstk & Warrs & Wpc & Wpay & Wdisj & W18 & Wcw & Wad).
    unfold wf_state. rewrite Rg, S, Ar, Pc, Py, HB, Wdisj, Wcw, Wad.
    rewrite (forallb_aval_mono _ _ _ N Wregs).
    assert (Hstk : forallb (fun c => aval_below (c_val c) (s_next st')) (s_stk st) = true).
    { rewrite forallb_forall in Wstk |- *. intros c Hc. eapply aval_below_mono; [exact N | apply Wstk; exact Hc]. }
    assert (Harrs : forallb (fun a => afact_below (ar_fact a) (s_next st')) (s_arrs st) = true).
    { rewrite forallb_forall in Warrs |- *. intros a Ha. specialize (Warrs a Ha). destruct (ar_fact a); [|reflexivity].
      cbn in Warrs |- *. eapply lin_below_mono; [exact N | exact Warrs]. }
    assert (Hpc : forallb (fun e : lin * Z * sym => let '(o, _, x) := e in (lin_below o (s_next st') &&& Nat.ltb x (s_next st'))%bool) (s_pcache st) = true).
    { rewrite forallb_forall in Wpc |- *. intros [[o sx] x] He. specialize (Wpc _ He). cbn in Wpc |- *.
      apply andb_prop in Wpc as [W1 W2]. rewrite (lin_below_mono _ _ _ N W1). apply Nat.ltb_lt in W2. apply Nat.ltb_lt. lia. }
    assert (Hpay : forallb (fun e : lin * itv => lin_below (fst e) (s_next st')) (s_pay st) = true).
    { rewrite forallb_forall in Wpay |- *. intros e He. eapply lin_below_mono; [exact N | apply Wpay; exact He]. }
    rewrite Hstk, Harrs, Hpc, Hpay. replace (Nat.leb 19 (s_next st')) with true by (symmetry; apply Nat.leb_le; lia). reflexivity.
  Qed.

  Lemma agree_vext_lext : forall rho st rho0 st0 rho1 st1,
    vext rho st rho0 st0 -> lext rho0 st0 rho1 st1 -> agree (s_next st) rho rho1.
  Proof.
    intros rho st rho0 st0 rho1 st1 (A & N & _) (A1 & _). intros x Hx. rewrite A1 by lia. apply A. exact Hx.
  Qed.

  Lemma alu_add_bv : forall a b : word, alu64 ALU_ADD a b = (a + b)%bv.
  Proof. reflexivity. Qed.

  Lemma sound_load : forall rho st ms sz sx rd rs1 imm isz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Load sz sx rd rs1 imm) isz ->
    sound_res rho (s_next st) ms (exec_instr U st (Load sz sx rd rs1 imm) isz).
  Proof.
    intros rho st ms sz sx rd rs1 imm isz Hwf HR Hcan. cbn [exec_instr].
    pose proof (R_VS _ _ _ HR) as HVS.
    destruct (aalu_sound rho st ALU_ADD (getreg st (regn rs1)) (alit (immz imm)) (rget (core_of ms) rs1) (sext 64 imm)
                (R_galign _ _ _ HR) (wf_next2 st Hwf) HVS (getreg_sound rho st ms rs1 HR) ltac:(rewrite sext_w64; apply alit_ok)
                (getreg_below st (regn rs1) Hwf) (alit_below _ _)) as (rho0 & A & B & C & D).
    destruct (aalu st ALU_ADD _ _) as [a st0]. cbn [fst snd] in *.
    assert (HR0 : R U G M0 rho0 st0 ms) by (eapply R_vext; eauto).
    assert (Hwf0 : wf_state st0 = true) by (eapply wf_vext; eauto).
    rewrite alu_add_bv in C.
    pose proof (msize_pos sz) as Hw || idtac.
    assert (Hw : 0 < msize_w sz <= 8) by (destruct sz; cbn; lia).
    destruct (do_load U st0 a (msize_w sz) sx) as [v st1|o p|] eqn:Hld; [| |exact I].
    - destruct (do_load_sound U G M0 UOK SCOK rho0 st0 ms a _ (msize_w sz) sx v st1 Hwf0 HR0 C D ltac:(lia) ltac:(lia) Hld)
        as (rho1 & bs & Hrd & HR1 & Hlx & Hv & Bv).
      cbn [sound_res]. eexists _, rho1. split; [|split; [|split; [eapply agree_vext_lext; eauto | nxt; destruct A as (_ & ?N & _); destruct Hlx as (_ & ?N1 & _); lia]]].
      + apply Hcan. cbn [exec]. rewrite (interp_load_val segs sz sx _ _ (ms_mem ms) bs Hrd), interp_done. reflexivity.
      + rewrite <- with_pc_rset, (npc_eq rho st ms isz HR).
        assert (Epc : s_pc st = s_pc st1).
        { destruct Hlx as (_ & _ & E1 & _). destruct A as (_ & _ & E0 & _). rewrite E1, E0. reflexivity. }
        rewrite Epc. apply set_pc_sound. apply wr_sound; [exact HR1 | exact Hv].
    - destruct (lin_below o (s_next st0) &&& lin_below p (s_next st0))%bool eqn:Eb; [|exact I].
      apply andb_prop in Eb as [Bo Bp].
      cbn [sound_res]. left. exists rho0. split; [|split; [exact (proj1 A) | nxt; destruct A as (_ & ?N & _); lia]]. pose proof (R_VS _ _ _ HR0) as HVS0.
      destruct (Z.lt_ge_cases (evl rho0 o) (evl rho0 p)) as [Hlt|Hge].
      + left. destruct (learn_sound rho0 st0 (laddc (lsub p o) (-1)) HVS0 ltac:(apply laddc_below; apply lsub_below; assumption)
                          ltac:(rewrite laddc_sound, lsub_sound; lia)) as [E V]. eapply R_vext; eauto.
      + right. destruct (learn_sound rho0 st0 (lsub o p) HVS0 ltac:(apply lsub_below; assumption)
                          ltac:(rewrite lsub_sound; lia)) as [E V]. eapply R_vext; eauto.
  Qed.

  Lemma classify_abs_sound : forall rho av wa x,
    classify av = Some (AAbs x) -> val_ok rho av wa -> wa = w64 x /\ 0 <= x < two64z /\ bv_unsigned wa = x.
  Proof.
    intros rho av wa x Hc Hv. unfold classify in Hc. destruct av as [|l| |]; try discriminate.
    destruct (is_const l) as [c|] eqn:K.
    - injection Hc; intros <-. cbn in Hv. rewrite (is_const_sound rho l c K) in Hv. subst wa.
      rewrite two64z_eq. pose proof (Z.mod_pos_bound c (2 ^ 64) ltac:(lia)).
      split; [apply w64_eq_mod; rewrite Z.mod_mod by lia; reflexivity|]. split; [lia|]. rewrite w64_unsigned. reflexivity.
    - exfalso. repeat match type of Hc with
        | context [if ?c then _ else _] => destruct c; try discriminate
        | context [match ?c with _ => _ end] => destruct c; try discriminate
        end.
  Qed.

  Lemma inval_resv_with_pc : forall a p c, inval_resv a (with_pc p c) = with_pc p (inval_resv a c).
  Proof. intros a p c. unfold inval_resv. cbn. destruct (c_resv c) as [r|]; [destruct (Z.eqb _ _)|]; reflexivity. Qed.

  Lemma resv_after_store_sound : forall rho st ms a wa st',
    R U G M0 rho st ms -> val_ok rho a wa -> resv_after_store st a = Some st' ->
    R U G M0 rho st' (ms_of ms (inval_resv wa (core_of ms)) (ms_mem ms))
    /\ s_next st' = s_next st /\ (wf_state st = true -> wf_state st' = true).
  Proof.
    intros rho st ms a wa st' HR Ha H. unfold resv_after_store in H.
    pose proof (r_resv _ _ _ _ _ _ HR) as Hrv.
    destruct (s_resv st) as [r|] eqn:Er.
    - destruct (classify a) as [[| | |x]|] eqn:Hc; try discriminate. injection H; intros <-.
      destruct (classify_abs_sound rho a wa x Hc Ha) as (Hwa & Hx & Hux).
      unfold resv_ok in Hrv. destruct (ms_resv ms) as [cw|] eqn:Ecr; [|destruct Hrv]. destruct Hrv as [Hcw Hr].
      unfold inval_resv. cbn [c_resv core_of]. rewrite Ecr, Hux, Hcw, w64_unsigned, two64z_eq in *.
      rewrite Z.mod_small by lia.
      destruct (Z.eqb_spec r x) as [->|NE].
      + split; [|split; [reflexivity | intros W; exact W]].
        apply (R_core_upd rho st ms); try reflexivity; try exact HR; cbn;
          first [exact (r_pc _ _ _ _ _ _ HR) | exact (r_regs _ _ _ _ _ _ HR) | exact I | exact (r_frm _ _ _ _ _ _ HR)].
      + split; [|split; [reflexivity | intros W; exact W]].
        first [ apply R_ms_of; exact HR
              | apply (R_core_upd rho st ms); try reflexivity; try exact HR; cbn;
                first [exact (r_pc _ _ _ _ _ _ HR) | exact (r_regs _ _ _ _ _ _ HR) | exact (r_frm _ _ _ _ _ _ HR)
                      | rewrite Er; cbn; rewrite two64z_eq; split; [reflexivity | lia] ] ].
    - injection H; intros <-. unfold resv_ok in Hrv. destruct (ms_resv ms) as [cw|] eqn:Ecr; [destruct Hrv|].
      unfold inval_resv. cbn [c_resv core_of]. rewrite Ecr.
      split; [|split; [reflexivity | intros W; exact W]]. apply R_ms_of. exact HR.
  Qed.

  Lemma interp_store_val : forall sz a (v : word) k m,
    store_ok segs m a (Z.to_nat (msize_w sz)) = true ->
    interp_eff segs (store_val sz a v k) m = interp_eff segs k (write_to_mem m a (store_bytes (msize_w sz) v)).
  Proof.
    intros sz a v k m Hst. unfold store_bytes.
    destruct sz; cbn [store_val msize_w] in *;
      [ change (Z.to_nat 1) with 1%nat in * | change (Z.to_nat 2) with 2%nat in * | change (Z.to_nat 4) with 4%nat in * | change (Z.to_nat 8) with 8%nat in * ].
    - rewrite (interp_estore segs 8 1%nat) by (first [exact Hst | lia]).
      rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_le_bytes_wrap by (cbn; lia). reflexivity.
    - rewrite (interp_estore segs 16 2%nat) by (first [exact Hst | lia]).
      rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_le_bytes_wrap by (cbn; lia). reflexivity.
    - rewrite (interp_estore segs 32 4%nat) by (first [exact Hst | lia]).
      unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_le_bytes_wrap by (cbn; lia). reflexivity.
    - rewrite (interp_estore segs 64 8%nat) by (first [exact Hst | lia]). reflexivity.
  Qed.

  Lemma ms_with_mem_of : forall ms c m m', ms_with_mem (ms_of ms c m) m' = ms_of ms c m'.
  Proof. reflexivity. Qed.

  Lemma sound_store : forall rho st ms sz rs1 rs2 imm isz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Store sz rs1 rs2 imm) isz ->
    sound_res rho (s_next st) ms (exec_instr U st (Store sz rs1 rs2 imm) isz).
  Proof.
    intros rho st ms sz rs1 rs2 imm isz Hwf HR Hcan. cbn [exec_instr].
    pose proof (R_VS _ _ _ HR) as HVS.
    destruct (aalu_sound rho st ALU_ADD (getreg st (regn rs1)) (alit (immz imm)) (rget (core_of ms) rs1) (sext 64 imm)
                (R_galign _ _ _ HR) (wf_next2 st Hwf) HVS (getreg_sound rho st ms rs1 HR) ltac:(rewrite sext_w64; apply alit_ok)
                (getreg_below st (regn rs1) Hwf) (alit_below _ _)) as (rho0 & A & B & C & D).
    destruct (aalu st ALU_ADD _ _) as [a st0]. cbn [fst snd] in *.
    assert (HR0 : R U G M0 rho0 st0 ms) by (eapply R_vext; eauto).
    assert (Hwf0 : wf_state st0 = true) by (eapply wf_vext; eauto).
    rewrite alu_add_bv in C.
    assert (Hw : 0 < msize_w sz <= 8) by (destruct sz; cbn; lia).
    destruct (resv_after_store st0 a) as [st0'|] eqn:Hra; [|exact I].
    destruct (resv_after_store_sound rho0 st0 ms a _ st0' HR0 C Hra) as (HR0' & Hn' & Hwf0').
    specialize (Hwf0' Hwf0). set (ms0 := ms_of ms (inval_resv _ (core_of ms)) (ms_mem ms)) in HR0'.
    destruct (do_store U st0' a (msize_w sz) (getreg st0' (regn rs2))) as [st1|] eqn:Hst; [|exact I].
    pose proof (getreg_sound rho0 st0' ms0 rs2 HR0') as Hv2.
    assert (Erg : rget (core_of ms0) rs2 = rget (core_of ms) rs2).
    { subst ms0. unfold rget, inval_resv. cbn. destruct (ms_resv ms); [destruct (Z.eqb _ _)|]; reflexivity. }
    rewrite Erg in Hv2.
    rewrite <- Hn' in D.
    destruct (do_store_sound U G M0 UOK rho0 st0' ms0 a _ (msize_w sz) (getreg st0' (regn rs2)) (rget (core_of ms) rs2) st1
                Hwf0' HR0' C D Hv2 (getreg_below st0' (regn rs2) Hwf0') ltac:(lia) ltac:(lia) Hst)
      as (Hok & HR1 & Hn1 & Hpc1 & _).
    subst ms0. cbn [ms_mem ms_of] in Hok, HR1. rewrite ms_with_mem_of in HR1.
    cbn [sound_res]. eexists _, rho0. split; [|split; [|split; [exact (proj1 A) | nxt; destruct A as (_ & ?N & _); lia]]].
    - apply Hcan. cbn [exec]. rewrite (interp_store_val sz _ _ _ (ms_mem ms) Hok), interp_done. reflexivity.
    - rewrite inval_resv_with_pc, (npc_eq rho st ms isz HR).
      assert (Epc : s_pc st = s_pc st1).
      { rewrite Hpc1. destruct A as (_ & _ & E0 & _). rewrite <- E0.
        unfold resv_after_store in Hra. destruct (s_resv st0); [destruct (classify a) as [[| | |x]|]; try discriminate; injection Hra; intros <-; destruct (Z.eqb _ _); reflexivity | injection Hra; intros <-; reflexivity]. }
      rewrite Epc. apply set_pc_sound. exact HR1.
  Qed.

  Lemma sound_fload : forall rho st ms fmt rd rs1 imm isz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (FLoad fmt rd rs1 imm) isz ->
    sound_res rho (s_next st) ms (exec_instr U st (FLoad fmt rd rs1 imm) isz).
  Proof.
    intros rho st ms fmt rd rs1 imm isz Hwf HR Hcan. cbn [exec_instr].
    pose proof (R_VS _ _ _ HR) as HVS.
    destruct (aalu_sound rho st ALU_ADD (getreg st (regn rs1)) (alit (immz imm)) (rget (core_of ms) rs1) (sext 64 imm)
                (R_galign _ _ _ HR) (wf_next2 st Hwf) HVS (getreg_sound rho st ms rs1 HR) ltac:(rewrite sext_w64; apply alit_ok)
                (getreg_below st (regn rs1) Hwf) (alit_below _ _)) as (rho0 & A & B & C & D).
    destruct (aalu st ALU_ADD _ _) as [a st0]. cbn [fst snd] in *.
    assert (HR0 : R U G M0 rho0 st0 ms) by (eapply R_vext; eauto).
    assert (Hwf0 : wf_state st0 = true) by (eapply wf_vext; eauto).
    rewrite alu_add_bv in C.
    set (w := match fmt with FMT_S => 4 | FMT_D => 8 end).
    assert (Hw : 0 < w <= 8) by (destruct fmt; cbn; lia).
    destruct (do_load U st0 a w false) as [v st1|o p|] eqn:Hld; try exact I.
    destruct (do_load_sound U G M0 UOK SCOK rho0 st0 ms a _ w false v st1 Hwf0 HR0 C D ltac:(lia) ltac:(lia) Hld)
      as (rho1 & bs & Hrd & HR1 & Hlx & Hv & Bv).
    cbn [sound_res].
    assert (Epc : s_pc st = s_pc st1).
    { destruct Hlx as (_ & _ & E1 & _). destruct A as (_ & _ & E0 & _). rewrite E1, E0. reflexivity. }
    destruct fmt; subst w.
    - eexists _, rho1. split; [|split; [|split; [eapply agree_vext_lext; eauto | nxt; destruct A as (_ & ?N & _); destruct Hlx as (_ & ?N1 & _); lia]]].
      + apply Hcan. cbn [exec]. rewrite (interp_eload segs 32 4%nat _ _ (ms_mem ms) bs) by (first [left; split; reflexivity | exact Hrd]).
        rewrite interp_done. reflexivity.
      + rewrite (npc_eq rho st ms isz HR), Epc.
        apply (R_core_upd rho1 st1 ms); try reflexivity; try exact HR1; cbn;
          first [exact (r_regs _ _ _ _ _ _ HR1) | exact (r_resv _ _ _ _ _ _ HR1) | exact (r_frm _ _ _ _ _ _ HR1)].
    - eexists _, rho1. split; [|split; [|split; [eapply agree_vext_lext; eauto | nxt; destruct A as (_ & ?N & _); destruct Hlx as (_ & ?N1 & _); lia]]].
      + apply Hcan. cbn [exec]. rewrite (interp_eload segs 64 8%nat _ _ (ms_mem ms) bs) by (first [right; split; reflexivity | exact Hrd]).
        rewrite interp_done. reflexivity.
      + rewrite (npc_eq rho st ms isz HR), Epc.
        apply (R_core_upd rho1 st1 ms); try reflexivity; try exact HR1; cbn;
          first [exact (r_regs _ _ _ _ _ _ HR1) | exact (r_resv _ _ _ _ _ _ HR1) | exact (r_frm _ _ _ _ _ _ HR1)].
  Qed.

  Lemma store_bytes_zext32 : forall (x : bv 32), store_bytes 4 (zext 64 x) = Z_to_le_bytes 4 (bv_unsigned x).
  Proof. intros x. unfold store_bytes, zext. rewrite bv_zero_extend_unsigned by (cbn; lia). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma finish_mem : forall rho st1 ms m' p c,
    R U G M0 rho st1 (ms_with_mem ms m') ->
    c_regs c = ms_regs ms -> c_pc c = w64 p -> resv_ok (s_resv st1) (c_resv c) -> frm_ok (c_fcsr c) ->
    R U G M0 rho (set_pc st1 p) (ms_of ms c m').
  Proof.
    intros rho st1 ms m' p c HR Hregs Hpc Hresv Hfrm.
    destruct HR; constructor; cbn in *; try rewrite ?Hregs; try assumption; reflexivity.
  Qed.

  Lemma sound_fstore : forall rho st ms fmt rs1 rs2 imm isz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (FStore fmt rs1 rs2 imm) isz ->
    sound_res rho (s_next st) ms (exec_instr U st (FStore fmt rs1 rs2 imm) isz).
  Proof.
    intros rho st ms fmt rs1 rs2 imm isz Hwf HR Hcan. cbn [exec_instr].
    pose proof (R_VS _ _ _ HR) as HVS.
    destruct (aalu_sound rho st ALU_ADD (getreg st (regn rs1)) (alit (immz imm)) (rget (core_of ms) rs1) (sext 64 imm)
                (R_galign _ _ _ HR) (wf_next2 st Hwf) HVS (getreg_sound rho st ms rs1 HR) ltac:(rewrite sext_w64; apply alit_ok)
                (getreg_below st (regn rs1) Hwf) (alit_below _ _)) as (rho0 & A & B & C & D).
    destruct (aalu st ALU_ADD _ _) as [a st0]. cbn [fst snd] in *.
    assert (HR0 : R U G M0 rho0 st0 ms) by (eapply R_vext; eauto).
    assert (Hwf0 : wf_state st0 = true) by (eapply wf_vext; eauto).
    rewrite alu_add_bv in C.
    destruct (s_resv st0) as [r|] eqn:Er; [destruct fmt; exact I|].
    assert (Hcr : ms_resv ms = None).
    { pose proof (r_resv _ _ _ _ _ _ HR0) as Hrv. rewrite Er in Hrv. unfold resv_ok in Hrv. destruct (ms_resv ms); [destruct Hrv | reflexivity]. }
    assert (GEN : forall w (wv : word) (n : N) nb (vn : bv n),
      0 < w <= 8 -> (n = 8%N /\ nb = 1%nat \/ n = 16%N /\ nb = 2%nat \/ n = 32%N /\ nb = 4%nat \/ n = 64%N /\ nb = 8%nat) ->
      Z.to_nat w = nb -> Z_to_le_bytes nb (bv_unsigned vn) = store_bytes w wv ->
      (forall c' m', interp_eff segs (EStore n (rget (core_of ms) rs1 + sext 64 imm)%bv vn
                                       (EDone (inval_resv (rget (core_of ms) rs1 + sext 64 imm)%bv (with_pc (c_pc (core_of ms) + Z_to_bv 64 isz)%bv (core_of ms)))))
                        (ms_mem ms) = MachineOk (c', m') -> cstep ms (ms_of ms c' m')) ->
      sound_res rho (s_next st) ms match do_store U st0 a w Top with
                       | Some st1 => SNext (set_pc st1 (s_pc st + isz))
                       | None => SFail (s_pc st) (R_STORE w a)
                       end).
    { intros w wv n nb vn Hw Hn Hnb Hbytes Hc.
      destruct (do_store U st0 a w Top) as [st1|] eqn:Hst; [|exact I].
      destruct (do_store_sound U G M0 UOK rho0 st0 ms a _ w Top wv st1 Hwf0 HR0 C D I eq_refl ltac:(lia) ltac:(lia) Hst)
        as (Hok & HR1 & Hn1 & Hpc1 & Hrg1 & Hrv1).
      assert (Epc : s_pc st = s_pc st1).
      { rewrite Hpc1. destruct A as (_ & _ & E0 & _). rewrite E0. reflexivity. }
      cbn [sound_res]. eexists _, rho0. split; [|split; [|split; [exact (proj1 A) | nxt; destruct A as (_ & ?N & _); lia]]].
      - apply Hc. rewrite (interp_estore segs n nb) by (first [exact Hn | rewrite <- Hnb; exact Hok]). rewrite interp_done. reflexivity.
      - rewrite (npc_eq rho st ms isz HR), Epc, Hbytes.
        apply finish_mem; [exact HR1 | | | | ]; unfold inval_resv; cbn; rewrite ?Hcr; cbn;
          first [reflexivity | rewrite Hrv1, Er, ?Hcr; cbn; exact I | exact (r_frm _ _ _ _ _ _ HR)]. }
    destruct fmt.
    - apply (GEN 4 (zext 64 (low32 (fget (core_of ms) rs2))) 32%N 4%nat (low32 (fget (core_of ms) rs2))); [lia | lia | reflexivity | symmetry; apply store_bytes_zext32 |].
      intros c' m' Hi. apply Hcan. cbn [exec]. exact Hi.
    - apply (GEN 8 (fget (core_of ms) rs2) 64%N 8%nat (fget (core_of ms) rs2)); [lia | lia | reflexivity | reflexivity |].
      intros c' m' Hi. apply Hcan. cbn [exec]. exact Hi.
  Qed.

  Lemma with_resv_rset : forall r rd v c, with_resv r (rset rd v c) = rset rd v (with_resv r c).
  Proof. intros. unfold rset. destruct (is_x0 rd); reflexivity. Qed.
  Lemma with_resv_with_pc : forall r p c, with_resv r (with_pc p c) = with_pc p (with_resv r c).
  Proof. reflexivity. Qed.
  Lemma wf_set_resv : forall st r, wf_state (set_resv st r) = wf_state st.
  Proof. reflexivity. Qed.
  Lemma c_regs_rset_resv : forall rd v r c, c_regs (rset rd v (with_resv r c)) = c_regs (rset rd v c).
  Proof. intros. unfold rset. destruct (is_x0 rd); reflexivity. Qed.

  Lemma sound_lr : forall rho st ms wd aq rl rd rs1 isz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Lr wd aq rl rd rs1) isz ->
    sound_res rho (s_next st) ms (exec_instr U st (Lr wd aq rl rd rs1) isz).
  Proof.
    intros rho st ms wd aq rl rd rs1 isz Hwf HR Hcan. cbn [exec_instr].
    pose proof (R_VS _ _ _ HR) as HVS.
    pose proof (getreg_sound rho st ms rs1 HR) as Ha. pose proof (getreg_below st (regn rs1) Hwf) as Ba.
    destruct (classify (getreg st (regn rs1))) as [[| | |x]|] eqn:Hc; try exact I.
    destruct (classify_abs_sound rho _ _ x Hc Ha) as (Hwa & Hx & Hux).
    destruct (Z.eqb (x mod amo_bytes wd) 0) eqn:Hal; cbn [negb]; [|exact I].
    assert (Hw : 0 < amo_bytes wd <= 8) by (destruct wd; cbn; lia).
    destruct (do_load U st (getreg st (regn rs1)) (amo_bytes wd) true) as [v st1|o p|] eqn:Hld; try exact I.
    destruct (do_load_sound U G M0 UOK SCOK rho st ms _ _ (amo_bytes wd) true v st1 Hwf HR Ha Ba ltac:(lia) ltac:(lia) Hld)
      as (rho1 & bs & Hrd & HR1 & Hlx & Hv & Bv).
    pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
    assert (Epc : s_pc st1 = s_pc st) by (destruct Hlx as (_ & _ & E & _); exact E).
    assert (Hal' : amo_aligned wd (rget (core_of ms) rs1) = true) by (unfold amo_aligned; rewrite Hux; exact Hal).
    assert (GEN : forall (n : N) nb (ext : bv n -> word),
      (n = 32%N /\ nb = 4%nat \/ n = 64%N /\ nb = 8%nat) -> Z.to_nat (amo_bytes wd) = nb ->
      ext (bv_extract 0 n (le_bytes_to_word bs)) = ldval (amo_bytes wd) true bs ->
      (forall c' m', interp_eff segs (ELoad n (rget (core_of ms) rs1) (fun v0 => EDone (with_resv (Some (rget (core_of ms) rs1))
                          (rset rd (ext v0) (with_pc (c_pc (core_of ms) + Z_to_bv 64 isz)%bv (core_of ms)))))) (ms_mem ms) = MachineOk (c', m') ->
                     cstep ms (ms_of ms c' m')) ->
      sound_res rho (s_next st) ms (SNext (set_pc (set_resv (wr st1 (regn rd) v) (Some x)) (s_pc st + isz)))).
    { intros n nb ext Hn Hnb Hext Hc'. cbn [sound_res]. eexists _, rho1. split; [|split; [|split; [exact (proj1 Hlx) | nxt; destruct Hlx as (_ & ?N1 & _); lia]]].
      - apply Hc'. rewrite (interp_eload segs n nb _ _ (ms_mem ms) bs) by (first [exact Hn | rewrite <- Hnb; exact Hrd]). rewrite interp_done. reflexivity.
      - pose proof (wr_sound rho1 st1 ms rd v _ HR1 Hv) as HR2.
        rewrite Hext, with_resv_rset, with_resv_with_pc, <- with_pc_rset.
        apply (R_core_upd rho1 (wr st1 (regn rd) v) _ _ _ HR2); try reflexivity.
        + cbn. rewrite <- Epc. apply (npc_eq rho1 st1 ms isz HR1).
        + cbn [c_regs with_pc s_regs set_pc set_resv]. rewrite c_regs_rset_resv. exact (r_regs _ _ _ _ _ _ HR2).
        + unfold rset. destruct (is_x0 rd); cbn; (split; [exact Hwa | exact Hx]).
        + unfold rset. destruct (is_x0 rd); cbn; exact (r_frm _ _ _ _ _ _ HR). }
    destruct wd; cbn [amo_bytes] in *.
    - apply (GEN 32%N 4%nat (fun v0 => sext 64 v0)); [lia | reflexivity | |].
      + apply (ldval_small 32 4 true bs); try lia; rewrite ?Hlen; reflexivity.
      + intros c' m' Hi. apply Hcan. cbn [exec]. rewrite Hal'. cbn [negb]. exact Hi.
    - apply (GEN 64%N 8%nat (fun v0 => v0)); [lia | reflexivity | |].
      + rewrite bv_extract_full. reflexivity.
      + intros c' m' Hi. apply Hcan. cbn [exec]. rewrite Hal'. cbn [negb]. exact Hi.
  Qed.

  Lemma store_bytes_low32 : forall (v : word), Z_to_le_bytes 4 (bv_unsigned (low32 v)) = store_bytes 4 v.
  Proof. intros v. unfold store_bytes, low32. rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_le_bytes_wrap by (cbn; lia). reflexivity. Qed.

  Lemma R_set_resv_none : forall rho st ms,
    R U G M0 rho st ms -> R U G M0 rho (set_resv st None) (ms_of ms (with_resv None (core_of ms)) (ms_mem ms)).
  Proof.
    intros rho st ms HR. apply (R_core_upd rho st ms); try reflexivity; try exact HR; cbn;
      first [exact (r_pc _ _ _ _ _ _ HR) | exact (r_regs _ _ _ _ _ _ HR) | exact I | exact (r_frm _ _ _ _ _ _ HR)].
  Qed.

  Lemma sound_sc : forall rho st ms wd aq rl rd rs1 rs2 isz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Sc wd aq rl rd rs1 rs2) isz ->
    sound_res rho (s_next st) ms (exec_instr U st (Sc wd aq rl rd rs1 rs2) isz).
  Proof.
    intros rho st ms wd aq rl rd rs1 rs2 isz Hwf HR Hcan. cbn [exec_instr].
    pose proof (R_VS _ _ _ HR) as HVS.
    pose proof (getreg_sound rho st ms rs1 HR) as Ha. pose proof (getreg_below st (regn rs1) Hwf) as Ba.
    destruct (classify (getreg st (regn rs1))) as [[| | |x]|] eqn:Hc; try exact I.
    destruct (classify_abs_sound rho _ _ x Hc Ha) as (Hwa & Hx & Hux).
    destruct (Z.eqb (x mod amo_bytes wd) 0) eqn:Hal; cbn [negb]; [|exact I].
    assert (Hw : 0 < amo_bytes wd <= 8) by (destruct wd; cbn; lia).
    assert (Hal' : amo_aligned wd (rget (core_of ms) rs1) = true) by (unfold amo_aligned; rewrite Hux; exact Hal).
    pose proof (r_resv _ _ _ _ _ _ HR) as Hrv.
    set (ok := match c_resv (core_of ms) with Some r => Z.eqb (bv_unsigned r) (bv_unsigned (rget (core_of ms) rs1)) | None => false end).
    assert (Hok_eq : ok = match s_resv st with Some r => Z.eqb r x | None => false end).
    { subst ok. cbn [c_resv core_of]. unfold resv_ok in Hrv. destruct (s_resv st) as [r|], (ms_resv ms) as [cw|]; try (exfalso; exact Hrv); try reflexivity.
      destruct Hrv as [-> Hr]. rewrite Hux, w64_unsigned. rewrite two64z_eq in Hr. rewrite Z.mod_small by lia. reflexivity. }
    (* [comment removed for export] *)
    assert (FAILARM : ok = false -> sound_res rho (s_next st) ms (SNext (set_pc (wr (set_resv st None) (regn rd) (alit 1)) (s_pc st + isz)))).
    { intros Hokf. pose proof (R_set_resv_none rho st ms HR) as HR0.
      pose proof (wr_sound rho (set_resv st None) _ rd (alit 1) w1 HR0 (alit_ok rho 1)) as HR1.
      rewrite core_of_ms_of in HR1. cbn [ms_mem ms_of] in HR1. rewrite ms_of_idem in HR1.
      cbn [sound_res]. eexists _, rho. split; [|split; [|split; [apply agree_refl | nxt]]].
      - apply Hcan. cbn [exec]. rewrite Hal'. cbn [negb]. fold ok. rewrite Hokf. rewrite interp_done. reflexivity.
      - rewrite with_resv_with_pc, <- with_pc_rset, (npc_eq rho st ms isz HR). apply set_pc_sound. exact HR1. }
    destruct (s_resv st) as [r|] eqn:Er.
    - destruct (Z.eqb_spec r x) as [->|NE]; [|apply FAILARM; rewrite Hok_eq; first [reflexivity | apply (proj2 (Z.eqb_neq r x)); exact NE]].
      pose proof (R_set_resv_none rho st ms HR) as HR0.
      assert (Hwf0 : wf_state (set_resv st None) = true) by (rewrite wf_set_resv; exact Hwf).
      set (ms0 := ms_of ms (with_resv None (core_of ms)) (ms_mem ms)) in HR0.
      pose proof (getreg_sound rho (set_resv st None) ms0 rs2 HR0) as Hv2.
      assert (Erg : rget (core_of ms0) rs2 = rget (core_of ms) rs2) by reflexivity. rewrite Erg in Hv2.
      destruct (do_store U (set_resv st None) (getreg st (regn rs1)) (amo_bytes wd) (getreg st (regn rs2))) as [st1|] eqn:Hst; [|exact I].
      change (getreg st (regn rs2)) with (getreg (set_resv st None) (regn rs2)) in Hst.
      destruct (do_store_sound U G M0 UOK rho (set_resv st None) ms0 _ _ (amo_bytes wd) _ (rget (core_of ms) rs2) st1
                  Hwf0 HR0 Ha Ba Hv2 (getreg_below _ (regn rs2) Hwf0) ltac:(lia) ltac:(lia) Hst)
        as (Hsok & HR1 & Hn1 & Hpc1 & Hrg1 & Hrv1).
      subst ms0. cbn [ms_mem ms_of] in Hsok, HR1. rewrite ms_with_mem_of in HR1. cbn [s_pc set_resv] in Hpc1.
      pose proof (wr_sound rho st1 _ rd (alit 0) w0 HR1 (alit_ok rho 0)) as HR2.
      rewrite core_of_ms_of in HR2. cbn [ms_mem ms_of] in HR2. rewrite ms_of_idem in HR2.
      cbn [sound_res].
      destruct wd; cbn [amo_bytes width_bytes] in *;
        (eexists _, rho; split; [|split; [|split; [apply agree_refl | nxt]]];
         [ apply Hcan; cbn [exec]; rewrite Hal'; cbn [negb]; fold ok; rewrite Hok_eq;
           first [ rewrite (interp_estore segs 32 4%nat) by (first [lia | exact Hsok])
                 | rewrite (interp_estore segs 64 8%nat) by (first [lia | exact Hsok]) ];
           rewrite interp_done; reflexivity
         | rewrite with_resv_with_pc, <- with_pc_rset, (npc_eq rho st ms isz HR), <- Hpc1;
           cbn [width_bytes]; change (Pos.to_nat 4) with 4%nat; change (Pos.to_nat 8) with 8%nat;
           rewrite ?store_bytes_low32; apply set_pc_sound; exact HR2 ]).
    - apply FAILARM. exact Hok_eq.
  Qed.

  Lemma low32_of_sext : forall (v : bv 32), low32 (sext 64 v) = v.
  Proof.
    intros v. apply bv_eq. unfold low32, sext. rewrite bv_extract_unsigned, Z.shiftr_0_r, bv_sign_extend_unsigned.
    pose proof (bv_unsigned_in_range _ v) as Hv. change (bv_modulus 32) with (2 ^ 32) in Hv.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 32 * 2 ^ 32). change (bv_modulus 32) with (2 ^ 32).
    rewrite Zaux.Zmod_mod_mult by lia. unfold bv_signed, bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32).
    change (bv_half_modulus 32) with (2 ^ 31).
    rewrite Zminus_mod_idemp_l. replace (bv_unsigned v + 2 ^ 31 - 2 ^ 31) with (bv_unsigned v) by lia.
    apply Z.mod_small. lia.
  Qed.

  Lemma store_bytes_amo32 : forall (r : bv 32),
    Z_to_le_bytes 4 (bv_unsigned r) = store_bytes 4 (w64 (snorm (uw (sext 64 r : word)))).
  Proof.
    intros r. unfold store_bytes, uw. change (Z.to_nat 4) with 4%nat. rewrite w64_snorm, w64_of_unsigned.
    rewrite <- (low32_of_sext r) at 1. unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply Z_to_le_bytes_wrap. cbn; lia.
  Qed.

  Lemma store_bytes_amo64 : forall (r : word),
    Z_to_le_bytes 8 (bv_unsigned r) = store_bytes 8 (w64 (snorm (uw r))).
  Proof. intros r. unfold store_bytes, uw. change (Z.to_nat 8) with 8%nat. rewrite w64_snorm, w64_of_unsigned. reflexivity. Qed.

  Lemma ldval4_sext : forall bs, length bs = 4%nat -> sext 64 (bv_extract 0 32 (le_bytes_to_word bs)) = ldval 4 true bs.
  Proof. intros bs H. apply (ldval_small 32 4 true bs); try lia; rewrite ?H; reflexivity. Qed.

  Lemma resv_after_store_pc : forall st a st', resv_after_store st a = Some st' -> s_pc st' = s_pc st.
  Proof.
    intros st a st' H. unfold resv_after_store in H. destruct (s_resv st) as [r|].
    - destruct (classify a) as [[| | |y]|]; try discriminate. injection H; intros <-. destruct (Z.eqb r y); reflexivity.
    - injection H; intros <-. reflexivity.
  Qed.

  Lemma sound_amo : forall rho st ms op wd aq rl rd rs1 rs2 isz,
    wf_state st = true -> R U G M0 rho st ms -> can_exec ms (Amo op wd aq rl rd rs1 rs2) isz ->
    sound_res rho (s_next st) ms (exec_instr U st (Amo op wd aq rl rd rs1 rs2) isz).
  Proof.
    intros rho st ms op wd aq rl rd rs1 rs2 isz Hwf HR Hcan. cbn [exec_instr].
    pose proof (R_VS _ _ _ HR) as HVS.
    pose proof (getreg_sound rho st ms rs1 HR) as Ha. pose proof (getreg_below st (regn rs1) Hwf) as Ba.
    destruct (classify (getreg st (regn rs1))) as [[| | |x]|] eqn:Hc; try exact I.
    destruct (classify_abs_sound rho _ _ x Hc Ha) as (Hwa & Hx & Hux).
    destruct (Z.eqb (x mod amo_bytes wd) 0) eqn:Hal; cbn [negb]; [|exact I].
    assert (Hw : 0 < amo_bytes wd <= 8) by (destruct wd; cbn; lia).
    assert (Hal' : amo_aligned wd (rget (core_of ms) rs1) = true) by (unfold amo_aligned; rewrite Hux; exact Hal).
    destruct (do_load U st (getreg st (regn rs1)) (amo_bytes wd) true) as [old st1|o p|] eqn:Hld; try exact I.
    destruct (do_load_sound U G M0 UOK SCOK rho st ms _ _ (amo_bytes wd) true old st1 Hwf HR Ha Ba ltac:(lia) ltac:(lia) Hld)
      as (rho1 & bs & Hrd & HR1 & Hlx & Hv & Bv).
    pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
    destruct (wf_state st1) eqn:Hwf1; cbn [negb]; [|exact I].
    destruct (aval_lit old) as [o|] eqn:Lo; [|exact I].
    destruct (aval_lit (getreg st1 (regn rs2))) as [sv|] eqn:Ls; [|exact I].
    pose proof (aval_lit_sound rho1 old o _ Lo Hv) as Hold.
    pose proof (aval_lit_sound rho1 _ sv _ Ls (getreg_sound rho1 st1 ms rs2 HR1)) as Hsrc.
    assert (Ha1 : val_ok rho1 (getreg st (regn rs1)) (rget (core_of ms) rs1)).
    { eapply val_ok_agree; [exact Ba | exact (proj1 Hlx) | exact Ha]. }
    destruct (resv_after_store st1 (getreg st (regn rs1))) as [st2|] eqn:Hra; [|exact I].
    destruct (resv_after_store_sound rho1 st1 ms _ _ st2 HR1 Ha1 Hra) as (HR2 & Hn2 & Hwf2). specialize (Hwf2 Hwf1).
    set (ms2 := ms_of ms (inval_resv (rget (core_of ms) rs1) (core_of ms)) (ms_mem ms)) in HR2.
    set (nv := match wd with
               | AW => snorm (uw (sext 64 (amo_val op (low32 (LXI.w64 o)) (low32 (LXI.w64 sv))) : word))
               | AD => snorm (uw (amo_val op (LXI.w64 o) (LXI.w64 sv)))
               end).
    destruct (do_store U st2 (getreg st (regn rs1)) (amo_bytes wd) (alit nv)) as [st3|] eqn:Hst; [|exact I].
    assert (Ba2 : aval_below (getreg st (regn rs1)) (s_next st2) = true).
    { rewrite Hn2. eapply aval_below_mono; [exact (proj1 (proj2 Hlx)) | exact Ba]. }
    destruct (do_store_sound U G M0 UOK rho1 st2 ms2 _ _ (amo_bytes wd) (alit nv) (w64 nv) st3
                Hwf2 HR2 Ha1 Ba2 (alit_ok rho1 nv) (alit_below _ _) ltac:(lia) ltac:(lia) Hst)
      as (Hsok & HR3 & Hn3 & Hpc3 & Hrg3 & Hrv3).
    subst ms2. cbn [ms_mem ms_of] in Hsok, HR3. rewrite ms_with_mem_of in HR3.
    assert (Bv3 : aval_below old (s_next st3) = true) by (rewrite Hn3, Hn2; exact Bv).
    pose proof (wr_sound rho1 st3 _ rd old _ HR3 Hv) as HR4.
    rewrite core_of_ms_of in HR4. cbn [ms_mem ms_of] in HR4. rewrite ms_of_idem in HR4.
    assert (Epc : s_pc st3 = s_pc st).
    { rewrite Hpc3. destruct Hlx as (_ & _ & E1 & _). rewrite <- E1. apply (resv_after_store_pc _ _ _ Hra). }
    cbn [sound_res].
    destruct wd; cbn [amo_bytes] in *.
    - eexists _, rho1. split; [|split; [|split; [exact (proj1 Hlx) | nxt; destruct Hlx as (_ & ?N1 & _); lia]]].
      + apply Hcan. cbn [exec]. rewrite Hal'. cbn [negb].
        rewrite (interp_eload segs 32 4%nat _ _ (ms_mem ms) bs) by (first [left; split; reflexivity | exact Hrd]).
        rewrite (interp_estore segs 32 4%nat) by (first [lia | exact Hsok]). rewrite interp_done. reflexivity.
      + rewrite inval_resv_with_pc, <- with_pc_rset, (npc_eq rho st ms isz HR), <- Epc.
        rewrite (ldval4_sext bs Hlen).
        rewrite <- (low32_of_sext (bv_extract 0 32 (le_bytes_to_word bs))). rewrite (ldval4_sext bs Hlen), Hold, Hsrc.
        cbn [width_bytes]. change (Pos.to_nat 4) with 4%nat. rewrite store_bytes_amo32.
        rewrite Hold in HR4. apply set_pc_sound. exact HR4.
    - eexists _, rho1. split; [|split; [|split; [exact (proj1 Hlx) | nxt; destruct Hlx as (_ & ?N1 & _); lia]]].
      + apply Hcan. cbn [exec]. rewrite Hal'. cbn [negb].
        rewrite (interp_eload segs 64 8%nat _ _ (ms_mem ms) bs) by (first [right; split; reflexivity | exact Hrd]).
        rewrite (interp_estore segs 64 8%nat) by (first [lia | exact Hsok]). rewrite interp_done. reflexivity.
      + rewrite inval_resv_with_pc, <- with_pc_rset, (npc_eq rho st ms isz HR), <- Epc.
        rewrite bv_extract_full. change (le_bytes_to_word bs) with (ldval 8 true bs). rewrite Hold, Hsrc.
        cbn [width_bytes]. change (Pos.to_nat 8) with 8%nat. rewrite store_bytes_amo64.
        rewrite Hold in HR4. apply set_pc_sound. exact HR4.
  Qed.

  Theorem step_sound : forall rho st ms,
    wf_state st = true -> R U G M0 rho st ms -> sound_res rho (s_next st) ms (LXI.step U st).
  Proof.
    intros rho st0 ms Hwf0 HR0.
    (* [comment removed for export] *)
    pose proof (LXWF.gc_facts_wf st0 Hwf0) as Hwf.
    pose proof (LXSM.R_vext U G M0 rho st0 ms rho (gc_facts st0) Hwf0 HR0 (LXSV.gc_facts_vext rho st0)
                  (LXSV.gc_facts_VS rho st0 (r_vs _ _ _ _ _ _ HR0))) as HR.
    pose proof (LXWF.gc_facts_same st0) as (_ & _ & En & _). rewrite <- En. clear En.
    unfold LXI.step, fetch. set (st := gc_facts st0) in *. clearbody st. clear Hwf0 HR0 st0.
    destruct (fetch_word (ue_segs U) (LXI.w64 (s_pc st))) as [w|] eqn:Hf; [|exact I].
    destruct (is_ecall w) eqn:He; [exact I|].
    destruct (decode_any w) as [[i isz]|] eqn:Hd; [|exact I].
    assert (Hcan : can_exec ms i isz).
    { intros c' m' Hi. unfold cstep. eapply step_via; eauto. rewrite (r_pc _ _ _ _ _ _ HR). exact Hf. }
    destruct i;
      [ apply sound_lui | apply sound_auipc | apply sound_jal | apply sound_jalr | apply sound_branch
      | apply sound_load | apply sound_store | apply sound_opimm | apply sound_shiftimm | apply sound_op
      | apply sound_opimm32 | apply sound_shiftimm32 | apply sound_op32 | apply sound_fence | apply sound_fencei
      | exact I | exact I | apply sound_mul | apply sound_mul32 | apply sound_lr | apply sound_sc | apply sound_amo
      | exact I | exact I | apply sound_fload | apply sound_fstore | apply sound_fma | apply sound_fari | apply sound_fsqrt
      | apply sound_fsgnj | apply sound_fminmax | apply sound_fcmp | apply sound_fcvt | apply sound_fmv | apply sound_fclass ];
      assumption.
  Qed.

End WithU.

End LXSS.
