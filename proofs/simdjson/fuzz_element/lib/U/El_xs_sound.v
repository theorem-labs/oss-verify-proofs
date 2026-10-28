(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import MState Mem Frame Cells Step Exec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec CatExec CatSim StoreOk AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_xs_stepG El_xs_soundG El_xs_full El_xs_core.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2SG.
Open Scope Z_scope.

Lemma lor_shl_disjoint8 : forall a b, 0 <= a -> 0 <= b < 256 -> Z.lor b (Z.shiftl a 8) = b + 256 * a.
Proof.
  intros a b Ha Hb. rewrite Z.shiftl_mul_pow2 by lia.
  assert (D : Z.land b (a * 2 ^ 8) = 0).
  { apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec0 k 8).
    - rewrite (Z.mul_pow2_bits_low a 8 k) by lia. apply andb_false_r.
    - replace b with (b mod 2 ^ 8) by (apply Z.mod_small; lia). rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b rest IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg rest) as Hr.
  rewrite (lor_shl_disjoint8 (bytes_le_to_Z rest) (bv_unsigned b)) by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z rest) with (bv_unsigned b + bytes_le_to_Z rest * 256) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256) with (bytes_le_to_Z rest); [exact IH|].
    replace (bv_unsigned b + 256 * bytes_le_to_Z rest) with (bytes_le_to_Z rest * 256 + bv_unsigned b) by lia.
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma le8_of_rdn_val : forall (bs : list byte) (w : word),
  length bs = 8%nat -> Z_to_bv 64 (bytes_le_to_Z bs) = w -> word_to_le_bytes 8 w = bs.
Proof.
  intros bs w Hl Hv. unfold word_to_le_bytes. rewrite <- Hv, Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite Hl in B. change (2 ^ (8 * Z.of_nat 8)) with (bv_modulus 64) in B.
  rewrite bv_wrap_small by exact B. rewrite <- Hl. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma rdn_defined_at : forall segs m (a : word) n bs,
  rdn segs m a n = Some bs ->
  forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> exists b, mrd segs m x = Some b.
Proof.
  intros segs m a n. revert a. induction n as [|n IH]; intros a bs Hr x Hx; [lia|].
  cbn [rdn] in Hr. change (match m a with Some b => Some b | None => seg_rom segs a end) with (mrd segs m a) in Hr.
  destruct (mrd segs m a) as [b|] eqn:Hb; [|discriminate].
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Ex|Nx].
  - exists b. replace x with a; [exact Hb|]. apply bv_eq. lia.
  - destruct n as [|n']; [lia|].
    destruct (rdn segs m (a + 1)%bv (S n')) as [rest|] eqn:Hr'; [|discriminate].
    pose proof (u64_range x) as Rx.
    assert (Hu1 : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    apply (IH (a + 1)%bv rest Hr'). rewrite Hu1. lia.
Qed.

Lemma adenot_SA : forall E b off, adenot E (SA b off) = Z_to_bv 64 (bv_unsigned (edenot E b) + off).
Proof. intros. reflexivity. Qed.

Lemma rdn_common : forall segs m a n,
  OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Common.PropExec.rdn segs m a n = OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS.PropExec.rdn segs m a n.
Proof. intros segs m a n. revert a. induction n as [|n IH]; intros a; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma reg_enum : forall r : reg, exists k : Z, 0 <= k < 32 /\ r = Z_to_bv 5 k.
Proof. intros r. exists (bv_unsigned r). split; [pose proof (bv_unsigned_in_range 5 r) as H; unfold bv_modulus in H; cbn in H; lia| apply bv_eq; rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity| apply bv_unsigned_in_range]]. Qed.

Ltac reg_cases r :=
  let k := fresh "k" in let Hk := fresh "Hk" in let E := fresh "E" in
  destruct (reg_enum r) as (k & Hk & E); subst r;
  assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12
                \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23
                \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia;
  clear Hk; repeat (destruct Hk' as [-> | Hk']); [ .. | subst k].

Section S.
Variable segs : list Segment.
Variable t : itab.
Hypothesis Ht : itab_sound segs t.
Variables SETPC CPYPC FSDPC FLDPC : Z.
Hypothesis Hset : set_contract segs SETPC.
Hypothesis Hcpy : cpy_contract segs CPYPC.
Hypothesis Hfsd : fsd_contract segs FSDPC.
Hypothesis Hfld : fld_contract segs FLDPC.
Let rom := seg_rom segs.

#[local] Notation CIX := (CIX segs) (only parsing).
#[local] Notation CI := (CI segs) (only parsing).

Definition node_ok (fc : bv 32) (ss ss' : sym_state) (E : env) (W RW : list wrange) (m0 base : word -> option byte) (ms : machine_state) : Prop :=
  exists E' base' ms', eagree (s_next ss) E E' /\ (s_next ss <= s_next ss')%nat /\ Exec.msteps segs ms ms' /\ CIX fc E' W RW m0 base' ss' ms'.

Lemma in_W_In : forall W b lo hi, in_W W b lo hi = true ->
  exists wb wlo whi, In (wb, wlo, whi) W /\ b = wb /\ wlo <= lo /\ hi <= whi.
Proof.
  induction W as [|[[wb wlo] whi] W' IH]; cbn [in_W]; intros b lo hi H; [discriminate|].
  apply orb_prop in H. destruct H as [H|H].
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    exists wb, wlo, whi. split; [left; reflexivity|]. auto.
  - destruct (IH _ _ _ H) as (wb' & wlo' & whi' & HIn & E & A & B). exists wb', wlo', whi'. split; [right; exact HIn|]. auto.
Qed.

Lemma log_inW_out : forall E W log base x,
  log_flat E log -> log_inW W log = true -> ~ Wd E W x -> mem_denot E base log x = base x.
Proof.
  intros E W log base x. induction log as [|[a w v] rest IH]; intros HF HL HW; [reflexivity|].
  cbn [mem_denot]. cbn [log_flat] in HF. destruct HF as (Hw & Hfl & HF).
  cbn [log_inW forallb] in HL. apply andb_prop in HL as [H1 HL].
  unfold se_inW in H1. cbn [e_addr e_width] in H1. destruct a as [b off]. cbn [a_base a_off] in H1.
  destruct (in_W_In _ _ _ _ H1) as (wb & wlo & whi & HIn & -> & A & B).
  pose proof (flat_u E _ _ Hfl) as EU. destruct Hfl as (F1 & F2 & F3 & F4).
  rewrite wbytes_out.
  - exact (IH HF HL HW).
  - rewrite EU. rewrite length_N_to_le_bytes. lia.
  - rewrite EU. rewrite length_N_to_le_bytes. unfold estart in *. cbn [a_base a_off] in *.
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E wb) + off)) as [L|L]; [left; lia|].
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E wb) + off + Z.of_nat w)) as [L2|L2]; [|right; lia].
    exfalso. apply HW. exists wb, wlo, whi. split; [exact HIn|]. lia.
Qed.

Lemma Wd_eagree : forall E E' W x, wf_W W = true -> eagree FPB E E' -> Wd E W x -> Wd E' W x.
Proof.
  intros E E' W x HW HA (wb & wlo & whi & HIn & H). exists wb, wlo, whi. split; [exact HIn|].
  unfold wf_W in HW. rewrite forallb_forall in HW. specialize (HW _ HIn). cbn [fst] in HW.
  rewrite <- (edenot_evars_lt FPB E E' wb HA HW). exact H.
Qed.

Theorem node_run_sound : forall fc W RW fuel stops ss ss' E m0 base ms,
  wf_W W = true -> wf_W RW = true ->
  node_run segs t W fuel stops ss = Some ss' -> CIX fc E W RW m0 base ss ms -> node_ok fc ss ss' E W RW m0 base ms.
Proof.
  intros fc W RW fuel stops ss ss' E m0 base ms HW HRW Hn [Hnx HC]. unfold node_run in Hn.
  destruct (log_inW W (s_log (sym_execTX segs t KCAP fuel true stops ss))) eqn:HL; [|discriminate]. injection Hn as <-.
  destruct (HC E (eagree_refl _ _)) as (R & F & Hms & HR & HLF & HK & HFR & HFP & HMI & HWM & HB & HLW & HRD).
  pose (fx := PropExec.mkFP F fc).
  assert (HST : forall E', eagree (s_next ss) E E' -> @st_ok fx segs E' base rom ss ms).
  { intros E' HA. destruct (HC E' HA) as (R' & F' & Hms' & HR' & HLF' & HK' & _).
    exists R'. rewrite Hms in Hms' |- *. injection Hms' as ER EF EM. subst R'.
    split; [unfold mkst; cbn; rewrite <- EM; reflexivity|]. split; [exact HR'|]. split; [exact HLF'| exact HK']. }
  destruct (@sym_execTX_sound fx segs t KCAP fuel true stops ss E base rom ms Ht HST) as (E1 & ms1 & HA1 & Hle & HMS & HALL).
  exists E1, base, ms1. split; [exact HA1|]. split; [exact Hle|]. split; [apply msteps_lib_of_as; exact HMS|].
  unfold El_xs_core.CIX. split. { cbn [s_next] in *. lia. }
  intros E'' HA''. destruct (HALL E'' HA'') as (R1 & Hms1 & HR1 & HLF1 & HK1).
  pose proof (msteps_lib_of_as _ _ _ HMS) as HMSL.
  exists R1, F. split; [exact Hms1|]. split; [exact HR1|]. split; [exact HLF1|]. split; [exact HK1|].
  split. { pose proof (msteps_full segs _ _ HMSL) as X. rewrite Hms, Hms1 in X. cbn in X. apply X. exact HFR. }
  assert (HAE : eagree (FPB + 32) E E'').
  { eapply eagree_le; [| exact Hnx]. eapply eagree_trans; [exact HA1|]. eapply eagree_le; [exact HA''| exact Hle]. }
  split. { intros i Hi. rewrite <- (HFP i Hi). symmetry. apply (proj1 HAE). unfold FPB in *. lia. }
  pose proof (msteps_mem_inv segs _ _ HMSL HMI) as (HMI1 & HWM1 & HOV1).
  split; [exact HMI1|]. split; [eapply wmono_trans; [exact HWM| exact HWM1]|].
  split. { intros x Hx. apply HB. intros HWd. apply Hx. eapply Wd_eagree; [exact HW| eapply eagree_le; [exact HAE| lia]| exact HWd]. }
  split; [exact HL|].
  intros x Hx. assert (Hx0 : Wd E RW x). { eapply Wd_eagree; [exact HRW| apply eagree_sym; eapply eagree_le; [exact HAE| lia]| exact Hx]. }
  destruct (HRD x Hx0) as [D1 D2]. split; [apply HOV1; exact D1| exact D2].
Qed.

Theorem node_flush_sound : forall fc W RW ss ss' E m0 base ms,
  wf_W W = true -> wf_W RW = true ->
  node_flush ss = Some ss' -> CIX fc E W RW m0 base ss ms -> node_ok fc ss ss' E W RW m0 base ms.
Proof.
  intros fc W RW ss ss' E m0 base ms HW HRW Hn [Hnx HC]. unfold node_flush in Hn.
  destruct (carry (s_log ss) (s_know ss) []) as [[kn' scs] hs] eqn:Hc. destruct scs; [|discriminate]. injection Hn as <-.
  exists E, (ms_mem ms), ms. split; [apply eagree_refl|]. split; [cbn; lia|]. split; [apply Exec.msteps_refl|]. split; [cbn; exact Hnx|].
  intros E' HA. destruct (HC E' HA) as (R & F & Hms & HR & HLF & HK & HFR & HFP & HMI & HWM & HB & HLW & HRD).
  exists R, F. cbn [s_pc s_regs s_log s_know s_next].
  assert (EM : ms_mem ms = mem_denot E' base (s_log ss)) by (rewrite Hms; reflexivity).
  split; [cbn [mem_denot]; rewrite Hms at 1; rewrite EM; reflexivity|].
  split; [exact HR|]. split; [exact I|].
  split. { rewrite EM. eapply (carry_sound segs E' base); [exact Hc| exact HLF| exact HK| constructor]. }
  split; [exact HFR|]. split; [exact HFP|]. split; [exact HMI|]. split; [exact HWM|].
  split. { intros x Hx. rewrite EM. rewrite (log_inW_out E' W _ _ x HLF HLW Hx). apply HB. exact Hx. }
  split; [reflexivity| exact HRD].
Qed.

Fixpoint eupds (E : env) (nx : nat) (vals : list word) : env :=
  match vals with [] => E | v :: vs => eupds (eupd E nx v) (S nx) vs end.

Lemma eupds_agree : forall vals E nx, eagree nx E (eupds E nx vals).
Proof.
  induction vals as [|v vs IH]; intros E nx; cbn [eupds]; [apply eagree_refl|].
  eapply eagree_trans; [apply eagree_upd|]. eapply eagree_le; [apply IH| lia].
Qed.

Lemma eupds_at : forall vals E nx j, (j < length vals)%nat -> ev (eupds E nx vals) (nx + j)%nat = nth j vals (Z_to_bv 64 0).
Proof.
  induction vals as [|v vs IH]; intros E nx j Hj; cbn [length] in Hj; [lia|]. cbn [eupds].
  destruct j as [|j].
  - rewrite Nat.add_0_r. pose proof (eupds_agree vs (eupd E nx v) (S nx)) as [A _]. rewrite <- (A nx) by lia. cbn [nth]. apply eupd_at.
  - replace (nx + S j)%nat with (S nx + j)%nat by lia. cbn [nth]. apply IH. lia.
Qed.

Fixpoint regupds (R : bvmap 5 word) (rs : list nat) (vals : list word) : bvmap 5 word :=
  match rs, vals with
  | r :: rs', v :: vals' => regupds (regupd R (Z_to_bv 5 (Z.of_nat r)) v) rs' vals'
  | _, _ => R
  end.

Lemma havoc_regs_ok : forall E rs sr R nx vals,
  regs_ok E sr R -> length vals = length rs -> (forall r, In r rs -> (0 < r < 32)%nat) ->
  (forall j, (j < length vals)%nat -> ev E (nx + j)%nat = nth j vals (Z_to_bv 64 0)) ->
  regs_ok E (havoc_regs sr rs nx) (regupds R rs vals).
Proof.
  intros E rs. induction rs as [|r rs IH]; intros sr R nx vals HR Hlen Hrs Hev.
  - destruct vals; [exact HR| cbn in Hlen; lia].
  - destruct vals as [|v vals]; [cbn in Hlen; lia|]. cbn [havoc_regs regupds].
    assert (Hr : (0 < r < 32)%nat) by (apply Hrs; left; reflexivity).
    assert (NZ : bv_eqb (Z_to_bv 5 (Z.of_nat r)) 0 = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned, bv_wrap_small; [| unfold bv_modulus; cbn [Z.pow Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul]; lia].
      rewrite bv_0_unsigned || (change (bv_unsigned (0%bv : bv 5)) with 0%Z). lia. }
    assert (RI : ridx (Z_to_bv 5 (Z.of_nat r)) = r).
    { unfold ridx. rewrite Z_to_bv_unsigned, bv_wrap_small; [lia| unfold bv_modulus; cbn [Z.pow Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul]; lia]. }
    apply IH.
    + pose proof (regs_ok_upd E sr R (Z_to_bv 5 (Z.of_nat r)) v (EVar nx) HR) as X. rewrite NZ, RI in X. apply X.
      cbn [edenot]. specialize (Hev 0%nat ltac:(cbn; lia)). rewrite Nat.add_0_r in Hev. exact Hev.
    + cbn in Hlen. lia.
    + intros r' Hin. apply Hrs. right. exact Hin.
    + intros j Hj. replace (S nx + j)%nat with (nx + S j)%nat by lia. rewrite Hev by (cbn; lia). reflexivity.
Qed.

Lemma regs_ok_ext : forall E sr R R', regs_ok E sr R -> (forall r, getr R' r = getr R r) -> regs_ok E sr R'.
Proof. intros E sr R R' H HE r. rewrite HE. apply H. Qed.

Lemma CLOB_range : forall r, In r CLOB -> (0 < r < 32)%nat.
Proof. intros r H. unfold CLOB in H. cbn in H. lia. Qed.

Lemma regupds_CLOB : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13,
  regupds (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          CLOB [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13]
  = mkR x1 x2 x3 x4 v0 v1 v2 x8 x9 x10 v3 v4 v5 v6 v7 v8 v9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 v10 v11 v12 v13.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma reg_get_mkR_1_10_11_12 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  let R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  reg_get R (Z_to_bv 5 1) = x1 /\ reg_get R (Z_to_bv 5 10) = x10 /\ reg_get R (Z_to_bv 5 11) = x11 /\ reg_get R (Z_to_bv 5 12) = x12.
Proof. intros. vm_compute. repeat split; reflexivity. Qed.

Lemma mod4_mod2 : forall ra, ra mod 4 = 0 -> ra mod 2 = 0.
Proof.
  intros ra H. pose proof (Z.div_mod ra 4 ltac:(lia)) as D. rewrite H in D.
  replace ra with (2 * (2 * (ra / 4))) by lia. rewrite Z.mul_comm, Z.mod_mul; [reflexivity| lia].
Qed.

Lemma call_gate_sound : forall W RW PC ss ra db dk n,
  call_gate W RW PC ss = Some (ra, db, dk, n) ->
  s_log ss = [] /\ s_pc ss = PC
  /\ sr_get (s_regs ss) (Z_to_bv 5 1) = ELit ra /\ sr_get (s_regs ss) (Z_to_bv 5 12) = ELit n
  /\ split_lit (sr_get (s_regs ss) (Z_to_bv 5 10)) = (db, dk)
  /\ 0 <= ra < two64 /\ ra mod 4 = 0 /\ 0 < n <= 4096
  /\ range_flat (facts_of (s_know ss)) db dk n = true /\ kwr_find (s_know ss) db dk n = true
  /\ in_W W db dk (dk + n) = true /\ in_W RW db dk (dk + n) = true.
Proof.
  intros W RW PC ss ra db dk n H. unfold call_gate in H.
  destruct (s_log ss); [|discriminate].
  destruct (sr_get (s_regs ss) (Z_to_bv 5 1)) as [ra'| | | | | | |]; try discriminate.
  destruct (sr_get (s_regs ss) (Z_to_bv 5 12)) as [n'| | | | | | |]; try discriminate.
  destruct (split_lit (sr_get (s_regs ss) (Z_to_bv 5 10))) as [db' dk'].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate] end. injection H as <- <- <- <-.
  apply andb_prop in Hg as [Hg G10]. apply andb_prop in Hg as [Hg G9]. apply andb_prop in Hg as [Hg G8]. apply andb_prop in Hg as [Hg G7].
  apply andb_prop in Hg as [Hg G6]. apply andb_prop in Hg as [Hg G5]. apply andb_prop in Hg as [Hg G4]. apply andb_prop in Hg as [Hg G3].
  apply andb_prop in Hg as [G1 G2].
  apply Z.eqb_eq in G1. apply Z.leb_le in G2. apply Z.ltb_lt in G3. apply Z.eqb_eq in G4. apply Z.ltb_lt in G5. apply Z.leb_le in G6.
  repeat split; try assumption; try reflexivity; try lia.
Qed.

Lemma defined_bytes : forall (m : word -> option byte) A n,
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, A <= bv_unsigned x < A + Z.of_nat n -> m x <> None) ->
  exists junk, length junk = n /\ bytes_at segs m A junk.
Proof.
  intros m A n HA Hn HD.
  exists (map (fun i => match m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
  split; [rewrite length_map, length_seq; reflexivity|].
  split; [exact HA|]. split; [rewrite length_map, length_seq; exact Hn|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite nth_error_map, nth_error_seq. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). cbn [option_map Nat.add].
  unfold mrd. specialize (HD (wa (A + Z.of_nat i))). unfold wa in HD |- *. rewrite u_small in HD by lia.
  destruct (m (Z_to_bv 64 (A + Z.of_nat i))) as [b|] eqn:Eb; [reflexivity|]. exfalso. apply HD; [lia| reflexivity].
Qed.

Lemma rw_cells_CB : forall m A n junk,
  length junk = n -> bytes_at segs m A junk -> wr_at segs m A (Z.of_nat n) -> rw_cells segs m A [CB n junk].
Proof.
  intros m A n junk Hl HB HW. split.
  - split; [cbn; split; [exact Hl| exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma kzeros8_ok : forall E M b k cnt,
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + 8 * Z.of_nat cnt <= 2 ^ 64 ->
  (forall j, (j < cnt)%nat -> rdn segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + k + 8 * Z.of_nat j)) 8 = Some (repeat (Z_to_bv 8 0) 8)) ->
  know_ok segs E M (kzeros8 b k cnt).
Proof.
  intros E M b k cnt. revert k. induction cnt as [|c IH]; intros k Hlo Hhi Hrd; [constructor|].
  cbn [kzeros8]. constructor.
  - cbn [kentry_ok]. split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off]; lia|].
    rewrite adenot_SA. specialize (Hrd 0%nat ltac:(lia)). rewrite Z.mul_0_r, Z.add_0_r in Hrd. rewrite Hrd. reflexivity.
  - apply (IH (k + 8)); [lia| lia|]. intros j Hj.
    replace (bv_unsigned (edenot E b) + (k + 8) + 8 * Z.of_nat j) with (bv_unsigned (edenot E b) + k + 8 * Z.of_nat (S j)) by lia. apply Hrd. lia.
Qed.
Lemma kzeros1_ok : forall E M b k cnt,
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + Z.of_nat cnt <= 2 ^ 64 ->
  (forall j, (j < cnt)%nat -> rdn segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + k + Z.of_nat j)) 1 = Some [Z_to_bv 8 0]) ->
  know_ok segs E M (kzeros1 b k cnt).
Proof.
  intros E M b k cnt. revert k. induction cnt as [|c IH]; intros k Hlo Hhi Hrd; [constructor|].
  cbn [kzeros1]. constructor.
  - cbn [kentry_ok]. split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off]; lia|].
    rewrite adenot_SA. specialize (Hrd 0%nat ltac:(lia)). rewrite Z.add_0_r in Hrd. rewrite Hrd. reflexivity.
  - apply (IH (k + 1)); [lia| lia|]. intros j Hj.
    replace (bv_unsigned (edenot E b) + (k + 1) + Z.of_nat j) with (bv_unsigned (edenot E b) + k + Z.of_nat (S j)) by lia. apply Hrd. lia.
Qed.

Lemma skipn_repeat' : forall {A} (x : A) i n, skipn i (repeat x n) = repeat x (n - i).
Proof. intros A x i. induction i as [|i IH]; intros n; [cbn; rewrite Nat.sub_0_r; reflexivity|]. destruct n as [|n]; [reflexivity|]. cbn. apply IH. Qed.
Lemma firstn_repeat' : forall {A} (x : A) k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. intros A x k. induction k as [|k IH]; intros n H; [reflexivity|]. destruct n as [|n]; [lia|]. cbn. f_equal. apply IH. lia. Qed.
Lemma firstn_skipn_repeat : forall {A} (x : A) n i k, (i + k <= n)%nat -> firstn k (skipn i (repeat x n)) = repeat x k.
Proof.
  intros A x n i k H. rewrite skipn_repeat', firstn_repeat'; [reflexivity| lia].
Qed.

Lemma kzeros_ok : forall E M b k n,
  0 <= bv_unsigned (edenot E b) + k -> 0 <= n -> bv_unsigned (edenot E b) + k + n <= 2 ^ 64 ->
  bytes_at segs M (bv_unsigned (edenot E b) + k) (repeat (Z_to_bv 8 0) (Z.to_nat n)) ->
  know_ok segs E M (kzeros b k n).
Proof.
  intros E M b k n Hlo Hn Hhi HB. unfold kzeros.
  pose proof (Z.div_mod n 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as MB.
  assert (D0 : 0 <= n / 8) by (apply Z.div_pos; lia).
  apply Forall_app. split.
  - apply kzeros8_ok; [lia| lia|]. intros j Hj.
    replace (bv_unsigned (edenot E b) + k + 8 * Z.of_nat j) with (bv_unsigned (edenot E b) + k + Z.of_nat (8 * j)) by lia.
    pose proof (bytes_at_rdn segs M _ _ (8 * j) 8 HB ltac:(rewrite repeat_length; lia)) as X. rewrite rdn_common in X. unfold wa in X.
    rewrite X. f_equal. apply firstn_skipn_repeat. lia.
  - apply kzeros1_ok; [lia| lia|]. intros j Hj.
    replace (bv_unsigned (edenot E b) + (k + 8 * (n / 8)) + Z.of_nat j) with (bv_unsigned (edenot E b) + k + Z.of_nat (Z.to_nat (8 * (n / 8)) + j)) by lia.
    pose proof (bytes_at_rdn segs M _ _ (Z.to_nat (8 * (n / 8)) + j) 1 HB ltac:(rewrite repeat_length; lia)) as X. rewrite rdn_common in X. unfold wa in X.
    rewrite X. f_equal. change [Z_to_bv 8 0] with (repeat (Z_to_bv 8 0) 1). apply firstn_skipn_repeat. lia.
Qed.

Lemma node_drop_sound : forall fc W RW b lo hi ss ss' E m0 base ms,
  wf_W RW = true ->
  node_drop b lo hi ss = Some ss' -> CIX fc E W RW m0 base ss ms -> node_ok fc ss ss' E W RW m0 base ms.
Proof.
  intros fc W RW b lo hi ss ss' E m0 base ms HRW Hn [Hnx HC]. unfold node_drop in Hn.
  destruct (s_log ss) eqn:HL; [|discriminate]. injection Hn as <-.
  exists E, base, ms. split; [apply eagree_refl|]. split; [cbn; lia|]. split; [apply Exec.msteps_refl|].
  split; [cbn; exact Hnx|]. intros E' HA. destruct (HC E' HA) as (R & F & Hms & HR & HLF & HK & HFR & HFP & HMI & HWM & HB & HLW & HRD).
  exists R, F. cbn [s_pc s_regs s_log s_know s_next]. rewrite HL in Hms, HLF. cbn [mem_denot] in Hms |- *.
  repeat (split; [assumption|]). split.
  { unfold know_ok in *. rewrite Forall_forall in HK |- *. intros K HIn. apply List.filter_In in HIn as [HIn _]. apply HK. exact HIn. }
  repeat (split; [assumption|]). split; [reflexivity| exact HRD].
Qed.

Lemma split_lit_val : forall E e b k,
  split_lit e = (b, k) -> bv_unsigned (edenot E e) = (bv_unsigned (edenot E b) + k) mod two64.
Proof.
  intros E e b k Hs.
  pose proof (to_saddr_denot E e 0) as X. unfold to_saddr in X. rewrite Hs in X.
  unfold adenot, v_addi in X. cbn [a_base a_off] in X. rewrite Z.add_0_r in X.
  apply (f_equal bv_unsigned) in X. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in X.
  rewrite ?Z.add_0_r in X. rewrite (Z.mod_small (bv_unsigned (edenot E e))) in X by apply u64_range. symmetry. unfold two64. exact X.
Qed.

Lemma range_flat_sound : forall E M fk b k n,
  know_ok segs E M fk -> range_flat fk b k n = true ->
  0 <= bv_unsigned (edenot E b) + k /\ 0 <= n /\ bv_unsigned (edenot E b) + k + n <= two64.
Proof.
  intros E M fk b k n Hfk H. unfold range_flat in H.
  destruct (base_range fk b) as [[lo hi]|] eqn:Hb; [|discriminate].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  pose proof (base_range_sound segs E M fk b lo hi Hfk Hb) as [A B]. lia.
Qed.

Lemma dst_val : forall E e db dk fk M n,
  split_lit e = (db, dk) -> know_ok segs E M fk -> range_flat fk db dk n = true -> 0 < n ->
  bv_unsigned (edenot E e) = bv_unsigned (edenot E db) + dk.
Proof.
  intros E e db dk fk M n Hs Hfk Hr Hn.
  rewrite (split_lit_val E e db dk Hs). apply Z.mod_small.
  pose proof (range_flat_sound E M fk db dk n Hfk Hr). pose proof (u64_range (edenot E db)). unfold two64 in *. lia.
Qed.

Lemma MS_inj : forall R F pc fc rv m ro R' F' pc' fc' rv' m' ro',
  MS R F pc fc rv m ro = MS R' F' pc' fc' rv' m' ro' -> R = R' /\ F = F' /\ pc = pc' /\ fc = fc' /\ m = m'.
Proof. intros. unfold MS in H. injection H. intros. subst. repeat split; reflexivity. Qed.

Lemma CI_same_ms : forall E1 E2 W RW m0 base ss ms R F fc,
  ms = MS R F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E1 base (s_log ss)) rom ->
  CI fc E2 W RW m0 base ss ms ->
  regs_ok E2 (s_regs ss) R /\ log_flat E2 (s_log ss) /\ know_ok segs E2 base (s_know ss) /\ fp_ok E2 F
  /\ mem_denot E2 base (s_log ss) = mem_denot E1 base (s_log ss) /\ (forall x, ~ Wd E2 W x -> base x = m0 x)
  /\ (forall x, Wd E2 RW x -> ms_mem ms x <> None /\ seg_rom segs x = None).
Proof.
  intros E1 E2 W RW m0 base ss ms R F fc Hms (R' & F' & Hms' & HR & HLF & HK & HFR & HFP & HMI & HWM & HB & HLW & HRD).
  rewrite Hms in Hms'. apply MS_inj in Hms' as (<- & <- & _ & _ & EM).
  split; [exact HR|]. split; [exact HLF|]. split; [exact HK|]. split; [exact HFP|]. split; [symmetry; exact EM|]. split; [exact HB| exact HRD].
Qed.

Lemma check_fp_sound : forall E F base ss b k i cnt,
  check_fp segs ss (facts_of (s_know ss)) b k i cnt = true ->
  log_flat E (s_log ss) -> know_ok segs E base (s_know ss) -> fp_ok E F ->
  (i + cnt <= 32)%nat ->
  forall j, (j < cnt)%nat ->
    rdn segs (mem_denot E base (s_log ss)) (Z_to_bv 64 (bv_unsigned (edenot E b) + (k + 8 * Z.of_nat j))) 8 = Some (fle8 F (i + j)).
Proof.
  intros E F base ss b k i cnt. revert k i. induction cnt as [|c IH]; intros k i HC HLF HK HFP Hic j Hj; [lia|].
  cbn [check_fp] in HC.
  destruct (sym_read segs ss (facts_of (s_know ss)) scr_nil (SA b k) 8 false) as [[[[v scs] scr'] nx]|] eqn:HS; [|discriminate].
  destruct v as [| vj | | | | | |]; try discriminate. destruct scs; [|discriminate].
  apply andb_prop in HC as [HC H3]. apply andb_prop in HC as [H1 H2]. apply Nat.eqb_eq in H1. subst vj.
  destruct j as [|j].
  - destruct (sym_read_sound segs E base ss scr_nil (SA b k) 8 false _ [] scr' nx HS ltac:(constructor) HLF HK ltac:(lia) ltac:(lia))
      as (Hfl & bs & Hrd & Hlen & Hval).
    rewrite Nat.add_0_r. replace (k + 8 * Z.of_nat 0) with k by lia. rewrite <- adenot_SA. rewrite Hrd. f_equal.
    symmetry. apply le8_of_rdn_val; [exact Hlen|]. cbn [extz] in Hval. rewrite Hval. cbn [edenot]. rewrite (HFP i) by lia.
    unfold fle8. reflexivity.
  - replace (k + 8 * Z.of_nat (S j)) with ((k + 8) + 8 * Z.of_nat j) by lia. replace (i + S j)%nat with (S i + j)%nat by lia.
    apply (IH (k + 8) (S i)); try assumption; lia.
Qed.

Theorem node_fld_sound : forall fc W RW ss ss' E m0 base ms,
  wf_W W = true -> wf_W RW = true ->
  node_fld segs FLDPC ss = Some ss' -> CIX fc E W RW m0 base ss ms -> node_ok fc ss ss' E W RW m0 base ms.
Proof.
  intros fc W RW ss ss' E m0 base ms HW HRW Hn [Hnx HC]. unfold node_fld in Hn.
  destruct (split_lit (sr_get (s_regs ss) (Z_to_bv 5 10))) as [db dk] eqn:Hsp.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate] end. injection Hn as <-.
  apply andb_prop in Hg as [Hg H3]. apply andb_prop in Hg as [H1 H2]. apply Z.eqb_eq in H1.
  destruct (HC E (eagree_refl _ _)) as (R & F & Hms & HR & HLF & HK & HFR & HFP & HMI & HWM & HB & HLW & HRD).
  pose proof (facts_of_ok segs E base _ HK) as HFK.
  assert (A0 : bv_unsigned (reg_get R (Z_to_bv 5 10)) = bv_unsigned (edenot E db) + dk).
  { change (reg_get R (Z_to_bv 5 10)) with (getr R (Z_to_bv 5 10)). rewrite (HR (Z_to_bv 5 10)). eapply dst_val; [exact Hsp| exact HFK| exact H2| lia]. }
  pose proof (range_flat_sound E base _ db dk 512 HFK H2) as (F1 & _ & F3).
  assert (RD : forall i : nat, (i < 32)%nat ->
            rdn segs (mem_denot E base (s_log ss)) (Z_to_bv 64 (bv_unsigned (reg_get R (Z_to_bv 5 10)) + 256 + 8 * Z.of_nat i)) 8 = Some (fle8 F i)).
  { intros i Hi. rewrite A0. replace (bv_unsigned (edenot E db) + dk + 256 + 8 * Z.of_nat i) with (bv_unsigned (edenot E db) + ((dk + 256) + 8 * Z.of_nat i)) by lia.
    apply (check_fp_sound E F base ss db (dk + 256) 0 32 H3 HLF HK HFP ltac:(lia) i Hi). }
  pose proof (Hfld R F fc (mem_denot E base (s_log ss)) HFR ltac:(unfold two64 in F3; lia) RD) as EV.
  rewrite <- H1, <- Hms in EV. destruct EV as (ms' & HMS & F' & Hms' & HF').
  exists E, base, ms'. split; [apply eagree_refl|]. split; [cbn; lia|]. split; [exact HMS|].
  split; [cbn; exact Hnx|]. intros E' HA. cbn [s_next] in HA.
  destruct (CI_same_ms E E' W RW m0 base ss ms R F fc Hms (HC E' HA)) as (HR' & HLF' & HK' & HFP' & EM & HB' & HRD').
  exists R, F'. cbn [s_pc s_regs s_log s_know s_next].
  split; [rewrite EM, <- H1; exact Hms'|]. split; [exact HR'|]. split; [exact HLF'|]. split; [exact HK'|]. split; [exact HFR|].
  split; [intros i Hi; rewrite (HF' _); apply HFP'; exact Hi|].
  rewrite Hms'. cbn [ms_mem]. rewrite Hms in HMI, HWM, HRD'. cbn [ms_mem] in HMI, HWM, HRD'.
  split; [exact HMI|]. split; [exact HWM|]. split; [exact HB'|]. split; [exact HLW| exact HRD'].
Qed.

Lemma store_ok_wmono : forall M M' (a : word) (m : nat),
  (bv_unsigned a + Z.of_nat m <= 2 ^ 64)%Z ->
  store_ok segs M a m = true -> wmono segs M M' -> store_ok segs M' a m = true.
Proof.
  intros M M' a m Hnw Hs HW. apply StoreOk.store_ok_of_all; [exact Hnw|].
  intros x Hx. replace x with (wa (bv_unsigned a + Z.of_nat (Z.to_nat (bv_unsigned x - bv_unsigned a)))).
  - apply HW. eapply store_ok_wview; [exact Hs| lia].
  - unfold wa. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. pose proof (u64_range x). unfold bv_modulus. lia.
Qed.

Lemma kkeep_sound : forall E M M' fk b k n K,
  know_ok segs E M fk -> kentry_ok segs E M K -> kkeep fk b k n K = true ->
  0 < n -> n < two64 ->
  (forall x : word, ~ (bv_unsigned (edenot E b) + k <= bv_unsigned x < bv_unsigned (edenot E b) + k + n) -> M' x = M x) ->
  wmono segs M M' ->
  kentry_ok segs E M' K.
Proof.
  intros E M M' fk b k n K HFK HK Hkp Hn0 Hn1 HM HW.
  assert (EN : elenZ E (ELit n) = n) by (rewrite elenZ_lit; apply Z.mod_small; unfold two64 in Hn1; lia).
  assert (ESB : estart E (SA b k) = bv_unsigned (edenot E b) + k) by reflexivity.
  assert (APART : forall kb kk len, ranges_apart_x fk kb kk len b k (ELit n) = true ->
            estart E (SA kb kk) + elenZ E len <= bv_unsigned (edenot E b) + k \/ bv_unsigned (edenot E b) + k + n <= estart E (SA kb kk)).
  { intros kb kk len H. pose proof (ranges_apart_x_sound segs E M fk kb kk len b k (ELit n) HFK H) as X. rewrite EN, ESB in X. exact X. }
  assert (PT : forall (a : saddr) (len : expr) i, flat E a (elenZ E len) -> 0 <= i < elenZ E len ->
            (estart E a + elenZ E len <= bv_unsigned (edenot E b) + k \/ bv_unsigned (edenot E b) + k + n <= estart E a) ->
            M' (Z_to_bv 64 (estart E a + i)) = M (Z_to_bv 64 (estart E a + i))).
  { intros a len i Hfl Hi Hap. apply HM. rewrite u_small; [lia|]. destruct Hfl as (?&?&?&?). lia. }
  destruct K as [[kb kk] w v | [kb kk] len | [kb kk] len j | lo hi | e m | e lo hi | a len | a1 n1 a2 n2 | [kb kk] len c | [kb kk] len]; cbn [kkeep] in Hkp; cbn [kentry_ok] in HK |- *.
  -   destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite <- Hrd. pose proof (APART _ _ _ Hkp) as X. rewrite elenZ_elen in X by exact Hw.
    pose proof (flat_u E _ _ Hfl) as EU. destruct Hfl as (F1 & F2 & F3 & F4).
    apply rdn_ext; [rewrite EU; lia|]. intros x Hx. apply HM. rewrite EU in Hx. lia.
  -   destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (PT _ _ i Hfl Hi (APART _ _ _ Hkp)). apply Hz. exact Hi.
  -   destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi. rewrite (PT _ _ i Hfl Hi (APART _ _ _ Hkp)). apply Hz. exact Hi.
  -   destruct HK as (H0 & H1 & Hz). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite HM; [apply Hz; exact Hi|]. rewrite u_small by lia.
    apply orb_prop in Hkp. destruct Hkp as [Hkp|Hkp].
    + destruct (base_range fk b) as [[blo bhi]|] eqn:Hbr; [|discriminate].
      pose proof (base_range_sound segs E M fk b blo bhi HFK Hbr) as [A B].
      apply orb_prop in Hkp. destruct Hkp as [Hkp|Hkp]; apply Z.leb_le in Hkp; lia.
    + apply andb_prop in Hkp as [Hkp Hap]. apply andb_prop in Hkp as [Hkp Hw]. apply andb_prop in Hkp as [Hlo Hlh].
      apply Z.leb_le in Hlo. apply Z.ltb_lt in Hlh. apply Z.ltb_lt in Hw.
      pose proof (APART _ _ _ Hap) as X. unfold estart in X. cbn [a_base a_off edenot] in X.
      rewrite u_lit64, elenZ_lit in X. unfold two64 in *. rewrite (Z.mod_small 0), (Z.mod_small (hi - lo)) in X by lia. lia.
  - exact HK.
  - exact HK.
  -   destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd Hdm.
    pose proof (flat_u E _ _ Hfl) as EU. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|].
    apply (store_ok_wmono M M'); [rewrite u_small; lia| apply Hs; assumption| exact HW].
  - exact HK.
  -   destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (PT _ _ i Hfl Hi (APART _ _ _ Hkp)). apply Hz. exact Hi.
  -   destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (PT _ _ i Hfl Hi (APART _ _ _ Hkp)). apply Hz. exact Hi.
Qed.

Lemma kkeep_filter_sound : forall E M M' kn b k n,
  know_ok segs E M kn ->
  0 < n -> n < two64 ->
  (forall x : word, ~ (bv_unsigned (edenot E b) + k <= bv_unsigned x < bv_unsigned (edenot E b) + k + n) -> M' x = M x) ->
  wmono segs M M' ->
  know_ok segs E M' (List.filter (kkeep (facts_of kn) b k n) kn).
Proof.
  intros E M M' kn b k n HK Hn0 Hn1 HM HW. pose proof (facts_of_ok segs E M kn HK) as HFK.
  unfold know_ok in *. rewrite Forall_forall in HK |- *. intros K HIn. apply List.filter_In in HIn as [HIn Hkp].
  eapply kkeep_sound; eauto.
Qed.

Lemma kwr_find_sound : forall E M kn b k n,
  know_ok segs E M kn -> kwr_find kn b k n = true -> 0 <= n ->
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + n <= 2 ^ 64 ->
  wr_at segs M (bv_unsigned (edenot E b) + k) n.
Proof.
  intros E M kn b k n HK Hf Hn Hlo Hhi. split; [exact Hlo|]. split; [exact Hhi|].
  revert Hf. induction kn as [|K rest IH]; cbn [kwr_find]; intros Hf; [discriminate|].
  apply Forall_cons_iff in HK as [HK1 HK]. specialize (IH HK).
  destruct K as [| | | | | |[kb kk] [len| | | | | | |]| | |]; try (apply IH; exact Hf).
  apply orb_prop in Hf. destruct Hf as [Hf|Hf]; [| apply IH; exact Hf].
  apply andb_prop in Hf as [Hf H5]. apply andb_prop in Hf as [Hf H4]. apply andb_prop in Hf as [Hf H3]. apply andb_prop in Hf as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5. subst kb.
  cbn [kentry_ok] in HK1. destruct HK1 as [Hfl Hs]. rewrite elenZ_lit in Hfl, Hs. unfold two64 in H5. rewrite (Z.mod_small len) in Hfl, Hs by lia.
  pose proof (flat_u E _ _ Hfl) as EU. destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
  intros i Hi.
  specialize (Hs (k + i - kk) 1%nat ltac:(lia) ltac:(lia)).
  pose proof (store_ok_wview segs M _ 1 0 Hs ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite Z.add_0_r in X.
  rewrite u_small in X by lia. unfold wa in X |- *.
  replace (bv_unsigned (edenot E b) + k + i) with (bv_unsigned (edenot E b) + kk + (k + i - kk)) by lia. exact X.
Qed.

Lemma in_W_Wd : forall E W b lo hi x,
  in_W W b lo hi = true -> bv_unsigned (edenot E b) + lo <= bv_unsigned x < bv_unsigned (edenot E b) + hi -> Wd E W x.
Proof.
  intros E W b lo hi x H Hx. destruct (in_W_In _ _ _ _ H) as (wb & wlo & whi & HIn & -> & A & B).
  exists wb, wlo, whi. split; [exact HIn|]. lia.
Qed.

Lemma kfp_ok : forall E F M b k i cnt,
  (i + cnt <= 32)%nat -> fp_ok E F ->
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + 8 * Z.of_nat cnt <= 2 ^ 64 ->
  (forall j, (j < cnt)%nat -> rdn segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + k + 8 * Z.of_nat j)) 8 = Some (fle8 F (i + j))) ->
  know_ok segs E M (kfp b k i cnt).
Proof.
  intros E F M b k i cnt. revert k i. induction cnt as [|c IH]; intros k i Hic HFP Hlo Hhi Hrd; [constructor|].
  cbn [kfp]. constructor.
  - cbn [kentry_ok]. split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off]; lia|].
    rewrite adenot_SA. specialize (Hrd 0%nat ltac:(lia)). rewrite Z.mul_0_r, Z.add_0_r, Nat.add_0_r in Hrd. rewrite Hrd.
    f_equal. unfold fle8. cbn [edenot]. rewrite (HFP i) by lia. reflexivity.
  - apply (IH (k + 8) (S i)); [lia| exact HFP| lia| lia|].
    intros j Hj. replace (bv_unsigned (edenot E b) + (k + 8) + 8 * Z.of_nat j) with (bv_unsigned (edenot E b) + k + 8 * Z.of_nat (S j)) by lia.
    replace (S i + j)%nat with (i + S j)%nat by lia. apply Hrd. lia.
Qed.

Theorem node_fsd_sound : forall fc W RW ss ss' E m0 base ms,
  wf_W W = true -> wf_W RW = true ->
  node_fsd W RW FSDPC ss = Some ss' -> CIX fc E W RW m0 base ss ms -> node_ok fc ss ss' E W RW m0 base ms.
Proof.
  intros fc W RW ss ss' E m0 base ms HW HRW Hn [Hnx HC]. unfold node_fsd in Hn.
  destruct (split_lit (sr_get (s_regs ss) (Z_to_bv 5 10))) as [db dk] eqn:Hsp.
  destruct (s_log ss) eqn:HL; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate] end. injection Hn as <-.
  apply andb_prop in Hg as [Hg H5]. apply andb_prop in Hg as [Hg H4]. apply andb_prop in Hg as [Hg H3]. apply andb_prop in Hg as [H1 H2]. apply Z.eqb_eq in H1.

  assert (GEO : forall E', eagree (s_next ss) E E' -> forall R F, ms = MS R F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom ->
            bv_unsigned (reg_get R (Z_to_bv 5 10)) = bv_unsigned (edenot E' db) + dk
            /\ 0 <= bv_unsigned (edenot E' db) + dk /\ bv_unsigned (edenot E' db) + dk + 512 <= 2 ^ 64).
  { intros E' HA R F Hms. destruct (CI_same_ms E E' W RW m0 base ss ms R F fc Hms (HC E' HA)) as (HR' & _ & HK' & _).
    pose proof (facts_of_ok segs E' base _ HK') as HFK'.
    pose proof (range_flat_sound E' base _ db dk 512 HFK' H2) as (F1 & _ & F3). unfold two64 in F3.
    split; [| lia]. change (reg_get R (Z_to_bv 5 10)) with (getr R (Z_to_bv 5 10)). rewrite (HR' (Z_to_bv 5 10)).
    eapply dst_val; [exact Hsp| exact HFK'| exact H2| lia]. }
  destruct (HC E (eagree_refl _ _)) as (R & F & Hms & HR & HLF & HK & HFR & HFP & HMI & HWM & HB & HLW & HRD).
  rewrite HL in Hms. cbn [mem_denot] in Hms.
  destruct (GEO E (eagree_refl _ _) R F ltac:(rewrite HL; exact Hms)) as (A0 & F1 & F3).
  rewrite Hms in HMI, HWM, HRD. unfold MS in HMI, HWM, HRD. cbn [ms_mem] in HMI, HWM, HRD.
  destruct (defined_bytes base (bv_unsigned (edenot E db) + (dk + 256)) 256%nat ltac:(lia) ltac:(lia)) as (junk & Hjl & Hjb).
  { intros x Hx. apply (proj1 (HRD x ltac:(eapply in_W_Wd; [exact H5| lia]))). }
  assert (RWC : rw_cells segs base (bv_unsigned (reg_get R (Z_to_bv 5 10)) + 256) [CB 256 junk]).
  { rewrite A0. replace (bv_unsigned (edenot E db) + dk + 256) with (bv_unsigned (edenot E db) + (dk + 256)) by lia.
    apply rw_cells_CB; [exact Hjl| exact Hjb|]. eapply kwr_find_sound; [exact HK| exact H3| lia| lia| lia]. }
  pose proof (Hfsd R F fc base junk HFR RWC ltac:(lia) HMI) as EV. rewrite <- H1, <- Hms in EV.
  destruct EV as (ms' & HMS & m' & Hms' & HMU & HWM' & HMI' & HRDF).
  exists E, m', ms'. split; [apply eagree_refl|]. split; [cbn; lia|]. split; [exact HMS|].
  split; [cbn; exact Hnx|]. intros E' HA. cbn [s_next] in HA.
  destruct (CI_same_ms E E' W RW m0 base ss ms R F fc ltac:(rewrite HL; exact Hms) (HC E' HA)) as (HR' & HLF' & HK' & HFP' & EM & HB' & HRD').
  destruct (GEO E' HA R F ltac:(rewrite HL; exact Hms)) as (A0' & F1' & F3').
  assert (OUT : forall x : word, ~ (bv_unsigned (edenot E' db) + (dk + 256) <= bv_unsigned x < bv_unsigned (edenot E' db) + (dk + 256) + 256) -> m' x = base x).
  { intros x Hx. apply HMU. cbn [outside]. split; [| exact I]. rewrite A0'. lia. }
  assert (KF : know_ok segs E' m' (kfp db (dk + 256) 0 32)).
  { apply (kfp_ok E' F m' db (dk + 256) 0 32); [lia| exact HFP'| lia| lia|].
    intros j Hj. cbn [Nat.add]. rewrite <- (HRDF j Hj). f_equal. f_equal. rewrite A0'. lia. }
  assert (KK : know_ok segs E' m' (List.filter (kkeep (facts_of (s_know ss)) db (dk + 256) 256) (s_know ss))).
  { eapply kkeep_filter_sound; [exact HK'| lia| unfold two64; lia| exact OUT| exact HWM']. }
  assert (KA : know_ok segs E' m' (kfp db (dk + 256) 0 32 ++ List.filter (kkeep (facts_of (s_know ss)) db (dk + 256) 256) (s_know ss))).
  { unfold know_ok. apply Forall_app. split; [exact KF| exact KK]. }
  exists R, F. cbn [s_pc s_regs s_log s_know s_next mem_denot].
  split; [rewrite <- H1; exact Hms'|]. split; [exact HR'|]. split; [exact I|].
  split; [exact KA|].
  split; [exact HFR|]. split; [exact HFP'|].
  rewrite Hms'. cbn [ms_mem]. split; [exact HMI'|]. split; [eapply wmono_trans; [exact HWM| exact HWM']|].
  split. { intros x Hx. rewrite OUT; [apply HB'; exact Hx|]. intros HIN. apply Hx. eapply in_W_Wd; [exact H4| lia]. }
  split; [reflexivity|].
  rewrite Hms in HRD'. cbn [ms_mem] in HRD'.
  intros x Hx. destruct (HRD' x Hx) as [D1 D2]. split; [| exact D2].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E' db) + (dk + 256))) as [L|L]; [rewrite OUT by lia; exact D1|].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E' db) + (dk + 256) + 256)) as [L2|L2]; [| rewrite OUT by lia; exact D1].

  set (j := Z.to_nat ((bv_unsigned x - (bv_unsigned (edenot E' db) + (dk + 256))) / 8)).
  assert (Hj : (j < 32)%nat) by (subst j; apply Nat2Z.inj_lt; rewrite Z2Nat.id; [apply Z.div_lt_upper_bound|apply Z.div_pos]; lia).
  pose proof (HRDF j Hj) as RD. rewrite A0' in RD.
  destruct (rdn_defined_at segs m' _ 8 _ RD x) as [b Hb].
  { rewrite u_small; [| lia]. subst j. rewrite Z2Nat.id by (apply Z.div_pos; lia).
    pose proof (Z.mul_div_le (bv_unsigned x - (bv_unsigned (edenot E' db) + (dk + 256))) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned x - (bv_unsigned (edenot E' db) + (dk + 256))) 8 ltac:(lia)).
    rewrite Z.mod_eq in H0 by lia. lia. }
  intros Hn. unfold MS in Hn. cbn [ms_mem] in Hn. unfold mrd in Hb. rewrite Hn in Hb.
  assert (X : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Common.PropExec.seg_rom segs x = None) by exact D2.
  rewrite X in Hb. discriminate Hb.
Qed.

Lemma getr_lit : forall E sr R r z, regs_ok E sr R -> sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z.
Proof. intros E sr R r z HR Hs. rewrite (HR r), Hs. reflexivity. Qed.

Lemma bytes_at_defined : forall (m : word -> option byte) A bs (x : word),
  bytes_at segs m A bs -> OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS.PropExec.seg_rom segs x = None ->
  A <= bv_unsigned x < A + Z.of_nat (length bs) -> m x <> None.
Proof.
  intros m A bs x (HA & Hl & HB) Hrom Hx Hn.
  specialize (HB (Z.to_nat (bv_unsigned x - A)) ltac:(lia)).
  replace (wa (A + Z.of_nat (Z.to_nat (bv_unsigned x - A)))) with x in HB.
  2:{ unfold wa. apply bv_eq. rewrite u_small; [lia|]. pose proof (u64_range x). lia. }
  unfold mrd in HB. rewrite Hn in HB.
  assert (X : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Common.PropExec.seg_rom segs x = None) by exact Hrom.
  rewrite X in HB. symmetry in HB. apply nth_error_None in HB. lia.
Qed.

Theorem node_set_sound : forall fc W RW ss ss' E m0 base ms,
  wf_W W = true -> wf_W RW = true ->
  node_set W RW SETPC ss = Some ss' -> CIX fc E W RW m0 base ss ms -> node_ok fc ss ss' E W RW m0 base ms.
Proof.
  intros fc W RW ss ss' E m0 base ms HW HRW Hn [Hnx HC]. unfold node_set in Hn.
  destruct (call_gate W RW SETPC ss) as [[[[ra db] dk] n]|] eqn:Hg; [|discriminate].
  destruct (sr_get (s_regs ss) (Z_to_bv 5 11)) as [c| | | | | | |] eqn:H11; try discriminate.
  destruct c as [|p|p]; try discriminate. injection Hn as <-.
  destruct (call_gate_sound W RW SETPC ss ra db dk n Hg) as (HL & HPC & H1 & H12 & Hsp & Hra & Hra4 & Hnn & Hrf & Hkw & HiW & HiRW).

  assert (GEO : forall E', eagree (s_next ss) E E' -> forall R F, ms = MS R F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom ->
            bv_unsigned (reg_get R (Z_to_bv 5 10)) = bv_unsigned (edenot E' db) + dk
            /\ 0 <= bv_unsigned (edenot E' db) + dk /\ bv_unsigned (edenot E' db) + dk + n <= 2 ^ 64
            /\ reg_get R (Z_to_bv 5 12) = Z_to_bv 64 n /\ reg_get R (Z_to_bv 5 11) = Z_to_bv 64 0 /\ reg_get R (Z_to_bv 5 1) = Z_to_bv 64 ra).
  { intros E' HA R F Hms. destruct (CI_same_ms E E' W RW m0 base ss ms R F fc Hms (HC E' HA)) as (HR' & _ & HK' & _).
    pose proof (facts_of_ok segs E' base _ HK') as HFK'.
    pose proof (range_flat_sound E' base _ db dk n HFK' Hrf) as (F1 & _ & F3). unfold two64 in F3.
    split. { change (reg_get R (Z_to_bv 5 10)) with (getr R (Z_to_bv 5 10)). rewrite (HR' (Z_to_bv 5 10)). eapply dst_val; [exact Hsp| exact HFK'| exact Hrf| lia]. }
    split; [lia|]. split; [lia|].
    split; [exact (getr_lit E' _ R _ _ HR' H12)|]. split; [exact (getr_lit E' _ R _ _ HR' H11)| exact (getr_lit E' _ R _ _ HR' H1)]. }
  destruct (HC E (eagree_refl _ _)) as (R & F & Hms & HR & HLF & HK & HFR & HFP & HMI & HWM & HB & HLW & HRD).
  destruct (GEO E (eagree_refl _ _) R F Hms) as (A0 & F1 & F3 & A2 & A1 & Ara).
  rewrite HL in Hms. cbn [mem_denot] in Hms. rewrite Hms in HMI, HWM, HRD. unfold MS in HMI, HWM, HRD. cbn [ms_mem] in HMI, HWM, HRD.

  destruct (defined_bytes base (bv_unsigned (edenot E db) + dk) (Z.to_nat n) ltac:(lia) ltac:(lia)) as (junk & Hjl & Hjb).
  { intros x Hx. apply (proj1 (HRD x ltac:(eapply in_W_Wd; [exact HiRW| lia]))). }
  assert (RWC : rw_cells segs base (bv_unsigned (reg_get R (Z_to_bv 5 10))) [CB (Z.to_nat (bv_unsigned (reg_get R (Z_to_bv 5 12)))) junk]).
  { rewrite A0, A2. rewrite u_small by lia. apply rw_cells_CB; [exact Hjl| exact Hjb|]. rewrite Z2Nat.id by lia.
    eapply kwr_find_sound; [exact HK| exact Hkw| lia| lia| lia]. }
  destruct HFR as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
                   x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ER). subst R.
  pose proof (Hset x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc base junk RWC HMI) as EV.
  rewrite <- HPC in EV. rewrite <- Hms in EV.
  destruct EV as (ms' & HMS & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms' & HMU & HWM' & HMI' & HRW').
  set (vals := [t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6']).
  exists (eupds E (s_next ss) vals), m', ms'.
  split; [apply eupds_agree|]. split; [cbn [s_next]; lia|]. split; [exact HMS|].
  unfold El_xs_core.CIX. split; [cbn [s_next] in *; lia|]. intros E'' HA''. cbn [s_next] in HA''.
  assert (HAE : eagree (s_next ss) E E'').
  { eapply eagree_trans; [apply (eupds_agree vals)|]. eapply eagree_le; [exact HA''| lia]. }
  destruct (CI_same_ms E E'' W RW m0 base ss ms _ F fc ltac:(rewrite HL; exact Hms) (HC E'' HAE)) as (HR'' & HLF'' & HK'' & HFP'' & EM & HB'' & HRD'').
  destruct (GEO E'' HAE _ F ltac:(rewrite HL; exact Hms)) as (A0'' & F1'' & F3'' & _).
  destruct (reg_get_mkR_1_10_11_12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as (G1 & G10 & G11 & G12).
  rewrite G10 in A0, A0''. rewrite G12 in A2. rewrite G11 in A1. rewrite G1 in Ara.
  assert (OUT : forall x : word, ~ (bv_unsigned (edenot E'' db) + dk <= bv_unsigned x < bv_unsigned (edenot E'' db) + dk + n) -> m' x = base x).
  { intros x Hx. apply HMU. cbn [outside]. split; [| exact I]. rewrite A0'', A2. rewrite u_small by lia. lia. }
  assert (KZ : know_ok segs E'' m' (kzeros db dk n)).
  { apply kzeros_ok; [lia| lia| lia|].
    destruct HRW' as [[_ HBm] _]. cbn [cells_bytes cbytes] in HBm. rewrite app_nil_r in HBm.
    rewrite A0'', A2, A1 in HBm. rewrite !u_small in HBm by lia.
    change (0 mod 256) with 0 in HBm. exact HBm. }
  assert (KK : know_ok segs E'' m' (List.filter (kkeep (facts_of (s_know ss)) db dk n) (s_know ss))).
  { eapply kkeep_filter_sound; [exact HK''| lia| unfold two64; lia| exact OUT| exact HWM']. }
  assert (KA : know_ok segs E'' m' (kzeros db dk n ++ List.filter (kkeep (facts_of (s_know ss)) db dk n) (s_know ss))).
  { unfold know_ok. apply Forall_app. split; [exact KZ| exact KK]. }
  assert (RO : regs_ok E'' (havoc_regs (s_regs ss) CLOB (s_next ss))
               (mkR x1 x2 x3 x4 t0' t1' t2' x8 x9 x10 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')).
  { rewrite <- (regupds_CLOB x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
    apply havoc_regs_ok; [exact HR''| reflexivity| apply CLOB_range|].
    intros j Hj. pose proof (proj1 HA'' (s_next ss + j)%nat ltac:(cbn in Hj; lia)) as X. rewrite <- X. apply eupds_at. exact Hj. }
  exists (mkR x1 x2 x3 x4 t0' t1' t2' x8 x9 x10 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6'), F.
  cbn [s_pc s_regs s_log s_know s_next mem_denot].
  split. { rewrite Hms'. rewrite Ara. pose proof (mod4_mod2 ra Hra4) as M2.
           rewrite ret_pc_even by (unfold two64 in Hra; lia). unfold retZ.
           replace (ra - ra mod 2) with ra by lia. reflexivity. }
  split; [exact RO|]. split; [exact I|]. split; [exact KA|]. split; [apply fullR_mkR|]. split; [exact HFP''|].
  rewrite Hms'. unfold MS. cbn [ms_mem].
  split; [exact HMI'|]. split; [eapply wmono_trans; [exact HWM| exact HWM']|].
  split. { intros x Hx. rewrite OUT; [apply HB''; exact Hx|]. intros HIN. apply Hx. eapply in_W_Wd; [exact HiW| lia]. }
  split; [reflexivity|].
  intros x Hx. destruct (HRD'' x Hx) as [D1 D2]. rewrite Hms in D1. unfold MS in D1. cbn [ms_mem] in D1. split; [| exact D2].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E'' db) + dk)) as [L|L]; [rewrite OUT by lia; exact D1|].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E'' db) + dk + n)) as [L2|L2]; [| rewrite OUT by lia; exact D1].
  destruct HRW' as [[_ HBm] _]. cbn [cells_bytes cbytes] in HBm. rewrite app_nil_r in HBm.
  rewrite A0'', A2 in HBm. rewrite !u_small in HBm by lia.
  eapply bytes_at_defined; [exact HBm| exact D2|]. rewrite repeat_length. lia.
Qed.

Lemma read_words_sound : forall E base ss sb sk cnt vs,
  read_words segs ss (facts_of (s_know ss)) sb sk cnt = Some vs ->
  log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  length vs = cnt /\
  forall j, (j < cnt)%nat -> exists bs,
    rdn segs (mem_denot E base (s_log ss)) (Z_to_bv 64 (bv_unsigned (edenot E sb) + (sk + 8 * Z.of_nat j))) 8 = Some bs
    /\ length bs = 8%nat /\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E (nth j vs (ELit 0)).
Proof.
  intros E base ss sb sk cnt. revert sk. induction cnt as [|c IH]; intros sk vs HR HLF HK.
  - cbn in HR. injection HR as <-. split; [reflexivity|]. intros j Hj. lia.
  - cbn [read_words] in HR.
    destruct (sym_read segs ss (facts_of (s_know ss)) scr_nil (SA sb sk) 8 false) as [[[[v scs] scr'] nx]|] eqn:HS; [|discriminate].
    destruct scs; [|discriminate]. destruct (Nat.eqb nx (s_next ss)); [|discriminate].
    destruct (read_words segs ss (facts_of (s_know ss)) sb (sk + 8) c) as [vs'|] eqn:HR'; [|discriminate]. injection HR as <-.
    destruct (IH (sk + 8) vs' HR' HLF HK) as [Hlen Hrd].
    split; [cbn; lia|]. intros j Hj. destruct j as [|j].
    + destruct (sym_read_sound segs E base ss scr_nil (SA sb sk) 8 false _ [] scr' nx HS ltac:(constructor) HLF HK ltac:(lia) ltac:(lia))
        as (Hfl & bs & Hrd0 & Hl0 & Hv0).
      exists bs. replace (sk + 8 * Z.of_nat 0) with sk by lia. rewrite <- adenot_SA. split; [exact Hrd0|]. split; [exact Hl0|]. cbn [extz] in Hv0. cbn [nth]. exact Hv0.
    + destruct (Hrd j ltac:(lia)) as (bs & A & B & C). exists bs.
      replace (sk + 8 * Z.of_nat (S j)) with (sk + 8 + 8 * Z.of_nat j) by lia. cbn [nth]. split; [exact A|]. split; [exact B| exact C].
Qed.

Lemma readable_bytes : forall (m : word -> option byte) A n,
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, A <= bv_unsigned x < A + Z.of_nat n -> exists b, mrd segs m x = Some b) ->
  exists bs, length bs = n /\ bytes_at segs m A bs.
Proof.
  intros m A n HA Hn HD.
  exists (map (fun i => match mrd segs m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
  split; [rewrite length_map, length_seq; reflexivity|].
  split; [exact HA|]. split; [rewrite length_map, length_seq; exact Hn|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite nth_error_map, nth_error_seq. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). cbn [option_map Nat.add].
  destruct (HD (wa (A + Z.of_nat i))) as [b Hb]; [unfold wa; rewrite u_small; lia|]. rewrite Hb. reflexivity.
Qed.

Lemma kwords8_ok : forall E M b k vs,
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + 8 * Z.of_nat (length vs) <= 2 ^ 64 ->
  (forall j, (j < length vs)%nat -> rdn segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + k + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 (edenot E (nth j vs (ELit 0))))) ->
  know_ok segs E M (kwords8 b k vs).
Proof.
  intros E M b k vs. revert k. induction vs as [|v vs IH]; intros k Hlo Hhi Hrd; [constructor|].
  cbn [length] in Hhi, Hrd. cbn [kwords8]. constructor.
  - cbn [kentry_ok]. split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off]; lia|].
    rewrite adenot_SA. specialize (Hrd 0%nat ltac:(lia)). rewrite Z.mul_0_r, Z.add_0_r in Hrd. exact Hrd.
  - apply (IH (k + 8)); [lia| lia|]. intros j Hj.
    replace (bv_unsigned (edenot E b) + (k + 8) + 8 * Z.of_nat j) with (bv_unsigned (edenot E b) + k + 8 * Z.of_nat (S j)) by lia.
    apply (Hrd (S j)). lia.
Qed.

Theorem node_cpy_sound : forall fc W RW ss ss' E m0 base ms,
  wf_W W = true -> wf_W RW = true ->
  node_cpy segs W RW CPYPC ss = Some ss' -> CIX fc E W RW m0 base ss ms -> node_ok fc ss ss' E W RW m0 base ms.
Proof.
  intros fc W RW ss ss' E m0 base ms HW HRW Hn [Hnx HC]. unfold node_cpy in Hn.
  destruct (call_gate W RW CPYPC ss) as [[[[ra db] dk] n]|] eqn:Hg; [|discriminate].
  destruct (split_lit (sr_get (s_regs ss) (Z_to_bv 5 11))) as [sb sk] eqn:Hsp1.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hap]. apply andb_prop in Hc as [Hm8 Hrf1]. apply Z.eqb_eq in Hm8.
  destruct (read_words segs ss (facts_of (s_know ss)) sb sk (Z.to_nat (n / 8))) as [vs|] eqn:HRDW; [|discriminate]. injection Hn as <-.
  destruct (call_gate_sound W RW CPYPC ss ra db dk n Hg) as (HL & HPC & H1 & H12 & Hsp & Hra & Hra4 & Hnn & Hrf & Hkw & HiW & HiRW).
  pose proof (Z.div_mod n 8 ltac:(lia)) as DM. rewrite Hm8, Z.add_0_r in DM.

  assert (GEO : forall E', eagree (s_next ss) E E' -> forall R F, ms = MS R F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom ->
            bv_unsigned (reg_get R (Z_to_bv 5 10)) = bv_unsigned (edenot E' db) + dk
            /\ 0 <= bv_unsigned (edenot E' db) + dk /\ bv_unsigned (edenot E' db) + dk + n <= 2 ^ 64
            /\ bv_unsigned (reg_get R (Z_to_bv 5 11)) = bv_unsigned (edenot E' sb) + sk
            /\ 0 <= bv_unsigned (edenot E' sb) + sk /\ bv_unsigned (edenot E' sb) + sk + n <= 2 ^ 64
            /\ (bv_unsigned (edenot E' db) + dk + n <= bv_unsigned (edenot E' sb) + sk \/ bv_unsigned (edenot E' sb) + sk + n <= bv_unsigned (edenot E' db) + dk)
            /\ reg_get R (Z_to_bv 5 12) = Z_to_bv 64 n /\ reg_get R (Z_to_bv 5 1) = Z_to_bv 64 ra
            /\ (length vs = Z.to_nat (n / 8) /\ forall j, (j < Z.to_nat (n / 8))%nat -> exists bs,
                  rdn segs (mem_denot E' base (s_log ss)) (Z_to_bv 64 (bv_unsigned (edenot E' sb) + (sk + 8 * Z.of_nat j))) 8 = Some bs
                  /\ length bs = 8%nat /\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E' (nth j vs (ELit 0)))).
  { intros E' HA R F Hms. destruct (CI_same_ms E E' W RW m0 base ss ms R F fc Hms (HC E' HA)) as (HR' & HLF' & HK' & _).
    pose proof (facts_of_ok segs E' base _ HK') as HFK'.
    pose proof (range_flat_sound E' base _ db dk n HFK' Hrf) as (F1 & _ & F3). pose proof (range_flat_sound E' base _ sb sk n HFK' Hrf1) as (F1' & _ & F3'). unfold two64 in F3, F3'.
    split. { change (reg_get R (Z_to_bv 5 10)) with (getr R (Z_to_bv 5 10)). rewrite (HR' (Z_to_bv 5 10)). eapply dst_val; [exact Hsp| exact HFK'| exact Hrf| lia]. }
    split; [lia|]. split; [lia|].
    split. { change (reg_get R (Z_to_bv 5 11)) with (getr R (Z_to_bv 5 11)). rewrite (HR' (Z_to_bv 5 11)). eapply dst_val; [exact Hsp1| exact HFK'| exact Hrf1| lia]. }
    split; [lia|]. split; [lia|].
    split. { pose proof (ranges_apart_x_sound segs E' base _ db dk (ELit n) sb sk (ELit n) HFK' Hap) as X.
             rewrite !elenZ_lit in X. unfold estart in X. cbn [a_base a_off] in X. rewrite (Z.mod_small n) in X by lia. exact X. }
    split; [exact (getr_lit E' _ R _ _ HR' H12)|]. split; [exact (getr_lit E' _ R _ _ HR' H1)|].
    exact (read_words_sound E' base ss sb sk _ vs HRDW HLF' HK'). }
  destruct (HC E (eagree_refl _ _)) as (R & F & Hms & HR & HLF & HK & HFR & HFP & HMI & HWM & HB & HLW & HRD).
  destruct (GEO E (eagree_refl _ _) R F Hms) as (A0 & F1 & F3 & A1 & F1' & F3' & AP & A2 & Ara & Hlen & HRDS).
  rewrite HL in Hms, HRDS. cbn [mem_denot] in Hms, HRDS. rewrite Hms in HMI, HWM, HRD. unfold MS in HMI, HWM, HRD. cbn [ms_mem] in HMI, HWM, HRD.

  destruct (defined_bytes base (bv_unsigned (edenot E db) + dk) (Z.to_nat n) ltac:(lia) ltac:(lia)) as (junk & Hjl & Hjb).
  { intros x Hx. apply (proj1 (HRD x ltac:(eapply in_W_Wd; [exact HiRW| lia]))). }
  assert (RWC : rw_cells segs base (bv_unsigned (reg_get R (Z_to_bv 5 10))) [CB (Z.to_nat (bv_unsigned (reg_get R (Z_to_bv 5 12)))) junk]).
  { rewrite A0, A2. rewrite u_small by lia. apply rw_cells_CB; [exact Hjl| exact Hjb|]. rewrite Z2Nat.id by lia.
    eapply kwr_find_sound; [exact HK| exact Hkw| lia| lia| lia]. }

  destruct (readable_bytes base (bv_unsigned (edenot E sb) + sk) (Z.to_nat n) ltac:(lia) ltac:(lia)) as (src & Hsl & Hsb).
  { intros x Hx. set (j := Z.to_nat ((bv_unsigned x - (bv_unsigned (edenot E sb) + sk)) / 8)).
    assert (Hj : (j < Z.to_nat (n / 8))%nat).
    { subst j. apply Z2Nat.inj_lt; [apply Z.div_pos; lia| lia|]. apply Z.div_lt_upper_bound; [lia|]. lia. }
    destruct (HRDS j Hj) as (bs & Hbs & _ & _).
    apply (rdn_defined_at segs base _ 8 bs Hbs x). rewrite u_small; [| lia]. subst j. rewrite Z2Nat.id by (apply Z.div_pos; lia).
    pose proof (Z.mul_div_le (bv_unsigned x - (bv_unsigned (edenot E sb) + sk)) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned x - (bv_unsigned (edenot E sb) + sk)) 8 ltac:(lia)).
    rewrite Z.mod_eq in H0 by lia. lia. }
  destruct HFR as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
                   x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ER). subst R.
  destruct (reg_get_mkR_1_10_11_12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as (G1 & G10 & G11 & G12).
  rewrite G10 in A0, RWC. rewrite G12 in A2, RWC. rewrite G11 in A1. rewrite G1 in Ara.
  pose proof (Hcpy x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc base src junk) as EV.
  assert (U12 : bv_unsigned x12 = n) by (rewrite A2; apply u_small; lia).
  rewrite <- A1 in Hsb.
  specialize (EV Hsb ltac:(rewrite U12, Hsl; reflexivity) RWC ltac:(rewrite A1, A0, U12; lia) HMI).
  rewrite A1, A0, U12 in EV.
  rewrite <- HPC, <- Hms in EV.
  destruct EV as (ms' & HMS & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms' & HMU & HWM' & HMI' & HRW' & HSB').
  set (vals := [t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6']).
  exists (eupds E (s_next ss) vals), m', ms'.
  split; [apply eupds_agree|]. split; [cbn [s_next]; lia|]. split; [exact HMS|].
  unfold El_xs_core.CIX. split; [cbn [s_next] in *; lia|]. intros E'' HA''. cbn [s_next] in HA''.
  assert (HAE : eagree (s_next ss) E E'').
  { eapply eagree_trans; [apply (eupds_agree vals)|]. eapply eagree_le; [exact HA''| lia]. }
  destruct (CI_same_ms E E'' W RW m0 base ss ms _ F fc ltac:(rewrite HL; exact Hms) (HC E'' HAE)) as (HR'' & HLF'' & HK'' & HFP'' & EM & HB'' & HRD'').
  destruct (GEO E'' HAE _ F ltac:(rewrite HL; exact Hms)) as (A0'' & F1'' & F3'' & A1'' & F1x & F3x & AP'' & _ & _ & Hlen'' & HRDSj).
  rewrite G10 in A0''. rewrite G11 in A1''. rewrite HL in HRDSj. cbn [mem_denot] in HRDSj.
  assert (OUT : forall x : word, ~ (bv_unsigned (edenot E'' db) + dk <= bv_unsigned x < bv_unsigned (edenot E'' db) + dk + n) -> m' x = base x).
  { intros x Hx. apply HMU. cbn [outside]. split; [| exact I]. lia. }
  assert (KWD : know_ok segs E'' m' (kwords8 db dk vs)).
  { apply kwords8_ok; [lia| rewrite Hlen'', Z2Nat.id by lia; lia|].
    intros j Hj. rewrite Hlen'' in Hj.
    destruct HRW' as [[_ HBm] _]. cbn [cells_bytes cbytes] in HBm. rewrite app_nil_r in HBm. rewrite <- A0 in HBm.

    pose proof (bytes_at_rdn segs m' _ src (8 * j) 8 HBm ltac:(rewrite Hsl; lia)) as X. rewrite rdn_common in X. unfold wa in X.
    replace (bv_unsigned (edenot E'' db) + dk + 8 * Z.of_nat j) with (bv_unsigned x10 + Z.of_nat (8 * j)) by lia. rewrite X. f_equal.
    pose proof (bytes_at_rdn segs base _ src (8 * j) 8 Hsb ltac:(rewrite Hsl; lia)) as Y. rewrite rdn_common in Y. unfold wa in Y.
    destruct (HRDSj j Hj) as (bs & Hbs & Hbl & Hbv).
    replace (bv_unsigned (edenot E'' sb) + (sk + 8 * Z.of_nat j)) with (bv_unsigned x11 + Z.of_nat (8 * j)) in Hbs by lia.
    rewrite Y in Hbs. assert (EQ : firstn 8 (skipn (8 * j) src) = bs) by congruence. rewrite EQ. symmetry. apply le8_of_rdn_val; [exact Hbl| exact Hbv]. }
  assert (KK : know_ok segs E'' m' (List.filter (kkeep (facts_of (s_know ss)) db dk n) (s_know ss))).
  { eapply kkeep_filter_sound; [exact HK''| lia| unfold two64; lia| exact OUT| exact HWM']. }
  assert (KA : know_ok segs E'' m' (kwords8 db dk vs ++ List.filter (kkeep (facts_of (s_know ss)) db dk n) (s_know ss))).
  { unfold know_ok. apply Forall_app. split; [exact KWD| exact KK]. }
  assert (RO : regs_ok E'' (havoc_regs (s_regs ss) CLOB (s_next ss))
               (mkR x1 x2 x3 x4 t0' t1' t2' x8 x9 x10 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')).
  { rewrite <- (regupds_CLOB x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
    apply havoc_regs_ok; [exact HR''| reflexivity| apply CLOB_range|].
    intros j Hj. pose proof (proj1 HA'' (s_next ss + j)%nat ltac:(cbn in Hj; lia)) as X. rewrite <- X. apply eupds_at. exact Hj. }
  exists (mkR x1 x2 x3 x4 t0' t1' t2' x8 x9 x10 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6'), F.
  cbn [s_pc s_regs s_log s_know s_next mem_denot].
  split. { rewrite Hms'. rewrite Ara. pose proof (mod4_mod2 ra Hra4) as M2.
           rewrite ret_pc_even by (unfold two64 in Hra; lia). unfold retZ.
           replace (ra - ra mod 2) with ra by lia. reflexivity. }
  split; [exact RO|]. split; [exact I|]. split; [exact KA|]. split; [apply fullR_mkR|]. split; [exact HFP''|].
  rewrite Hms'. unfold MS. cbn [ms_mem].
  split; [exact HMI'|]. split; [eapply wmono_trans; [exact HWM| exact HWM']|].
  split. { intros x Hx. rewrite OUT; [apply HB''; exact Hx|]. intros HIN. apply Hx. eapply in_W_Wd; [exact HiW| lia]. }
  split; [reflexivity|].
  intros x Hx. destruct (HRD'' x Hx) as [D1 D2]. rewrite Hms in D1. unfold MS in D1. cbn [ms_mem] in D1. split; [| exact D2].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E'' db) + dk)) as [L|L]; [rewrite OUT by lia; exact D1|].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E'' db) + dk + n)) as [L2|L2]; [| rewrite OUT by lia; exact D1].
  destruct HRW' as [[_ HBm] _]. cbn [cells_bytes cbytes] in HBm. rewrite app_nil_r in HBm. rewrite <- A0, A0'' in HBm.
  eapply bytes_at_defined; [exact HBm| exact D2|]. rewrite Hsl. lia.
Qed.

Lemma node_ok_bind : forall fc ss ss1 ss' E W RW m0 base ms,
  node_ok fc ss ss1 E W RW m0 base ms ->
  (forall E1 base1 ms1, CIX fc E1 W RW m0 base1 ss1 ms1 -> node_ok fc ss1 ss' E1 W RW m0 base1 ms1) ->
  node_ok fc ss ss' E W RW m0 base ms.
Proof.
  intros fc ss ss1 ss' E W RW m0 base ms (E1 & base1 & ms1 & HA1 & HL1 & HM1 & HC1) K.
  destruct (K E1 base1 ms1 HC1) as (E2 & base2 & ms2 & HA2 & HL2 & HM2 & HC2).
  exists E2, base2, ms2. split; [eapply eagree_trans; [exact HA1| eapply eagree_le; [exact HA2| exact HL1]]|].
  split; [lia|]. split; [eapply Exec.msteps_trans; eauto| exact HC2].
Qed.

Lemma obind_some : forall x f y, obind x f = Some y -> exists z, x = Some z /\ f z = Some y.
Proof. intros [z|] f y H; cbn in H; [exists z; auto| discriminate]. Qed.

Theorem xauto_sound : forall fc W RW ENDPC fuel k ss ss' E m0 base ms,
  wf_W W = true -> wf_W RW = true ->
  xauto segs t SETPC CPYPC FSDPC FLDPC W RW ENDPC fuel k ss = Some ss' ->
  CIX fc E W RW m0 base ss ms -> node_ok fc ss ss' E W RW m0 base ms.
Proof.
  intros fc W RW ENDPC fuel k. induction k as [|k IH]; intros ss ss' E m0 base ms HW HRW Hx HC; [discriminate|].
  cbn [xauto] in Hx.
  destruct (node_run segs t W fuel (STOPS SETPC CPYPC FSDPC FLDPC ENDPC) ss) as [ss1|] eqn:Hr; [|discriminate].
  eapply node_ok_bind; [eapply node_run_sound; eauto|]. intros E1 base1 ms1 HC1.
  destruct (Z.eqb (s_pc ss1) ENDPC).
  { eapply node_flush_sound; eauto. }
  destruct (Z.eqb (s_pc ss1) FLDPC).
  { apply obind_some in Hx as (ss2 & H2 & Hx). eapply node_ok_bind; [eapply node_fld_sound; eauto|].
    intros E2 base2 ms2 HC2. eapply IH; eauto. }
  apply obind_some in Hx as (ss3 & H3 & Hx). apply obind_some in H3 as (ss2 & H2 & H3).
  eapply node_ok_bind; [eapply node_flush_sound; eauto|]. intros E2 base2 ms2 HC2.
  eapply node_ok_bind.
  { unfold gc_sp in H3. destruct (split_lit (sr_get (s_regs ss2) (Z_to_bv 5 2))) as [b kk]. eapply node_drop_sound; eauto. }
  intros E3 base3 ms3 HC3.
  apply obind_some in Hx as (ss4 & H4 & Hx).
  eapply node_ok_bind; [| intros E4 base4 ms4 HC4; eapply IH; eauto].
  destruct (Z.eqb (s_pc ss1) SETPC); [eapply node_set_sound; eauto|].
  destruct (Z.eqb (s_pc ss1) CPYPC); [eapply node_cpy_sound; eauto|].
  destruct (Z.eqb (s_pc ss1) FSDPC); [eapply node_fsd_sound; eauto| discriminate].
Qed.

End S.
