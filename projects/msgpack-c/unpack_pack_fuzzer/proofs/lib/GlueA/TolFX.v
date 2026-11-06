(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import TolC MemOps.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS TolC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module TolFX.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Lemma region_ok_unk : forall priv E m k lo hi w bg g d sa s' cells,
  region_ok segs priv E m k (Region lo hi w bg (IMap.add g (Gran d sa) cells)) ->
  IMap.bst cells -> slot_sorted s' -> incl s' sa ->
  region_ok segs priv E m k (Region lo hi w bg (IMap.add g (Gran true s') cells)).
Proof.
  intros priv E m k lo hi w bg g d sa s' cells RO B SS INC.
  destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg]. cbn [rg_cells rg_lo rg_hi rg_w rg_bg] in *.
  assert (FA : forall g0 gr, IMap.find g0 (IMap.add g (Gran true s') cells) = Some gr ->
            (g0 = g /\ gr = Gran true s') \/ (g0 <> g /\ IMap.find g0 (IMap.add g (Gran d sa) cells) = Some gr)).
  { intros g0 gr F. destruct (eqbP g g0) as [X|X].
    - apply to_Z_inj in X. subst g0. rewrite IMap.find_add_same in F by exact B. injection F as <-. left. auto.
    - assert (N : g <> g0) by (intros Y; apply X; rewrite Y; reflexivity).
      rewrite IMap.find_add_other in F by assumption. right. split; [congruence|].
      rewrite IMap.find_add_other by assumption. exact F. }
  assert (FG : IMap.find g (IMap.add g (Gran d sa) cells) = Some (Gran d sa)) by (apply IMap.find_add_same; exact B).
  constructor; cbn [rg_cells rg_lo rg_hi rg_w rg_bg].
  - apply IMap.bst_add. exact B.
  - exact Rrange.
  - exact Rvalid.
  - intros g0 gr F. destruct (FA g0 gr F) as [[-> ->]|[N F']]; [| exact (Rcells g0 gr F')].
    destruct (Rcells g _ FG) as [_ Fc]. cbn [g_cells] in *. split; [exact SS|].
    apply Forall_forall. intros c Hc. exact (proj1 (Forall_forall _ _) Fc c (INC c Hc)).
  - intros g0 gr c i F Hc Hi. destruct (FA g0 gr F) as [[-> ->]|[N F']]; [| exact (Rin g0 gr c i F' Hc Hi)].
    cbn [g_cells] in Hc. exact (Rin g (Gran d sa) c i FG (INC c Hc) Hi).
  - intros o H1 H2 U. apply (Rbg o H1 H2).
    unfold uncovered in U |- *. cbn [rg_cells] in U |- *.
    intros g0 gr KG F0. destruct (eqbP g g0) as [X|X].
    + apply to_Z_inj in X. subst g0.
      destruct (U g (Gran true s') KG ltac:(apply IMap.find_add_same; exact B)) as [DD _]. cbn in DD. discriminate DD.
    + assert (N : g <> g0) by (intros Y; apply X; rewrite Y; reflexivity).
      apply (U g0 gr KG). rewrite IMap.find_add_other by assumption. rewrite IMap.find_add_other in F0 by assumption. exact F0.
Qed.

Lemma lit_byte : forall (E : env) (b : byte), store_bytes 1%uint63 (den E (VL (Z2w (bv_unsigned b)))) = [b].
Proof.
  intros E b. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  unfold store_bytes. change (Z.to_nat (to_Z 1%uint63)) with 1%nat. cbn [Z_to_le_bytes].
  rewrite den_VL. f_equal.
  assert (W : w2Z (Z2w (bv_unsigned b)) = bv_unsigned b).
  { rewrite <- (den_VL E). cbn [den]. rewrite wbv_Z2w. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. unfold two64. lia. }
  rewrite W. apply Z_to_bv_bv_unsigned.
Qed.

Lemma in_granule_1 : forall o, in_granule o 1%uint63 = true.
Proof.
  intros o. unfold in_granule. destruct (gidx_ok o) as [_ R]. apply Uint63.leb_spec.
  rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. change (to_Z 8%uint63) with 8.
  rewrite Z.mod_small; [lia|]. change wB with (2 ^ 63). lia.
Qed.

Lemma region_unk1_sound : forall priv E m fs k r key (b : byte),
  facts_hold E fs -> ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m k r ->
  can_write segs fs priv k r key 1%uint63 = true ->
  let A := addrZ E k key in
  let m' := write_to_mem m (Z_to_bv 64 A) [b] in
  region_ok segs priv E m' k (region_unk1 r key)
  /\ rg_lo (region_unk1 r key) = rg_lo r /\ rg_hi (region_unk1 r key) = rg_hi r /\ rg_w (region_unk1 r key) = rg_w r
  /\ rg_bg (region_unk1 r key) = rg_bg r.
Proof.
  intros priv E m fs k r key b Hfs Hz RO CW. cbv zeta.
  assert (Hw : wok 1%uint63) by (left; reflexivity).
  destruct (region_store_sound segs priv E m fs k r key 1%uint63 (VL (Z2w (bv_unsigned b))) Hfs Hz RO Hw CW)
    as (_ & RO' & _ & _ & _ & _ & _).
  cbv zeta in RO'. rewrite lit_byte in RO'.
  unfold region_store in RO'. rewrite in_granule_1 in RO'. unfold region_store1 in RO'. unfold region_unk1.
  pose proof (ro_bst _ _ _ _ _ _ RO) as B.
  assert (GW : forall (d : bool) s, slot_ok segs E m (bv_unsigned (ev E k) + 8 * keyZ (granule key)) s ->
            slot_sorted (cut s (gidx key) 1%uint63) /\ incl (cut s (gidx key) 1%uint63) (slot_store s (gidx key) 1%uint63 (VL (Z2w (bv_unsigned b))))).
  { intros d s SO. destruct (gidx_ok key) as [_ RG].
    destruct SO as [Ss Fc].
    assert (W : Forall cell_wf s).
    { eapply Forall_impl; [|exact Fc]. intros c (C1 & C2 & C3 & _). unfold cell_wf. lia. }
    pose proof (slot_sorted_csorted s Ss W) as CS.
    destruct (cut_sorted E (gidx key) 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia) ltac:(change (to_Z 1%uint63) with 1; lia) s CS W) as (CS' & _ & _).
    split; [apply csorted_slot_sorted; exact CS'|].
    intros c Hc. unfold slot_store. apply insert_sorted_In. right. exact Hc. }
  destruct (IMap.find (granule key) (rg_cells r)) as [[d s]|] eqn:F.
  - destruct (GW d s (ro_cells _ _ _ _ _ _ RO _ _ F)) as [S1 I1].
    split; [| cbn; repeat split; reflexivity].
    exact (region_ok_unk priv E _ k _ _ _ _ _ d _ _ _ RO' B S1 I1).
  - split; [| cbn; repeat split; reflexivity].
    apply (region_ok_unk priv E _ k _ _ _ _ _ false _ _ _ RO' B); [exact I| intros c []].
Qed.

Lemma write_unk_sound : forall E st ms model a k o r key w rv mrv r' bs,
  st_ok segs OPS E st ms model -> wok w ->
  addr_of a = Some (k, o) -> IMap.find k (s_regs st) = Some r -> okey o = Some key ->
  can_write segs (s_facts st) (s_priv st) k r key w = true ->
  resv_ok E rv mrv ->
  Z.of_nat (length bs) = to_Z w ->
  region_ok segs (s_priv st) E (write_to_mem (ms_mem ms) (Z_to_bv 64 (addrZ E k key)) bs) k r' ->
  rg_lo r' = rg_lo r -> rg_hi r' = rg_hi r -> rg_w r' = rg_w r ->
  den E a = Z_to_bv 64 (addrZ E k key)
  /\ st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) rv (IMap.add k r' (s_regs st))
                        (s_facts st) (s_ops st) (s_priv st) (s_next st))
          (ms_upd ms (with_resv mrv (core_of ms)) (write_to_mem (ms_mem ms) (den E a) bs)) model.
Proof.
  intros E st ms model a k o r key w rv mrv r' bs HS Hw Ha Hr Hk CW Hrv LEN RO' F1 F2 F3.
  pose proof HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops Hapart Hmf Hcov Hminv].
  pose proof (Hreg k r Hr) as RO.
  destruct (can_write_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key w Hfacts Hz RO Hw CW) as (CR & WB & SEGW).
  destruct (can_read_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key w Hfacts Hz RO Hw CR) as (RA & RAw & RB & RNG & ABS).
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  cbv zeta in *. unfold addrZ in *.
  set (A := bv_unsigned (ev E k) + keyZ key) in *.
  assert (DA : den E a = Z_to_bv 64 A) by exact (access_addr E a k o key A Hz Ha Hk eq_refl RA ltac:(lia)).
  split; [exact DA|]. rewrite DA.
  set (m' := write_to_mem (ms_mem ms) (Z_to_bv 64 A) bs) in *.
  assert (FR : forall a0, 0 <= a0 < two64 -> ~ (A <= a0 < A + to_Z w) -> m' (Z_to_bv 64 a0) = ms_mem ms (Z_to_bv 64 a0)).
  { intros a0 Ha0 Hna. subst m'. apply write_to_mem_frame; rewrite ?LEN; lia. }

  assert (W1 : forall a0, A <= a0 < A + to_Z w -> PrimInt63.eqb k 0%uint63 = false ->
            bv_unsigned (ev E k) + loZ r <= a0 < bv_unsigned (ev E k) + hiZ E r).
  { intros a0 Ha0 K. pose proof (RNG K (a0 - A) ltac:(lia)). subst A. lia. }
  assert (W2 : forall a0, A <= a0 < A + to_Z w -> PrimInt63.eqb k 0%uint63 = true ->
            (exists seg, find_segment segs a0 1 = Some seg) /\ ~ in_priv (s_priv st) a0).
  { intros a0 Ha0 K. destruct (ABS K (a0 - A) ltac:(lia)) as [[bs0 M] P].
    replace (A + (a0 - A)) with a0 in M, P by lia. split; [| exact P].
    apply (memory_read_find_segment segs a0 bs0); [lia| exact M]. }

  assert (OTHER : forall k1 r1 a0, IMap.find k1 (s_regs st) = Some r1 -> k <> k1 -> 0 <= a0 < two64 ->
            (PrimInt63.eqb k1 0%uint63 = false -> bv_unsigned (ev E k1) + loZ r1 <= a0 < bv_unsigned (ev E k1) + hiZ E r1) ->
            (PrimInt63.eqb k1 0%uint63 = true -> (exists seg, find_segment segs a0 1 = Some seg) /\ ~ in_priv (s_priv st) a0) ->
            ~ (A <= a0 < A + to_Z w)).
  { intros k1 r1 a0 H1 N Ha0 V1 V2 X. pose proof (Hreg k1 r1 H1) as RO1.
    destruct (PrimInt63.eqb k 0%uint63) eqn:K.
    - destruct (W2 a0 X eq_refl) as [[seg SG] _].
      destruct (PrimInt63.eqb k1 0%uint63) eqn:K1.
      + apply N. apply eqb_correct in K. apply eqb_correct in K1. congruence.
      + pose proof (ro_valid _ _ _ _ _ _ RO1 K1 a0 (V1 eq_refl)) as (_ & _ & NS). congruence.
    - pose proof (W1 a0 X eq_refl) as IN.
      destruct (PrimInt63.eqb k1 0%uint63) eqn:K1.
      + destruct (V2 eq_refl) as [[seg SG] _].
        pose proof (ro_valid _ _ _ _ _ _ RO K a0 IN) as (_ & _ & NS). congruence.
      + refine (Hdisj k r k1 r1 Hr H1 N K K1 _ a0 (conj IN (V1 eq_refl))).
        left. unfold can_write in CW. rewrite K in CW. apply andb_prop in CW as [CW _]. exact CW. }
  assert (REG : forall k1 r1, IMap.find k1 (IMap.add k r' (s_regs st)) = Some r1 ->
            region_ok segs (s_priv st) E m' k1 r1).
  { intros k1 r1 H1.
    destruct (StepM.find_add_cases E (s_regs st) k r r' Hbst Hr F1 F2 k1 r1 H1)
      as (r0 & G0 & _ & _ & [[-> ->]|[N ->]]); [exact RO'|].
    apply (region_ok_frame segs (s_priv st) E (ms_mem ms) m' k1 r0 Hz (Hreg k1 r0 G0)).
    intros a0 Ha0 V1 V2. apply FR; [exact Ha0|]. exact (OTHER k1 r0 a0 G0 N Ha0 V1 V2). }
  split; cbn_st; try assumption; try reflexivity.
  - apply IMap.bst_add. exact Hbst.
  - apply (same_range_disjoint E (s_regs st) k r); assumption.
  - exact (pub_of_regions segs (s_priv st) E m' _ REG).
  - unfold ops_hold in *. apply Forall_forall. intros op Hop.
    pose proof (proj1 (Forall_forall _ _) Hops op Hop) as HOLD.
    pose proof (proj1 (Forall_forall _ _) Hapart op Hop) as AP.
    apply (op_frame OPS (op_id op) (map (den E) (op_args op)) (ms_mem ms) m' model); [| |exact HOLD].
    2:{ intros a0 _ M0. subst m'. apply MemP.write_to_mem_mapped. exact M0. }
    intros a0 Ha0 FP. symmetry. apply FR; [exact Ha0|]. intros X.
    destruct (AP a0 FP) as [NB PR].
    destruct (PrimInt63.eqb k 0%uint63) eqn:K.
    + destruct (W2 a0 X eq_refl) as [SG NP]. exact (NP (PR SG)).
    + apply NB. exists k, r. split; [exact Hr|]. split; [exact K|]. exact (W1 a0 X eq_refl).
  - unfold ops_apart in *. apply Forall_forall. intros op Hop a0 FP.
    destruct (proj1 (Forall_forall _ _) Hapart op Hop a0 FP) as [NB PR]. split; [|exact PR].
    intros IB. apply NB. apply (same_range_in_based E (s_regs st) k r r'); assumption.
  -
    intros a0 [IB|SG]; apply Hcov; [left | right; exact SG].
    apply (same_range_in_based E (s_regs st) k r r'); assumption.
  -
    intros aw bw Hab seg Hseg.
    pose proof (bv_unsigned_in_range _ aw) as Ra. rewrite bv_modulus_64 in Ra.
    rewrite <- (Z_to_bv_bv_unsigned _ aw) in Hab.
    assert (DEC : (A <= bv_unsigned aw < A + to_Z w) \/ ~ (A <= bv_unsigned aw < A + to_Z w)) by lia.
    destruct DEC as [IN|OUT].
    + destruct (PrimInt63.eqb k 0%uint63) eqn:K.
      * destruct (SEGW eq_refl (bv_unsigned aw - A) ltac:(lia)) as (seg' & F' & W').
        replace (A + (bv_unsigned aw - A)) with (bv_unsigned aw) in F' by lia.
        rewrite F' in Hseg. injection Hseg as <-. exact W'.
      * exfalso. pose proof (ro_valid _ _ _ _ _ _ RO K (bv_unsigned aw) (W1 _ IN eq_refl)) as (_ & _ & NS). rewrite NS in Hseg. discriminate Hseg.
    + rewrite (FR (bv_unsigned aw) Ra OUT) in Hab. rewrite Z_to_bv_bv_unsigned in Hab. exact (Hminv aw bw Hab seg Hseg).
Qed.

Lemma ov_read_bytes_inv : forall m A n bs, ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs ->
  0 <= A -> A + Z.of_nat n <= two64 ->
  length bs = n /\ forall i, 0 <= i < Z.of_nat n -> rb segs m (A + i) = nth_error bs (Z.to_nat i).
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A bs H HA HAn.
  - cbn in H. injection H as <-. split; [reflexivity | intros i Hi; lia].
  - cbn [ov_read_bytes] in H. rewrite <- rb_unfold in H.
    destruct (rb segs m A) as [b|] eqn:Hb; [|discriminate H].
    rewrite Z_to_bv_succ in H.
    destruct (ov_read_bytes segs m (Z_to_bv 64 (A + 1)) n) as [bs'|] eqn:Hr; [|discriminate H]. injection H as <-.
    destruct (IH (A + 1) bs' Hr ltac:(lia) ltac:(lia)) as [Hlen Hbs]. split; [cbn; lia|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Z.add_0_r. cbn. exact Hb.
    + replace (A + i) with (A + 1 + (i - 1)) by lia. rewrite Hbs by lia.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma stored_is_loaded : forall (w : int) (x : word) bs, (to_Z w = 1 \/ to_Z w = 8) -> length bs = Z.to_nat (to_Z w) ->
  x = ext_word false 0 (to_Z w) (le_bytes_to_word bs) -> store_bytes w x = bs.
Proof.
  intros w x bs Hw Len ->.
  pose proof (MemFX.MemFX.Z_to_le_bytes_to_Z bs) as RT. pose proof (bytes_le_to_Z_bound bs) as BD.
  destruct Hw as [W1|W8].
  - assert (w = 1%uint63) by (apply Uint63.to_Z_inj; rewrite W1; reflexivity). subst w. change (to_Z 1%uint63) with 1 in *.
    change (Z.to_nat 1) with 1%nat in Len. destruct bs as [|b [|? ?]]; try discriminate Len. clear RT BD.
    rewrite <- (bytes_val_ext_word false 1 [b] eq_refl ltac:(lia)). unfold store_bytes, bytes_val.
    change (Z.to_nat (to_Z 1%uint63)) with 1%nat. cbn [Z_to_le_bytes]. f_equal.
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
    assert (EB : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_cons; cbn; lia).
    rewrite EB, (ext_Z_small_id false 1 (bv_unsigned b)); [| lia| unfold two64; lia| change (2 ^ (8 * 1 - 0)) with 256; lia].
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite (bv_wrap_small 64 (bv_unsigned b)) by (rewrite bv_modulus_64; unfold W64.two64; lia).
    apply bv_wrap_small. unfold bv_modulus. cbn. lia.
  - assert (w = 8%uint63) by (apply Uint63.to_Z_inj; rewrite W8; reflexivity). subst w. change (to_Z 8%uint63) with 8 in *.
    rewrite <- store_bytes_64. rewrite <- RT at 2. rewrite Len. change (Z.to_nat 8) with 8%nat. f_equal.
    rewrite Len in BD. change (8 * Z.of_nat (Z.to_nat 8)) with 64 in BD.
    rewrite ext_word_id64. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact BD.
Qed.

Definition piece_ok (E : env) (ms : machine_state) (mo : Model) (st st' : sstate) (S D w : Z) : Prop :=
  exists bs, Z.of_nat (length bs) = w
    /\ St.st_ok segs OPS E st' (ms_with_mem ms (write_to_mem (ms_mem ms) (Z_to_bv 64 D) bs)) mo
    /\ (forall t, 0 <= t < w -> rb segs (ms_mem ms) (S + t) = nth_error bs (Z.to_nat t))
    /\ s_pc st' = s_pc st /\ s_rf st' = s_rf st /\ s_ff st' = s_ff st /\ s_resv st' = RNone /\ s_facts st' = s_facts st
    /\ s_ops st' = s_ops st /\ s_priv st' = s_priv st /\ s_next st' = s_next st.

Lemma load_store_piece : forall E st ms mo asrc adst (w : int) v st' S D,
  St.st_ok segs OPS E st ms mo -> s_resv st = RNone -> ms_resv ms = None ->
  (to_Z w = 1 \/ to_Z w = 8) ->
  do_load segs st asrc w false = inl (Some v) -> do_store segs st adst w v = inl st' ->
  den E asrc = Z_to_bv 64 S -> den E adst = Z_to_bv 64 D -> 0 <= S -> S + to_Z w <= two64 ->
  piece_ok E ms mo st st' S D (to_Z w).
Proof.
  intros E st ms mo asrc a w v st' S D HS RV MRV W18 DL DS DSa DA S0 S1.
  assert (Hw : wok w) by (unfold wok; destruct W18 as [Q|Q]; rewrite Q; auto).
  destruct (do_load_sound segs OPS E st ms mo asrc w false v HS Hw DL) as (bs & LEN & OV & DV).
  unfold do_store in DS. destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate DS].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate DS].
  destruct (okey o) as [key|] eqn:Hk; [|discriminate DS].
  destruct (can_write segs (s_facts st) (s_priv st) k r key w) eqn:CW; [|discriminate DS].
  injection DS as <-. rewrite RV. cbn [resv_after_store].
  destruct (store_sound segs OPS E st ms mo a k o r key w v RNone None HS Hw Ha Hr Hk CW eq_refl) as [SOK ST].
  replace (with_resv None (core_of ms)) with (core_of ms) in ST by (unfold with_resv, core_of; rewrite MRV; reflexivity).
  assert (BS : store_bytes w (den E v) = bs) by (apply (stored_is_loaded w (den E v) bs W18 LEN DV)).
  rewrite BS, DA in ST.
  assert (LBS : Z.of_nat (length bs) = to_Z w) by (rewrite LEN; lia).
  rewrite DSa in OV.
  destruct (ov_read_bytes_inv (ms_mem ms) S _ bs OV S0 ltac:(rewrite Z2Nat.id by lia; lia)) as [_ RDB].
  rewrite Z2Nat.id in RDB by lia.
  exists bs. split; [exact LBS|]. split; [exact ST|]. split; [exact RDB|].
  cbn [s_pc s_rf s_ff s_resv s_facts s_ops s_priv s_next]. repeat split; reflexivity.
Qed.

Lemma skip_piece : forall E st ms mo asrc adst st' S D,
  St.st_ok segs OPS E st ms mo -> s_resv st = RNone -> ms_resv ms = None ->
  skip_byte segs st asrc adst = Some st' ->
  den E asrc = Z_to_bv 64 S -> den E adst = Z_to_bv 64 D -> 0 <= S < two64 -> 0 <= D < two64 ->
  piece_ok E ms mo st st' S D 1.
Proof.
  intros E st ms mo asrc a st' S D HS RV MRV SK DSa DA RS RD.
  pose proof HS as [_ _ _ _ _ _ _ _ Hz _ Hreg _ _ Hfacts _ _ _ _ _].
  assert (Hw : wok 1%uint63) by (left; reflexivity).
  unfold skip_byte in SK. destruct (src_byte_ok segs st asrc) eqn:SB; [|discriminate SK].

  unfold src_byte_ok in SB. destruct (addr_of asrc) as [[ks os]|] eqn:Has; [|discriminate SB].
  destruct (IMap.find ks (s_regs st)) as [rs|] eqn:Hrs; [|discriminate SB].
  destruct (okey os) as [keys|] eqn:Hks; [|discriminate SB].
  destruct (can_read_sound segs (s_priv st) E (ms_mem ms) (s_facts st) ks rs keys 1%uint63 Hfacts Hz (Hreg ks rs Hrs) Hw SB) as (RA & RAw & RB & _ & _).
  cbv zeta in RA, RAw, RB. change (to_Z 1%uint63) with 1 in *.
  pose proof (access_addr E asrc ks os keys _ Hz Has Hks eq_refl RA ltac:(lia)) as DAS. rewrite DSa in DAS.
  assert (ES : S = addrZ E ks keys).
  { apply (f_equal bv_unsigned) in DAS. rewrite !Z_to_bv_small in DAS by (unfold two64 in *; lia). exact DAS. }
  specialize (RB 0 ltac:(lia)). rewrite Z.add_0_r, <- ES in RB.
  destruct (rb segs (ms_mem ms) S) as [b|] eqn:RBS; [| exfalso; apply RB; reflexivity].

  unfold forget_byte in SK. destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate SK].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate SK].
  destruct (okey o) as [key|] eqn:Hk; [|discriminate SK].
  destruct (is_block_bg (rg_bg r) && can_write segs (s_facts st) (s_priv st) k r key 1%uint63)%bool eqn:CK; [|discriminate SK].
  apply andb_prop in CK as [_ CW]. injection SK as <-.
  destruct (region_unk1_sound (s_priv st) E (ms_mem ms) (s_facts st) k r key b Hfacts Hz (Hreg k r Hr) CW) as (RO' & F1 & F2 & F3 & _).
  cbv zeta in RO'.
  destruct (write_unk_sound E st ms mo a k o r key 1%uint63 RNone None (region_unk1 r key) [b] HS Hw Ha Hr Hk CW eq_refl eq_refl RO' F1 F2 F3)
    as [DA' ST].
  replace (with_resv None (core_of ms)) with (core_of ms) in ST by (unfold with_resv, core_of; rewrite MRV; reflexivity).
  rewrite DA in ST. rewrite RV.
  exists [b]. split; [reflexivity|]. split; [exact ST|]. split.
  { intros t Ht. assert (t = 0) by lia. subst t. rewrite Z.add_0_r. exact RBS. }
  cbn [s_pc s_rf s_ff s_resv s_facts s_ops s_priv s_next]. repeat split; reflexivity.
Qed.

Definition copied (E : env) (ms : machine_state) (mo : Model) (st stn : sstate) (S D i len : Z) : Prop :=
  exists m', St.st_ok segs OPS E stn (ms_with_mem ms m') mo
    /\ (forall a, 0 <= a < two64 -> ~ (D + i <= a < D + len) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a))
    /\ (forall j, i <= j < len -> exists b, rb segs (ms_mem ms) (S + j) = Some b /\ m' (Z_to_bv 64 (D + j)) = Some b)
    /\ (forall x, ms_mem ms x <> None -> m' x <> None)
    /\ s_pc stn = s_pc st /\ s_rf stn = s_rf st /\ s_ff stn = s_ff st /\ s_resv stn = RNone /\ s_facts stn = s_facts st
    /\ s_ops stn = s_ops st /\ s_priv stn = s_priv st /\ s_next stn = s_next st.

Lemma piece_compose : forall E ms mo st st1 stn S D i w len,
  piece_ok E ms mo st st1 (S + i) (D + i) w -> 1 <= w -> 0 <= i -> i + w <= len ->
  0 <= S -> 0 <= D -> D + len < two64 -> S + len < two64 -> (S + len <= D \/ D + len <= S) ->
  (forall bs, St.st_ok segs OPS E st1 (ms_with_mem ms (write_to_mem (ms_mem ms) (Z_to_bv 64 (D + i)) bs)) mo ->
     copied E (ms_with_mem ms (write_to_mem (ms_mem ms) (Z_to_bv 64 (D + i)) bs)) mo st1 stn S D (i + w) len) ->
  copied E ms mo st stn S D i len.
Proof.
  intros E ms mo st st1 stn S D i w len (bs & LBS & ST & RDB & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8) W1 I0 IW S0 D0 NWD NWS DISJ REST.
  set (m1 := write_to_mem (ms_mem ms) (Z_to_bv 64 (D + i)) bs) in *.
  destruct (REST bs ST) as (m' & HS' & FR' & IN' & MONO' & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). fold m1 in HS', FR', IN', MONO'.
  cbn [ms_mem ms_with_mem ms_upd] in FR', MONO', IN'.

  assert (SRC1 : forall j, i <= j < len -> rb segs m1 (S + j) = rb segs (ms_mem ms) (S + j)).
  { intros j Hj. unfold rb, m1. rewrite write_to_mem_frame; [reflexivity| lia| rewrite LBS; unfold two64 in *; lia| unfold two64 in *; lia| rewrite LBS; lia]. }
  exists m'. split; [exact HS'|]. split; [| split; [| split]].
  - intros x Hx NI. rewrite (FR' x Hx) by lia. unfold m1.
    apply write_to_mem_frame; [lia | rewrite LBS; unfold two64 in *; lia | exact Hx | rewrite LBS; lia].
  - intros j Hj. destruct (Z_lt_le_dec j (i + w)) as [Q|Q].
    + pose proof (RDB (j - i) ltac:(lia)) as RJ. replace (S + i + (j - i)) with (S + j) in RJ by lia.
      destruct (nth_error bs (Z.to_nat (j - i))) as [b|] eqn:NB; [| exfalso; apply nth_error_None in NB; lia].
      exists b. split; [exact RJ|].
      rewrite (FR' (D + j)) by (unfold two64 in *; lia). unfold m1.
      replace (D + j) with (D + i + (j - i)) by lia.
      rewrite write_to_mem_in by (rewrite ?LBS; unfold two64 in *; lia). exact NB.
    + destruct (IN' j ltac:(lia)) as (b & RB1 & MB). exists b. split; [rewrite <- (SRC1 j ltac:(lia)); exact RB1| exact MB].
  - intros x Hx. apply MONO'. unfold m1. apply write_to_mem_mapped. exact Hx.
  - rewrite F1, F2, F3, F5, F6, F7, F8, P1, P2, P3, P5, P6, P7, P8. repeat split; try reflexivity. exact F4.
Qed.
End WithSegs.
End TolFX.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import TolC.TwinB MemOps.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS TolC.TwinB.TolC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module TolFX.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Lemma region_ok_unk : forall priv E m k lo hi w bg g d sa s' cells,
  region_ok segs priv E m k (Region lo hi w bg (IMap.add g (Gran d sa) cells)) ->
  IMap.bst cells -> slot_sorted s' -> incl s' sa ->
  region_ok segs priv E m k (Region lo hi w bg (IMap.add g (Gran true s') cells)).
Proof.
  intros priv E m k lo hi w bg g d sa s' cells RO B SS INC.
  destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg]. cbn [rg_cells rg_lo rg_hi rg_w rg_bg] in *.
  assert (FA : forall g0 gr, IMap.find g0 (IMap.add g (Gran true s') cells) = Some gr ->
            (g0 = g /\ gr = Gran true s') \/ (g0 <> g /\ IMap.find g0 (IMap.add g (Gran d sa) cells) = Some gr)).
  { intros g0 gr F. destruct (eqbP g g0) as [X|X].
    - apply to_Z_inj in X. subst g0. rewrite IMap.find_add_same in F by exact B. injection F as <-. left. auto.
    - assert (N : g <> g0) by (intros Y; apply X; rewrite Y; reflexivity).
      rewrite IMap.find_add_other in F by assumption. right. split; [congruence|].
      rewrite IMap.find_add_other by assumption. exact F. }
  assert (FG : IMap.find g (IMap.add g (Gran d sa) cells) = Some (Gran d sa)) by (apply IMap.find_add_same; exact B).
  constructor; cbn [rg_cells rg_lo rg_hi rg_w rg_bg].
  - apply IMap.bst_add. exact B.
  - exact Rrange.
  - exact Rvalid.
  - intros g0 gr F. destruct (FA g0 gr F) as [[-> ->]|[N F']]; [| exact (Rcells g0 gr F')].
    destruct (Rcells g _ FG) as [_ Fc]. cbn [g_cells] in *. split; [exact SS|].
    apply Forall_forall. intros c Hc. exact (proj1 (Forall_forall _ _) Fc c (INC c Hc)).
  - intros g0 gr c i F Hc Hi. destruct (FA g0 gr F) as [[-> ->]|[N F']]; [| exact (Rin g0 gr c i F' Hc Hi)].
    cbn [g_cells] in Hc. exact (Rin g (Gran d sa) c i FG (INC c Hc) Hi).
  - intros o H1 H2 U. apply (Rbg o H1 H2).
    unfold uncovered in U |- *. cbn [rg_cells] in U |- *.
    intros g0 gr KG F0. destruct (eqbP g g0) as [X|X].
    + apply to_Z_inj in X. subst g0.
      destruct (U g (Gran true s') KG ltac:(apply IMap.find_add_same; exact B)) as [DD _]. cbn in DD. discriminate DD.
    + assert (N : g <> g0) by (intros Y; apply X; rewrite Y; reflexivity).
      apply (U g0 gr KG). rewrite IMap.find_add_other by assumption. rewrite IMap.find_add_other in F0 by assumption. exact F0.
Qed.

Lemma lit_byte : forall (E : env) (b : byte), store_bytes 1%uint63 (den E (VL (Z2w (bv_unsigned b)))) = [b].
Proof.
  intros E b. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  unfold store_bytes. change (Z.to_nat (to_Z 1%uint63)) with 1%nat. cbn [Z_to_le_bytes].
  rewrite den_VL. f_equal.
  assert (W : w2Z (Z2w (bv_unsigned b)) = bv_unsigned b).
  { rewrite <- (den_VL E). cbn [den]. rewrite wbv_Z2w. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. unfold two64. lia. }
  rewrite W. apply Z_to_bv_bv_unsigned.
Qed.

Lemma in_granule_1 : forall o, in_granule o 1%uint63 = true.
Proof.
  intros o. unfold in_granule. destruct (gidx_ok o) as [_ R]. apply Uint63.leb_spec.
  rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. change (to_Z 8%uint63) with 8.
  rewrite Z.mod_small; [lia|]. change wB with (2 ^ 63). lia.
Qed.

Lemma region_unk1_sound : forall priv E m fs k r key (b : byte),
  facts_hold E fs -> ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m k r ->
  can_write segs fs priv k r key 1%uint63 = true ->
  let A := addrZ E k key in
  let m' := write_to_mem m (Z_to_bv 64 A) [b] in
  region_ok segs priv E m' k (region_unk1 r key)
  /\ rg_lo (region_unk1 r key) = rg_lo r /\ rg_hi (region_unk1 r key) = rg_hi r /\ rg_w (region_unk1 r key) = rg_w r
  /\ rg_bg (region_unk1 r key) = rg_bg r.
Proof.
  intros priv E m fs k r key b Hfs Hz RO CW. cbv zeta.
  assert (Hw : wok 1%uint63) by (left; reflexivity).
  destruct (region_store_sound segs priv E m fs k r key 1%uint63 (VL (Z2w (bv_unsigned b))) Hfs Hz RO Hw CW)
    as (_ & RO' & _ & _ & _ & _ & _).
  cbv zeta in RO'. rewrite lit_byte in RO'.
  unfold region_store in RO'. rewrite in_granule_1 in RO'. unfold region_store1 in RO'. unfold region_unk1.
  pose proof (ro_bst _ _ _ _ _ _ RO) as B.
  assert (GW : forall (d : bool) s, slot_ok segs E m (bv_unsigned (ev E k) + 8 * keyZ (granule key)) s ->
            slot_sorted (cut s (gidx key) 1%uint63) /\ incl (cut s (gidx key) 1%uint63) (slot_store s (gidx key) 1%uint63 (VL (Z2w (bv_unsigned b))))).
  { intros d s SO. destruct (gidx_ok key) as [_ RG].
    destruct SO as [Ss Fc].
    assert (W : Forall cell_wf s).
    { eapply Forall_impl; [|exact Fc]. intros c (C1 & C2 & C3 & _). unfold cell_wf. lia. }
    pose proof (slot_sorted_csorted s Ss W) as CS.
    destruct (cut_sorted E (gidx key) 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia) ltac:(change (to_Z 1%uint63) with 1; lia) s CS W) as (CS' & _ & _).
    split; [apply csorted_slot_sorted; exact CS'|].
    intros c Hc. unfold slot_store. apply insert_sorted_In. right. exact Hc. }
  destruct (IMap.find (granule key) (rg_cells r)) as [[d s]|] eqn:F.
  - destruct (GW d s (ro_cells _ _ _ _ _ _ RO _ _ F)) as [S1 I1].
    split; [| cbn; repeat split; reflexivity].
    exact (region_ok_unk priv E _ k _ _ _ _ _ d _ _ _ RO' B S1 I1).
  - split; [| cbn; repeat split; reflexivity].
    apply (region_ok_unk priv E _ k _ _ _ _ _ false _ _ _ RO' B); [exact I| intros c []].
Qed.

Lemma write_unk_sound : forall E st ms model a k o r key w rv mrv r' bs,
  st_ok segs OPS E st ms model -> wok w ->
  addr_of a = Some (k, o) -> IMap.find k (s_regs st) = Some r -> okey o = Some key ->
  can_write segs (s_facts st) (s_priv st) k r key w = true ->
  resv_ok E rv mrv ->
  Z.of_nat (length bs) = to_Z w ->
  region_ok segs (s_priv st) E (write_to_mem (ms_mem ms) (Z_to_bv 64 (addrZ E k key)) bs) k r' ->
  rg_lo r' = rg_lo r -> rg_hi r' = rg_hi r -> rg_w r' = rg_w r ->
  den E a = Z_to_bv 64 (addrZ E k key)
  /\ st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) rv (IMap.add k r' (s_regs st))
                        (s_facts st) (s_ops st) (s_priv st) (s_next st))
          (ms_upd ms (with_resv mrv (core_of ms)) (write_to_mem (ms_mem ms) (den E a) bs)) model.
Proof.
  intros E st ms model a k o r key w rv mrv r' bs HS Hw Ha Hr Hk CW Hrv LEN RO' F1 F2 F3.
  pose proof HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops Hapart Hmf Hcov Hminv].
  pose proof (Hreg k r Hr) as RO.
  destruct (can_write_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key w Hfacts Hz RO Hw CW) as (CR & WB & SEGW).
  destruct (can_read_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key w Hfacts Hz RO Hw CR) as (RA & RAw & RB & RNG & ABS).
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  cbv zeta in *. unfold addrZ in *.
  set (A := bv_unsigned (ev E k) + keyZ key) in *.
  assert (DA : den E a = Z_to_bv 64 A) by exact (access_addr E a k o key A Hz Ha Hk eq_refl RA ltac:(lia)).
  split; [exact DA|]. rewrite DA.
  set (m' := write_to_mem (ms_mem ms) (Z_to_bv 64 A) bs) in *.
  assert (FR : forall a0, 0 <= a0 < two64 -> ~ (A <= a0 < A + to_Z w) -> m' (Z_to_bv 64 a0) = ms_mem ms (Z_to_bv 64 a0)).
  { intros a0 Ha0 Hna. subst m'. apply write_to_mem_frame; rewrite ?LEN; lia. }

  assert (W1 : forall a0, A <= a0 < A + to_Z w -> PrimInt63.eqb k 0%uint63 = false ->
            bv_unsigned (ev E k) + loZ r <= a0 < bv_unsigned (ev E k) + hiZ E r).
  { intros a0 Ha0 K. pose proof (RNG K (a0 - A) ltac:(lia)). subst A. lia. }
  assert (W2 : forall a0, A <= a0 < A + to_Z w -> PrimInt63.eqb k 0%uint63 = true ->
            (exists seg, find_segment segs a0 1 = Some seg) /\ ~ in_priv (s_priv st) a0).
  { intros a0 Ha0 K. destruct (ABS K (a0 - A) ltac:(lia)) as [[bs0 M] P].
    replace (A + (a0 - A)) with a0 in M, P by lia. split; [| exact P].
    apply (memory_read_find_segment segs a0 bs0); [lia| exact M]. }

  assert (OTHER : forall k1 r1 a0, IMap.find k1 (s_regs st) = Some r1 -> k <> k1 -> 0 <= a0 < two64 ->
            (PrimInt63.eqb k1 0%uint63 = false -> bv_unsigned (ev E k1) + loZ r1 <= a0 < bv_unsigned (ev E k1) + hiZ E r1) ->
            (PrimInt63.eqb k1 0%uint63 = true -> (exists seg, find_segment segs a0 1 = Some seg) /\ ~ in_priv (s_priv st) a0) ->
            ~ (A <= a0 < A + to_Z w)).
  { intros k1 r1 a0 H1 N Ha0 V1 V2 X. pose proof (Hreg k1 r1 H1) as RO1.
    destruct (PrimInt63.eqb k 0%uint63) eqn:K.
    - destruct (W2 a0 X eq_refl) as [[seg SG] _].
      destruct (PrimInt63.eqb k1 0%uint63) eqn:K1.
      + apply N. apply eqb_correct in K. apply eqb_correct in K1. congruence.
      + pose proof (ro_valid _ _ _ _ _ _ RO1 K1 a0 (V1 eq_refl)) as (_ & _ & NS). congruence.
    - pose proof (W1 a0 X eq_refl) as IN.
      destruct (PrimInt63.eqb k1 0%uint63) eqn:K1.
      + destruct (V2 eq_refl) as [[seg SG] _].
        pose proof (ro_valid _ _ _ _ _ _ RO K a0 IN) as (_ & _ & NS). congruence.
      + refine (Hdisj k r k1 r1 Hr H1 N K K1 _ a0 (conj IN (V1 eq_refl))).
        left. unfold can_write in CW. rewrite K in CW. apply andb_prop in CW as [CW _]. exact CW. }
  assert (REG : forall k1 r1, IMap.find k1 (IMap.add k r' (s_regs st)) = Some r1 ->
            region_ok segs (s_priv st) E m' k1 r1).
  { intros k1 r1 H1.
    destruct (StepM.find_add_cases E (s_regs st) k r r' Hbst Hr F1 F2 k1 r1 H1)
      as (r0 & G0 & _ & _ & [[-> ->]|[N ->]]); [exact RO'|].
    apply (region_ok_frame segs (s_priv st) E (ms_mem ms) m' k1 r0 Hz (Hreg k1 r0 G0)).
    intros a0 Ha0 V1 V2. apply FR; [exact Ha0|]. exact (OTHER k1 r0 a0 G0 N Ha0 V1 V2). }
  split; cbn_st; try assumption; try reflexivity.
  - apply IMap.bst_add. exact Hbst.
  - apply (same_range_disjoint E (s_regs st) k r); assumption.
  - exact (pub_of_regions segs (s_priv st) E m' _ REG).
  - unfold ops_hold in *. apply Forall_forall. intros op Hop.
    pose proof (proj1 (Forall_forall _ _) Hops op Hop) as HOLD.
    pose proof (proj1 (Forall_forall _ _) Hapart op Hop) as AP.
    apply (op_frame OPS (op_id op) (map (den E) (op_args op)) (ms_mem ms) m' model); [| |exact HOLD].
    2:{ intros a0 _ M0. subst m'. apply MemP.write_to_mem_mapped. exact M0. }
    intros a0 Ha0 FP. symmetry. apply FR; [exact Ha0|]. intros X.
    destruct (AP a0 FP) as [NB PR].
    destruct (PrimInt63.eqb k 0%uint63) eqn:K.
    + destruct (W2 a0 X eq_refl) as [SG NP]. exact (NP (PR SG)).
    + apply NB. exists k, r. split; [exact Hr|]. split; [exact K|]. exact (W1 a0 X eq_refl).
  - unfold ops_apart in *. apply Forall_forall. intros op Hop a0 FP.
    destruct (proj1 (Forall_forall _ _) Hapart op Hop a0 FP) as [NB PR]. split; [|exact PR].
    intros IB. apply NB. apply (same_range_in_based E (s_regs st) k r r'); assumption.
  -
    intros a0 [IB|SG]; apply Hcov; [left | right; exact SG].
    apply (same_range_in_based E (s_regs st) k r r'); assumption.
  -
    intros aw bw Hab seg Hseg.
    pose proof (bv_unsigned_in_range _ aw) as Ra. rewrite bv_modulus_64 in Ra.
    rewrite <- (Z_to_bv_bv_unsigned _ aw) in Hab.
    assert (DEC : (A <= bv_unsigned aw < A + to_Z w) \/ ~ (A <= bv_unsigned aw < A + to_Z w)) by lia.
    destruct DEC as [IN|OUT].
    + destruct (PrimInt63.eqb k 0%uint63) eqn:K.
      * destruct (SEGW eq_refl (bv_unsigned aw - A) ltac:(lia)) as (seg' & F' & W').
        replace (A + (bv_unsigned aw - A)) with (bv_unsigned aw) in F' by lia.
        rewrite F' in Hseg. injection Hseg as <-. exact W'.
      * exfalso. pose proof (ro_valid _ _ _ _ _ _ RO K (bv_unsigned aw) (W1 _ IN eq_refl)) as (_ & _ & NS). rewrite NS in Hseg. discriminate Hseg.
    + rewrite (FR (bv_unsigned aw) Ra OUT) in Hab. rewrite Z_to_bv_bv_unsigned in Hab. exact (Hminv aw bw Hab seg Hseg).
Qed.

Lemma ov_read_bytes_inv : forall m A n bs, ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs ->
  0 <= A -> A + Z.of_nat n <= two64 ->
  length bs = n /\ forall i, 0 <= i < Z.of_nat n -> rb segs m (A + i) = nth_error bs (Z.to_nat i).
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A bs H HA HAn.
  - cbn in H. injection H as <-. split; [reflexivity | intros i Hi; lia].
  - cbn [ov_read_bytes] in H. rewrite <- rb_unfold in H.
    destruct (rb segs m A) as [b|] eqn:Hb; [|discriminate H].
    rewrite Z_to_bv_succ in H.
    destruct (ov_read_bytes segs m (Z_to_bv 64 (A + 1)) n) as [bs'|] eqn:Hr; [|discriminate H]. injection H as <-.
    destruct (IH (A + 1) bs' Hr ltac:(lia) ltac:(lia)) as [Hlen Hbs]. split; [cbn; lia|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Z.add_0_r. cbn. exact Hb.
    + replace (A + i) with (A + 1 + (i - 1)) by lia. rewrite Hbs by lia.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma stored_is_loaded : forall (w : int) (x : word) bs, (to_Z w = 1 \/ to_Z w = 8) -> length bs = Z.to_nat (to_Z w) ->
  x = ext_word false 0 (to_Z w) (le_bytes_to_word bs) -> store_bytes w x = bs.
Proof.
  intros w x bs Hw Len ->.
  pose proof (MemFX.MemFX.Z_to_le_bytes_to_Z bs) as RT. pose proof (bytes_le_to_Z_bound bs) as BD.
  destruct Hw as [W1|W8].
  - assert (w = 1%uint63) by (apply Uint63.to_Z_inj; rewrite W1; reflexivity). subst w. change (to_Z 1%uint63) with 1 in *.
    change (Z.to_nat 1) with 1%nat in Len. destruct bs as [|b [|? ?]]; try discriminate Len. clear RT BD.
    rewrite <- (bytes_val_ext_word false 1 [b] eq_refl ltac:(lia)). unfold store_bytes, bytes_val.
    change (Z.to_nat (to_Z 1%uint63)) with 1%nat. cbn [Z_to_le_bytes]. f_equal.
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
    assert (EB : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_cons; cbn; lia).
    rewrite EB, (ext_Z_small_id false 1 (bv_unsigned b)); [| lia| unfold two64; lia| change (2 ^ (8 * 1 - 0)) with 256; lia].
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite (bv_wrap_small 64 (bv_unsigned b)) by (rewrite bv_modulus_64; unfold W64.two64; lia).
    apply bv_wrap_small. unfold bv_modulus. cbn. lia.
  - assert (w = 8%uint63) by (apply Uint63.to_Z_inj; rewrite W8; reflexivity). subst w. change (to_Z 8%uint63) with 8 in *.
    rewrite <- store_bytes_64. rewrite <- RT at 2. rewrite Len. change (Z.to_nat 8) with 8%nat. f_equal.
    rewrite Len in BD. change (8 * Z.of_nat (Z.to_nat 8)) with 64 in BD.
    rewrite ext_word_id64. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact BD.
Qed.

Definition piece_ok (E : env) (ms : machine_state) (mo : Model) (st st' : sstate) (S D w : Z) : Prop :=
  exists bs, Z.of_nat (length bs) = w
    /\ St.st_ok segs OPS E st' (ms_with_mem ms (write_to_mem (ms_mem ms) (Z_to_bv 64 D) bs)) mo
    /\ (forall t, 0 <= t < w -> rb segs (ms_mem ms) (S + t) = nth_error bs (Z.to_nat t))
    /\ s_pc st' = s_pc st /\ s_rf st' = s_rf st /\ s_ff st' = s_ff st /\ s_resv st' = RNone /\ s_facts st' = s_facts st
    /\ s_ops st' = s_ops st /\ s_priv st' = s_priv st /\ s_next st' = s_next st.

Lemma load_store_piece : forall E st ms mo asrc adst (w : int) v st' S D,
  St.st_ok segs OPS E st ms mo -> s_resv st = RNone -> ms_resv ms = None ->
  (to_Z w = 1 \/ to_Z w = 8) ->
  do_load segs st asrc w false = inl (Some v) -> do_store segs st adst w v = inl st' ->
  den E asrc = Z_to_bv 64 S -> den E adst = Z_to_bv 64 D -> 0 <= S -> S + to_Z w <= two64 ->
  piece_ok E ms mo st st' S D (to_Z w).
Proof.
  intros E st ms mo asrc a w v st' S D HS RV MRV W18 DL DS DSa DA S0 S1.
  assert (Hw : wok w) by (unfold wok; destruct W18 as [Q|Q]; rewrite Q; auto).
  destruct (do_load_sound segs OPS E st ms mo asrc w false v HS Hw DL) as (bs & LEN & OV & DV).
  unfold do_store in DS. destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate DS].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate DS].
  destruct (okey o) as [key|] eqn:Hk; [|discriminate DS].
  destruct (can_write segs (s_facts st) (s_priv st) k r key w) eqn:CW; [|discriminate DS].
  injection DS as <-. rewrite RV. cbn [resv_after_store].
  destruct (store_sound segs OPS E st ms mo a k o r key w v RNone None HS Hw Ha Hr Hk CW eq_refl) as [SOK ST].
  replace (with_resv None (core_of ms)) with (core_of ms) in ST by (unfold with_resv, core_of; rewrite MRV; reflexivity).
  assert (BS : store_bytes w (den E v) = bs) by (apply (stored_is_loaded w (den E v) bs W18 LEN DV)).
  rewrite BS, DA in ST.
  assert (LBS : Z.of_nat (length bs) = to_Z w) by (rewrite LEN; lia).
  rewrite DSa in OV.
  destruct (ov_read_bytes_inv (ms_mem ms) S _ bs OV S0 ltac:(rewrite Z2Nat.id by lia; lia)) as [_ RDB].
  rewrite Z2Nat.id in RDB by lia.
  exists bs. split; [exact LBS|]. split; [exact ST|]. split; [exact RDB|].
  cbn [s_pc s_rf s_ff s_resv s_facts s_ops s_priv s_next]. repeat split; reflexivity.
Qed.

Lemma skip_piece : forall E st ms mo asrc adst st' S D,
  St.st_ok segs OPS E st ms mo -> s_resv st = RNone -> ms_resv ms = None ->
  skip_byte segs st asrc adst = Some st' ->
  den E asrc = Z_to_bv 64 S -> den E adst = Z_to_bv 64 D -> 0 <= S < two64 -> 0 <= D < two64 ->
  piece_ok E ms mo st st' S D 1.
Proof.
  intros E st ms mo asrc a st' S D HS RV MRV SK DSa DA RS RD.
  pose proof HS as [_ _ _ _ _ _ _ _ Hz _ Hreg _ _ Hfacts _ _ _ _ _].
  assert (Hw : wok 1%uint63) by (left; reflexivity).
  unfold skip_byte in SK. destruct (src_byte_ok segs st asrc) eqn:SB; [|discriminate SK].

  unfold src_byte_ok in SB. destruct (addr_of asrc) as [[ks os]|] eqn:Has; [|discriminate SB].
  destruct (IMap.find ks (s_regs st)) as [rs|] eqn:Hrs; [|discriminate SB].
  destruct (okey os) as [keys|] eqn:Hks; [|discriminate SB].
  destruct (can_read_sound segs (s_priv st) E (ms_mem ms) (s_facts st) ks rs keys 1%uint63 Hfacts Hz (Hreg ks rs Hrs) Hw SB) as (RA & RAw & RB & _ & _).
  cbv zeta in RA, RAw, RB. change (to_Z 1%uint63) with 1 in *.
  pose proof (access_addr E asrc ks os keys _ Hz Has Hks eq_refl RA ltac:(lia)) as DAS. rewrite DSa in DAS.
  assert (ES : S = addrZ E ks keys).
  { apply (f_equal bv_unsigned) in DAS. rewrite !Z_to_bv_small in DAS by (unfold two64 in *; lia). exact DAS. }
  specialize (RB 0 ltac:(lia)). rewrite Z.add_0_r, <- ES in RB.
  destruct (rb segs (ms_mem ms) S) as [b|] eqn:RBS; [| exfalso; apply RB; reflexivity].

  unfold forget_byte in SK. destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate SK].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate SK].
  destruct (okey o) as [key|] eqn:Hk; [|discriminate SK].
  destruct (is_block_bg (rg_bg r) && can_write segs (s_facts st) (s_priv st) k r key 1%uint63)%bool eqn:CK; [|discriminate SK].
  apply andb_prop in CK as [_ CW]. injection SK as <-.
  destruct (region_unk1_sound (s_priv st) E (ms_mem ms) (s_facts st) k r key b Hfacts Hz (Hreg k r Hr) CW) as (RO' & F1 & F2 & F3 & _).
  cbv zeta in RO'.
  destruct (write_unk_sound E st ms mo a k o r key 1%uint63 RNone None (region_unk1 r key) [b] HS Hw Ha Hr Hk CW eq_refl eq_refl RO' F1 F2 F3)
    as [DA' ST].
  replace (with_resv None (core_of ms)) with (core_of ms) in ST by (unfold with_resv, core_of; rewrite MRV; reflexivity).
  rewrite DA in ST. rewrite RV.
  exists [b]. split; [reflexivity|]. split; [exact ST|]. split.
  { intros t Ht. assert (t = 0) by lia. subst t. rewrite Z.add_0_r. exact RBS. }
  cbn [s_pc s_rf s_ff s_resv s_facts s_ops s_priv s_next]. repeat split; reflexivity.
Qed.

Definition copied (E : env) (ms : machine_state) (mo : Model) (st stn : sstate) (S D i len : Z) : Prop :=
  exists m', St.st_ok segs OPS E stn (ms_with_mem ms m') mo
    /\ (forall a, 0 <= a < two64 -> ~ (D + i <= a < D + len) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a))
    /\ (forall j, i <= j < len -> exists b, rb segs (ms_mem ms) (S + j) = Some b /\ m' (Z_to_bv 64 (D + j)) = Some b)
    /\ (forall x, ms_mem ms x <> None -> m' x <> None)
    /\ s_pc stn = s_pc st /\ s_rf stn = s_rf st /\ s_ff stn = s_ff st /\ s_resv stn = RNone /\ s_facts stn = s_facts st
    /\ s_ops stn = s_ops st /\ s_priv stn = s_priv st /\ s_next stn = s_next st.

Lemma piece_compose : forall E ms mo st st1 stn S D i w len,
  piece_ok E ms mo st st1 (S + i) (D + i) w -> 1 <= w -> 0 <= i -> i + w <= len ->
  0 <= S -> 0 <= D -> D + len < two64 -> S + len < two64 -> (S + len <= D \/ D + len <= S) ->
  (forall bs, St.st_ok segs OPS E st1 (ms_with_mem ms (write_to_mem (ms_mem ms) (Z_to_bv 64 (D + i)) bs)) mo ->
     copied E (ms_with_mem ms (write_to_mem (ms_mem ms) (Z_to_bv 64 (D + i)) bs)) mo st1 stn S D (i + w) len) ->
  copied E ms mo st stn S D i len.
Proof.
  intros E ms mo st st1 stn S D i w len (bs & LBS & ST & RDB & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8) W1 I0 IW S0 D0 NWD NWS DISJ REST.
  set (m1 := write_to_mem (ms_mem ms) (Z_to_bv 64 (D + i)) bs) in *.
  destruct (REST bs ST) as (m' & HS' & FR' & IN' & MONO' & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). fold m1 in HS', FR', IN', MONO'.
  cbn [ms_mem ms_with_mem ms_upd] in FR', MONO', IN'.

  assert (SRC1 : forall j, i <= j < len -> rb segs m1 (S + j) = rb segs (ms_mem ms) (S + j)).
  { intros j Hj. unfold rb, m1. rewrite write_to_mem_frame; [reflexivity| lia| rewrite LBS; unfold two64 in *; lia| unfold two64 in *; lia| rewrite LBS; lia]. }
  exists m'. split; [exact HS'|]. split; [| split; [| split]].
  - intros x Hx NI. rewrite (FR' x Hx) by lia. unfold m1.
    apply write_to_mem_frame; [lia | rewrite LBS; unfold two64 in *; lia | exact Hx | rewrite LBS; lia].
  - intros j Hj. destruct (Z_lt_le_dec j (i + w)) as [Q|Q].
    + pose proof (RDB (j - i) ltac:(lia)) as RJ. replace (S + i + (j - i)) with (S + j) in RJ by lia.
      destruct (nth_error bs (Z.to_nat (j - i))) as [b|] eqn:NB; [| exfalso; apply nth_error_None in NB; lia].
      exists b. split; [exact RJ|].
      rewrite (FR' (D + j)) by (unfold two64 in *; lia). unfold m1.
      replace (D + j) with (D + i + (j - i)) by lia.
      rewrite write_to_mem_in by (rewrite ?LBS; unfold two64 in *; lia). exact NB.
    + destruct (IN' j ltac:(lia)) as (b & RB1 & MB). exists b. split; [rewrite <- (SRC1 j ltac:(lia)); exact RB1| exact MB].
  - intros x Hx. apply MONO'. unfold m1. apply write_to_mem_mapped. exact Hx.
  - rewrite F1, F2, F3, F5, F6, F7, F8, P1, P2, P3, P5, P6, P7, P8. repeat split; try reflexivity. exact F4.
Qed.
End WithSegs.
End TolFX.
End TwinB.
