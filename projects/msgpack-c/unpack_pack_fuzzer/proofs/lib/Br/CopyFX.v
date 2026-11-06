(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX MemFX.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM PlanS CtrLib CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module CopyFX.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Definition keyof (R : IMap.t Mem.region) (a : sv) : option int :=
  match addr_of a with
  | Some (k, _) => Some k
  | None => match sym_addr_of R a with Some (k, _, _) => Some k | None => None end
  end.

Definition zone (R : IMap.t Mem.region) (priv : list (int * int)) (E : env) (k : int) (A : Z) : Prop :=
  if PrimInt63.eqb k 0%uint63 then (exists seg, find_segment segs A 1 = Some seg) /\ ~ in_priv priv A
  else exists r, IMap.find k R = Some r /\ bv_unsigned (ev E k) + loZ r <= A < bv_unsigned (ev E k) + hiZ E r.

Definition same_ranges (R R' : IMap.t Mem.region) : Prop :=
  forall k, (forall r', IMap.find k R' = Some r' -> exists r, IMap.find k R = Some r /\ Mem.rg_lo r' = Mem.rg_lo r /\ Mem.rg_hi r' = Mem.rg_hi r /\ Mem.rg_w r' = Mem.rg_w r)
         /\ (forall r, IMap.find k R = Some r -> exists r', IMap.find k R' = Some r').

Lemma same_ranges_refl : forall R, same_ranges R R.
Proof. intros R k. split; [intros r' H; exists r'; auto| intros r H; exists r; exact H]. Qed.

Lemma same_ranges_trans : forall R1 R2 R3, same_ranges R1 R2 -> same_ranges R2 R3 -> same_ranges R1 R3.
Proof.
  intros R1 R2 R3 A B k. destruct (A k) as [A1 A2]. destruct (B k) as [B1 B2]. split.
  - intros r3 H3. destruct (B1 r3 H3) as (r2 & H2 & L2 & Hh2 & W2). destruct (A1 r2 H2) as (r1 & H1 & L1 & Hh1 & W1).
    exists r1. rewrite L2, Hh2, W2. auto.
  - intros r1 H1. destruct (A2 r1 H1) as (r2 & H2). exact (B2 r2 H2).
Qed.

Lemma zone_same_ranges : forall R R' priv E k A, same_ranges R R' -> zone R' priv E k A -> zone R priv E k A.
Proof.
  intros R R' priv E k A SR Z. unfold zone in *. destruct (PrimInt63.eqb k 0%uint63); [exact Z|].
  destruct Z as (r' & H' & RG). destruct (proj1 (SR k) r' H') as (r & H & L & Hh & _). exists r. split; [exact H|].
  unfold loZ, hiZ in *. rewrite <- L, <- Hh. exact RG.
Qed.

Lemma keyof_same_ranges : forall R R' a, same_ranges R R' -> keyof R' a = keyof R a.
Proof.
  intros R R' a SR. unfold keyof. destruct (addr_of a); [reflexivity|].
  assert (FS : forall k, (exists r, IMap.find k R' = Some r) <-> (exists r, IMap.find k R = Some r)).
  { intros k. split; intros (r & H); [destruct (proj1 (SR k) r H) as (r0 & H0 & _); eauto| exact (proj2 (SR k) r H)]. }
  assert (FD : forall k, match IMap.find k R' with Some _ => true | None => false end = match IMap.find k R with Some _ => true | None => false end).
  { intros k. destruct (IMap.find k R') eqn:A; destruct (IMap.find k R) eqn:B; try reflexivity.
    - destruct (proj1 (FS k) ltac:(eauto)) as (r0 & H0). rewrite H0 in B. discriminate.
    - destruct (proj2 (FS k) ltac:(eauto)) as (r0 & H0). rewrite H0 in A. discriminate. }
  unfold sym_addr_of.
  destruct a as [| |op x y| | | | | | | |]; try reflexivity. destruct op; try reflexivity.
  destruct x as [|k1 o1| | | | | | | | |];
  destruct y as [|k2 o2| | | | | | | | |]; try reflexivity;
  repeat match goal with
  | |- context [IMap.find ?k R'] => pose proof (FD k); destruct (IMap.find k R'); destruct (IMap.find k R); try discriminate; try reflexivity
  end.
Qed.

Lemma load1_where : forall E st ms mo a v,
  St.st_ok segs OPS E st ms mo -> do_load segs st a 1%uint63 false = inl (Some v) ->
  let A := bv_unsigned (den E a) in
  exists k b, keyof (s_regs st) a = Some k /\ zone (s_regs st) (s_priv st) E k A /\ A + 1 < two64
    /\ rb segs (ms_mem ms) A = Some b /\ store_bytes 1%uint63 (den E v) = [b]
    /\ (forall k' o, addr_of a = Some (k', o) -> exists key, Mem.okey o = Some key /\ A = bv_unsigned (ev E k') + keyZ key).
Proof.
  intros E st ms mo a v HS H. cbv zeta.
  pose proof (so_zero _ _ _ _ _ _ HS) as Hz. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  assert (W1 : wok 1%uint63) by (left; reflexivity).
  destruct (do_load_sound segs OPS E st ms mo a 1%uint63 false v HS W1 H) as (bs & Len & OV & Dv).
  change (Z.to_nat (to_Z 1%uint63)) with 1%nat in Len, OV. change (to_Z 1%uint63) with 1 in Dv.
  destruct bs as [|b [|]]; try discriminate Len.
  assert (RB : rb segs (ms_mem ms) (bv_unsigned (den E a)) = Some b).
  { rewrite rb_unfold, Z_to_bv_bv_unsigned. cbn [ov_read_bytes] in OV.
    destruct (match ms_mem ms (den E a) with Some b0 => Some b0 | None => match memory_read segs (den E a) 1 with Some (b0 :: _) => Some b0 | _ => None end end) as [b0|]; [|discriminate OV].
    cbn in OV. injection OV as <-. reflexivity. }
  assert (SB : store_bytes 1%uint63 (den E v) = [b]).
  { rewrite Dv, <- (bytes_val_ext_word false 1 [b] eq_refl ltac:(lia)). unfold store_bytes, bytes_val.
    change (Z.to_nat (to_Z 1%uint63)) with 1%nat. cbn [Z_to_le_bytes]. f_equal.
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
    assert (EB : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_cons; cbn; lia).
    rewrite EB, (ext_Z_small_id false 1 (bv_unsigned b)); [| lia| unfold two64; lia| change (2 ^ (8 * 1 - 0)) with 256; lia].
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite (bv_wrap_small 64 (bv_unsigned b)) by (rewrite bv_modulus_64; unfold W64.two64; lia).
    apply bv_wrap_small. unfold bv_modulus. cbn. lia. }
  unfold do_load in H.
  destruct (addr_of a) as [[k o]|] eqn:Ha.
  - destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
    destruct (Mem.okey o) as [key|] eqn:Hk; [|discriminate].
    destruct (can_read segs (s_facts st) (s_priv st) k r key 1%uint63) eqn:CR; [|discriminate].
    pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO.
    pose proof (can_read_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key 1%uint63 Hfs Hz RO W1 CR) as (RA & RAw & _ & RNG & ABS).
    cbv zeta in RA, RAw. change (to_Z 1%uint63) with 1 in *.
    pose proof (access_addr E a k o key (addrZ E k key) Hz Ha Hk eq_refl RA ltac:(lia)) as DA.
    assert (EA : bv_unsigned (den E a) = addrZ E k key).
    { rewrite DA, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. lia. }
    exists k, b. split; [unfold keyof; rewrite Ha; reflexivity|]. rewrite EA.
    split; [| split; [| split; [rewrite <- EA; exact RB| split; [exact SB| intros k' o' E1; first [injection E1 as <- <- | (rewrite Ha in E1; injection E1 as <- <-)]; exists key; split; [first [exact Hk | reflexivity]| reflexivity]]]]].
    + unfold zone. destruct (PrimInt63.eqb k 0%uint63) eqn:K0.
      * destruct (ABS eq_refl 0 ltac:(lia)) as ([bs' MR] & NP). rewrite Z.add_0_r in MR, NP.
        assert (A0 : addrZ E k key = keyZ key).
        { unfold addrZ. rewrite (proj1 (Uint63.eqb_spec _ _) K0), (ev0_zero E Hz). apply Z.add_0_l. }
        rewrite A0 in *. split; [| exact NP]. apply (memory_read_find_segment segs (keyZ key) bs'); [| exact MR].
        pose proof (keyZ_range key). unfold two64. lia.
      * exists r. split; [exact Hr|]. pose proof (RNG eq_refl 0 ltac:(lia)) as X. unfold addrZ. lia.
    + destruct (PrimInt63.eqb k 0%uint63) eqn:K0.
      * assert (A0 : addrZ E k key = keyZ key).
        { unfold addrZ. rewrite (proj1 (Uint63.eqb_spec _ _) K0), (ev0_zero E Hz). apply Z.add_0_l. }
        rewrite A0. pose proof (keyZ_range key). unfold two64. lia.
      * pose proof (RNG eq_refl 0 ltac:(lia)) as X. pose proof (ro_range _ _ _ _ _ _ RO K0) as [_ RH]. unfold addrZ. lia.
  - destruct (sym_addr_of (s_regs st) a) as [[[k r] off]|] eqn:SA; [|discriminate].
    destruct (sym_addr_of_sound E (s_regs st) a k r off SA) as [Hr Da].
    assert (KLH : PrimInt63.eqb k 0%uint63 = false /\ loZ r = 0 /\ bv_unsigned (den E off) + 1 <= hiZ E r).
    { destruct (can_read_sym (s_facts st) k r off 1%uint63) as [j|] eqn:CS.
      - destruct (can_read_sym_sound E (s_facts st) k r off 1%uint63 j Hfs CS) as (K & _ & _ & LO & _ & HI). change (to_Z 1%uint63) with 1 in HI. auto.
      -
        destruct (can_read_symz (s_facts st) k r off 1%uint63) eqn:CZ; [|discriminate].
        destruct (can_read_symz_sound E (s_facts st) k r off 1%uint63 Hfs CZ) as (K & _ & _ & LO & _ & HI). change (to_Z 1%uint63) with 1 in HI. auto. }
    destruct KLH as (K & LO & HI).
    pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO. pose proof (ro_range _ _ _ _ _ _ RO K) as [RL RH]. rewrite LO in RL.
    pose proof (bv_unsigned_in_range 64 (den E off)) as RU. rewrite bv_modulus_64 in RU.
    assert (EA : bv_unsigned (den E a) = bv_unsigned (ev E k) + bv_unsigned (den E off)).
    { rewrite Da, bv_add_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. unfold two64 in *. lia. }
    exists k, b. split; [unfold keyof; rewrite Ha, SA; reflexivity|]. rewrite EA.
    split; [| split; [unfold two64 in *; lia| split; [rewrite <- EA; exact RB| split; [exact SB| intros k' o' E1; first [discriminate E1 | (rewrite Ha in E1; discriminate E1)]]]]].
    unfold zone. rewrite K. exists r. split; [exact Hr|]. rewrite LO. lia.
Qed.

Definition zoneW (R : IMap.t Mem.region) (priv : list (int * int)) (E : env) (k : int) (A : Z) : Prop :=
  zone R priv E k A /\ (PrimInt63.eqb k 0%uint63 = false -> exists r, IMap.find k R = Some r /\ Mem.rg_w r = true).

Lemma zoneW_same_ranges : forall R R' priv E k A, same_ranges R R' -> zoneW R' priv E k A -> zoneW R priv E k A.
Proof.
  intros R R' priv E k A SR [Z W]. split; [exact (zone_same_ranges R R' priv E k A SR Z)|].
  intros K. destruct (W K) as (r' & H' & W'). destruct (proj1 (SR k) r' H') as (r & H & _ & _ & Wq). exists r. rewrite <- Wq. auto.
Qed.

Lemma store1_where : forall E st (R F : bvmap 5 word) pc fc m rom mo a v st',
  St.st_ok segs OPS E st (MS R F pc fc None m rom) mo -> s_resv st = RNone ->
  do_store segs st a 1%uint63 v = inl st' ->
  let A := bv_unsigned (den E a) in
  St.st_ok segs OPS E st' (MS R F pc fc None (write_to_mem m (Z_to_bv 64 A) (store_bytes 1%uint63 (den E v))) rom) mo
  /\ st' = SS (s_pc st) (s_rf st) (s_ff st) RNone (s_regs st') (s_facts st) (s_ops st) (s_priv st) (s_next st)
  /\ same_ranges (s_regs st) (s_regs st')
  /\ exists k o key, addr_of a = Some (k, o) /\ Mem.okey o = Some key /\ A = bv_unsigned (ev E k) + keyZ key
       /\ zoneW (s_regs st) (s_priv st) E k A /\ A + 1 < two64
       /\ wb segs m A = true /\ rb segs m A <> None.
Proof.
  intros E st R F pc fc m rom mo a v st' HS RV H. cbv zeta.
  pose proof (so_zero _ _ _ _ _ _ HS) as Hz. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof (so_bst _ _ _ _ _ _ HS) as HB.
  assert (W1 : wok 1%uint63) by (left; reflexivity).
  unfold do_store in H.
  destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
  destruct (Mem.okey o) as [key|] eqn:Hk; [|discriminate].
  destruct (can_write segs (s_facts st) (s_priv st) k r key 1%uint63) eqn:CW; [|discriminate].
  apply inl_inj in H. subst st'. rewrite RV. cbn [resv_after_store s_regs].
  pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO.
  destruct (can_write_sound segs (s_priv st) E m (s_facts st) k r key 1%uint63 Hfs Hz RO W1 CW) as (CR & WB & SEGW).
  pose proof (can_read_sound segs (s_priv st) E m (s_facts st) k r key 1%uint63 Hfs Hz RO W1 CR) as (RA & RAw & RBk & RNG & ABS).
  cbv zeta in RA, RAw. change (to_Z 1%uint63) with 1 in *.
  pose proof (access_addr E a k o key (addrZ E k key) Hz Ha Hk eq_refl RA ltac:(lia)) as DA.
  assert (EA : bv_unsigned (den E a) = addrZ E k key).
  { rewrite DA, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. lia. }
  rewrite EA.
  destruct (store_sound segs OPS E st (MS R F pc fc None m rom) mo a k o r key 1%uint63 v RNone None HS W1 Ha Hr Hk CW eq_refl) as [SOK ST].
  cbn [ms_mem MS core_of with_resv ms_upd ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_rom c_regs c_fregs c_pc c_fcsr c_resv] in ST.
  rewrite DA in ST.
  destruct (region_store_sound segs (s_priv st) E m (s_facts st) k r key 1%uint63 v Hfs Hz RO W1 CW) as (_ & _ & Flo & Fhi & Fw & Fbg & _).
  split; [exact ST|]. split; [reflexivity|]. split.
  - intros k1. split.
    + intros r' H'. destruct (Uint63.eqb k k1) eqn:Q.
      * apply Uint63.eqb_correct in Q. subst k1. rewrite IMap.find_add_same in H' by exact HB. injection H' as <-.
        exists r. rewrite Flo, Fhi, Fw. auto.
      * apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H' by (exact HB || exact Q). exists r'. auto.
    + intros r1 H1. destruct (Uint63.eqb k k1) eqn:Q.
      * apply Uint63.eqb_correct in Q. subst k1. eexists. rewrite IMap.find_add_same by exact HB. reflexivity.
      * apply Uint63.eqb_false_spec in Q. exists r1. rewrite IMap.find_add_other by (exact HB || exact Q). exact H1.
  - exists k, o, key. split; [reflexivity|]. split; [first [exact Hk | reflexivity]|]. split; [reflexivity|].
    split; [| split; [| split; [| exact (RBk 0 ltac:(lia)) || (rewrite <- (Z.add_0_r (addrZ E k key)); exact (RBk 0 ltac:(lia)))]]].
    + split.
      * unfold zone. destruct (PrimInt63.eqb k 0%uint63) eqn:K0.
        -- destruct (ABS eq_refl 0 ltac:(lia)) as ([bs' MR] & NP). rewrite Z.add_0_r in MR, NP.
           assert (A0 : addrZ E k key = keyZ key).
           { unfold addrZ. rewrite (proj1 (Uint63.eqb_spec _ _) K0), (ev0_zero E Hz). apply Z.add_0_l. }
           rewrite A0 in *. split; [| exact NP]. apply (memory_read_find_segment segs (keyZ key) bs'); [| exact MR].
           pose proof (keyZ_range key). unfold two64. lia.
        -- exists r. split; [exact Hr|]. pose proof (RNG eq_refl 0 ltac:(lia)) as X. unfold addrZ. lia.
      * intros K0. exists r. split; [exact Hr|]. unfold can_write in CW. rewrite K0 in CW. apply andb_prop in CW as [W _]. exact W.
    + destruct (PrimInt63.eqb k 0%uint63) eqn:K0.
      * assert (A0 : addrZ E k key = keyZ key).
        { unfold addrZ. rewrite (proj1 (Uint63.eqb_spec _ _) K0), (ev0_zero E Hz). apply Z.add_0_l. }
        rewrite A0. pose proof (keyZ_range key). unfold two64. lia.
      * pose proof (RNG eq_refl 0 ltac:(lia)) as X. pose proof (ro_range _ _ _ _ _ _ RO K0) as [_ RH]. unfold addrZ. lia.
    + pose proof (WB 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma den_add_lit : forall E a (i : int), den E (sv_alu ALU_ADD a (VL (wlit i))) = (den E a + Z_to_bv 64 (to_Z i))%bv.
Proof. intros E a i. rewrite den_sv_alu. cbn [alu64 alu den]. unfold wbv. rewrite wlit_ok. reflexivity. Qed.

Lemma write1 : forall m a b x, write_to_mem m a [b] x = if bv_eqb x a then Some b else m x.
Proof. reflexivity. Qed.

Lemma bv_eqb_true : forall (a b : word), bv_eqb a b = true -> a = b.
Proof. intros a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma unsigned_add_lit : forall (W : word) j, bv_unsigned (W + Z_to_bv 64 j)%bv = (bv_unsigned W + j) mod two64.
Proof.
  intros W j. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
  rewrite Z.add_mod_idemp_r by (unfold two64; lia). reflexivity.
Qed.

Lemma word_add_inj : forall (W : word) j j', 0 <= j < two64 -> 0 <= j' < two64 -> (W + Z_to_bv 64 j)%bv = (W + Z_to_bv 64 j')%bv -> j = j'.
Proof.
  intros W j j' Hj Hj' H. apply (f_equal bv_unsigned) in H. rewrite !unsigned_add_lit in H.
  pose proof (bv_unsigned_in_range 64 W) as RW. rewrite bv_modulus_64 in RW.
  set (u := bv_unsigned W) in *. unfold two64 in *.
  pose proof (Z.div_mod (u + j) 18446744073709551616 ltac:(lia)) as D1. pose proof (Z.div_mod (u + j') 18446744073709551616 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (u + j) 18446744073709551616 ltac:(lia)) as B1. pose proof (Z.mod_pos_bound (u + j') 18446744073709551616 ltac:(lia)) as B2.
  set (q1 := (u + j) / 18446744073709551616) in *. set (q2 := (u + j') / 18446744073709551616) in *.
  set (r1 := (u + j) mod 18446744073709551616) in *. set (r2 := (u + j') mod 18446744073709551616) in *.
  clearbody q1 q2 r1 r2. subst r1. lia.
Qed.

Lemma addr_exact : forall (W : word) (n : Z),
  (forall j, 0 <= j < n -> bv_unsigned (W + Z_to_bv 64 j)%bv + 1 < two64) ->
  forall j, 0 <= j < n -> bv_unsigned (W + Z_to_bv 64 j)%bv = bv_unsigned W + j.
Proof.
  intros W n B j [Hj0 Hjn]. pose proof (bv_unsigned_in_range 64 W) as RW. rewrite bv_modulus_64 in RW.
  revert Hjn. revert j Hj0. apply (natlike_ind (fun j => j < n -> bv_unsigned (W + Z_to_bv 64 j)%bv = bv_unsigned W + j)).
  - intros _. rewrite unsigned_add_lit, Z.add_0_r. apply Z.mod_small. lia.
  - intros k Hk IH Hk1. pose proof (IH ltac:(lia)) as E1. pose proof (B k ltac:(lia)) as Bk. rewrite E1 in Bk.
    rewrite unsigned_add_lit. unfold Z.succ. apply Z.mod_small. lia.
Qed.

Section COPY.
Variables (E : env) (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rom : word -> option byte) (mo : Model).
Variables (src dst : sv) (st0 : sstate) (m0 : word -> option byte).
Hypothesis RV0 : s_resv st0 = RNone.

Definition saddr (j : Z) : word := (den E src + Z_to_bv 64 j)%bv.
Definition daddr (j : Z) : word := (den E dst + Z_to_bv 64 j)%bv.

Record CINV (i : Z) (sti : sstate) (mi : word -> option byte) (bs : list byte) : Prop := MKCI {
  ci_ok : St.st_ok segs OPS E sti (MS R F pc fc None mi rom) mo;
  ci_shape : sti = SS (s_pc st0) (s_rf st0) (s_ff st0) RNone (s_regs sti) (s_facts st0) (s_ops st0) (s_priv st0) (s_next st0);
  ci_ranges : same_ranges (s_regs st0) (s_regs sti);
  ci_len : length bs = Z.to_nat i;
  ci_frame : forall x, (forall j, 0 <= j < i -> x <> daddr j) -> mi x = m0 x;
  ci_written : forall j, 0 <= j < i -> mi (daddr j) = Some (nth (Z.to_nat j) bs (Z_to_bv 8 0));
  ci_read : forall j, 0 <= j < i -> (forall j', 0 <= j' < j -> saddr j <> daddr j') ->
              rb segs m0 (bv_unsigned (saddr j)) = Some (nth (Z.to_nat j) bs (Z_to_bv 8 0));
  ci_src : forall j, 0 <= j < i -> exists k, keyof (s_regs st0) (sv_alu ALU_ADD src (VL (wlit (of_Z j)))) = Some k
              /\ zone (s_regs st0) (s_priv st0) E k (bv_unsigned (saddr j)) /\ bv_unsigned (saddr j) + 1 < two64
              /\ (forall k' o, addr_of (sv_alu ALU_ADD src (VL (wlit (of_Z j)))) = Some (k', o) -> exists key, Mem.okey o = Some key /\
                    bv_unsigned (saddr j) = bv_unsigned (ev E k') + keyZ key);
  ci_dst : forall j, 0 <= j < i -> exists k o key, addr_of (sv_alu ALU_ADD dst (VL (wlit (of_Z j)))) = Some (k, o)
              /\ Mem.okey o = Some key /\ bv_unsigned (daddr j) = bv_unsigned (ev E k) + keyZ key
              /\ zoneW (s_regs st0) (s_priv st0) E k (bv_unsigned (daddr j)) /\ bv_unsigned (daddr j) + 1 < two64
              /\ wb segs m0 (bv_unsigned (daddr j)) = true /\ rb segs m0 (bv_unsigned (daddr j)) <> None }.

Lemma CINV0 : St.st_ok segs OPS E st0 (MS R F pc fc None m0 rom) mo -> CINV 0 st0 m0 [].
Proof.
  intros HS. constructor; try (intros; lia).
  - exact HS.
  - destruct st0; cbn in RV0 |- *. subst. reflexivity.
  - apply same_ranges_refl.
  - reflexivity.
  - intros x _. reflexivity.
Qed.

Lemma of_Z_small : forall j, 0 <= j <= 256 -> to_Z (of_Z j) = j.
Proof. intros j Hj. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_two63, two63_eq. lia. Qed.

Lemma copy_step : forall i (iw : int) sti mi bs v st',
  0 <= i < 256 -> to_Z iw = i -> CINV i sti mi bs ->
  do_load segs sti (sv_alu ALU_ADD src (VL (wlit iw))) 1%uint63 false = inl (Some v) ->
  do_store segs sti (sv_alu ALU_ADD dst (VL (wlit iw))) 1%uint63 v = inl st' ->
  exists b, CINV (i + 1) st' (write_to_mem mi (daddr i) [b]) (bs ++ [b]).
Proof.
  intros i iw sti mi bs v st' Hi Hiw CI HL HST.
  destruct CI as [OK SH SR LEN FR WR RD SRC DST].
  assert (RVi : s_resv sti = RNone) by (rewrite SH; reflexivity).
  assert (PRIVi : s_priv sti = s_priv st0) by (rewrite SH; reflexivity).
  destruct (load1_where E sti _ mo _ v OK HL) as (k & b & KO & ZO & B1 & RB & SB & XA). cbn [ms_mem MS] in RB.
  destruct (store1_where E sti R F pc fc mi rom mo _ v st' OK RVi HST) as (OK' & SH' & SR' & kd & od & keyd & AD & OKd & XD & ZW & B2 & WB & RB2).
  rewrite !den_add_lit, !Hiw in *. fold (saddr i) (daddr i) in *. fold (saddr i) in KO, ZO, B1, RB, XA. fold (daddr i) in OK', XD, ZW, B2, WB, RB2.
  rewrite SB in OK'. rewrite Z_to_bv_bv_unsigned in OK'.
  assert (NW : forall j, 0 <= j < i -> daddr i <> daddr j).
  { intros j Hj X. apply word_add_inj in X; unfold two64 in *; lia. }
  assert (MI : mi (daddr i) = m0 (daddr i)) by (apply FR; intros j Hj X; exact (NW j Hj X)).
  exists b. constructor.
  - exact OK'.
  - rewrite SH' at 1. rewrite SH. reflexivity.
  - eapply same_ranges_trans; [exact SR| exact SR'].
  - rewrite length_app, LEN. cbn. lia.
  - intros x Hx. rewrite write1. destruct (bv_eqb x (daddr i)) eqn:Q.
    + exfalso. apply bv_eqb_true in Q. exact (Hx i ltac:(lia) Q).
    + apply FR. intros j Hj. apply Hx. lia.
  - intros j Hj. rewrite write1. destruct (bv_eqb (daddr j) (daddr i)) eqn:Q.
    + apply bv_eqb_true in Q. assert (j = i) by (apply (word_add_inj (den E dst)); unfold two64 in *; [lia| lia| exact Q]). subst j.
      rewrite app_nth2 by (rewrite LEN; lia). rewrite LEN, Nat.sub_diag. reflexivity.
    + assert (j <> i) by (intros ->; rewrite bv_eqb_refl in Q; discriminate). rewrite WR by lia.
      rewrite app_nth1 by (rewrite LEN; lia). reflexivity.
  - intros j Hj SEP. destruct (Z.eq_dec j i) as [->|NE].
    + rewrite app_nth2 by (rewrite LEN; lia). rewrite LEN, Nat.sub_diag. cbn [nth].
      rewrite <- RB. unfold rb. rewrite Z_to_bv_bv_unsigned. rewrite (FR (saddr i)); [reflexivity|]. intros j' Hj'. apply SEP. lia.
    + rewrite RD by (try lia; intros j' Hj'; apply SEP; lia). rewrite app_nth1 by (rewrite LEN; lia). reflexivity.
  - intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [| apply SRC; lia].
    exists k. replace (of_Z i) with iw by (apply Uint63.to_Z_inj; rewrite of_Z_small by lia; exact Hiw).
    split; [rewrite <- (keyof_same_ranges (s_regs st0) (s_regs sti) _ SR); exact KO|].
    split; [rewrite <- PRIVi; exact (zone_same_ranges _ _ _ _ _ _ SR ZO)|]. split; [exact B1| exact XA].
  - intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [| apply DST; lia].
    exists kd, od, keyd. replace (of_Z i) with iw by (apply Uint63.to_Z_inj; rewrite of_Z_small by lia; exact Hiw).
    split; [exact AD|]. split; [exact OKd|]. split; [exact XD|]. split; [rewrite <- PRIVi; exact (zoneW_same_ranges _ _ _ _ _ _ SR ZW)|]. split; [exact B2|].
    unfold wb, rb in *. rewrite Z_to_bv_bv_unsigned in *. unfold wview in WB |- *. rewrite <- MI. split; [exact WB| exact RB2].
Qed.

Lemma copy_bytes_ind : forall cnt i (iw : int) sti mi bs stn,
  0 <= i -> i + Z.of_nat cnt <= 256 -> to_Z iw = i -> CINV i sti mi bs ->
  CtrM.copy_bytes segs cnt iw src dst sti = Some stn ->
  exists mn bsn, CINV (i + Z.of_nat cnt) stn mn bsn.
Proof.
  induction cnt as [|cnt IH]; intros i iw sti mi bs stn Hi Hc Hiw CI H.
  - cbn in H. injection H as <-. exists mi, bs. rewrite Z.add_0_r. exact CI.
  - cbn [CtrM.copy_bytes] in H.
    destruct (do_load segs sti (sv_alu ALU_ADD src (VL (wlit iw))) 1%uint63 false) as [[v|]|] eqn:HL; try discriminate.
    destruct (do_store segs sti (sv_alu ALU_ADD dst (VL (wlit iw))) 1%uint63 v) as [st'|] eqn:HST; [|discriminate].
    destruct (copy_step i iw sti mi bs v st' ltac:(lia) Hiw CI HL HST) as (b & CI').
    assert (Hiw1 : to_Z (PrimInt63.add iw 1%uint63) = i + 1).
    { rewrite add_Z; [| change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; pose proof (int_range iw); lia]. change (to_Z 1%uint63) with 1. lia. }
    destruct (IH (i + 1) (PrimInt63.add iw 1%uint63) st' _ _ stn ltac:(lia) ltac:(lia) Hiw1 CI' H) as (mn & bsn & CIn).
    exists mn, bsn. replace (i + Z.of_nat (S cnt)) with (i + 1 + Z.of_nat cnt) by lia. exact CIn.
Qed.

End COPY.

Lemma addr_of_add_lit : forall a k o c, addr_of a = Some (k, o) -> addr_of (sv_alu ALU_ADD a (VL c)) = Some (k, wadd o c).
Proof.
  intros a k o c H. unfold sv_alu. destruct a; cbn in H; try discriminate; injection H as <- <-; cbn; [|reflexivity].
  reflexivity.
Qed.

Lemma keyof_add_lit : forall Rg a k c, keyof Rg a = Some k -> keyof Rg (sv_alu ALU_ADD a (VL c)) = Some k.
Proof.
  intros Rg a k c H. unfold keyof in *. unfold sv_alu.
  destruct a as [x|k1 o1|op x y| | | | | | | |]; cbn [sv_alu0 addr_of] in *; try (injection H as <-; reflexivity);
    try discriminate H.
  destruct op; try (cbn in H; discriminate H). destruct (weqb c wzero) eqn:Hc; [destruct x; exact H|].

  destruct x as [|kx ox|[] x1 x2| | | | | | | |]; destruct y as [|ky oy|[] y1 y2| | | | | | | |]; cbn [add_lit_fold addr_of sym_addr_of] in *;
    try discriminate H;
    repeat match goal with |- context [match IMap.find ?kk Rg with _ => _ end] => destruct (IMap.find kk Rg) end;
    cbn in *; first [exact H | discriminate H | congruence].
Qed.

Lemma bytes_at_of_rb : forall m A (bs : list byte),
  0 <= A -> A + Z.of_nat (length bs) <= two64 ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> rb segs m (A + j) = Some (nth (Z.to_nat j) bs (Z_to_bv 8 0))) ->
  bytes_at segs m A bs.
Proof.
  intros m A bs HA HB RB. split; [lia|]. split; [unfold two64 in HB; lia|].
  intros i Hi. rewrite <- MemFX.rb_mrd. rewrite (RB (Z.of_nat i)) by lia. rewrite Nat2Z.id. symmetry. apply nth_error_nth'. lia.
Qed.

Lemma rw_cells_of_views : forall m A (n : nat),
  0 <= A -> A + Z.of_nat n <= two64 ->
  (forall j, 0 <= j < Z.of_nat n -> rb segs m (A + j) <> None /\ wb segs m (A + j) = true) ->
  exists junk, length junk = n /\ rw_cells segs m A [CB n junk].
Proof.
  intros m A n HA HB V.
  set (f := fun i : nat => match rb segs m (A + Z.of_nat i) with Some b => b | None => Z_to_bv 8 0 end).
  exists (map f (seq 0 n)).
  assert (L : length (map f (seq 0 n)) = n) by (rewrite length_map, length_seq; reflexivity).
  split; [exact L|]. split.
  - split; [cbn; auto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_of_rb; [lia| rewrite L; lia|]. rewrite L.
    intros j Hj. destruct (V j Hj) as [RBj _].
    rewrite <- (Z2Nat.id j) at 1 by lia.
    rewrite (nth_indep _ (Z_to_bv 8 0) (f 0%nat)) by (rewrite L; lia). rewrite map_nth, seq_nth by lia. cbn [Nat.add].
    subst f. cbn beta. destruct (rb segs m (A + Z.of_nat (Z.to_nat j))) eqn:X; [reflexivity| exfalso; apply RBj; rewrite <- X; f_equal; lia].
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [unfold two64 in HB; lia|].
    intros i Hi. apply (proj1 (MemFX.wb_wview segs _ _)). apply (V i Hi).
Qed.

Lemma sep_of_pointwise : forall S D n, 0 < n ->
  (forall j j', 0 <= j < n -> 0 <= j' < n -> S + j <> D + j') -> S + n <= D \/ D + n <= S.
Proof.
  intros S D n Hn P.
  destruct (Z_lt_le_dec D (S + n)) as [L1|G1]; [| left; lia].
  destruct (Z_lt_le_dec S (D + n)) as [L2|G2]; [| right; lia].
  exfalso. destruct (Z_le_gt_dec S D) as [L|G].
  - exact (P (D - S) 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (P 0 (S - D) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

End WithSegs.
End CopyFX.
