(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs MemProofs StepSoundBase.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step ValP MemP StepB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module StepM.

Ltac cbn_st := cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next setpc setf setresv setregs addfact
                    ms_upd c_regs c_fregs c_pc c_fcsr c_resv
                    ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending
                    with_pc with_regs with_fregs with_resv with_fcsr core_of rget fget rset fset].

Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Lemma interp_EDone : forall c m, interp_eff segs (EDone c) m = MachineOk (c, m).
Proof. reflexivity. Qed.

Lemma Some_inj : forall (A : Type) (x y : A), Some x = Some y -> x = y.
Proof. intros A x y H. injection H. auto. Qed.
Lemma inl_inj : forall (A B : Type) (x y : A), @inl A B x = inl y -> x = y.
Proof. intros A B x y H. injection H. auto. Qed.
Lemma XOk_inj : forall x y, XOk x = XOk y -> x = y.
Proof. intros x y H. injection H. auto. Qed.
Lemma some3_inj : forall (A B C : Type) (a a' : A) (b b' : B) (c c' : C),
  Some (a, b, c) = Some (a', b', c') -> a = a' /\ b = b' /\ c = c'.
Proof. intros A B C a a' b b' c c' H. injection H. auto. Qed.

Lemma interp_ELoad : forall n a k m bs, ov_read_bytes segs m a (width_bytes n) = Some bs ->
  interp_eff segs (ELoad n a k) m = interp_eff segs (k (bv_extract 0 n (le_bytes_to_word bs))) m.
Proof.
  intros n a k m bs H. unfold interp_eff. cbn [interp_eff_accesses]. rewrite H.
  destruct (interp_eff_accesses segs (k _) m) as [[v acc]| |]; reflexivity.
Qed.

Lemma interp_EStore : forall n a v k m, store_ok segs m a (width_bytes n) = true ->
  interp_eff segs (EStore n a v k) m = interp_eff segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))).
Proof.
  intros n a v k m H. unfold interp_eff. cbn [interp_eff_accesses]. rewrite H.
  destruct (interp_eff_accesses segs k _) as [[v' acc]| |]; reflexivity.
Qed.

Lemma addr_of_den : forall E a k o, ev E 0%uint63 = Z_to_bv 64 0 -> addr_of a = Some (k, o) ->
  den E a = den E (VP k o).
Proof.
  intros E a k o Hz H. destruct a; cbn in H; try discriminate; injection H as <- <-; [|reflexivity].
  cbn [den]. rewrite Hz. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned, bv_wrap_0, Z.add_0_l.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma access_addr : forall E a k o key A,
  ev E 0%uint63 = Z_to_bv 64 0 -> addr_of a = Some (k, o) -> okey o = Some key ->
  A = addrZ E k key -> 0 <= A -> A < two64 ->
  den E a = Z_to_bv 64 A.
Proof.
  intros E a k o key A Hz Ha Hk -> H0 H1.
  rewrite (addr_of_den E a k o Hz Ha). apply (den_VP_addr E k o key Hk). lia.
Qed.

Lemma bytes_val_ext_word : forall sx w bs, length bs = Z.to_nat w -> 1 <= w <= 8 ->
  bytes_val sx w bs = ext_word sx 0 w (le_bytes_to_word bs).
Proof.
  intros sx w bs Len Hw. unfold bytes_val, ext_word, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite Len, Z2Nat.id in B by lia.
  assert (HP : 2 ^ (8 * w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (Z_to_bv_small (bytes_le_to_Z bs)) by (unfold two64; lia). reflexivity.
Qed.

Lemma ext_word_1 : forall sx x,
  ext_word sx 0 1 x = (if sx then sext 64 (bv_extract 0 8 x) else zext 64 (bv_extract 0 8 x)).
Proof. intros [|] x; [apply ext_word_sext_k| apply ext_word_zext_k]; reflexivity. Qed.
Lemma ext_word_2 : forall sx x,
  ext_word sx 0 2 x = (if sx then sext 64 (bv_extract 0 16 x) else zext 64 (bv_extract 0 16 x)).
Proof. intros [|] x; [apply ext_word_sext_k| apply ext_word_zext_k]; reflexivity. Qed.
Lemma ext_word_4 : forall sx x,
  ext_word sx 0 4 x = (if sx then sext 64 (bv_extract 0 32 x) else zext 64 (bv_extract 0 32 x)).
Proof. intros [|] x; [apply ext_word_sext_k| apply ext_word_zext_k]; reflexivity. Qed.
Lemma bv_extract_64 : forall x : word, bv_extract 0 64 x = x.
Proof.
  intros x. apply bv_eq. rewrite bv_extract_0_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma ext_word_8 : forall sx x, ext_word sx 0 8 x = bv_extract 0 64 x.
Proof. intros sx x. rewrite bv_extract_64. apply ext_word_id64. Qed.

Lemma sym_addr_of_sound : forall E R a k r off, sym_addr_of R a = Some (k, r, off) ->
  IMap.find k R = Some r /\ den E a = (ev E k + den E off)%bv.
Proof.
  intros E R a k r off H. unfold sym_addr_of in H.
  destruct a as [| |op x y| | | | | | | |]; try discriminate. destruct op; try discriminate.
  destruct x as [|k1 o1| | | | | | | | |].
  all: try (destruct y as [|k2 o2| | | | | | | | |]; try discriminate;
            destruct (IMap.find k2 R) as [r2|] eqn:F2; [|discriminate];
            destruct (some3_inj _ _ _ _ _ _ _ _ _ H) as (<- & <- & <-);
            split; [exact F2|]; rewrite den_sv_alu; cbn [den alu64 alu]; bv_solve).
  destruct (IMap.find k1 R) as [r1|] eqn:F1.
  - destruct (some3_inj _ _ _ _ _ _ _ _ _ H) as (<- & <- & <-). split; [exact F1|]. rewrite den_sv_alu. cbn [den alu64 alu]. bv_solve.
  - destruct y as [|k2 o2| | | | | | | | |]; try discriminate.
    destruct (IMap.find k2 R) as [r2|] eqn:F2; [|discriminate].
    destruct (some3_inj _ _ _ _ _ _ _ _ _ H) as (<- & <- & <-).
    split; [exact F2|]. cbn [den alu64 alu]. rewrite wbv_wadd. bv_solve.
Qed.

Lemma andb4 : forall a b, a && b = true -> a = true /\ b = true.
Proof. intros a b H. apply andb_prop in H. exact H. Qed.

Lemma can_read_sym_sound : forall E fs k r off w j, facts_hold E fs ->
  can_read_sym fs k r off w = Some j ->
  PrimInt63.eqb k 0%uint63 = false /\ rg_cells r = IMap.Leaf /\ rg_bg r = BGBlob j 0%uint63 /\ loZ r = 0
  /\ 1 <= to_Z w <= 8
  /\ bv_unsigned (den E off) + to_Z w <= hiZ E r.
Proof.
  intros E fs k r off w j Hfs H. unfold can_read_sym in H.
  destruct (PrimInt63.eqb k 0%uint63) eqn:K; [discriminate|].
  destruct (rg_cells r) eqn:RC; [|discriminate].
  destruct (rg_bg r) as [| | | |j' sh] eqn:BG; try discriminate.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end.
  injection H as ->.
  destruct (andb4 _ _ C) as [C5 L2]. destruct (andb4 _ _ C5) as [C4 L1]. destruct (andb4 _ _ C4) as [C3 W8].
  destruct (andb4 _ _ C3) as [C2 W0]. destruct (andb4 _ _ C2) as [SH LO].
  apply eqb_correct in SH. subst sh. apply eqb_correct in LO.
  apply ltb_spec in W0. apply leb_spec in W8. change (to_Z 0%uint63) with 0 in W0. change (to_Z 8%uint63) with 8 in W8.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [unfold loZ; rewrite LO; reflexivity|].
  split; [lia|].

  assert (DTI : forall x, dec_true x = true -> x = Some true) by (intros [[|]|]; cbn; congruence).
  assert (DFI : forall x, dec_false x = true -> x = Some false) by (intros [[|]|]; cbn; congruence).
  unfold hiZ.
  pose proof (DTI _ L1) as D1.
  apply (decide_ltu_sound E fs Hfs) in D1. apply (proj1 (ltu_iff _ _ true)) in D1.
  apply orb_prop in L2. destruct L2 as [W1|L2].
  - apply eqb_correct in W1. subst w. change (to_Z 1%uint63) with 1. lia.
  - destruct (andb4 _ _ L2) as [L3 L4].
    set (last := sv_alu ALU_ADD off (VL (wlit (PrimInt63.sub w 1)))) in *.
    pose proof (DTI _ L3) as D2. pose proof (DFI _ L4) as D3.
    apply (decide_ltu_sound E fs Hfs) in D2. apply (proj1 (ltu_iff _ _ true)) in D2.
    apply (decide_ltu_sound E fs Hfs) in D3. apply (proj1 (ltu_iff _ _ false)) in D3.
    assert (DL : bv_unsigned (den E last) = (bv_unsigned (den E off) + (to_Z w - 1)) mod two64).
    { subst last. rewrite den_sv_alu. cbn [den alu64 alu]. rewrite bv_add_unsigned. unfold wbv. rewrite wlit_ok, Z_to_bv_unsigned.
      rewrite sub_spec. change (to_Z 1%uint63) with 1. pose proof (int_range w).
      rewrite (Z.mod_small (to_Z w - 1)) by (rewrite wB_two63 in *; unfold two63 in *; lia).
      unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.add_mod_idemp_r by (unfold two64; lia). reflexivity. }
    pose proof (bv_unsigned_in_range 64 (den E off)) as Ro. rewrite bv_modulus_64 in Ro.
    rewrite DL in D2, D3. rewrite (mod_cases2 _ two64) in D2, D3 by (unfold two64 in *; lia).
    destruct (Z.ltb_spec (bv_unsigned (den E off) + (to_Z w - 1)) two64); unfold two64 in *; lia.
Qed.

Lemma sym_load_sound : forall priv E m k r off w sx j,
  ev E 0%uint63 = Z_to_bv 64 0 -> region_ok segs priv E m k r ->
  PrimInt63.eqb k 0%uint63 = false -> rg_cells r = IMap.Leaf -> rg_bg r = BGBlob j 0%uint63 -> loZ r = 0 ->
  1 <= to_Z w <= 8 -> bv_unsigned (den E off) + to_Z w <= hiZ E r ->
  let A := bv_unsigned (ev E k) + bv_unsigned (den E off) in
  0 <= A /\ A + to_Z w <= two64 /\
  exists bs, length bs = Z.to_nat (to_Z w)
    /\ ov_read_bytes segs m (Z_to_bv 64 A) (Z.to_nat (to_Z w)) = Some bs
    /\ den E (sv_ext sx 0%uint63 w (VBlob false j off w)) = bytes_val sx (to_Z w) bs.
Proof.
  intros priv E m k r off w sx j Hz RO K RC BG LO Hw HI. cbv zeta.
  set (U := bv_unsigned (den E off)) in *.
  pose proof (bv_unsigned_in_range 64 (den E off)) as RU. rewrite bv_modulus_64 in RU. fold U in RU.
  pose proof (bv_unsigned_in_range 64 (ev E k)) as RB. rewrite bv_modulus_64 in RB.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [R1 R2].
  split; [lia|]. split; [unfold two64 in *; lia|].
  set (L0 := blob_bytes (eb E j) U (to_Z w)).
  destruct (bytes_val_false (to_Z w) L0 Hw) as (D & R & By).
  apply (load_finish segs E m _ w sx _ (ext_Z false 0 (to_Z w) (bytes_le_to_Z L0))); try lia.
  - rewrite den_sv_ext by (unfold width_ok; change (to_Z 0%uint63) with 0; lia). unfold ext_word.
    cbn [den]. fold U. fold L0. rewrite D. change (to_Z 0%uint63) with 0. reflexivity.
  - intros t Ht.
    assert (UC : uncovered r (U + t)).
    { intros g gr _ F. rewrite RC in F. cbn in F. discriminate. }
    pose proof (ro_bg _ _ _ _ _ _ RO (U + t) ltac:(intros _; lia) ltac:(intros X; rewrite K in X; discriminate X) UC) as G.
    unfold bg_byte in G. rewrite BG in G.
    exists (nth (Z.to_nat (U + t - to_Z 0%uint63)) (eb E j) (Z_to_bv 8 0)). split.
    + rewrite <- G. f_equal. lia.
    + rewrite By by exact Ht. f_equal. subst L0. unfold blob_bytes. rewrite nth_firstn_lt by lia. rewrite nth_skipn. f_equal.
      change (to_Z 0%uint63) with 0. lia.
Qed.

Lemma can_read_symz_sound : forall E fs k r off w, facts_hold E fs ->
  can_read_symz fs k r off w = true ->
  PrimInt63.eqb k 0%uint63 = false /\ rg_cells r = IMap.Leaf /\ rg_bg r = BGZero /\ loZ r = 0
  /\ 1 <= to_Z w <= 8
  /\ bv_unsigned (den E off) + to_Z w <= hiZ E r.
Proof.
  intros E fs k r off w Hfs H. unfold can_read_symz in H.
  destruct (PrimInt63.eqb k 0%uint63) eqn:K; [discriminate|].
  destruct (rg_cells r) eqn:RC; [|discriminate].
  destruct (rg_bg r) eqn:BG; try discriminate.
  rename H into C.
  destruct (andb4 _ _ C) as [C4 L2]. destruct (andb4 _ _ C4) as [C3 L1]. destruct (andb4 _ _ C3) as [C2 W8].
  destruct (andb4 _ _ C2) as [LO W0].
  apply eqb_correct in LO.
  apply ltb_spec in W0. apply leb_spec in W8. change (to_Z 0%uint63) with 0 in W0. change (to_Z 8%uint63) with 8 in W8.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [unfold loZ; rewrite LO; reflexivity|].
  split; [lia|].
  assert (DTI : forall x, dec_true x = true -> x = Some true) by (intros [[|]|]; cbn; congruence).
  assert (DFI : forall x, dec_false x = true -> x = Some false) by (intros [[|]|]; cbn; congruence).
  unfold hiZ.
  pose proof (DTI _ L1) as D1.
  apply (decide_ltu_sound E fs Hfs) in D1. apply (proj1 (ltu_iff _ _ true)) in D1.
  apply orb_prop in L2. destruct L2 as [W1|L2].
  - apply eqb_correct in W1. subst w. change (to_Z 1%uint63) with 1. lia.
  - destruct (andb4 _ _ L2) as [L3 L4].
    set (last := sv_alu ALU_ADD off (VL (wlit (PrimInt63.sub w 1)))) in *.
    pose proof (DTI _ L3) as D2. pose proof (DFI _ L4) as D3.
    apply (decide_ltu_sound E fs Hfs) in D2. apply (proj1 (ltu_iff _ _ true)) in D2.
    apply (decide_ltu_sound E fs Hfs) in D3. apply (proj1 (ltu_iff _ _ false)) in D3.
    assert (DL : bv_unsigned (den E last) = (bv_unsigned (den E off) + (to_Z w - 1)) mod two64).
    { subst last. rewrite den_sv_alu. cbn [den alu64 alu]. rewrite bv_add_unsigned. unfold wbv. rewrite wlit_ok, Z_to_bv_unsigned.
      rewrite sub_spec. change (to_Z 1%uint63) with 1. pose proof (int_range w).
      rewrite (Z.mod_small (to_Z w - 1)) by (rewrite wB_two63 in *; unfold two63 in *; lia).
      unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.add_mod_idemp_r by (unfold two64; lia). reflexivity. }
    pose proof (bv_unsigned_in_range 64 (den E off)) as Ro. rewrite bv_modulus_64 in Ro.
    rewrite DL in D2, D3. rewrite (mod_cases2 _ two64) in D2, D3 by (unfold two64 in *; lia).
    destruct (Z.ltb_spec (bv_unsigned (den E off) + (to_Z w - 1)) two64); unfold two64 in *; lia.
Qed.

Lemma symz_load_sound : forall priv E m k r off w sx,
  ev E 0%uint63 = Z_to_bv 64 0 -> region_ok segs priv E m k r ->
  PrimInt63.eqb k 0%uint63 = false -> rg_cells r = IMap.Leaf -> rg_bg r = BGZero -> loZ r = 0 ->
  1 <= to_Z w <= 8 -> bv_unsigned (den E off) + to_Z w <= hiZ E r ->
  let A := bv_unsigned (ev E k) + bv_unsigned (den E off) in
  0 <= A /\ A + to_Z w <= two64 /\
  exists bs, length bs = Z.to_nat (to_Z w)
    /\ ov_read_bytes segs m (Z_to_bv 64 A) (Z.to_nat (to_Z w)) = Some bs
    /\ den E (VL wzero) = bytes_val sx (to_Z w) bs.
Proof.
  intros priv E m k r off w sx Hz RO K RC BG LO Hw HI. cbv zeta.
  set (U := bv_unsigned (den E off)) in *.
  pose proof (bv_unsigned_in_range 64 (den E off)) as RU. rewrite bv_modulus_64 in RU. fold U in RU.
  pose proof (bv_unsigned_in_range 64 (ev E k)) as RB. rewrite bv_modulus_64 in RB.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [R1 R2].
  split; [lia|]. split; [unfold two64 in *; lia|].
  apply (load_finish segs E m _ w sx _ 0); try lia.
  - cbn [den]. apply bv_eq. rewrite wbv_unsigned, wzero_ok, Z_to_bv_unsigned.
    assert (EZ : ext_Z sx 0 (to_Z w) 0 = 0).
    { unfold ext_Z. rewrite Z.div_0_l by (apply Z.pow_nonzero; lia). rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
      destruct sx; [|reflexivity].
      assert (P : 0 < 2 ^ (8 * to_Z w - 1)) by (apply Z.pow_pos_nonneg; lia).
      destruct (Z.leb_spec (2 ^ (8 * to_Z w - 1)) 0); [lia|]. reflexivity. }
    rewrite EZ. reflexivity.
  - intros t Ht.
    assert (UC : uncovered r (U + t)).
    { intros g gr _ F. rewrite RC in F. cbn in F. discriminate. }
    pose proof (ro_bg _ _ _ _ _ _ RO (U + t) ltac:(intros _; lia) ltac:(intros X; rewrite K in X; discriminate X) UC) as G.
    unfold bg_byte in G. rewrite BG in G.
    exists (Z_to_bv 8 0). split.
    + rewrite <- G. f_equal. lia.
    + unfold zbyte. rewrite Z.div_0_l, Z.mod_0_l by (try (apply Z.pow_nonzero; lia); lia). reflexivity.
Qed.

Lemma do_load_sound : forall E st ms model a w sx v,
  st_ok segs OPS E st ms model -> wok w ->
  do_load segs st a w sx = inl (Some v) ->
  exists bs, length bs = Z.to_nat (to_Z w)
    /\ ov_read_bytes segs (ms_mem ms) (den E a) (Z.to_nat (to_Z w)) = Some bs
    /\ den E v = ext_word sx 0 (to_Z w) (le_bytes_to_word bs).
Proof.
  intros E st ms model a w sx v HS Hw H. unfold do_load in H.
  pose proof (so_zero _ _ _ _ _ _ HS) as Hz. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  destruct (addr_of a) as [[k o]|] eqn:Ha.
  - destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
    destruct (okey o) as [key|] eqn:Hk; [|discriminate].
    destruct (can_read segs (s_facts st) (s_priv st) k r key w) eqn:CR; [|discriminate].
    destruct (Mem.region_load segs k r key w sx) as [v'|] eqn:RL; [|discriminate].
    apply inl_inj, Some_inj in H. subst v. rewrite (den_narrow_f E (s_facts st) Hfs).
    pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO.
    destruct (region_load_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key w sx v' Hfs Hz RO Hw CR RL)
      as (bs & Len & OV & Dv).
    pose proof (can_read_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key w Hfs Hz RO Hw CR) as (RA & RAw & _).
    exists bs. split; [exact Len|]. split.
    + rewrite (access_addr E a k o key (addrZ E k key) Hz Ha Hk eq_refl RA ltac:(lia)). exact OV.
    + rewrite Dv. apply bytes_val_ext_word; [exact Len| exact Hw8].
  - destruct (sym_addr_of (s_regs st) a) as [[[k r] off]|] eqn:SA; [|discriminate].
    destruct (can_read_sym (s_facts st) k r off w) as [j|] eqn:CS.
    2: {
         destruct (can_read_symz (s_facts st) k r off w) eqn:CZ; [|discriminate].
         apply inl_inj, Some_inj in H. subst v.
         destruct (sym_addr_of_sound E (s_regs st) a k r off SA) as [Hr Da].
         destruct (can_read_symz_sound E (s_facts st) k r off w Hfs CZ) as (K & RC & BG & LO & _ & HI).
         pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO.
         destruct (symz_load_sound (s_priv st) E (ms_mem ms) k r off w sx Hz RO K RC BG LO Hw8 HI) as (RA & RAw & bs & Len & OV & Dv).
         exists bs. split; [exact Len|]. split.
         + rewrite Da. replace (ev E k + den E off)%bv with (Z_to_bv 64 (bv_unsigned (ev E k) + bv_unsigned (den E off))); [exact OV|].
           apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity.
         + rewrite Dv. apply bytes_val_ext_word; [exact Len| exact Hw8]. }
    apply inl_inj, Some_inj in H. subst v.
    destruct (sym_addr_of_sound E (s_regs st) a k r off SA) as [Hr Da].
    destruct (can_read_sym_sound E (s_facts st) k r off w j Hfs CS) as (K & RC & BG & LO & _ & HI).
    pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO.
    destruct (sym_load_sound (s_priv st) E (ms_mem ms) k r off w sx j Hz RO K RC BG LO Hw8 HI) as (RA & RAw & bs & Len & OV & Dv).
    exists bs. split; [exact Len|]. split.
    + rewrite Da. replace (ev E k + den E off)%bv with (Z_to_bv 64 (bv_unsigned (ev E k) + bv_unsigned (den E off))); [exact OV|].
      apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity.
    + rewrite Dv. apply bytes_val_ext_word; [exact Len| exact Hw8].
Qed.

Section SameRange.
Variables (E : env) (R : IMap.t region) (k : int) (r r' : region).
Hypothesis HB : IMap.bst R.
Hypothesis Hf : IMap.find k R = Some r.
Hypothesis Hlo : rg_lo r' = rg_lo r.
Hypothesis Hhi : rg_hi r' = rg_hi r.

Lemma find_add_cases : forall k1 r1, IMap.find k1 (IMap.add k r' R) = Some r1 ->
  exists r0, IMap.find k1 R = Some r0 /\ loZ r1 = loZ r0 /\ hiZ E r1 = hiZ E r0
    /\ ((k1 = k /\ r1 = r') \/ (k <> k1 /\ r1 = r0)).
Proof.
  intros k1 r1 H. destruct (eqbP k k1) as [X|X].
  - apply to_Z_inj in X. subst k1. rewrite IMap.find_add_same in H by exact HB. injection H as <-.
    exists r. unfold loZ, hiZ. rewrite Hlo, Hhi. split; [exact Hf|]. split; [reflexivity|]. split; [reflexivity|]. left; auto.
  - assert (N : k <> k1) by (intros Y; apply X; rewrite Y; reflexivity).
    rewrite IMap.find_add_other in H by assumption. exists r1. split; [exact H|]. split; [reflexivity|]. split; [reflexivity|]. right; auto.
Qed.

Lemma same_range_disjoint : rg_w r' = rg_w r -> regions_disjoint E R -> regions_disjoint E (IMap.add k r' R).
Proof.
  intros HW D k1 r1 k2 r2 H1 H2 N K1 K2 W a.
  destruct (find_add_cases k1 r1 H1) as (r10 & G1 & L1 & M1 & C1).
  destruct (find_add_cases k2 r2 H2) as (r20 & G2 & L2 & M2 & C2).
  rewrite L1, M1, L2, M2. apply (D k1 r10 k2 r20 G1 G2 N K1 K2).
  destruct C1 as [[E1 ->]|[_ ->]]; destruct C2 as [[E2 ->]|[_ ->]].
  - exfalso. apply N. congruence.
  - subst k1. rewrite Hf in G1. injection G1 as <-. rewrite <- HW. exact W.
  - subst k2. rewrite Hf in G2. injection G2 as <-. rewrite <- HW. exact W.
  - exact W.
Qed.

Lemma same_range_in_based : forall a, in_based E (IMap.add k r' R) a -> in_based E R a.
Proof.
  intros a (k1 & r1 & H1 & K1 & Ha). destruct (find_add_cases k1 r1 H1) as (r10 & G1 & L1 & M1 & _).
  exists k1, r10. rewrite <- L1, <- M1. auto.
Qed.
End SameRange.

Lemma pub_of_regions : forall priv E m R,
  (forall k r, IMap.find k R = Some r -> region_ok segs priv E m k r) -> abs_cells_public priv R.
Proof.
  intros priv E m R H r g gr c Hr Hg Hc i Hi.
  pose proof (ro_cells_in _ _ _ _ _ _ (H _ _ Hr) g gr c i Hg Hc Hi) as [_ P]. cbv zeta in P.
  exact (proj2 (proj2 (P eq_refl))).
Qed.

Lemma store_sound : forall E st ms model a k o r key w v rv mrv,
  st_ok segs OPS E st ms model -> wok w ->
  addr_of a = Some (k, o) -> IMap.find k (s_regs st) = Some r -> okey o = Some key ->
  can_write segs (s_facts st) (s_priv st) k r key w = true ->
  resv_ok E rv mrv ->
  store_ok segs (ms_mem ms) (den E a) (Z.to_nat (to_Z w)) = true
  /\ st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) rv (IMap.add k (Mem.region_store r key w v) (s_regs st))
                        (s_facts st) (s_ops st) (s_priv st) (s_next st))
          (ms_upd ms (with_resv mrv (core_of ms)) (write_to_mem (ms_mem ms) (den E a) (store_bytes w (den E v)))) model.
Proof.
  intros E st ms model a k o r key w v rv mrv HS Hw Ha Hr Hk CW Hrv.
  pose proof HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops Hapart Hmf Hcov Hminv].
  pose proof (Hreg k r Hr) as RO.
  destruct (region_store_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key w v Hfacts Hz RO Hw CW)
    as (SOK & RO' & F1 & F2 & F3 & F4 & FR).
  destruct (can_write_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key w Hfacts Hz RO Hw CW) as (CR & WB & SEGW).
  destruct (can_read_sound segs (s_priv st) E (ms_mem ms) (s_facts st) k r key w Hfacts Hz RO Hw CR) as (RA & RAw & RB & RNG & ABS).
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  cbv zeta in *. unfold addrZ in *.
  set (A := bv_unsigned (ev E k) + keyZ key) in *.
  rewrite (access_addr E a k o key A Hz Ha Hk eq_refl RA ltac:(lia)).
  set (m' := write_to_mem (ms_mem ms) (Z_to_bv 64 A) (store_bytes w (den E v))) in *.
  split; [exact SOK|].

  assert (W1 : forall a0, A <= a0 < A + to_Z w -> PrimInt63.eqb k 0%uint63 = false ->
            bv_unsigned (ev E k) + loZ r <= a0 < bv_unsigned (ev E k) + hiZ E r).
  { intros a0 Ha0 K. pose proof (RNG K (a0 - A) ltac:(lia)). subst A. lia. }
  assert (W2 : forall a0, A <= a0 < A + to_Z w -> PrimInt63.eqb k 0%uint63 = true ->
            (exists seg, find_segment segs a0 1 = Some seg) /\ ~ in_priv (s_priv st) a0).
  { intros a0 Ha0 K. destruct (ABS K (a0 - A) ltac:(lia)) as [[bs M] P].
    replace (A + (a0 - A)) with a0 in M, P by lia. split; [| exact P].
    apply (memory_read_find_segment segs a0 bs); [lia| exact M]. }

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
  assert (REG : forall k1 r1, IMap.find k1 (IMap.add k (Mem.region_store r key w v) (s_regs st)) = Some r1 ->
            region_ok segs (s_priv st) E m' k1 r1).
  { intros k1 r1 H1.
    destruct (find_add_cases E (s_regs st) k r (Mem.region_store r key w v) Hbst Hr F1 F2 k1 r1 H1)
      as (r0 & G0 & _ & _ & [[-> ->]|[N ->]]); [exact RO'|].
    apply (region_ok_frame segs (s_priv st) E (ms_mem ms) m' k1 r0 Hz (Hreg k1 r0 G0)).
    intros a0 Ha0 V1 V2. apply FR; [exact Ha0|]. exact (OTHER k1 r0 a0 G0 N Ha0 V1 V2). }
  split; cbn_st; try assumption; try reflexivity.
  - apply IMap.bst_add. exact Hbst.
  - apply (same_range_disjoint E (s_regs st) k r); assumption.
  - exact (pub_of_regions (s_priv st) E m' _ REG).
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
    intros IB. apply NB. apply (same_range_in_based E (s_regs st) k r (Mem.region_store r key w v)); assumption.
  -
    intros a0 [IB|SG]; apply Hcov; [left | right; exact SG].
    apply (same_range_in_based E (s_regs st) k r (Mem.region_store r key w v)); assumption.
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

Definition mresv_after (a : word) (mr : option word) : option word :=
  match mr with
  | Some r => if Z.eqb (bv_unsigned r) (bv_unsigned a) then None else mr
  | None => None
  end.

Lemma inval_resv_eq : forall a c, inval_resv a c = with_resv (mresv_after a (c_resv c)) c.
Proof.
  intros a [rg fr pc fc rv]. unfold inval_resv, mresv_after. cbn [c_resv with_resv].
  destruct rv as [r|]; [destruct (Z.eqb _ _)|]; reflexivity.
Qed.

Lemma resv_after_store_ok : forall E fs rv mr a, facts_hold E fs -> resv_ok E rv mr ->
  resv_ok E (resv_after_store fs rv a) (mresv_after (den E a) mr).
Proof.
  intros E fs rv mr a Hfs H. destruct rv as [|a'|]; cbn [resv_after_store resv_ok] in *.
  - subst mr. reflexivity.
  - subst mr. unfold mresv_after. destruct (decide_eq fs a' a) as [[|]|] eqn:D; cbn [resv_ok].
    + apply (decide_eq_sound E fs Hfs) in D. apply (proj1 (eqb_iff _ _ true)) in D. rewrite D, Z.eqb_refl. reflexivity.
    + apply (decide_eq_sound E fs Hfs) in D. apply (proj1 (eqb_iff _ _ false)) in D.
      destruct (Z.eqb_spec (bv_unsigned (den E a')) (bv_unsigned (den E a))) as [X|X]; [|reflexivity].
      exfalso. apply D. apply bv_eq. exact X.
    + exact I.
  - exact I.
Qed.

Lemma st_ok_resv : forall E st ms model rv mrv,
  st_ok segs OPS E st ms model -> resv_ok E rv mrv ->
  st_ok segs OPS E (setresv st rv) (ms_upd ms (with_resv mrv (core_of ms)) (ms_mem ms)) model.
Proof.
  intros E st ms model rv mrv HS Hrv.
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops Hapart Hmf].
  split; cbn_st; try assumption; try reflexivity.
Qed.

Lemma st_ok_ms_eq : forall E st st2 ms ms2 model,
  st_ok segs OPS E st ms model -> st = st2 -> ms = ms2 -> st_ok segs OPS E st2 ms2 model.
Proof. intros; subst; assumption. Qed.

Lemma do_store_inv : forall st a w v st', do_store segs st a w v = inl st' ->
  exists k o r key, addr_of a = Some (k, o) /\ IMap.find k (s_regs st) = Some r /\ okey o = Some key
    /\ can_write segs (s_facts st) (s_priv st) k r key w = true
    /\ st' = SS (s_pc st) (s_rf st) (s_ff st) (resv_after_store (s_facts st) (s_resv st) a)
                (IMap.add k (Mem.region_store r key w v) (s_regs st)) (s_facts st) (s_ops st) (s_priv st) (s_next st).
Proof.
  intros st a w v st' H. unfold do_store in H.
  destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
  destruct (okey o) as [key|] eqn:Hk; [|discriminate].
  destruct (can_write segs (s_facts st) (s_priv st) k r key w) eqn:CW; [|discriminate].
  apply inl_inj in H. subst st'. exists k, o, r, key. split; [reflexivity|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact CW| reflexivity].
Qed.

Lemma Z_to_le_bytes_mod : forall n z K, 8 * Z.of_nat n <= K -> Z_to_le_bytes n (z mod 2 ^ K) = Z_to_le_bytes n z.
Proof. intros n z K HK. apply Z_to_le_bytes_ext. intros t Ht. apply zbyte_mod; lia. Qed.

Lemma store_bytes_8 : forall v : word, Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 v)) = store_bytes 1%uint63 v.
Proof.
  intros v. rewrite bv_extract_0_unsigned. unfold store_bytes. change (Z.to_nat (to_Z 1%uint63)) with 1%nat.
  change (bv_wrap 8 (bv_unsigned v)) with (bv_unsigned v mod 2 ^ 8). apply Z_to_le_bytes_mod. cbn; lia.
Qed.
Lemma store_bytes_16 : forall v : word, Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 v)) = store_bytes 2%uint63 v.
Proof.
  intros v. rewrite bv_extract_0_unsigned. unfold store_bytes. change (Z.to_nat (to_Z 2%uint63)) with 2%nat.
  change (bv_wrap 16 (bv_unsigned v)) with (bv_unsigned v mod 2 ^ 16). apply Z_to_le_bytes_mod. cbn; lia.
Qed.
Lemma store_bytes_32 : forall v : word, Z_to_le_bytes 4 (bv_unsigned (low32 v)) = store_bytes 4%uint63 v.
Proof.
  intros v. unfold low32. rewrite bv_extract_0_unsigned. unfold store_bytes. change (Z.to_nat (to_Z 4%uint63)) with 4%nat.
  change (bv_wrap 32 (bv_unsigned v)) with (bv_unsigned v mod 2 ^ 32). apply Z_to_le_bytes_mod. cbn; lia.
Qed.
Lemma store_bytes_64 : forall v : word, Z_to_le_bytes 8 (bv_unsigned v) = store_bytes 8%uint63 v.
Proof. intros v. reflexivity. Qed.

Lemma store_bytes_eqm32 : forall (x : bv 32) (nv : word),
  eqm 32 (bv_unsigned x) (bv_unsigned nv) -> Z_to_le_bytes 4 (bv_unsigned x) = store_bytes 4%uint63 nv.
Proof.
  intros x nv H. unfold store_bytes. change (Z.to_nat (to_Z 4%uint63)) with 4%nat.
  apply Z_to_le_bytes_ext. intros t Ht. unfold eqm in H.
  rewrite <- (zbyte_mod (bv_unsigned x) 32), <- (zbyte_mod (bv_unsigned nv) 32) by lia. rewrite H. reflexivity.
Qed.

Lemma eqm_testbit : forall m a b, 0 <= m ->
  (eqm m a b <-> forall i, 0 <= i < m -> Z.testbit a i = Z.testbit b i).
Proof.
  intros m a b Hm. unfold eqm. split.
  - intros H i Hi. rewrite <- (Z.mod_pow2_bits_low a m i), <- (Z.mod_pow2_bits_low b m i) by lia. rewrite H. reflexivity.
  - intros H. apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i m).
    + rewrite !Z.mod_pow2_bits_low by lia. apply H. lia.
    + rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma eqm_bitwise : forall (f : Z -> Z -> Z) (g : bool -> bool -> bool) m a a' b b', 0 <= m ->
  (forall x y i, Z.testbit (f x y) i = g (Z.testbit x i) (Z.testbit y i)) ->
  eqm m a a' -> eqm m b b' -> eqm m (f a b) (f a' b').
Proof.
  intros f g m a a' b b' Hm Hf Ha Hb. apply (proj2 (eqm_testbit m _ _ Hm)). intros i Hi.
  rewrite !Hf. f_equal; [apply (proj1 (eqm_testbit m _ _ Hm) Ha) | apply (proj1 (eqm_testbit m _ _ Hm) Hb)]; exact Hi.
Qed.

Lemma sext32_eqm : forall o : bv 32, eqm 32 (bv_unsigned (sext 64 o)) (bv_unsigned o).
Proof.
  intros o. unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed.
  eapply eqm_trans; [apply eqm_wrap64; lia|]. apply bv_swrap32_eqm. lia.
Qed.

Lemma amo32_eqm : forall op (aop : aluop) (o : bv 32) (s : word),
  match op with
  | AMO_ADD => aop = ALU_ADD | AMO_XOR => aop = ALU_XOR | AMO_AND => aop = ALU_AND | AMO_OR => aop = ALU_OR
  | _ => False
  end ->
  eqm 32 (bv_unsigned (amo_val op o (low32 s))) (bv_unsigned (alu64 aop (sext 64 o) s)).
Proof.
  intros op aop o s H. destruct op; try contradiction; subst aop; cbn [amo_val alu64 alu].
  - rewrite !bv_add_unsigned. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite bv_modulus_64.
    eapply eqm_trans; [apply eqm_mod; lia|]. apply eqm_sym. eapply eqm_trans; [apply eqm_mod64; lia|].
    apply eqm_add; [apply sext32_eqm| apply eqm_sym, low32_eqm; lia].
  - rewrite !bv_xor_unsigned. apply (eqm_bitwise Z.lxor xorb); [lia| intros; apply Z.lxor_spec | apply eqm_sym, sext32_eqm | apply low32_eqm; lia].
  - rewrite !bv_and_unsigned. apply (eqm_bitwise Z.land andb); [lia| intros; apply Z.land_spec | apply eqm_sym, sext32_eqm | apply low32_eqm; lia].
  - rewrite !bv_or_unsigned. apply (eqm_bitwise Z.lor orb); [lia| intros; apply Z.lor_spec | apply eqm_sym, sext32_eqm | apply low32_eqm; lia].
Qed.

Lemma Z_to_bv64_mod : forall z, Z_to_bv 64 (z mod two64) = Z_to_bv 64 z.
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. apply Zmod_mod. Qed.
Lemma wbv_Z2w : forall z, wbv (Z2w z) = Z_to_bv 64 z.
Proof. intros z. unfold wbv. rewrite Z2w_ok. apply Z_to_bv64_mod. Qed.
Lemma wbv_w_of_imm : forall n (b : bv n), wbv (w_of_imm b) = sext 64 b.
Proof. intros n b. unfold w_of_imm. rewrite wbv_Z2w. reflexivity. Qed.

Lemma getr_den : forall E st ms model r r', st_ok segs OPS E st ms model -> r5_of_reg r' = Some r ->
  rget (core_of ms) r' = den E (getr st r).
Proof. intros E st ms model r r' HS H. rewrite <- (reg_of_r5_of_reg r' r H). exact (so_regs _ _ _ _ _ _ HS r). Qed.

Lemma getf_den : forall E st ms model r r', st_ok segs OPS E st ms model -> r5_of_reg r' = Some r ->
  fget (core_of ms) r' = den E (getf st r).
Proof. intros E st ms model r r' HS H. rewrite <- (reg_of_r5_of_reg r' r H). exact (so_fregs _ _ _ _ _ _ HS r). Qed.

Lemma ea_den : forall E st ms model rs1 rs1' n (imm : bv n), st_ok segs OPS E st ms model -> r5_of_reg rs1' = Some rs1 ->
  (rget (core_of ms) rs1' + sext 64 imm)%bv = den E (sv_alu ALU_ADD (getr st rs1) (VL (w_of_imm imm))).
Proof.
  intros E st ms model rs1 rs1' n imm HS H. rewrite den_sv_alu. cbn [den alu64 alu].
  rewrite (getr_den E st ms model rs1 rs1' HS H), wbv_w_of_imm. reflexivity.
Qed.

Lemma npc_eq : forall E st ms model, st_ok segs OPS E st ms model -> PrimInt63.ltb (s_pc st) bit62i = true ->
  (c_pc (core_of ms) + Z_to_bv 64 4)%bv = Z_to_bv 64 (to_Z (pc4 st)).
Proof.
  intros E st ms model HS Hpc. unfold pc4. rewrite (pc4_ok _ Hpc). cbn [c_pc core_of].
  rewrite (so_pc _ _ _ _ _ _ HS). reflexivity.
Qed.

Lemma msize_wok : forall sz, wok (msize_bytes sz).
Proof. intros sz; unfold wok; destruct sz; cbn [msize_bytes]; [left| right; left| right; right; left| right; right; right]; reflexivity. Qed.

Lemma awidth_wok : forall wd, wok (awidth_bytes wd).
Proof. intros wd; unfold wok; destruct wd; cbn [awidth_bytes]; [right; right; left| right; right; right]; reflexivity. Qed.

Lemma amo_aligned_ok : forall E fs a wd, facts_hold E fs -> aligned fs a (awidth_log wd) = true ->
  amo_aligned wd (den E a) = true.
Proof.
  intros E fs a wd Hfs H. unfold amo_aligned.
  assert (L : to_Z (awidth_log wd) <= 62)
    by (destruct wd; [change (to_Z (awidth_log AW)) with 2 | change (to_Z (awidth_log AD)) with 3]; lia).
  pose proof (aligned_sound E fs Hfs a (awidth_log wd) H L) as A.
  replace (amo_bytes wd) with (2 ^ to_Z (awidth_log wd)) by (destruct wd; reflexivity).
  rewrite A. reflexivity.
Qed.

Lemma low32_zext32 : forall y : bv 32, low32 (zext 64 y) = y.
Proof.
  intros y. apply bv_eq. unfold low32, zext. rewrite bv_extract_0_unsigned, bv_zero_extend_unsigned by lia.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Ltac do_ex := repeat match goal with |- exists _, _ => eexists end; split; [reflexivity|]; auto.
Ltac inv_of H :=
  unfold of_instr in H;
  repeat match type of H with
  | context [match r5_of_reg ?r with _ => _ end] => destruct (r5_of_reg r) eqn:?
  | context [match ?x with _ => _ end] => destruct x eqn:?
  end; try discriminate H.

Lemma of_instr_ILoad : forall i sz sx rd rs1 off, of_instr i = Some (ILoad sz sx rd rs1 off) ->
  exists rd' rs1' imm, i = Load sz sx rd' rs1' imm /\ r5_of_reg rd' = Some rd /\ r5_of_reg rs1' = Some rs1 /\ off = w_of_imm imm.
Proof. intros i sz sx rd rs1 off H; destruct i; inv_of H; injection H; intros; subst; do_ex. Qed.

Lemma of_instr_IStore : forall i sz rs1 rs2 off, of_instr i = Some (IStore sz rs1 rs2 off) ->
  exists rs1' rs2' imm, i = Store sz rs1' rs2' imm /\ r5_of_reg rs1' = Some rs1 /\ r5_of_reg rs2' = Some rs2 /\ off = w_of_imm imm.
Proof. intros i sz rs1 rs2 off H; destruct i; inv_of H; injection H; intros; subst; do_ex. Qed.

Lemma of_instr_ILr : forall i wd rd rs1, of_instr i = Some (ILr wd rd rs1) ->
  exists aq rl rd' rs1', i = Lr wd aq rl rd' rs1' /\ r5_of_reg rd' = Some rd /\ r5_of_reg rs1' = Some rs1.
Proof. intros i wd rd rs1 H; destruct i; inv_of H; injection H; intros; subst; do_ex. Qed.

Lemma of_instr_ISc : forall i wd rd rs1 rs2, of_instr i = Some (ISc wd rd rs1 rs2) ->
  exists aq rl rd' rs1' rs2', i = Sc wd aq rl rd' rs1' rs2' /\ r5_of_reg rd' = Some rd /\ r5_of_reg rs1' = Some rs1 /\ r5_of_reg rs2' = Some rs2.
Proof. intros i wd rd rs1 rs2 H; destruct i; inv_of H; injection H; intros; subst; do_ex. Qed.

Lemma of_instr_IAmo : forall i op wd rd rs1 rs2, of_instr i = Some (IAmo op wd rd rs1 rs2) ->
  exists aq rl rd' rs1' rs2', i = Amo op wd aq rl rd' rs1' rs2' /\ r5_of_reg rd' = Some rd /\ r5_of_reg rs1' = Some rs1 /\ r5_of_reg rs2' = Some rs2.
Proof. intros i op wd rd rs1 rs2 H; destruct i; inv_of H; injection H; intros; subst; do_ex. Qed.

Lemma of_instr_IFLoad : forall i fmt rd rs1 off, of_instr i = Some (IFLoad fmt rd rs1 off) ->
  exists rd' rs1' imm, i = FLoad fmt rd' rs1' imm /\ r5_of_reg rd' = Some rd /\ r5_of_reg rs1' = Some rs1 /\ off = w_of_imm imm.
Proof. intros i fmt rd rs1 off H; destruct i; inv_of H; injection H; intros; subst; do_ex. Qed.

Lemma of_instr_IFStore : forall i fmt rs1 rs2 off, of_instr i = Some (IFStore fmt rs1 rs2 off) ->
  exists rs1' rs2' imm, i = FStore fmt rs1' rs2' imm /\ r5_of_reg rs1' = Some rs1 /\ r5_of_reg rs2' = Some rs2 /\ off = w_of_imm imm.
Proof. intros i fmt rs1 rs2 off H; destruct i; inv_of H; injection H; intros; subst; do_ex. Qed.

Lemma sound_ILoad : forall (i : instr) (sz : msize) (sx : bool) (rd rs1 : r5) (off : w64), case_stmt segs OPS i (ILoad sz sx rd rs1 off).
Proof.
  intros i sz sx rd rs1 off E st ms model st' HS Hpc Hof Hx.
  destruct (of_instr_ILoad i sz sx rd rs1 off Hof) as (rd' & rs1' & imm & -> & Hrd & Hrs1 & ->).
  cbn [exec] in Hx.
  destruct (do_load segs st (sv_alu ALU_ADD (getr st rs1) (VL (w_of_imm imm))) (msize_bytes sz) sx) as [[v|]|why] eqn:DL;
    try discriminate. apply XOk_inj in Hx. subst st'.
  destruct (do_load_sound E st ms model _ _ sx v HS (msize_wok sz) DL) as (bs & Len & OV & Dv).
  rewrite <- (ea_den E st ms model rs1 rs1' _ imm HS Hrs1) in OV.
  cbn [Sem.exec load_val]. rewrite <- (reg_of_r5_of_reg rd' rd Hrd). rewrite (npc_eq E st ms model HS Hpc).
  destruct sz; cbn [msize_bytes load_val] in *;
    (erewrite interp_ELoad by exact OV); rewrite interp_EDone; eexists; eexists; (split; [reflexivity|]);
    apply (st_ok_reg_pc segs OPS E st ms model rd v _ (pc4 st) HS); rewrite Dv.
  - change (to_Z 1%uint63) with 1. apply ext_word_1.
  - change (to_Z 2%uint63) with 2. apply ext_word_2.
  - change (to_Z 4%uint63) with 4. apply ext_word_4.
  - change (to_Z 8%uint63) with 8. apply ext_word_8.
Qed.

Lemma sound_IStore : forall (i : instr) (sz : msize) (rs1 rs2 : r5) (off : w64), case_stmt segs OPS i (IStore sz rs1 rs2 off).
Proof.
  intros i sz rs1 rs2 off E st ms model st' HS Hpc Hof Hx.
  destruct (of_instr_IStore i sz rs1 rs2 off Hof) as (rs1' & rs2' & imm & -> & Hrs1 & Hrs2 & ->).
  cbn [exec] in Hx.
  set (a := sv_alu ALU_ADD (getr st rs1) (VL (w_of_imm imm))) in Hx.
  destruct (do_store segs st a (msize_bytes sz) (getr st rs2)) as [st1|why] eqn:DS; [|discriminate]. apply XOk_inj in Hx. subst st'.
  destruct (do_store_inv st a _ _ st1 DS) as (k & o & r & key & Ha & Hr & Hk & CW & ->).
  pose proof (resv_after_store_ok E (s_facts st) (s_resv st) (ms_resv ms) a (so_facts _ _ _ _ _ _ HS) (so_resv _ _ _ _ _ _ HS)) as RV.
  destruct (store_sound E st ms model a k o r key (msize_bytes sz) (getr st rs2) _ _ HS (msize_wok sz) Ha Hr Hk CW RV) as [SOK ST1].
  subst a. rewrite <- (ea_den E st ms model rs1 rs1' _ imm HS Hrs1) in SOK, ST1.
  rewrite <- (getr_den E st ms model rs2 rs2' HS Hrs2) in ST1.
  cbn [Sem.exec store_val]. rewrite inval_resv_eq. cbn [c_resv with_pc core_of]. rewrite (npc_eq E st ms model HS Hpc).
  pose proof (st_ok_pc segs OPS E _ _ model (pc4 st) ST1) as ST2.
  destruct sz; cbn [msize_bytes store_val] in *;
    (erewrite interp_EStore by exact SOK); rewrite interp_EDone; eexists; eexists; (split; [reflexivity|]);
    first [rewrite store_bytes_8 | rewrite store_bytes_16 | rewrite store_bytes_32 | rewrite store_bytes_64]; exact ST2.
Qed.

Lemma sound_ILr : forall (i : instr) (wd : awidth) (rd rs1 : r5), case_stmt segs OPS i (ILr wd rd rs1).
Proof.
  intros i wd rd rs1 E st ms model st' HS Hpc Hof Hx.
  destruct (of_instr_ILr i wd rd rs1 Hof) as (aq & rl & rd' & rs1' & -> & Hrd & Hrs1).
  cbn [exec] in Hx.
  destruct (aligned (s_facts st) (getr st rs1) (awidth_log wd)) eqn:AL; [|discriminate].
  destruct (do_load segs st (getr st rs1) (awidth_bytes wd) true) as [[v|]|why] eqn:DL; try discriminate. apply XOk_inj in Hx. subst st'.
  destruct (do_load_sound E st ms model _ _ true v HS (awidth_wok wd) DL) as (bs & Len & OV & Dv).
  pose proof (amo_aligned_ok E (s_facts st) (getr st rs1) wd (so_facts _ _ _ _ _ _ HS) AL) as AA.
  rewrite <- (getr_den E st ms model rs1 rs1' HS Hrs1) in OV, AA.
  cbn [Sem.exec]. rewrite AA. cbn [negb]. rewrite <- (reg_of_r5_of_reg rd' rd Hrd). rewrite (npc_eq E st ms model HS Hpc).
  pose proof (fun wv (H : den E v = wv) => st_ok_resv E _ _ model (RAddr (getr st rs1)) (Some (den E (getr st rs1)))
                (st_ok_reg_pc segs OPS E st ms model rd v wv (pc4 st) HS H) eq_refl) as ST.
  rewrite <- (getr_den E st ms model rs1 rs1' HS Hrs1) in ST.
  destruct wd; cbn [awidth_bytes] in *;
    (erewrite interp_ELoad by exact OV); rewrite interp_EDone; eexists; eexists; (split; [reflexivity|]).
  - apply ST. rewrite Dv. change (to_Z 4%uint63) with 4. apply (ext_word_4 true).
  - apply ST. rewrite Dv. change (to_Z 8%uint63) with 8. apply ext_word_8.
Qed.

Lemma den_wone : forall E, den E (VL wone) = w1. Proof. reflexivity. Qed.
Lemma den_wzero : forall E, den E (VL wzero) = w0. Proof. reflexivity. Qed.

Lemma sound_ISc : forall (i : instr) (wd : awidth) (rd rs1 rs2 : r5), case_stmt segs OPS i (ISc wd rd rs1 rs2).
Proof.
  intros i wd rd rs1 rs2 E st ms model st' HS Hpc Hof Hx.
  destruct (of_instr_ISc i wd rd rs1 rs2 Hof) as (aq & rl & rd' & rs1' & rs2' & -> & Hrd & Hrs1 & Hrs2).
  cbn [exec] in Hx.
  destruct (aligned (s_facts st) (getr st rs1) (awidth_log wd)) eqn:AL; [|discriminate].
  pose proof (amo_aligned_ok E (s_facts st) (getr st rs1) wd (so_facts _ _ _ _ _ _ HS) AL) as AA.
  rewrite <- (getr_den E st ms model rs1 rs1' HS Hrs1) in AA.
  cbn [Sem.exec]. rewrite AA. cbn [negb]. rewrite <- (reg_of_r5_of_reg rd' rd Hrd). rewrite (npc_eq E st ms model HS Hpc).
  pose proof (so_resv _ _ _ _ _ _ HS) as RV.

  assert (FAILC : st' = setpc (setresv (setr st rd (VL wone)) RNone) (pc4 st) ->
     exists c m', interp_eff segs (EDone (rset (reg_of_r5 rd) w1 (with_resv None (with_pc (Z_to_bv 64 (to_Z (pc4 st))) (core_of ms))))) (ms_mem ms)
                  = MachineOk (c, m') /\ st_ok segs OPS E st' (ms_upd ms c m') model).
  { intros ->. rewrite interp_EDone. eexists; eexists; split; [reflexivity|].
    eapply st_ok_ms_eq; [exact (st_ok_resv E _ _ model RNone None (st_ok_reg_pc segs OPS E st ms model rd (VL wone) w1 (pc4 st) HS (den_wone E)) eq_refl)
                        | reflexivity |].
    cbn_st. unfold rset. rewrite is_x0_reg_of_r5. destruct (r5_eqb rd X0); reflexivity. }
  destruct (s_resv st) as [|a'|] eqn:SR; cbn [resv_ok] in RV; [| |discriminate].
  -   cbn [c_resv core_of]. rewrite RV. apply FAILC. congruence.
  - cbn [c_resv core_of]. rewrite RV.
    destruct (decide_eq (s_facts st) a' (getr st rs1)) as [[|]|] eqn:D; [| |discriminate].
    +
      apply (decide_eq_sound E _ (so_facts _ _ _ _ _ _ HS)) in D. apply (proj1 (eqb_iff _ _ true)) in D.
      rewrite D, <- (getr_den E st ms model rs1 rs1' HS Hrs1), Z.eqb_refl.
      destruct (do_store segs (setresv st RNone) (getr st rs1) (awidth_bytes wd) (getr st rs2)) as [st1|why] eqn:DS; [|discriminate].
      apply XOk_inj in Hx. subst st'.
      destruct (do_store_inv (setresv st RNone) _ _ _ st1 DS) as (k & o & r & key & Ha & Hr & Hk & CW & ->). cbn_st. cbn [resv_after_store].
      cbn [s_regs s_facts s_priv setresv] in Hr, CW.
      destruct (store_sound E st ms model (getr st rs1) k o r key (awidth_bytes wd) (getr st rs2) RNone None HS (awidth_wok wd) Ha Hr Hk CW eq_refl) as [SOK ST1].
      rewrite <- (getr_den E st ms model rs1 rs1' HS Hrs1) in SOK, ST1.
      rewrite <- (getr_den E st ms model rs2 rs2' HS Hrs2) in ST1.
      pose proof (st_ok_resv E _ _ model RNone None (st_ok_reg_pc segs OPS E _ _ model rd (VL wzero) w0 (pc4 st) ST1 (den_wzero E)) eq_refl) as ST3.
      destruct wd; cbn [awidth_bytes] in *;
        (erewrite interp_EStore by exact SOK); rewrite interp_EDone; eexists; eexists; (split; [reflexivity|]);
        first [rewrite store_bytes_32 | rewrite store_bytes_64];
        (eapply st_ok_ms_eq; [exact ST3| reflexivity|]);
        cbn_st; unfold rset; rewrite is_x0_reg_of_r5; destruct (r5_eqb rd X0); reflexivity.
    +
      apply (decide_eq_sound E _ (so_facts _ _ _ _ _ _ HS)) in D. apply (proj1 (eqb_iff _ _ false)) in D.
      destruct (Z.eqb_spec (bv_unsigned (den E a')) (bv_unsigned (rget (core_of ms) rs1'))) as [X|X].
      { exfalso. apply D. apply bv_eq. rewrite X. rewrite (getr_den E st ms model rs1 rs1' HS Hrs1). reflexivity. }
      apply FAILC. congruence.
Qed.

Lemma sound_IAmo : forall (i : instr) (op : amoop) (wd : awidth) (rd rs1 rs2 : r5), case_stmt segs OPS i (IAmo op wd rd rs1 rs2).
Proof.
  intros i op wd rd rs1 rs2 E st ms model st' HS Hpc Hof Hx.
  destruct (of_instr_IAmo i op wd rd rs1 rs2 Hof) as (aq & rl & rd' & rs1' & rs2' & -> & Hrd & Hrs1 & Hrs2).
  cbn [exec] in Hx.
  destruct (aligned (s_facts st) (getr st rs1) (awidth_log wd)) eqn:AL; [|discriminate].
  pose proof (amo_aligned_ok E (s_facts st) (getr st rs1) wd (so_facts _ _ _ _ _ _ HS) AL) as AA.
  destruct (do_load segs st (getr st rs1) (awidth_bytes wd) true) as [[old|]|why] eqn:DL; try discriminate.
  destruct (do_load_sound E st ms model _ _ true old HS (awidth_wok wd) DL) as (bs & Len & OV & Dv).
  set (src := getr st rs2) in Hx.
  set (nvo := match op with
              | AMO_SWAP => Some src | AMO_ADD => Some (sv_alu ALU_ADD old src) | AMO_XOR => Some (sv_alu ALU_XOR old src)
              | AMO_AND => Some (sv_alu ALU_AND old src) | AMO_OR => Some (sv_alu ALU_OR old src) | _ => None end) in Hx.
  destruct nvo as [nv|] eqn:NV; [|discriminate].
  set (st1 := setresv st (resv_after_store (s_facts st) (s_resv st) (getr st rs1))) in Hx.
  destruct (do_store segs st1 (getr st rs1) (awidth_bytes wd) nv) as [st2|why] eqn:DS; [|discriminate]. apply XOk_inj in Hx. subst st'.
  destruct (do_store_inv st1 _ _ _ st2 DS) as (k & o & r & key & Ha & Hr & Hk & CW & ->). subst st1. cbn_st.
  cbn [s_regs s_facts s_priv setresv] in Hr, CW.
  pose proof (resv_after_store_ok E (s_facts st) (s_resv st) (ms_resv ms) (getr st rs1) (so_facts _ _ _ _ _ _ HS) (so_resv _ _ _ _ _ _ HS)) as RV.
  destruct (store_sound E st ms model (getr st rs1) k o r key (awidth_bytes wd) nv _ _ HS (awidth_wok wd) Ha Hr Hk CW RV) as [SOK ST1].
  rewrite <- (getr_den E st ms model rs1 rs1' HS Hrs1) in SOK, ST1, OV, AA.
  cbn [Sem.exec]. rewrite AA. cbn [negb]. rewrite <- (reg_of_r5_of_reg rd' rd Hrd).
  rewrite inval_resv_eq. cbn [c_resv with_pc core_of]. rewrite (npc_eq E st ms model HS Hpc).
  pose proof (fun wv (H : den E old = wv) => st_ok_reg_pc segs OPS E _ _ model rd old wv (pc4 st) ST1 H) as ST.
  assert (SRC : rget (core_of ms) rs2' = den E src) by (subst src; apply (getr_den E st ms model rs2 rs2' HS Hrs2)).
  destruct wd; cbn [awidth_bytes] in *;
    (erewrite interp_ELoad by exact OV); (erewrite interp_EStore by exact SOK); rewrite interp_EDone;
    eexists; eexists; (split; [reflexivity|]).
  -
    change (to_Z 4%uint63) with 4 in Dv. rewrite (ext_word_4 true) in Dv.
    rewrite SRC. erewrite store_bytes_eqm32; [apply ST; exact Dv|].
    destruct op; cbn in NV; try discriminate NV; injection NV as <-.
    + cbn [amo_val]. subst src. apply low32_eqm. lia.
    + rewrite ?den_sv_alu, ?den_sv_alu0, Dv. apply (amo32_eqm AMO_ADD). reflexivity.
    + rewrite ?den_sv_alu, ?den_xor_not_fold, ?den_sv_alu0, Dv. apply (amo32_eqm AMO_XOR). reflexivity.
    + rewrite ?den_sv_alu, ?den_and_refold, ?den_sv_alu0, Dv. apply (amo32_eqm AMO_AND). reflexivity.
    + rewrite ?den_sv_alu, ?BDP.den_refold, ?den_sv_alu0, Dv. apply (amo32_eqm AMO_OR). reflexivity.
  -
    change (to_Z 8%uint63) with 8 in Dv. rewrite ext_word_8 in Dv.
    rewrite SRC. rewrite store_bytes_64.

    destruct op; cbn in NV; try discriminate NV; injection NV as <-; cbn [amo_val].
    + apply ST. exact Dv.
    + rewrite den_sv_alu in ST. cbn [alu64 alu] in ST. rewrite Dv in ST. apply ST. reflexivity.
    + rewrite den_sv_alu in ST. cbn [alu64 alu] in ST. rewrite Dv in ST. apply ST. reflexivity.
    + rewrite den_sv_alu in ST. cbn [alu64 alu] in ST. rewrite Dv in ST. apply ST. reflexivity.
    + rewrite den_sv_alu in ST. cbn [alu64 alu] in ST. rewrite Dv in ST. apply ST. reflexivity.
Qed.

Lemma sound_IFLoad : forall (i : instr) (fmt : ffmt) (rd : r5) (rs1 : r5) (off : w64), case_stmt segs OPS i (IFLoad fmt rd rs1 off).
Proof.
  intros i fmt rd rs1 off E st ms model st' HS Hpc Hof Hx.
  destruct (of_instr_IFLoad i fmt rd rs1 off Hof) as (rd' & rs1' & imm & -> & Hrd & Hrs1 & ->).
  cbn [exec] in Hx.
  cbn [Sem.exec]. rewrite <- (reg_of_r5_of_reg rd' rd Hrd). rewrite (npc_eq E st ms model HS Hpc).
  destruct fmt.
  - destruct (do_load segs st (sv_alu ALU_ADD (getr st rs1) (VL (w_of_imm imm))) 4%uint63 false) as [[v|]|why] eqn:DL;
      try discriminate. apply XOk_inj in Hx. subst st'.
    destruct (do_load_sound E st ms model _ 4%uint63 false v HS ltac:(unfold wok; right; right; left; reflexivity) DL) as (bs & Len & OV & Dv).
    rewrite <- (ea_den E st ms model rs1 rs1' _ imm HS Hrs1) in OV.
    change (Z.to_nat (to_Z 4%uint63)) with (width_bytes 32) in OV.
    erewrite interp_ELoad by exact OV. rewrite interp_EDone. eexists; eexists; split; [reflexivity|].
    apply (st_ok_freg_pc segs OPS E st ms model rd _ _ (pc4 st) HS).
    cbn [den fop1_sem]. rewrite Dv. change (to_Z 4%uint63) with 4. rewrite (ext_word_4 false). rewrite low32_zext32. reflexivity.
  - destruct (do_load segs st (sv_alu ALU_ADD (getr st rs1) (VL (w_of_imm imm))) 8%uint63 false) as [[v|]|why] eqn:DL;
      try discriminate. apply XOk_inj in Hx. subst st'.
    destruct (do_load_sound E st ms model _ 8%uint63 false v HS ltac:(unfold wok; right; right; right; reflexivity) DL) as (bs & Len & OV & Dv).
    rewrite <- (ea_den E st ms model rs1 rs1' _ imm HS Hrs1) in OV.
    change (Z.to_nat (to_Z 8%uint63)) with (width_bytes 64) in OV.
    erewrite interp_ELoad by exact OV. rewrite interp_EDone. eexists; eexists; split; [reflexivity|].
    apply (st_ok_freg_pc segs OPS E st ms model rd _ _ (pc4 st) HS).
    rewrite Dv. change (to_Z 8%uint63) with 8. apply ext_word_8.
Qed.

Lemma sound_IFStore : forall (i : instr) (fmt : ffmt) (rs1 : r5) (rs2 : r5) (off : w64), case_stmt segs OPS i (IFStore fmt rs1 rs2 off).
Proof.
  intros i fmt rs1 rs2 off E st ms model st' HS Hpc Hof Hx.
  destruct (of_instr_IFStore i fmt rs1 rs2 off Hof) as (rs1' & rs2' & imm & -> & Hrs1 & Hrs2 & ->).
  cbn [exec] in Hx.
  set (a := sv_alu ALU_ADD (getr st rs1) (VL (w_of_imm imm))) in Hx.
  set (w := match fmt with FMT_S => 4%uint63 | FMT_D => 8%uint63 end) in Hx.
  assert (Hw : wok w) by (subst w; unfold wok; destruct fmt; [right; right; left| right; right; right]; reflexivity).
  destruct (do_store segs st a w (getf st rs2)) as [st1|why] eqn:DS; [|discriminate]. apply XOk_inj in Hx. subst st'.
  destruct (do_store_inv st a _ _ st1 DS) as (k & o & r & key & Ha & Hr & Hk & CW & ->).
  pose proof (resv_after_store_ok E (s_facts st) (s_resv st) (ms_resv ms) a (so_facts _ _ _ _ _ _ HS) (so_resv _ _ _ _ _ _ HS)) as RV.
  destruct (store_sound E st ms model a k o r key w (getf st rs2) _ _ HS Hw Ha Hr Hk CW RV) as [SOK ST1].
  subst a. rewrite <- (ea_den E st ms model rs1 rs1' _ imm HS Hrs1) in SOK, ST1.
  rewrite <- (getf_den E st ms model rs2 rs2' HS Hrs2) in ST1.
  cbn [Sem.exec]. rewrite inval_resv_eq. cbn [c_resv with_pc core_of]. rewrite (npc_eq E st ms model HS Hpc).
  pose proof (st_ok_pc segs OPS E _ _ model (pc4 st) ST1) as ST2.
  destruct fmt; subst w;
    (erewrite interp_EStore by exact SOK); rewrite interp_EDone; eexists; eexists; (split; [reflexivity|]);
    first [rewrite store_bytes_32 | rewrite store_bytes_64]; exact ST2.
Qed.

End WithSegs.
End StepM.
