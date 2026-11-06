(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie AxFetchFast.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import MState Mem Exec.
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound.
From OSSVerify.Proofs.openssl.bignum.lib.HXS Require Import HxsStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition sh_law (shbz : Z) (rho : valuation) (M : mem) : Prop :=
  forall s rg, mget M s = Some rg -> rg_abs rg = None -> tag_even s = false -> rho s = rho (s - 1)%uint63 / 8 + shbz.

Lemma sh_law_dirs (shbz : Z) (rho : valuation) (M M' : mem) : same_dirs M M' -> sh_law shbz rho M -> sh_law shbz rho M'.
Proof.
  intros Hd H s rg' G' Ea' Ev. specialize (Hd s). rewrite G' in Hd. destruct (mget M s) as [rg|] eqn:G; [|contradiction].
  destruct Hd as (Ea & _). apply (H s rg G); [congruence | exact Ev].
Qed.

Lemma tag_even_spec (t : int) : tag_even t = true -> to_Z t mod 2 = 0.
Proof.
  unfold tag_even. intros H. destruct (eqbP (t land 1)%uint63 0%uint63) as [E|E]; [|discriminate].
  rewrite land_spec' in E. change (to_Z 1%uint63) with (Z.ones 1) in E. rewrite Z.land_ones in E by lia. exact E.
Qed.

Lemma tag_even_false_spec (t : int) : tag_even t = false -> to_Z t mod 2 = 1.
Proof.
  unfold tag_even. intros H. destruct (eqbP (t land 1)%uint63 0%uint63) as [E|E]; [discriminate|].
  rewrite land_spec' in E. change (to_Z 1%uint63) with (Z.ones 1) in E. rewrite Z.land_ones in E by lia.
  change (to_Z 0%uint63) with 0 in E. change (2 ^ 1) with 2 in E. pose proof (Z.mod_pos_bound (to_Z t) 2 ltac:(lia)). lia.
Qed.

Lemma sh_tag_odd (t : int) : tag_even t = true -> to_Z t < to_Z TAGLIM -> tag_even (sh_tag t) = false /\ (sh_tag t - 1)%uint63 = t.
Proof.
  intros He Ht. pose proof (tag_even_spec t He) as Hm. pose proof (to_Z_bounded t) as Bt. change (to_Z TAGLIM) with 1048576 in Ht.
  assert (E1 : to_Z (sh_tag t) = to_Z t + 1).
  { unfold sh_tag. rewrite add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. rewrite wB_eq. unfold two63. lia. }
  split.
  - unfold tag_even. destruct (eqbP (sh_tag t land 1)%uint63 0%uint63) as [E|E]; [|reflexivity]. exfalso.
    rewrite land_spec' in E. change (to_Z 1%uint63) with (Z.ones 1) in E. rewrite Z.land_ones in E by lia.
    change (to_Z 0%uint63) with 0 in E. change (2 ^ 1) with 2 in E. rewrite E1 in E.
    rewrite Z.add_mod, Hm in E by lia. cbn in E. lia.
  - apply to_Z_inj. rewrite sub_spec, E1. change (to_Z 1%uint63) with 1. replace (to_Z t + 1 - 1) with (to_Z t) by ring.
    apply Z.mod_small. exact Bt.
Qed.

Section Rules.
Variable segs : list Segment.
Variable shb : w64.

Lemma is_three_spec (w : w64) : is_three w = true -> w = W false 3%uint63.
Proof.
  destruct w as [h l]. unfold is_three; cbn [wh wl]. intros H. apply andb_prop in H as [Hh Hl].
  destruct h; [discriminate|]. destruct (eqbP l 3%uint63) as [E|E]; [|discriminate]. apply to_Z_inj in E. subst l. reflexivity.
Qed.

Lemma sh_rule_ok (rho : valuation) (M : mem) (m : word -> option byte) (a v : hval) (x : word) :
  Rmem segs rho M m -> sh_law (wZ shb) rho M -> sh_rule shb M a = Some v -> den rho a x ->
  den rho v (alu64 ALU_SRL x (wbv (W false 3%uint63))).
Proof.
  intros HR Hlaw H Ha. pose proof (ctx_of_ok segs rho M m HR) as Hc. unfold sh_rule in H.
  destruct a as [|t o| |]; try discriminate.
  destruct (tag_even t) eqn:Eev; [|discriminate]. destruct (inb (ctx_of M) t o) eqn:Ei; [|discriminate]. cbn [andb] in H.
  destruct (ctx_of M t) as [[al sz]|] eqn:Ec; [|discriminate].
  destruct (mget M (sh_tag t)) as [rgs|] eqn:Egs; [|discriminate].
  destruct (rg_abs rgs) eqn:Eas; [discriminate|].
  destruct (3 <=? al)%uint63 eqn:E3; [|discriminate]. injection H as <-. apply leb_spec in E3. change (to_Z 3%uint63) with 3 in E3.
  destruct (Hc t al sz Ec) as (Hal & Hmod & Hpos & Hhi). destruct (inb_spec rho (ctx_of M) t o Hc Ei) as [Hr Ep].
  assert (Ht : to_Z t < to_Z TAGLIM).
  { unfold ctx_of in Ec. destruct (mget M t) as [rg|] eqn:Eg; [|discriminate]. exact (mget_lt M t rg Eg). }
  destruct (sh_tag_odd t Eev Ht) as [Hodd Hpred].
  pose proof (Hlaw (sh_tag t) rgs Egs Eas Hodd) as Hl. rewrite Hpred in Hl.
  assert (Ho : wh o = false).
  { unfold inb in Ei. rewrite Ec in Ei. apply andb_prop in Ei as [Hh _]. destruct (wh o); [discriminate | reflexivity]. }
  assert (Hm8 : rho t mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hmod; [|apply Z.pow_nonzero; lia].
    apply (Z.divide_trans _ (2 ^ to_Z al)); [|exact Hmod]. exists (2 ^ (to_Z al - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia.
    replace (to_Z al - 3 + 3) with (to_Z al) by ring. reflexivity. }
  cbn [den] in Ha |- *. subst x. unfold alu64, alu. apply bv_eq.
  rewrite bv_shiftr_unsigned, bv_and_unsigned, Ep, wbv_unsigned. rewrite Z_to_bv_unsigned.
  change (Z.land (wZ (W false 3%uint63)) (bv_wrap 64 63)) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold pword. rewrite Z_to_bv_unsigned. rewrite wZ_sub.
  assert (EwZ : wZ (W false (wl o >> 3)%uint63) = wZ o / 8).
  { rewrite !wZ_split. cbn [wh wl Z.b2z]. rewrite Ho. cbn [Z.b2z]. rewrite !Z.mul_0_l, !Z.add_0_l. rewrite lsr_spec. reflexivity. }
  rewrite EwZ, Hl. unfold bv_wrap. rewrite bv_modulus_64.
  rewrite Z.add_mod_idemp_r by (unfold two64; lia).
  replace (rho t / 8 + wZ shb + (wZ o / 8 - wZ shb)) with (rho t / 8 + wZ o / 8) by ring.
  assert (Ediv : (rho t + wZ o) / 8 = rho t / 8 + wZ o / 8).
  { rewrite (Z.div_mod (rho t) 8) at 1 by lia. rewrite Hm8, Z.add_0_r. rewrite Z.mul_comm, Z.add_comm, Z.div_add by lia. ring. }
  rewrite <- Ediv. symmetry. apply Z.mod_small. unfold two63, two64 in *.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma lxor_ones_sub (c : Z) : 0 <= c < two64 -> Z.lxor c (two64 - 1) = two64 - 1 - c.
Proof. intros H. rewrite Z.lxor_comm. change (two64 - 1) with (Z.ones 64). rewrite Z.lxor_comm. exact (lxor_ones64 c H). Qed.

Lemma al_rule_ok (rho : valuation) (M : mem) (m : word -> option byte) (t : int) (o mk : w64) (v : hval) (x : word) :
  Rmem segs rho M m -> al_rule M t o mk = Some v -> den rho (VP t o) x -> den rho v (alu64 ALU_AND x (wbv mk)).
Proof.
  intros HR H Ha. pose proof (ctx_of_ok segs rho M m HR) as Hc. unfold al_rule in H.
  destruct (ctx_of M t) as [[al sz]|] eqn:Ec; [|discriminate].
  destruct (inb (ctx_of M) t o) eqn:Ei; [|discriminate]. cbn [andb] in H.
  destruct (negb (wh (w_xor mk w_ones))) eqn:Eh; [|discriminate]. cbn [andb] in H.
  destruct (wl (w_xor mk w_ones) <? 1 << al)%uint63 eqn:El; [|discriminate]. injection H as <-.
  apply negb_true_iff in Eh. apply ltb_spec in El.
  destruct (Hc t al sz Ec) as (Hal & Hmod & Hpos & Hhi). destruct (inb_spec rho (ctx_of M) t o Hc Ei) as [Hr Ep].
  set (c := w_xor mk w_ones) in *.
  pose proof (to_Z_bounded al) as Bal.
  assert (E1s : to_Z (1 << al)%uint63 = 2 ^ to_Z al).
  { rewrite lsl_spec. change (to_Z 1%uint63) with 1. rewrite Z.mul_1_l. apply Z.mod_small. rewrite wB_eq. unfold two63.
    split; [apply Z.pow_nonneg; lia | change 9223372036854775808 with (2 ^ 63); apply Z.pow_lt_mono_r; lia]. }
  assert (Ec' : wZ c = to_Z (wl c)) by (rewrite wZ_split, Eh; cbn [Z.b2z]; lia).
  assert (Hc0 : 0 <= wZ c < 2 ^ to_Z al) by (pose proof (to_Z_bounded (wl c)); lia).
  assert (Emk : wZ mk = two64 - 1 - wZ c).
  { pose proof (wZ_range mk) as Rm. unfold c. rewrite wZ_xor, wZ_ones. rewrite (lxor_ones_sub (wZ mk) Rm). ring. }
  cbn [den] in Ha |- *. subst x. unfold alu64, alu. apply bv_eq. rewrite bv_and_unsigned, Ep, wbv_unsigned.
  unfold pword. rewrite Z_to_bv_unsigned. rewrite wZ_sub, wZ_and.

  set (X := rho t + wZ o) in *.
  assert (EXc : Z.land X (wZ c) = Z.land (wZ o) (wZ c)).
  { rewrite (HxVal.land_low_mod X (wZ c) (to_Z al)) by lia. rewrite (HxVal.land_low_mod (wZ o) (wZ c) (to_Z al)) by lia. f_equal.
    unfold X. rewrite Z.add_mod, Hmod, Z.add_0_l, Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity. }
  assert (Eld : Z.land X (wZ mk) = X - Z.land X (wZ c)).
  { rewrite Emk. change (two64 - 1) with (Z.ones 64).
    assert (E64 : Z.land X (Z.ones 64 - wZ c) = Z.ldiff X (wZ c)).
    { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec.
      destruct (Z_lt_le_dec i 64) as [Hlt|Hge].
      - assert (Eo : Z.ones 64 - wZ c = Z.lxor (wZ c) (Z.ones 64)).
        { change (Z.ones 64) with (two64 - 1). rewrite lxor_ones_sub; [ring|]. unfold two64. assert (2 ^ to_Z al <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia). lia. }
        rewrite Eo, Z.lxor_spec, Z.ones_spec_low by lia. rewrite xorb_true_r. reflexivity.
      - assert (EX : Z.testbit X i = false).
        { destruct (Z.eq_dec X 0) as [->|Hnz]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
          apply Z.lt_le_trans with 64; [|exact Hge]. apply Z.log2_lt_pow2; [lia|]. unfold two63 in Hr. lia. }
        rewrite EX. reflexivity. }
    rewrite E64.
    assert (El2 : Z.ldiff X (wZ c) = Z.ldiff X (Z.land X (wZ c))).
    { apply Z.bits_inj'. intros i Hi. rewrite !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit X i), (Z.testbit (wZ c) i); reflexivity. }
    rewrite El2. symmetry. apply Z.sub_nocarry_ldiff.
    apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit X i), (Z.testbit (wZ c) i); reflexivity. }
  rewrite Eld, EXc. unfold bv_wrap. rewrite bv_modulus_64.
  rewrite Z.add_mod_idemp_r by (unfold two64; lia).
  replace (rho t + (wZ o - Z.land (wZ o) (wZ c))) with (X - Z.land (wZ o) (wZ c)) by (unfold X; ring).
  symmetry. apply Z.mod_small.
  assert (Hl0 : 0 <= Z.land (wZ o) (wZ c) <= wZ o).
  { pose proof (wZ_range o) as Ro. split; [apply Z.land_nonneg; left; lia|].
    assert (Es : wZ o - Z.land (wZ o) (wZ c) = Z.ldiff (wZ o) (Z.land (wZ o) (wZ c))).
    { apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
      destruct (Z.testbit (wZ o) i), (Z.testbit (wZ c) i); reflexivity. }
    assert (0 <= Z.ldiff (wZ o) (Z.land (wZ o) (wZ c))) by (apply Z.ldiff_nonneg; left; lia). lia. }
  unfold X, two63, two64 in *. lia.
Qed.

Lemma xalu_ok (rho : valuation) (M : mem) (m : word -> option byte) (op : aluop) (a b v : hval) (x y : word) :
  Rmem segs rho M m -> sh_law (wZ shb) rho M -> xalu shb M op a b = Some v -> den rho a x -> den rho b y ->
  den rho v (alu64 op x y).
Proof.
  intros HR Hlaw H Ha Hb. unfold xalu in H.
  destruct op; try discriminate; destruct a as [|t o| |]; try discriminate; destruct b as [c| | |]; try discriminate.
  - destruct (is_three c) eqn:E3; [|discriminate]. apply is_three_spec in E3. subst c. cbn [den] in Hb. subst y.
    exact (sh_rule_ok rho M m (VP t o) v x HR Hlaw H Ha).
  - cbn [den] in Hb. subst y. exact (al_rule_ok rho M m t o c v x HR H Ha).
Qed.

Theorem hxs_step_sound (rho : valuation) (ic ic' : icache) (S S' : sstate) (ms : machine_state) :
  ic_ok segs ic -> R segs rho S ms -> sh_law (wZ shb) rho (s_mem S) -> hxs_step shb segs ic S = (ic', SNext S') ->
  ic_ok segs ic' /\ exists ms', mstep segs ms ms' /\ R segs rho S' ms'
                           /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_rom ms' = ms_rom ms
                           /\ mem_step rho (s_mem S) (ms_mem ms) (ms_mem ms') /\ regs_step (ms_regs ms) (ms_regs ms').
Proof.
  intros Hic HR Hlaw H.

  assert (Hcase : hx_step segs ic S = (ic', SNext S')
                  \/ exists d ic1 op rd (va vb v : hval),
                       hx_fetch segs ic (s_pc S) = Some (d, ic1) /\ ic' = ic1
                       /\ xalu shb (s_mem S) op va vb = Some v /\ S' = with_reg_pc S rd v (w_add (s_pc S) w_four)
                       /\ ((exists rs1 imm, d = DOpImm op rd rs1 imm /\ va = rget S rs1 /\ vb = VC imm)
                           \/ (exists rs1 sh, d = DShiftImm op rd rs1 sh /\ va = rget S rs1 /\ vb = VC sh)
                           \/ (exists rs1 rs2, d = DOp op rd rs1 rs2 /\ va = rget S rs1 /\ vb = rget S rs2))).
  { unfold hxs_step in H. unfold hx_step. destruct (hx_fetch segs ic (s_pc S)) as [[d ic1]|] eqn:Ef; [|left; exact H].
    injection H as <- H. unfold hxs_exec in H.
    destruct d; try (left; f_equal; exact H).
    - destruct (xalu shb (s_mem S) op (rget S rs1) (VC imm)) as [v|] eqn:Ex; [|left; f_equal; exact H].
      right. exists (DOpImm op rd rs1 imm), ic1, op, rd, (rget S rs1), (VC imm), v. injection H as <-.
      repeat (split; [reflexivity || assumption|]). left. exists rs1, imm. auto.
    - destruct (xalu shb (s_mem S) op (rget S rs1) (VC sh)) as [v|] eqn:Ex; [|left; f_equal; exact H].
      right. exists (DShiftImm op rd rs1 sh), ic1, op, rd, (rget S rs1), (VC sh), v. injection H as <-.
      repeat (split; [reflexivity || assumption|]). right. left. exists rs1, sh. auto.
    - destruct (xalu shb (s_mem S) op (rget S rs1) (rget S rs2)) as [v|] eqn:Ex; [|left; f_equal; exact H].
      right. exists (DOp op rd rs1 rs2), ic1, op, rd, (rget S rs1), (rget S rs2), v. injection H as <-.
      repeat (split; [reflexivity || assumption|]). right. right. exists rs1, rs2. auto. }
  destruct Hcase as [Hcore|(d & ic1 & op & rd & va & vb & v & Ef & -> & Ex & -> & Hform)].
  { exact (hx_step_sound segs rho ic ic' S S' ms Hic HR Hcore). }
  destruct (hx_fetch_sound segs ic ic1 (s_pc S) d Hic Ef) as (Hic1 & w & i & Hfw & Hec & Hdec & Ed).
  split; [exact Hic1|]. pose proof HR as (Hsvc & Hpc & _ & _ & Hmem).
  rewrite (MS_eta ms Hsvc) in HR |- *. rewrite <- Hpc in Hfw.
  set (Rg := ms_regs ms) in *. set (F := ms_fregs ms) in *. set (pc := ms_pc_val ms) in *. set (fc := ms_fcsr ms) in *.
  set (rv := ms_resv ms) in *. set (m := ms_mem ms) in *. set (ro := ms_rom ms) in *.
  pose proof (npc_ok segs rho Rg F pc fc rv m ro S HR) as Hnpc.
  assert (Hpost : exec_post segs rho Rg F fc m ro S (with_reg_pc S rd v (w_add (s_pc S) w_four))
                    (interp_eff segs (exec (Z_to_bv 64 4) i (Core Rg F pc fc rv)) m)).
  { destruct Hform as [(rs1 & imm & -> & -> & ->)|[(rs1 & sh & -> & -> & ->)|(rs1 & rs2 & -> & -> & ->)]];
      destruct i; cbn [predec] in Ed; try discriminate; injection Ed as -> -> ->; intros; subst; cbn [exec interp_eff];
      (apply post_reg; [exact HR | | exact Hnpc]).
    - eapply (xalu_ok rho (s_mem S) m _ _ _ _ _ _ Hmem Hlaw Ex); [apply (rget_ok segs rho Rg F pc fc rv m ro S _ HR) | apply den_imm].
    - eapply (xalu_ok rho (s_mem S) m _ _ _ _ _ _ Hmem Hlaw Ex); [apply (rget_ok segs rho Rg F pc fc rv m ro S _ HR) | apply den_imm].
    - eapply (xalu_ok rho (s_mem S) m _ _ _ _ _ _ Hmem Hlaw Ex); apply (rget_ok segs rho Rg F pc fc rv m ro S _ HR). }
  destruct Hpost as (c' & m' & Eres & HR' & Hf & Hc & Hst & Hrs).
  exists (MS_of_core c' m' ro). split; [|split; [exact HR'|]].
  - split; [reflexivity|]. rewrite (step_gen segs Rg F pc fc rv m ro w i 4 Hfw Hec Hdec). rewrite Eres. reflexivity.
  - unfold MS_of_core, MS. cbn [ms_fregs ms_fcsr ms_rom ms_mem]. auto.
Qed.

End Rules.
