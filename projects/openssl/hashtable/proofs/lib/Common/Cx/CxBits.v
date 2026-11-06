(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition and_lowmask (kn : list kentry) (a : expr) (m : Z) : option expr :=
  let m' := m mod two64 in
  let j := Z.log2_up (two64 - m') in
  if (Z.ltb 0 j && Z.leb j 63 && Z.leb (two64 - 2 ^ j) m')%bool then
    let l := lin_of a in
    if coeffs_divk kn (2 ^ j) (snd l) then
      let c := fst l in
      Some (unlin (c - c mod 2 ^ j + Z.land (c mod 2 ^ j) (m' mod 2 ^ j), snd l))
    else None
  else None.

Fixpoint bitnorm (kn : list kentry) (e : expr) : expr :=
  match e with
  | EAlu op a b =>
      let a' := bitnorm kn a in let b' := bitnorm kn b in
      match op, b' with
      | ALU_AND, ELit m => match and_lowmask kn a' m with Some r => r | None => mkAluK kn op a' b' end
      | _, _ => mkAluK kn op a' b'
      end
  | EMd op a b => mkMdK kn op (bitnorm kn a) (bitnorm kn b)
  | EAluw op a b =>
      (* [comment removed for export] *)
      match op, b with
      | ALU_SLL, ELit s =>
          let a' := bitnorm kn a in
          match erange kn a' with
          | Some (lo, hi) => if (Z.leb 0 s && Z.ltb s 32 && Z.ltb (hi * 2 ^ s) (2 ^ 31))%bool then unlin (lscale (2 ^ s) (lin_of a')) else e
          | None => e
          end
      | _, _ => e
      end
  | _ => e
  end.

Definition node_bitspell (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit r; e] =>
      let rn := Z.to_nat r in
      if (Z.leb 1 r && Z.leb r 31 && expr_vars_lt (nxt cs) e && respell_ok (kn cs) (bitnorm (kn cs) (reg cs rn)) e)%bool
      then Some (set_reg cs rn e) else None
  | _ => None
  end.

(* [comment removed for export] *)
Lemma land_lowmask : forall V m' j, 0 <= V < 2 ^ 64 -> 0 < j <= 63 -> 2 ^ 64 - 2 ^ j <= m' < 2 ^ 64 ->
  Z.land V m' = V - V mod 2 ^ j + Z.land (V mod 2 ^ j) (m' mod 2 ^ j).
Proof.
  intros V m' j HV Hj Hm.
  assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (Hm0 : 0 <= m') by (assert (2 ^ j <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia).
  assert (Hlow : (Z.land V m') mod 2 ^ j = Z.land (V mod 2 ^ j) (m' mod 2 ^ j)).
  { rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec. destruct (Z.testbit (Z.ones j) i); rewrite ?andb_true_r, ?andb_false_r; reflexivity. }
  assert (Hhigh : (Z.land V m') / 2 ^ j = V / 2 ^ j).
  { rewrite <- !Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_land.
    assert (Hm' : Z.shiftr m' j = Z.ones (64 - j)).
    { rewrite Z.shiftr_div_pow2 by lia. rewrite Z.ones_equiv.
      assert (E64 : 2 ^ 64 = 2 ^ (64 - j) * 2 ^ j) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (H1 : (2 ^ (64 - j) - 1) * 2 ^ j <= m') by lia.
      assert (H2 : m' < (2 ^ (64 - j) - 1 + 1) * 2 ^ j) by lia.
      symmetry. apply Z.div_unique with (r := m' - (2 ^ (64 - j) - 1) * 2 ^ j); lia. }
    rewrite Hm'. rewrite Z.land_ones by lia. apply Z.mod_small.
    split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (j + (64 - j)) with 64 by lia. lia. }
  pose proof (Z.div_mod (Z.land V m') (2 ^ j) ltac:(lia)) as D1.
  pose proof (Z.div_mod V (2 ^ j) ltac:(lia)) as D2.
  rewrite Hlow, Hhigh in D1. lia.
Qed.

Lemma and_lowmask_denot : forall segs E base kn a m r,
  know_ok segs E base kn -> and_lowmask kn a m = Some r ->
  edenot E r = alu64 ALU_AND (edenot E a) (Z_to_bv 64 m).
Proof.
  intros segs E base kn a m r HK H. unfold and_lowmask in H.
  set (m' := m mod two64) in *. set (j := Z.log2_up (two64 - m')) in *.
  destruct (Z.ltb 0 j && Z.leb j 63 && Z.leb (two64 - 2 ^ j) m')%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc Hm]. apply andb_prop in Hc as [Hj0 Hj63].
  apply Z.ltb_lt in Hj0. apply Z.leb_le in Hj63. apply Z.leb_le in Hm.
  destruct (lin_of a) as [c ts] eqn:Hl. cbn [fst snd] in H.
  destruct (coeffs_divk kn (2 ^ j) ts) eqn:Hcd; [|discriminate]. injection H as <-.
  assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (Hm64 : 0 <= m' < 2 ^ 64) by (unfold m', two64; apply Z.mod_pos_bound; lia).
  pose proof (lin_of_sound E a) as Hs. rewrite Hl in Hs. unfold lden in Hs. cbn [fst snd] in Hs.
  set (V := bv_unsigned (edenot E a)) in *. change (AX2S.uE E a) with V in Hs.
  assert (HV : 0 <= V < 2 ^ 64) by (pose proof (u64_range (edenot E a)) as X; unfold two64 in X; exact X).
  assert (Hmod : V mod 2 ^ j = c mod 2 ^ j).
  { rewrite <- (eqm_mod_pow2 _ _ j ltac:(lia) Hs). rewrite Z.add_mod, (coeffs_divk_sound segs E base kn _ ts HK Hp Hcd), Z.add_0_r, Z.mod_mod by lia. reflexivity. }
  rewrite <- (Z_to_bv_bv_unsigned 64 (alu64 ALU_AND _ _)). rewrite u_and64, u_lit64. fold V. fold m'.
  rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))). apply eqm_Z_to_bv.
  eapply eqm_trans; [apply unlin_sound|]. unfold lden. cbn [fst snd].
  rewrite (land_lowmask V m' j HV ltac:(lia) ltac:(unfold two64 in Hm; lia)). rewrite Hmod.
  destruct Hs as [q Hq]. exists q. lia.
Qed.

Lemma bitnorm_denot : forall segs E base kn e, know_ok segs E base kn -> edenot E (bitnorm kn e) = edenot E e.
Proof.
  intros segs E base kn e HK. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k off n]; cbn [bitnorm]; try reflexivity.
  - assert (Hdef : edenot E (mkAluK kn op (bitnorm kn a) (bitnorm kn b)) = edenot E (EAlu op a b))
      by (rewrite (mkAluK_denot segs E base kn _ _ _ HK), IHa, IHb; reflexivity).
    destruct op; try exact Hdef.
    destruct (bitnorm kn b) as [m| | | | | | |] eqn:Hb; try exact Hdef.
    destruct (and_lowmask kn (bitnorm kn a) m) as [r|] eqn:Hr; [|exact Hdef].
    rewrite (and_lowmask_denot segs E base kn _ m r HK Hr), IHa. cbn [edenot]. rewrite <- IHb. reflexivity.
  - (* [comment removed for export] *)
    destruct op; try reflexivity. destruct b as [s| | | | | | |]; try reflexivity.
    destruct (erange kn (bitnorm kn a)) as [[lo hi]|] eqn:Hr; [|reflexivity].
    destruct (Z.leb 0 s && Z.ltb s 32 && Z.ltb (hi * 2 ^ s) (2 ^ 31))%bool eqn:Hc; [|reflexivity].
    apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
    pose proof (erange_sound segs E base kn _ lo hi HK Hr) as Hb. rewrite IHa in Hb.
    set (V := bv_unsigned (edenot E a)) in *.
    assert (HV : 0 <= V < 2 ^ 64) by (pose proof (u64_range (edenot E a)) as X; unfold two64 in X; exact X).
    assert (Hp : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
    assert (Hs64 : bv_unsigned (Z_to_bv 64 s) mod 64 = s).
    { rewrite u_lit64. unfold two64. rewrite (Z.mod_small s (2 ^ 64)) by lia. apply Z.mod_small. lia. }
    assert (Hs32 : s mod 32 = s) by (apply Z.mod_small; lia).
    assert (Hsmall : V * 2 ^ (s mod 32) < 2 ^ 31) by (rewrite Hs32; nia).
    cbn [edenot].
    rewrite <- (Z_to_bv_bv_unsigned 64 (sext 64 _)).
    rewrite (u_sllw_small (edenot E a) (Z_to_bv 64 s) s Hs64 Hsmall). rewrite Hs32. fold V.
    rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))). apply eqm_Z_to_bv.
    eapply eqm_trans; [apply unlin_sound|]. eapply eqm_trans; [apply lscale_sound|].
    rewrite (Z.mul_comm V). apply eqm_mul_l.
    pose proof (lin_of_sound E (bitnorm kn a)) as Hl. unfold AX2S.uE in Hl. rewrite IHa in Hl. exact Hl.
  - rewrite (mkMdK_denot segs E base kn _ _ _ HK), IHa, IHb. reflexivity.
Qed.

Section Node.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable ISP : Z.
  Variable FS0 : Fs.Fs.

  Theorem node_bitspell_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_bitspell args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn HK. unfold node_bitspell in Hn.
    destruct args as [|[r| | | | | | |] [|e [|]]]; try discriminate Hn.
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection Hn as <-.
    apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HKn.
    pose proof (respell_ok_sound SEGS E _ (kn cs) _ e HKn Hok) as Heq.
    rewrite (bitnorm_denot SEGS E _ (kn cs) _ HKn) in Heq.
    assert (Hrefl : forall b, env_agree b E E) by (intros b; split; [intros; reflexivity | reflexivity]).
    apply (HK E R FULL model); [split; apply Hrefl | | reflexivity].
    destruct HC; constructor; cbn [set_reg with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption; try reflexivity.
    apply regs_ok_respell; [assumption | lia | unfold reg in Heq; symmetry; exact Heq].
  Qed.
End Node.
