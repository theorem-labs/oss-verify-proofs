(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxBits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition odd_atom (kn : list kentry) (a : expr) : bool :=
  match find_align kn (EAlu ALU_ADD a (ELit 1)) with
  | Some m => Z.eqb (m mod 2) 0
  | None => false
  end.

(* [comment removed for export] *)
Fixpoint lowsum (kn : list kentry) (m : Z) (ts : list (Z * expr)) : option Z :=
  match ts with
  | [] => Some 0
  | (k, a) :: rest =>
      match lowsum kn m rest with
      | None => None
      | Some s =>
          if (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0)%bool then Some s
          else if (odd_atom kn a && Z.eqb ((2 * k) mod m) 0)%bool then Some ((s + k) mod m)
          else None
      end
  end.

Definition and_lowmask_o (kn : list kentry) (a : expr) (m : Z) : option expr :=
  let m' := m mod two64 in
  let j := Z.log2_up (two64 - m') in
  if (Z.ltb 0 j && Z.leb j 63 && Z.leb (two64 - 2 ^ j) m')%bool then
    let l := lin_of a in
    match lowsum kn (2 ^ j) (snd l) with
    | Some s =>
        let c := fst l in
        let low := (c + s) mod 2 ^ j in
        Some (unlin (c - low + Z.land low (m' mod 2 ^ j), snd l))
    | None => None
    end
  else None.

Fixpoint bitnorm_o (kn : list kentry) (e : expr) : expr :=
  match e with
  | EAlu op a b =>
      let a' := bitnorm_o kn a in let b' := bitnorm_o kn b in
      match op, b' with
      | ALU_AND, ELit m => match and_lowmask_o kn a' m with Some r => r | None => mkAluK kn op a' b' end
      | _, _ => mkAluK kn op a' b'
      end
  | EMd op a b => mkMdK kn op (bitnorm_o kn a) (bitnorm_o kn b)
  | _ => e
  end.

Definition node_oddspell (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit r; e] =>
      let rn := Z.to_nat r in
      if (Z.leb 1 r && Z.leb r 31 && expr_vars_lt (nxt cs) e && respell_ok (kn cs) (bitnorm_o (kn cs) (reg cs rn)) e)%bool
      then Some (set_reg cs rn e) else None
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma odd_mul_mod : forall x k m, 0 < m -> x mod 2 = 1 -> (2 * k) mod m = 0 -> (k * x) mod m = k mod m.
Proof.
  intros x k m Hm Hx H2.
  pose proof (Z.div_mod x 2 ltac:(lia)) as D. rewrite Hx in D.
  set (q := x / 2) in *. clearbody q. subst x.
  replace (k * (2 * q + 1)) with (k + (2 * k) * q) by ring.
  rewrite Z.add_mod by lia. rewrite (Z.mul_mod (2 * k)) by lia. rewrite H2, Z.mul_0_l, Z.mod_0_l, Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.

Lemma odd_of_wrapped_even : forall V m, 0 <= V -> 0 < m -> m mod 2 = 0 -> ((V + 1) mod 2 ^ 64) mod m = 0 -> V mod 2 = 1.
Proof.
  intros V m HV Hm0 Hm2 Hmod.
  set (W := (V + 1) mod 2 ^ 64) in *.
  assert (HW2 : W mod 2 = 0).
  { pose proof (Z.div_mod W m ltac:(lia)) as DW. rewrite Hmod, Z.add_0_r in DW.
    pose proof (Z.div_mod m 2 ltac:(lia)) as Dm. rewrite Hm2, Z.add_0_r in Dm.
    set (P := W / m) in *. set (H2 := m / 2) in *. clearbody P H2.
    assert (EW : W = (H2 * P) * 2) by (rewrite DW, Dm; ring).
    rewrite EW. apply Z.mod_mul. lia. }
  assert (HVW : (V + 1) mod 2 = W mod 2).
  { unfold W. pose proof (Z.div_mod (V + 1) (2 ^ 64) ltac:(lia)) as D.
    set (Q := (V + 1) / 2 ^ 64) in *. set (Rm := (V + 1) mod 2 ^ 64) in *.
    rewrite D. replace (2 ^ 64 * Q + Rm) with (Rm + (2 ^ 63 * Q) * 2) by (change (2 ^ 64) with (2 ^ 63 * 2); ring).
    apply Z.mod_add. lia. }
  rewrite HW2 in HVW.
  pose proof (Z.mod_pos_bound V 2 ltac:(lia)) as HB.
  pose proof (Z.div_mod V 2 ltac:(lia)) as DV.
  pose proof (Z.div_mod (V + 1) 2 ltac:(lia)) as DV1. rewrite HVW in DV1. lia.
Qed.

Lemma odd_atom_sound : forall segs E base kn a, know_ok segs E base kn -> odd_atom kn a = true -> (AX2S.uE E a) mod 2 = 1.
Proof.
  intros segs E base kn a HK H. unfold odd_atom in H.
  destruct (find_align kn (EAlu ALU_ADD a (ELit 1))) as [m|] eqn:Hf; [|discriminate].
  apply Z.eqb_eq in H.
  destruct (find_align_sound segs E base kn _ m HK Hf) as [Hm0 Hmod].
  cbn [edenot] in Hmod. rewrite u_add64, u_lit64 in Hmod. unfold two64 in Hmod. rewrite (Z.mod_small 1 (2 ^ 64)) in Hmod by lia.
  unfold AX2S.uE.
  assert (HV : 0 <= bv_unsigned (edenot E a)) by (pose proof (u64_range (edenot E a)) as X; lia).
  exact (odd_of_wrapped_even _ m HV Hm0 H Hmod).
Qed.

Lemma lowsum_sound : forall segs E base kn m ts s, know_ok segs E base kn -> 0 < m ->
  lowsum kn m ts = Some s -> (AX2S.tden E ts) mod m = s mod m.
Proof.
  intros segs E base kn m ts. induction ts as [|[k a] rest IH]; intros s HK Hm H; cbn [lowsum AX2S.tden] in *.
  - injection H as <-. reflexivity.
  - destruct (lowsum kn m rest) as [s0|] eqn:Hr; [|discriminate]. specialize (IH s0 HK Hm eq_refl).
    destruct (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0)%bool eqn:Hd.
    + injection H as <-.
      assert (Hcd : coeffs_divk kn m [(k, a)] = true) by (cbn [coeffs_divk]; rewrite Hd; reflexivity).
      pose proof (coeffs_divk_sound segs E base kn m [(k, a)] HK Hm Hcd) as H0. cbn [AX2S.tden] in H0. rewrite Z.add_0_r in H0.
      rewrite Z.add_mod, H0, Z.add_0_l, Z.mod_mod by lia. exact IH.
    + destruct (odd_atom kn a && Z.eqb ((2 * k) mod m) 0)%bool eqn:Ho; [|discriminate]. injection H as <-.
      apply andb_prop in Ho as [Ho H2]. apply Z.eqb_eq in H2.
      pose proof (odd_atom_sound segs E base kn a HK Ho) as Hodd.
      rewrite Z.add_mod, (odd_mul_mod _ k m Hm Hodd H2), IH by lia. rewrite <- Z.add_mod by lia. rewrite Z.mod_mod by lia. f_equal. ring.
Qed.

Lemma and_lowmask_o_denot : forall segs E base kn a m r,
  know_ok segs E base kn -> and_lowmask_o kn a m = Some r ->
  edenot E r = alu64 ALU_AND (edenot E a) (Z_to_bv 64 m).
Proof.
  intros segs E base kn a m r HK H. unfold and_lowmask_o in H.
  set (m' := m mod two64) in *. set (j := Z.log2_up (two64 - m')) in *.
  destruct (Z.ltb 0 j && Z.leb j 63 && Z.leb (two64 - 2 ^ j) m')%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc Hm]. apply andb_prop in Hc as [Hj0 Hj63].
  apply Z.ltb_lt in Hj0. apply Z.leb_le in Hj63. apply Z.leb_le in Hm.
  destruct (lin_of a) as [c ts] eqn:Hl. cbn [fst snd] in H.
  destruct (lowsum kn (2 ^ j) ts) as [s|] eqn:Hls; [|discriminate]. injection H as <-.
  assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (Hm64 : 0 <= m' < 2 ^ 64) by (unfold m', two64; apply Z.mod_pos_bound; lia).
  pose proof (lin_of_sound E a) as Hs. rewrite Hl in Hs. unfold lden in Hs. cbn [fst snd] in Hs.
  set (V := bv_unsigned (edenot E a)) in *. change (AX2S.uE E a) with V in Hs.
  assert (HV : 0 <= V < 2 ^ 64) by (pose proof (u64_range (edenot E a)) as X; unfold two64 in X; exact X).
  assert (Hmod : V mod 2 ^ j = (c + s) mod 2 ^ j).
  { rewrite <- (eqm_mod_pow2 _ _ j ltac:(lia) Hs). rewrite Z.add_mod, (lowsum_sound segs E base kn _ ts s HK Hp Hls) by lia.
    rewrite <- Z.add_mod by lia. reflexivity. }
  rewrite <- (Z_to_bv_bv_unsigned 64 (alu64 ALU_AND _ _)). rewrite u_and64, u_lit64. fold V. fold m'.
  rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E (unlin _))). apply eqm_Z_to_bv.
  eapply eqm_trans; [apply unlin_sound|]. unfold lden. cbn [fst snd].
  rewrite (land_lowmask V m' j HV ltac:(lia) ltac:(unfold two64 in Hm; lia)). rewrite Hmod.
  destruct Hs as [q Hq]. exists q. lia.
Qed.

Lemma bitnorm_o_denot : forall segs E base kn e, know_ok segs E base kn -> edenot E (bitnorm_o kn e) = edenot E e.
Proof.
  intros segs E base kn e HK. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k off n]; cbn [bitnorm_o]; try reflexivity.
  - assert (Hdef : edenot E (mkAluK kn op (bitnorm_o kn a) (bitnorm_o kn b)) = edenot E (EAlu op a b))
      by (rewrite (mkAluK_denot segs E base kn _ _ _ HK), IHa, IHb; reflexivity).
    destruct op; try exact Hdef.
    destruct (bitnorm_o kn b) as [m| | | | | | |] eqn:Hb; try exact Hdef.
    destruct (and_lowmask_o kn (bitnorm_o kn a) m) as [r|] eqn:Hr; [|exact Hdef].
    rewrite (and_lowmask_o_denot segs E base kn _ m r HK Hr), IHa. cbn [edenot]. rewrite <- IHb. reflexivity.
  - rewrite (mkMdK_denot segs E base kn _ _ _ HK), IHa, IHb. reflexivity.
Qed.

(* [comment removed for export] *)
Definition odd_xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 40 then node_oddspell args cs else None.

Section Node.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable ISP : Z.
  Variable FS0 : Fs.Fs.

  Theorem node_oddspell_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_oddspell args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn HK. unfold node_oddspell in Hn.
    destruct args as [|[r| | | | | | |] [|e [|]]]; try discriminate Hn.
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection Hn as <-.
    apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HKn.
    pose proof (respell_ok_sound SEGS E _ (kn cs) _ e HKn Hok) as Heq.
    rewrite (bitnorm_o_denot SEGS E _ (kn cs) _ HKn) in Heq.
    assert (Hrefl : forall b, env_agree b E E) by (intros b; split; [intros; reflexivity | reflexivity]).
    apply (HK E R FULL model); [split; apply Hrefl | | reflexivity].
    destruct HC; constructor; cbn [set_reg with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption; try reflexivity.
    apply regs_ok_respell; [assumption | lia | unfold reg in Heq; symmetry; exact Heq].
  Qed.
  Theorem odd_xn_sound : ext_stmt SEGS A nx0 LIMIT odd_xn SINV argH ISP FS0.
  Proof.
    intros id args cs cs' E R FULL model T HC Hal Hn Hk. unfold odd_xn in Hn.
    destruct (Nat.eqb id 40); [|discriminate Hn].
    exact (node_oddspell_sound args cs cs' E R FULL model T HC Hal Hn Hk).
  Qed.
End Node.
