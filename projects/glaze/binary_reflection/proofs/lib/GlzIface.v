(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzNodesArith.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.



(* [comment removed for export] *)
Fixpoint terms_eqb (a b : list (Z * expr)) : bool :=
  match a, b with
  | [], [] => true
  | (k, e) :: a', (k', e') :: b' => (Z.eqb k k' && expr_eqb e e' && terms_eqb a' b')%bool
  | _, _ => false
  end.
Definition lin_eqb (a b : lin) : bool := (Z.eqb (fst a) (fst b) && terms_eqb (snd a) (snd b))%bool.

(* [comment removed for export] *)
Definition same_val (x' x : expr) : bool := (expr_eqb x' x || lin_eqb (lin_of x') (lin_of x))%bool.

(* [comment removed for export] *)
Definition mul_of (P x : expr) : option Z :=
  let lp := lin_of P in let lx := lin_of x in
  match snd lp, snd lx with
  | (kp, _) :: _, (kx, _) :: _ =>
      if Z.eqb kx 0 then None else
      if negb (Z.eqb (kp mod kx) 0) then None else
      let m := kp / kx in
      if (Z.ltb 0 m && lin_eqb lp (lscale m lx))%bool then Some m else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Inductive mkind := MK64 | MK32 | MKHU.

(* [comment removed for export] *)
Definition mulhu_lit (a b x : expr) : option Z :=
  match is_lit b with
  | Some m => if same_val a x then Some (m mod two64) else None
  | None => match is_lit a with
            | Some m => if same_val b x then Some (m mod two64) else None
            | None => None
            end
  end.

(* [comment removed for export] *)
Definition mulhu_under (P x : expr) : option Z :=
  match P with EMd M_MULHU a b => mulhu_lit a b x | _ => None end.

(* [comment removed for export] *)
Definition magic_of (x q : expr) : option (Z * Z * mkind) :=
  match q with
  | EAlu ALU_SRL P (ELit s) =>
      match mulhu_under P x with
      | Some m => Some (m, 64 + s mod 64, MKHU)
      | None => match mul_of P x with Some m => Some (m, s mod 64, MK64) | None => None end
      end
  | EAluw ALU_SRL P (ELit s) =>
      match mul_of P x with Some m => Some (m, (s mod 64) mod 32, MK32) | None => None end
  | EMd M_MULHU a b =>
      match mulhu_lit a b x with Some m => Some (m, 64, MKHU) | None => None end
  | _ => None
  end.

(* [comment removed for export] *)
Definition magic_okb (k : mkind) (m sh xh : Z) : bool :=
  match k with
  | MK64 => Z.ltb (m * xh) two64
  | MK32 => (Z.ltb (m * xh) (2 ^ 32) && Z.ltb (m * xh / 2 ^ sh) (2 ^ 31))%bool
  | MKHU => true
  end.

(* [comment removed for export] *)
Definition rem_expr (x q : expr) (d : Z) : expr := esub x (escale d q).

Definition node_divmagic (args : list expr) (cs : acs) : option acs :=
  match args with
  | [x; q; ELit d] =>
      match magic_of x q, xb2 (kn cs) x with
      | Some (m, sh, k), Some (xl, xh) =>
          let e := m * d - 2 ^ sh in
          let xl' := Z.max 0 xl in
          if (Z.leb 1 d && Z.ltb d two64 && Z.leb 0 e && Z.ltb (xh * e) (2 ^ sh) && Z.leb 0 sh
              && Z.leb xl' xh && magic_okb k m sh xh)%bool
          then Some (add_kn cs [KRange q (xl' / d) (xh / d); KRange (rem_expr x q d) 0 (d - 1)])
          else None
      | _, _ => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition ENUM_MAX : Z := 65536.

Definition eval_at (s e : expr) (j : Z) : option Z :=
  match evalS s (wrap64 j) e with Some v => Some (v mod two64) | None => None end.

Definition node_enumrange (args : list expr) (cs : acs) : option acs :=
  match args with
  | [e; s] =>
      match xb2 (kn cs) s with
      | Some (lo, hi) =>
          if (Z.leb 0 lo && Z.leb (hi - lo) ENUM_MAX)%bool then
            match enum_minmax (eval_at s e) lo hi with
            | Some (mn, mx) => Some (add_kn cs [KRange e mn mx])
            | None => None
            end
          else None
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma terms_eqb_eq : forall a b, terms_eqb a b = true -> a = b.
Proof.
  induction a as [|[k e] a IH]; intros [|[k' e'] b] H; cbn [terms_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply expr_eqb_eq in H2. apply IH in H3. subst. reflexivity.
Qed.

Lemma lin_eqb_eq : forall a b, lin_eqb a b = true -> a = b.
Proof.
  intros [c t] [c' t'] H. unfold lin_eqb in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply terms_eqb_eq in H2. subst. reflexivity.
Qed.

Lemma eqm_small_eq : forall a b, eqm a b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof. intros a b [q Hq] Ha Hb. assert (q = 0) by nia. subst q. lia. Qed.

Lemma uE_range : forall E e, 0 <= uE E e < 2 ^ 64.
Proof. intros E e. unfold uE. apply u64_range. Qed.

(* [comment removed for export] *)
Lemma same_val_sound : forall E x' x, same_val x' x = true -> uE E x' = uE E x.
Proof.
  intros E x' x H. unfold same_val in H. apply Bool.orb_true_iff in H as [H|H].
  - apply expr_eqb_eq in H. subst. reflexivity.
  - apply lin_eqb_eq in H.
    apply eqm_small_eq; [|apply uE_range|apply uE_range].
    eapply eqm_trans; [apply eqm_sym; apply lin_of_sound|]. rewrite H. apply lin_of_sound.
Qed.

(* [comment removed for export] *)
Lemma mul_of_sound : forall E P x m, mul_of P x = Some m -> 0 < m /\ eqm (uE E P) (m * uE E x).
Proof.
  intros E P x m H. unfold mul_of in H.
  destruct (snd (lin_of P)) as [|[kp ep] tp] eqn:HP; [discriminate|].
  destruct (snd (lin_of x)) as [|[kx ex] tx] eqn:HX; [discriminate|].
  destruct (Z.eqb kx 0); [discriminate|].
  destruct (negb (Z.eqb (kp mod kx) 0)); [discriminate|].
  destruct (Z.ltb 0 (kp / kx) && lin_eqb (lin_of P) (lscale (kp / kx) (lin_of x)))%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hm Heq]. apply Z.ltb_lt in Hm. apply lin_eqb_eq in Heq.
  split; [exact Hm|].
  eapply eqm_trans; [apply eqm_sym; apply lin_of_sound|]. rewrite Heq.
  eapply eqm_trans; [apply lscale_sound|]. apply eqm_mul_l. apply lin_of_sound.
Qed.

Lemma pow2_pos : forall k, 0 <= k -> 0 < 2 ^ k.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

Lemma is_lit_some : forall e m, is_lit e = Some m -> e = ELit m.
Proof. intros e m H. destruct e; cbn [is_lit] in H; try discriminate. injection H as <-. reflexivity. Qed.

Lemma mulhu_lit_sound : forall E a b x m0, mulhu_lit a b x = Some m0 ->
  0 <= m0 /\ uE E (EMd M_MULHU a b) = uE E x * m0 / 2 ^ 64.
Proof.
  intros E a b x m0 H. unfold mulhu_lit in H.
  destruct (is_lit b) as [m1|] eqn:Hb.
  - apply is_lit_some in Hb. subst b.
    destruct (same_val a x) eqn:Hs; [|discriminate]. injection H as <-.
    split; [apply Z.mod_pos_bound; rewrite two64_eq; lia|].
    pose proof (same_val_sound E a x Hs) as Q. unfold uE in *. cbn [edenot].
    rewrite u_mulhu64, u_lit64, Q. reflexivity.
  - destruct (is_lit a) as [m1|] eqn:Ha; [|discriminate].
    apply is_lit_some in Ha. subst a.
    destruct (same_val b x) eqn:Hs; [|discriminate]. injection H as <-.
    split; [apply Z.mod_pos_bound; rewrite two64_eq; lia|].
    pose proof (same_val_sound E b x Hs) as Q. unfold uE in *. cbn [edenot].
    rewrite u_mulhu64, u_lit64, Q, Z.mul_comm. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma magic_of_sound : forall E x q m sh k xh,
  magic_of x q = Some (m, sh, k) ->
  uE E x <= xh -> magic_okb k m sh xh = true ->
  0 <= m /\ 0 <= sh /\ uE E q = (uE E x * m) / 2 ^ sh.
Proof.
  intros E x q m sh k xh H Hxh Hok.
  pose proof (uE_range E x) as HX. set (X := uE E x) in *.
  assert (MULHU : forall a b m0, mulhu_lit a b x = Some m0 ->
            0 <= m0 /\ uE E (EMd M_MULHU a b) = X * m0 / 2 ^ 64).
  { intros a b m0 Hab. subst X. exact (mulhu_lit_sound E a b x m0 Hab). }
  unfold magic_of in H.
  destruct q as [| |op a b|op a b|op a b| | |]; try discriminate.
  - (* [comment removed for export] *)
    destruct op; try discriminate. destruct b as [s| | | | | | |]; try discriminate.
    destruct (mulhu_under a x) as [m0|] eqn:Hmu.
    + (* [comment removed for export] *)
      injection H as Em Esh Ek.
      destruct a as [| | | |op' a' b'| | |]; try discriminate Hmu. destruct op'; try discriminate Hmu.
      cbn [mulhu_under] in Hmu.
      destruct (MULHU a' b' _ Hmu) as [Hm0 Hv].
      split; [lia|]. split; [pose proof (Z.mod_pos_bound s 64); lia|].
      unfold uE. cbn [edenot]. rewrite u_srl64.
      change (bv_unsigned (mul_div M_MULHU (edenot E a') (edenot E b'))) with (uE E (EMd M_MULHU a' b')).
      rewrite Hv. cbn [edenot]. rewrite u_lit64, two64_eq.
      replace ((s mod 2 ^ 64) mod 64) with (s mod 64).
      2:{ symmetry. apply Z.mod_mod_divide. exists (2 ^ 58). reflexivity. }
      rewrite <- Esh, <- Em. rewrite Z.pow_add_r by (pose proof (Z.mod_pos_bound s 64); lia).
      rewrite Z.div_div; [reflexivity | lia | apply pow2_pos; pose proof (Z.mod_pos_bound s 64); lia].
    + (* [comment removed for export] *)
      destruct (mul_of a x) as [m0|] eqn:Hm; [|discriminate]. injection H as Em Esh Ek.
      destruct (mul_of_sound E a x m0 Hm) as [Hm0 Heqm]. fold X in Heqm.
      rewrite <- Ek in Hok. cbn [magic_okb] in Hok. apply Z.ltb_lt in Hok. rewrite two64_eq in Hok.
      assert (HP : uE E a = m0 * X).
      { apply eqm_small_eq; [exact Heqm | apply uE_range | nia]. }
      split; [lia|]. split; [pose proof (Z.mod_pos_bound s 64); lia|].
      unfold uE. cbn [edenot]. rewrite u_srl64. fold (uE E a). rewrite HP.
      cbn [edenot]. rewrite u_lit64, two64_eq.
      replace ((s mod 2 ^ 64) mod 64) with (s mod 64).
      2:{ symmetry. apply Z.mod_mod_divide. exists (2 ^ 58). reflexivity. }
      rewrite <- Esh, <- Em, Z.mul_comm. reflexivity.
  - (* [comment removed for export] *)
    destruct op; try discriminate. destruct b as [s| | | | | | |]; try discriminate.
    destruct (mul_of a x) as [m0|] eqn:Hm; [|discriminate]. injection H as Em Esh Ek.
    destruct (mul_of_sound E a x m0 Hm) as [Hm0 Heqm]. fold X in Heqm.
    rewrite <- Ek in Hok. cbn [magic_okb] in Hok. apply andb_prop in Hok as [Hok1 Hok2].
    apply Z.ltb_lt in Hok1. apply Z.ltb_lt in Hok2.
    assert (HP : uE E a = m0 * X).
    { apply eqm_small_eq; [exact Heqm | apply uE_range | nia]. }
    split; [lia|]. split; [pose proof (Z.mod_pos_bound (s mod 64) 32); lia|].
    unfold uE. cbn [edenot].
    rewrite (u_srlw_small (edenot E a) (Z_to_bv 64 s) (s mod 64)).
    + fold (uE E a). rewrite HP, Z.mul_comm, <- Esh, <- Em. reflexivity.
    + rewrite u_lit64, two64_eq. apply Z.mod_mod_divide. exists (2 ^ 58). reflexivity.
    + fold (uE E a). rewrite HP. subst m. nia.
    + fold (uE E a). rewrite HP. subst m sh.
      eapply Z.le_lt_trans; [|exact Hok2].
      apply Z.div_le_mono; [apply pow2_pos; pose proof (Z.mod_pos_bound (s mod 64) 32); lia | nia].
  - (* [comment removed for export] *)
    destruct op; try discriminate.
    destruct (mulhu_lit a b x) as [m0|] eqn:Hab; [|discriminate]. injection H as Em Esh Ek.
    destruct (MULHU a b _ Hab) as [Hm0 Hv]. rewrite <- Em, <- Esh. split; [exact Hm0|]. split; [lia|]. exact Hv.
Qed.

(* [comment removed for export] *)
Lemma divmagic_facts : forall SEGS E M x q d m sh k xl xh,
  magic_of x q = Some (m, sh, k) ->
  xl <= uE E x <= xh -> magic_okb k m sh xh = true ->
  1 <= d -> d < two64 -> 0 <= m * d - 2 ^ sh -> xh * (m * d - 2 ^ sh) < 2 ^ sh -> 0 <= sh ->
  kentry_ok SEGS E M (KRange q (Z.max 0 xl / d) (xh / d))
  /\ kentry_ok SEGS E M (KRange (rem_expr x q d) 0 (d - 1)).
Proof.
  intros SEGS E M x q d m sh k xl xh Hmg Hx Hok Hd Hd64 He Hhe HS.
  pose proof (uE_range E x) as HX.
  destruct (magic_of_sound E x q m sh k xh Hmg ltac:(lia) Hok) as (Hm0 & _ & HQ).
  set (X := uE E x) in *. set (Q := uE E q) in *.
  destruct (magic_div_facts X d m sh (m * d - 2 ^ sh) (Z.max 0 xl) xh Q) as (HQd & HQb & HR); try lia.
  split.
  - cbn [kentry_ok]. fold (uE E q). fold Q. exact HQb.
  - cbn [kentry_ok]. unfold rem_expr, esub, escale.
    rewrite mkAlu_denot, u_sub64, mkMd_denot, u_mul64. cbn [edenot]. rewrite u_lit64.
    fold (uE E x) (uE E q). fold X Q. rewrite two64_eq in Hd64. rewrite two64_eq.
    rewrite (Z.mod_small d) by lia.
    rewrite Zminus_mod_idemp_r. rewrite Z.mod_small by nia. exact HR.
Qed.

(* [comment removed for export] *)
Lemma eval_at_sound : forall E s e j v,
  uE E s = j -> eval_at s e j = Some v -> uE E e = v.
Proof.
  intros E s e j v Hs H. unfold eval_at in H.
  destruct (evalS s (wrap64 j) e) as [v0|] eqn:Hev; [|discriminate]. injection H as <-.
  rewrite evalS_eq in Hev.
  pose proof (eval_closed_sound E _ _ Hev) as Hd.
  rewrite (esubst_sound E s (ELit j) e) in Hd.
  - unfold uE. rewrite Hd, u_lit64, two64_eq. reflexivity.
  - cbn [edenot]. rewrite <- Hs. unfold uE. apply Z_to_bv_bv_unsigned.
Qed.

Lemma enumrange_fact : forall SEGS E M e s lo hi mn mx,
  lo <= uE E s <= hi ->
  enum_minmax (eval_at s e) lo hi = Some (mn, mx) ->
  kentry_ok SEGS E M (KRange e mn mx).
Proof.
  intros SEGS E M e s lo hi mn mx Hs H.
  destruct (enum_minmax_spec _ _ _ _ _ H (uE E s) Hs) as (v & Hv & Hb).
  cbn [kentry_ok]. fold (uE E e). rewrite (eval_at_sound E s e _ v eq_refl Hv). exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable nx0 : nat.
Variable PERMc : list (Z * Z).   (* [comment removed for export] *)
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ).

(* [comment removed for export] *)
Lemma add_facts_sound : forall (node : acs -> option acs),
  (forall cs cs' E fx R M model, cs_ok E cs fx R M model -> node cs = Some cs' ->
      exists K, cs' = add_kn cs K /\ know_ok SEGS E M K) ->
  node1_stmt always node.
Proof.
  intros node Hnode cs cs' E fx R M model T HC _ Hn Hk.
  destruct (Hnode cs cs' E fx R M model HC Hn) as (K & -> & HK).
  apply (Hk E fx R M model).
  - split; apply env_agree_refl.
  - unfold add_kn. apply cs_ok_set_kn; [exact HC|]. apply Forall_app. split; [exact HK | exact (co_know HC)].
  - reflexivity.
Qed.

Theorem node_divmagic_sound : forall args, node1_stmt always (node_divmagic args).
Proof.
  intros args. apply add_facts_sound. intros cs cs' E fx R M model HC Hn.
  unfold node_divmagic in Hn.
  destruct args as [|x [|q [|[d| | | | | | |] [|]]]]; try discriminate.
  destruct (magic_of x q) as [[[m sh] k]|] eqn:Hmg; [|discriminate].
  destruct (xb2 (kn cs) x) as [[xl xh]|] eqn:Hxb; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc Hlh]. apply andb_prop in Hc as [Hc HS].
  apply andb_prop in Hc as [Hc Hhe]. apply andb_prop in Hc as [Hc He]. apply andb_prop in Hc as [Hd1 Hd64].
  apply Z.leb_le in Hd1. apply Z.ltb_lt in Hd64. apply Z.leb_le in He. apply Z.ltb_lt in Hhe. apply Z.leb_le in HS.
  pose proof (xb2_sound SEGS E M (kn cs) x xl xh (co_know HC) Hxb) as Hx. fold (uE E x) in Hx.
  destruct (divmagic_facts SEGS E M x q d m sh k xl xh Hmg Hx Hok Hd1 Hd64 He Hhe HS) as [F1 F2].
  eexists. split; [reflexivity|]. constructor; [exact F1|]. constructor; [exact F2 | constructor].
Qed.

Theorem node_enumrange_sound : forall args, node1_stmt always (node_enumrange args).
Proof.
  intros args. apply add_facts_sound. intros cs cs' E fx R M model HC Hn.
  unfold node_enumrange in Hn.
  destruct args as [|e [|s [|]]]; try discriminate.
  destruct (xb2 (kn cs) s) as [[lo hi]|] eqn:Hxb; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (enum_minmax (eval_at s e) lo hi) as [[mn mx]|] eqn:Hen; [|discriminate].
  injection Hn as <-.
  pose proof (xb2_sound SEGS E M (kn cs) s lo hi (co_know HC) Hxb) as Hs. fold (uE E s) in Hs.
  eexists. split; [reflexivity|]. constructor; [|constructor].
  exact (enumrange_fact SEGS E M e s lo hi mn mx Hs Hen).
Qed.

End Sound.
End GlzNodesArith.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
(* [comment removed for export] *)
#[local] Notation "a || b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive smode : Type := MS | ML.

Definition hole (m : smode) : nat := match m with MS => 0%nat | ML => 1%nat end.
(* [comment removed for export] *)
Definition strS (obj s : expr) : list kentry := [ KWord (SA obj 0) 1 (escale 2 s); KRange s 0 22 ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record gtable : Type := GT {
  g_ro_lo : Z; g_ro_hi : Z;        (* [comment removed for export] *)
  g_img_lo : Z; g_img_hi : Z;      (* [comment removed for export] *)
  g_newh_got : Z; g_newh_cell : Z; g_newh_val : Z;
                                   (* [comment removed for export] *)
  g_priv : list (Z * Z);           (* [comment removed for export] *)
  g_tp : Z;                        (* [comment removed for export] *)
  g_malloc : Z; g_free : Z;        (* [comment removed for export] *)
  g_malloc_thunk : Z; g_free_thunk : Z;   (* [comment removed for export] *)
  g_opnew : Z; g_opdel : Z; g_opdel_sized : Z;   (* [comment removed for export] *)
  g_memcpy : Z; g_memset : Z; g_memmove : Z; g_strlen : Z;
  g_hello : Z;                      (* [comment removed for export] *)
  g_str_resize : Z                  (* [comment removed for export] *)
}.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition MSTK : Z := 2048.                (* [comment removed for export] *)
Definition NMAX : Z := 2 ^ 40.              (* [comment removed for export] *)
Definition MBLK : Z := 2 ^ 20 + 2 ^ 13.     (* [comment removed for export] *)
Definition mcost (nhi : Z) : Z := nhi + MBLK.   (* [comment removed for export] *)
Definition MCNT : Z := 1.                   (* [comment removed for export] *)
Definition LMAX : Z := 64.
                 (* [comment removed for export] *)
Definition GBUDGET : Z := 3 * 2 ^ 32.       (* [comment removed for export] *)
Definition GCOUNT : Z := LMAX.












   (* [comment removed for export] *)

Section WithTables.
Variable segs : list MemImageType.Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.
Variable G : gtable.
Variable bcap ccap : Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition load_range_fact (sz : msize) (sx : bool) (v : nat) : list kentry :=
  match sz, sx with
  | SZ1, false => [KRange (EVar v) 0 255]
  | SZ2, false => [KRange (EVar v) 0 65535]
  | SZ4, false => [KRange (EVar v) 0 4294967295]
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition node_imgload (cs : acs) : option acs :=
  match itab_lookup IT (pc cs) with
  | Some (Load sz sx rd rs imm) =>
      let n := msize_bytes sz in
      let a := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm) in
      match xlo (kn cs) a, xhi (kn cs) a with
      | Some lo, Some hi =>
          if (fresh_ok nx0 cs && Z.leb (g_ro_lo G) lo && Z.leb (hi + Z.of_nat n) (g_ro_hi G) && negb (bv_eqb rd 0%bv)
              && Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64
              && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool
          then let v := nxt cs in
               let ss := a_ss cs in
               Some (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs ss) (ridx rd) (EVar v))
                                       (load_range_fact sz sx v ++ s_know ss) (S v)))
          else None
      | _, _ => None
      end
  | Some _ => Some cs      (* [comment removed for export] *)
  | None => Some cs
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_range (K : kentry) : option (expr * Z * expr) :=
  match K with
  | KWord (SA b k) w _ => Some (b, k, ELit (Z.of_nat w))
  | KZero (SA b k) n | KBlob (SA b k) n _ | KWr (SA b k) n | KFill (SA b k) n _ | KUnk (SA b k) n => Some (b, k, n)
  | _ => None
  end.

Fixpoint lit_disjoint (lo hi : Z) (ps : list (Z * Z)) : bool :=
  match ps with
  | [] => true
  | (a, b) :: r => ((hi <=? a) || (b <=? lo)) && lit_disjoint lo hi r
  end%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition owned_x (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (b : expr) (off : Z) (n : expr) : bool :=
  existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in xinside k b off n lb lk (snd bl)) live
  || in_floor k fl top bud b off n.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bflat_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match base_range k b, xhi k n with
  | Some (lo, hi), Some nh => Z.leb 0 (lo + off) && Z.ltb (hi + off) two64 && Z.leb (hi + off + nh) two64
  | _, _ => false
  end%bool.
(* [comment removed for export] *)
Definition live_flat (cs : acs) : bool :=
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x (kn cs) lb lk (snd bl)) (a_vis cs ++ a_ghost cs).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition above_x (k : list kentry) (top sp : expr) (b : expr) (off : Z) (n : expr) : bool :=
  match xlo k top with
  | Some tlo => Z.ltb 0 tlo && lin_ge0 k [(b, off)] [(top, 0)] && lin_ge0 k [(top, 0)] [(sp, 0)] && flat_x k b off n
  | None => false
  end%bool.
Definition keep_sticky (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true
  | KImg lo hi => Z.leb (g_ro_lo G) lo && Z.leb hi (g_img_hi G) && lit_disjoint lo hi (g_priv G)
  | KWr (SA b off) n | KUnk (SA b off) n => owned_x k live fl top bud b off n || above_x k top sp b off n   (* [comment removed for export] *)
  | _ => false
  end%bool.
(* [comment removed for export] *)
Definition img_lit_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match xlo k (eaddz b off), xhi k (eaddz b off), xhi k n with
  | Some lo, Some hi, Some nh => Z.leb (g_ro_lo G) lo && Z.leb (hi + nh) (g_img_hi G) && Z.leb 0 nh && lit_disjoint lo (hi + nh) (g_priv G)
  | _, _, _ => false
  end%bool.
Definition keep_content (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KWord _ _ _ | KZero _ _ | KFill _ _ _ | KBlob _ _ _ =>
      match kentry_range K with
      | Some (b, off, n) =>
          let '(spb, spk) := split_lit sp in
          (owned_x k live fl top bud b off n && ranges_apart_x k b off n spb (spk - MSTK) (ELit MSTK)) || above_x k top sp b off n
          || img_lit_x k b off n
      | None => false
      end
  | _ => false
  end%bool.


(* [comment removed for export] *)
Definition keep_owned_ref (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (v : nat) : list kentry :=
  let '(spb, spk) := split_lit sp in
  List.filter (fun K => kentry_vars_lt v K && keep_sticky k live fl top bud sp K)%bool k
  ++ List.filter (fun K => kentry_vars_lt v K && keep_content k live fl top bud sp K)%bool (kn_cutout k spb (spk - MSTK) (ELit MSTK)).

(* [comment removed for export] *)
Definition in_floor_b (bc : AX2B.bctx) (fl : option expr) (top : expr) (bud : Z) (b : expr) (off : Z) (n : expr) : bool :=
  let '(tb, tk) := split_lit top in
  match AX2B.base_rangeB bc tb with
  | Some (tlo, thi) =>
      match fl with
      | None => if (Z.leb 0 bud && Z.leb CEIL (tlo + tk - bud) && Z.ltb (thi + tk) two64)%bool then AX2B.xinsideB bc b off n tb (tk - bud) (ELit bud) else false
      | Some f => if (Z.leb 0 bud && Z.ltb 0 (tlo + tk) && Z.ltb (thi + tk) two64)%bool
                  then (if AX2B.lin_ge0B bc [(b, off)] [(f, 0%Z)] then AX2B.lin_ge0B bc [(tb, tk)] [(b, off); (n, 0%Z)] else false) else false
      end
  | None => false
  end.
Lemma in_floor_b_eq : forall k fl top bud b off n, in_floor_b (AX2B.mkbc k) fl top bud b off n = in_floor k fl top bud b off n.
Proof.
  intros. unfold in_floor_b, in_floor. destruct (split_lit top) as [tb tk].
  rewrite AX2B.base_rangeB_eqf, AX2B.xinsideB_eqf, AX2B.lin_ge0B_eqf.
  destruct (base_range k tb) as [[tlo thi]|]; [|reflexivity]. destruct fl as [f|].
  - destruct (Z.leb 0 bud); [|reflexivity]. destruct (Z.ltb 0 (tlo + tk)); [|reflexivity]. destruct (Z.ltb (thi + tk) two64); [|reflexivity].
    cbn [andb]. destruct (lin_ge0 k [(b, off)] [(f, 0)]); reflexivity.
  - destruct (Z.leb 0 bud); [|reflexivity]. destruct (Z.leb CEIL (tlo + tk - bud)); [|reflexivity]. destruct (Z.ltb (thi + tk) two64); reflexivity.
Qed.
Fixpoint exists_inside_b (bc : AX2B.bctx) (b : expr) (off : Z) (n : expr) (live : list (expr * expr)) : bool :=
  match live with
  | [] => false
  | bl :: r => if (let '(lb, lk) := split_lit (fst bl) in AX2B.xinsideB bc b off n lb lk (snd bl)) then true else exists_inside_b bc b off n r
  end.
Lemma exists_inside_b_eq : forall k b off n live,
  exists_inside_b (AX2B.mkbc k) b off n live = existsb (fun bl => let '(lb, lk) := split_lit (fst bl) in xinside k b off n lb lk (snd bl)) live.
Proof.
  intros k b off n live. induction live as [|bl r IH]; [reflexivity|]. cbn [exists_inside_b existsb]. rewrite IH, AX2B.xinsideB_eqf.
  destruct (split_lit (fst bl)) as [lb lk]. destruct (xinside k b off n lb lk (snd bl)); reflexivity.
Qed.
Definition owned_x_b (bc : AX2B.bctx) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (b : expr) (off : Z) (n : expr) : bool :=
  if exists_inside_b bc b off n live then true else in_floor_b bc fl top bud b off n.
Lemma owned_x_b_eq : forall k live fl top bud b off n, owned_x_b (AX2B.mkbc k) live fl top bud b off n = owned_x k live fl top bud b off n.
Proof. intros. unfold owned_x_b, owned_x. rewrite exists_inside_b_eq, in_floor_b_eq. reflexivity. Qed.
Definition above_x_b (bc : AX2B.bctx) (top sp : expr) (b : expr) (off : Z) (n : expr) : bool :=
  match AX2B.xloB bc top with
  | Some tlo => if Z.ltb 0 tlo then (if AX2B.lin_ge0B bc [(b, off)] [(top, 0)] then (if AX2B.lin_ge0B bc [(top, 0)] [(sp, 0)] then flat_xB bc b off n else false) else false) else false
  | None => false
  end.
Lemma above_x_b_eq : forall k top sp b off n, above_x_b (AX2B.mkbc k) top sp b off n = above_x k top sp b off n.
Proof.
  intros. unfold above_x_b, above_x. rewrite AX2B.xloB_eqf, AX2B.lin_ge0B_eqf, flat_xB_eqf.
  destruct (xlo k top) as [tlo|]; [|reflexivity]. destruct (Z.ltb 0 tlo); [|reflexivity]. cbn [andb].
  destruct (lin_ge0 k [(b, off)] [(top, 0)]); [|reflexivity]. cbn [andb]. destruct (lin_ge0 k [(top, 0)] [(sp, 0)]); reflexivity.
Qed.
Definition keep_sticky_b (bc : AX2B.bctx) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true
  | KImg lo hi => Z.leb (g_ro_lo G) lo && Z.leb hi (g_img_hi G) && lit_disjoint lo hi (g_priv G)
  | KWr (SA b off) n | KUnk (SA b off) n => if owned_x_b bc live fl top bud b off n then true else above_x_b bc top sp b off n
  | _ => false
  end%bool.
Lemma keep_sticky_b_eq : forall k live fl top bud sp K, keep_sticky_b (AX2B.mkbc k) live fl top bud sp K = keep_sticky k live fl top bud sp K.
Proof. intros. unfold keep_sticky_b, keep_sticky. destruct K as [| | | | | | [b off] n0 | | | [b off] n0]; try reflexivity; rewrite owned_x_b_eq, above_x_b_eq; reflexivity. Qed.
Definition img_lit_x_b (bc : AX2B.bctx) (b : expr) (off : Z) (n : expr) : bool :=
  match AX2B.xloB bc (eaddz b off), AX2B.xhiB bc (eaddz b off), AX2B.xhiB bc n with
  | Some lo, Some hi, Some nh => Z.leb (g_ro_lo G) lo && Z.leb (hi + nh) (g_img_hi G) && Z.leb 0 nh && lit_disjoint lo (hi + nh) (g_priv G)
  | _, _, _ => false
  end%bool.
Lemma img_lit_x_b_eq : forall k b off n, img_lit_x_b (AX2B.mkbc k) b off n = img_lit_x k b off n.
Proof. intros. unfold img_lit_x_b, img_lit_x. rewrite AX2B.xloB_eqf, AX2B.xhiB_eqf. reflexivity. Qed.
Definition keep_content_b (bc : AX2B.bctx) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (K : kentry) : bool :=
  match K with
  | KWord _ _ _ | KZero _ _ | KFill _ _ _ | KBlob _ _ _ =>
      match kentry_range K with
      | Some (b, off, n) =>
          let '(spb, spk) := split_lit sp in
          if (if (if owned_x_b bc live fl top bud b off n then AX2B.ranges_apart_xB bc b off n spb (spk - MSTK) (ELit MSTK) else false) then true
              else above_x_b bc top sp b off n) then true else img_lit_x_b bc b off n
      | None => false
      end
  | _ => false
  end.
Lemma keep_content_b_eq : forall k live fl top bud sp K, keep_content_b (AX2B.mkbc k) live fl top bud sp K = keep_content k live fl top bud sp K.
Proof.
  intros. unfold keep_content_b, keep_content.
  destruct K; try reflexivity; (destruct (kentry_range _) as [[[b off] nn]|]; [|reflexivity]); destruct (split_lit sp) as [spb spk];
    rewrite owned_x_b_eq, above_x_b_eq, img_lit_x_b_eq, AX2B.ranges_apart_xB_eqf; destruct (owned_x k live fl top bud b off nn); cbn [andb]; reflexivity.
Qed.
Definition keep_owned (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (v : nat) : list kentry :=
  let '(spb, spk) := split_lit sp in
  let bc := AX2B.mkbc k in
  List.filter (fun K => if kentry_vars_lt v K then keep_sticky_b bc live fl top bud sp K else false) k
  ++ List.filter (fun K => if kentry_vars_lt v K then keep_content_b bc live fl top bud sp K else false) (kn_cutoutM k spb (spk - MSTK) (ELit MSTK)).
Lemma keep_owned_eq : forall k live fl top bud sp v, keep_owned k live fl top bud sp v = keep_owned_ref k live fl top bud sp v.
Proof.
  intros. unfold keep_owned, keep_owned_ref. destruct (split_lit sp) as [spb spk]. cbv zeta. rewrite kn_cutoutM_eq.
  f_equal; apply filter_ext; intros K; [rewrite keep_sticky_b_eq | rewrite keep_content_b_eq]; destruct (kentry_vars_lt v K); reflexivity.
Qed.

(* [comment removed for export] *)
Definition ret_regs (sr : list expr) (nx : nat) (rv : option expr) : list expr :=
  let sr1 := sr_fresh sr caller_saved nx in
  match rv with Some e => sr_upd sr1 10 e | None => sr1 end.

(* [comment removed for export] *)
Definition call_ok (entry : Z) (cs : acs) : option Z :=
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 4 with
  | Some ret, Some tp =>
      let k := kn cs in let sp := reg cs 2 in let '(spb, spk) := split_lit sp in
      if (Z.eqb tp (g_tp G) && fresh_ok nx0 cs && Nat.eqb (length (s_regs (a_ss cs))) 32
          && Z.leb 4 (ealign k sp) && kwritable_x k k spb (spk - MSTK) (ELit MSTK)
          && in_floor k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - MSTK) (ELit MSTK)     (* [comment removed for export] *)
          && live_flat cs)%bool
      then Some ret else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Fixpoint cost_hi (k : list kentry) (live : list (expr * expr)) : option Z :=
  match live with
  | [] => Some 0
  | (_, n) :: r => match xhi k n, cost_hi k r with Some h, Some c => Some (h + MBLK + c) | _, _ => None end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition disj_facts (p n : expr) (live : list (expr * expr)) : list kentry :=
  map (fun bl => let '(lb, lk) := split_lit (fst bl) in KDisj (SA p 0) n (SA lb lk) (snd bl)) live.

(* [comment removed for export] *)
Definition kdisj_of_fact (k : list kentry) (p n : expr) (K : kentry) : option kentry :=
  match kentry_range K with
  | Some (b, off, len) =>
      match b with
      | ELit _ => None                                   (* [comment removed for export] *)
      | _ => match xlo k len with
             | Some l => if Z.leb 1 l then Some (KDisj (SA p 0) n (SA b off) len) else None   (* [comment removed for export] *)
             | None => None
             end
      end
  | None => None
  end.
Fixpoint kdisj_of_facts (k : list kentry) (p n : expr) (ks : list kentry) (acc : list kentry) : list kentry :=
  match ks with
  | [] => acc
  | K :: r => match kdisj_of_fact k p n K with
              | Some D => if existsb (kentry_eqb D) acc then kdisj_of_facts k p n r acc else kdisj_of_facts k p n r (D :: acc)
              | None => kdisj_of_facts k p n r acc
              end
  end.
(* [comment removed for export] *)
Definition perm_nonempty (k : list kentry) (perm : list (expr * expr)) : list (expr * expr) :=
  List.filter (fun g : expr * expr => match xlo k (snd g) with Some l => Z.leb 1 l | None => false end) perm.
(* [comment removed for export] *)
Definition block_rng (p n : expr) (nlo : Z) : list kentry :=
  [KRange p PTRLO (PTRHI - nlo); KRange (eadd p n) (PTRLO + nlo) PTRHI; KAlign p 16].
(* [comment removed for export] *)
Definition floor_win (fl : option expr) (top : expr) (bud : Z) : saddr * expr :=
  match fl with
  | Some f => (SA f 0, ELit (bud + WSTK))   (* [comment removed for export] *)
  | None => let '(tb, tk) := split_lit top in (SA tb (tk - bud), ELit (bud + WSTK))
  end.
(* [comment removed for export] *)
Definition top_ok (k : list kentry) (fl : option expr) (top : expr) (bud : Z) : bool :=
  let '(tb, tk) := split_lit top in
  match base_range k tb with
  | Some (tlo, thi) =>
      match fl with
      | None => (Z.leb 0 bud && Z.leb CEIL (tlo + tk - bud) && Z.ltb (thi + tk) two64)%bool
      | Some _ => (Z.leb 0 bud && Z.ltb 0 (tlo + tk) && Z.ltb (thi + tk) two64)%bool
      end
  | None => false
  end.
(* [comment removed for export] *)
Definition block_place (b n : expr) (nlo : Z) (flr : option expr) (top : expr) (bud : Z) : list kentry :=
  let '(fw, fl) := floor_win flr top bud in
  [KRange b PTRLO (PTRHI - nlo); KRange (eadd b n) (PTRLO + nlo) PTRHI;
   KDisj (SA b 0) n fw fl; KDisj (SA b 0) n (SA (ELit 0) (g_img_lo G)) (ELit (g_img_hi G - g_img_lo G))].
(* [comment removed for export] *)
Definition block_sep (k : list kentry) (p n : expr) (flr : option expr) (top : expr) (bud : Z) (live perm : list (expr * expr)) (kept : list kentry) : list kentry :=
  let '(fw, fl) := floor_win flr top bud in
  [KDisj (SA p 0) n fw fl;
   KDisj (SA p 0) n (SA (ELit 0) (g_img_lo G)) (ELit (g_img_hi G - g_img_lo G))]
  ++ disj_facts p n (live ++ perm_nonempty k perm)
  ++ kdisj_of_facts k p n kept [].
Definition block_facts (k : list kentry) (p n : expr) (nlo : Z) (flr : option expr) (top : expr) (bud : Z) (live perm : list (expr * expr)) (kept : list kentry) : list kentry :=
  block_rng p n nlo ++ [KWr (SA p 0) n; KUnk (SA p 0) n] ++ block_sep k p n flr top bud live perm kept.

(* [comment removed for export] *)
Definition node_alloc (entry : Z) (cs : acs) : option acs :=
  match call_ok entry cs with
  | None => None
  | Some ret =>
      let k := kn cs in let n := reg cs 10 in let sp := reg cs 2 in
      match xlo k n, xhi k n, cost_hi k (a_vis cs) with
      | Some nlo, Some nhi, Some ch =>
          if (Z.leb 1 nlo && Z.leb nhi NMAX && Z.leb (ch + mcost nhi) bcap && Z.leb (Z.of_nat (length (a_vis cs)) + MCNT) ccap
              && expr_vars_lt (nxt cs) n)%bool then
            let v := nxt cs in let p := EVar v in
            let kept := keep_owned k (a_vis cs ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp (nxt cs) in
            let newf := block_facts k p n nlo (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (a_vis cs) (a_ghost cs) kept in
            let ss := a_ss cs in
            Some (ACS (mk_ss ret (ret_regs (s_regs ss) (S v) (Some p)) (newf ++ kept) (S v + NCS)%nat)
                      (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) ((p, n) :: a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
          else None
      | _, _, _ => None
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition node_opnew (cs : acs) : option acs := node_alloc (g_opnew G) cs.

(* [comment removed for export] *)
Definition fresh_chk (args : list expr) (cs : acs) : bool :=
  match args with
  | [] => true
  | [ELit nmin] => match xlo (kn cs) (reg cs 10) with Some l => Z.leb nmin l | None => false end
  | _ => false
  end.
Definition malloc_entry (cs : acs) : Z :=
  if Z.eqb (pc cs) (g_malloc_thunk G) then g_malloc_thunk G else g_malloc G.
(* [comment removed for export] *)
Definition node_null (ret : Z) (cs : acs) : acs :=
  with_ss cs (mk_ss ret (ret_regs (s_regs (a_ss cs)) (nxt cs) (Some (ELit 0)))
                    (keep_owned (kn cs) (a_vis cs ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) (nxt cs)) (nxt cs + NCS)%nat).
Definition node_malloc2 (args : list expr) (cs : acs) : option (acs * acs) :=
  let entry := malloc_entry cs in
  if fresh_chk args cs then
    match call_ok entry cs, node_alloc entry cs with
    | Some ret, Some ok => Some (node_null ret cs, ok)
    | _, _ => None
    end
  else None.

(* [comment removed for export] *)
Definition node_malloc1 (args : list expr) (cs : acs) : option acs :=
  match node_malloc2 args cs with Some (_, ok) => Some ok | None => None end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint remove_block (p : expr) (live : list (expr * expr)) : option (expr * list (expr * expr)) :=
  match live with
  | [] => None
  | (b, n) :: r => if expr_eqb b p then Some (n, r)
                   else match remove_block p r with Some (m, r') => Some (m, (b, n) :: r') | None => None end
  end.

(* [comment removed for export] *)
Definition node_blkfact (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b] =>
      match remove_block b (a_vis cs) with
      | Some (n, live') =>
          let k := kn cs in let fl := acs_floor (a_maps cs) in
          match xlo k n with
          | Some nlo => if (Z.leb 1 nlo && top_ok k fl (a_brk cs) (a_ylo cs) && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
                            && bflat_x k b 0 n && live_flat cs)%bool
                        then let kept0 := keep_owned k (live' ++ a_ghost cs) fl (a_brk cs) (a_ylo cs) (reg cs 2) (nxt cs) in
                             Some (add_kn cs (block_place b n nlo fl (a_brk cs) (a_ylo cs)
                                              ++ disj_facts b n (live' ++ perm_nonempty k (a_ghost cs))
                                              ++ kdisj_of_facts k b n kept0 []))
                        else None
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_release (entry : Z) (cs : acs) : option acs :=
  match call_ok entry cs with
  | None => None
  | Some ret =>
      let k := kn cs in let p := reg cs 10 in let sp := reg cs 2 in
      let ss := a_ss cs in
      match p with
      | ELit 0 =>
          Some (with_ss cs (mk_ss ret (ret_regs (s_regs ss) (nxt cs) None)
                                 (keep_owned k (a_vis cs ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp (nxt cs)) (nxt cs + NCS)%nat))
      | _ =>
          match remove_block p (a_vis cs) with
          | None => None
          | Some (m, live') =>
              Some (ACS (mk_ss ret (ret_regs (s_regs ss) (nxt cs) None)
                              (keep_owned k (live' ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp (nxt cs)) (nxt cs + NCS)%nat)
                        (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) live'
                        (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
          end
      end
  end.

Definition node_free (cs : acs) : option acs :=
  if Z.eqb (pc cs) (g_free_thunk G) then node_release (g_free_thunk G) cs else node_release (g_free G) cs.
Definition node_opdel : acs -> option acs := node_release (g_opdel G).
Definition node_opdel_sized : acs -> option acs := node_release (g_opdel_sized G).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dst_owned (cs : acs) : bool :=
  let '(db, dk) := split_lit (reg cs 10) in
  owned_x (kn cs) (a_vis cs ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) db dk (reg cs 12) && live_flat cs.
Definition node_memcpy (cs : acs) : option acs :=
  if dst_owned cs then summary_copy segs A nx0 cs (g_memcpy G) else None.
Definition node_memset (cs : acs) : option acs :=
  if dst_owned cs then summary_fill A nx0 cs (g_memset G) two64 else None.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition src_def_x (k : list kentry) (sb : expr) (sk : Z) (ne : expr) : bool :=
  kn_readable_x k sb sk ne
  || match ne with
     | ELit n => Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.leb (img_lo A) (img_hi A) && flat_x k sb sk ne
                 && off_image_x A k sb sk ne && cover_x (S (length k)) k sb sk (sk + n)
     | _ => false
     end%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_readable_xB (bc : AX2B.bctx) (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
  AX2B.existsb_lz (fun K => match K with
                    | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                        AX2B.xinsideB bc rb rk ne kb kk len
                    | _ => false
                    end) k.
Lemma kn_readable_xB_fe : forall k, kn_readable_xB (AX2B.mkbc k) k = kn_readable_x k.
Proof.
  intros k. do 3 (apply FunctionalExtensionality.functional_extensionality; intro). unfold kn_readable_xB, kn_readable_x.
  rewrite AX2B.existsb_lz_fe, AX2B.xinsideB_eqf. reflexivity.
Qed.
Definition src_def_xB (bc : AX2B.bctx) (k : list kentry) (sb : expr) (sk : Z) (ne : expr) : bool :=
  kn_readable_xB bc k sb sk ne
  || match ne with
     | ELit n => Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.leb (img_lo A) (img_hi A) && flat_xB bc sb sk ne
                 && off_image_xB A bc sb sk ne && cover_x (S (length k)) k sb sk (sk + n)
     | _ => false
     end%bool.
Lemma src_def_xB_eqf : forall k, src_def_xB (AX2B.mkbc k) k = src_def_x k.
Proof.
  intros k. do 3 (apply FunctionalExtensionality.functional_extensionality; intro). unfold src_def_xB, src_def_x.
  rewrite kn_readable_xB_fe, flat_xB_eqf, off_image_xB_eqf. reflexivity.
Qed.
Definition summary_move_ref (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xlo k ne, xhi k ne, xhi k dst, xhi k src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call nx0 cs ret (Some dst) k else
            if (kwritable_x k k db dk ne && off_image_x A k db dk ne && src_def_x k sb sk ne)%bool then
              let k1 := kn_havoc k db dk ne in
              let k2 := if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1 in
              after_call nx0 cs ret (Some dst) k2
            else None
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.
Definition summary_move (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      let bc := AX2B.mkbc k in
      match AX2B.xloB bc ne, AX2B.xhiB bc ne, AX2B.xhiB bc dst, AX2B.xhiB bc src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call nx0 cs ret (Some dst) k else
            if (kwritable_xB bc k db dk ne && off_image_xB A bc db dk ne && src_def_xB bc k sb sk ne)%bool then
              let k1 := kn_havocB bc db dk ne in
              let k2 := if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1 in
              after_call nx0 cs ret (Some dst) k2
            else None
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.
Lemma summary_move_eq : forall cs entry, summary_move cs entry = summary_move_ref cs entry.
Proof.
  intros cs entry. unfold summary_move, summary_move_ref. cbv zeta.
  rewrite !AX2B.xloB_eqf, !AX2B.xhiB_eqf, kwritable_xB_eqf, off_image_xB_eqf, src_def_xB_eqf, kn_havocB_eqf. reflexivity.
Qed.

(* [comment removed for export] *)
Definition node_memmove (cs : acs) : option acs :=
  if dst_owned cs then
    match summary_copy segs A nx0 cs (g_memmove G) with
    | Some cs' => Some cs'
    | None => summary_move cs (g_memmove G)
    end
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition node_strlen (cs : acs) : option acs :=
  if negb (Z.eqb (pc cs) (g_strlen G)) then None else
  match ret_lit cs, reg_lit cs 10 with
  | Some ret, Some a =>
      if (Z.eqb a (g_hello G) && img_cov (kn cs) (g_ro_lo G) (g_ro_hi G))%bool
      then after_call nx0 cs ret (Some (ELit 11)) (kn cs) else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition kentails_word (k : list kentry) (b : expr) (o : Z) (w : nat) (v : expr) : bool :=
  (existsb (fun X => kentry_eqb X (KWord (SA b o) w v)) k             (* [comment removed for export] *)
   || (Nat.leb 1 w && Nat.leb w 8 && flat_x k b o (ELit (Z.of_nat w))
       && match know_lookup segs k b o w false [] [] with
          | LHit v' [] _ => expr_eqb v v' || expr_eqb (EExt false 0 w v) v'   (* [comment removed for export] *)
          | _ => false
          end))%bool.

(* [comment removed for export] *)
Definition str_obj_ok (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (ob : expr) (ok : Z) : bool :=
  owned_x k live fl top bud ob ok (ELit 24) && bflat_x k ob ok (ELit 24).

Definition str_keep_ref (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp ob : expr) (ok : Z)
           (old : option (expr * expr)) (v : nat) : list kentry :=
  let k1 := kn_cutout (keep_owned k live fl top bud sp v) ob ok (ELit 24) in
  let k2 := match old with Some (od, olen) => let '(odb, odk) := split_lit od in kn_cutout k1 odb odk olen | None => k1 end in
  List.filter (fun K =>
     kentry_vars_lt v K &&
     match kentry_range K with
     | Some (b, off, n) =>
         ranges_apart_x k b off n ob ok (ELit 24)
         && match old with
            | Some (od, olen) => let '(odb, odk) := split_lit od in ranges_apart_x k b off n odb odk olen
            | None => true
            end
     | None => true
     end)%bool k2.

(* [comment removed for export] *)
Definition str_keep (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp ob : expr) (ok : Z)
           (old : option (expr * expr)) (v : nat) : list kentry :=
  let bc := AX2B.mkbc k in
  let k1 := kn_cutoutM (keep_owned k live fl top bud sp v) ob ok (ELit 24) in
  let k2 := match old with Some (od, olen) => let '(odb, odk) := split_lit od in kn_cutoutM k1 odb odk olen | None => k1 end in
  List.filter (fun K =>
     if kentry_vars_lt v K then
     match kentry_range K with
     | Some (b, off, n) =>
         if AX2B.ranges_apart_xB bc b off n ob ok (ELit 24)
         then match old with
              | Some (od, olen) => let '(odb, odk) := split_lit od in AX2B.ranges_apart_xB bc b off n odb odk olen
              | None => true
              end
         else false
     | None => true
     end else false) k2.
Lemma str_keep_eq : forall k live fl top bud sp ob ok old v,
  str_keep k live fl top bud sp ob ok old v = str_keep_ref k live fl top bud sp ob ok old v.
Proof.
  intros. unfold str_keep, str_keep_ref. cbv zeta. rewrite !kn_cutoutM_eq, AX2B.ranges_apart_xB_eqf.
  apply filter_ext. intros K. destruct (kentry_vars_lt v K); [|reflexivity]. cbn [andb].
  destruct (kentry_range K) as [[[b off] nn]|]; [|reflexivity]. destruct (ranges_apart_x k b off nn ob ok (ELit 24)); reflexivity.
Qed.


Definition SMAXR : Z := 2 ^ 36.


(* [comment removed for export] *)
Definition str_long_post2 (cs : acs) (ret : Z) (ob : expr) (ok : Z) (n : expr) (nlo nhi : Z) (Alo' Ahi' : Z)
           (oldA : option expr) (bnd : list kentry) (live' : list (expr * expr)) (kept : list kentry) : acs :=
  let v := nxt cs in let d' := EVar v in let A' := EVar (S v) in let len' := escale 8 A' in
  let obj := eaddz ob ok in
  let rel := bnd ++ match oldA with
             | Some A => [KRange (esub n (escale 8 A)) 0 nhi;                                   (* [comment removed for export] *)
                          KRange (esub (eaddz (eadd n (escale 16 A)) 6) len') 0 (16 * (SMAXR / 8) + 6);  (* [comment removed for export] *)
                          KRange (esub (eaddz (escale 2 n) 8) len') 0 (2 * nhi + 8)]               (* [comment removed for export] *)
             | None => [KRange n 23 nhi; KRange (esub (eaddz n 52) len') 0 52]              (* [comment removed for export] *)
             end in
  let newf := [KRange A' Alo' Ahi'; KRange (esub len' n) 1 (8 * Ahi' - nlo)]
              ++ block_rng d' len' (8 * Alo')
              ++ [KWr (SA d' 0) len'; KUnk (SA d' 0) len' (* [comment removed for export] *);
                  KWord (SA (eadd d' n) 0) 1 (ELit 0);
                  KWord (SA ob ok) 8 (eaddz len' 1); KWord (SA ob (ok + 8)) 8 n; KWord (SA ob (ok + 16)) 8 d';
                  KWr (SA ob ok) (ELit 24); KUnk (SA ob ok) (ELit 24)]
              ++ rel ++ block_sep (kn cs) d' len' (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) live' (a_ghost cs)
                                  (keep_owned (kn cs) (live' ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) (nxt cs)) in
                  (* [comment removed for export] *)
  ACS (mk_ss ret (ret_regs (s_regs (a_ss cs)) (S (S v)) (Some obj)) (newf ++ kept) (S (S v) + NCS)%nat)
      (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) ((d', len') :: live') (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
Definition grow_bound (k : list kentry) (growmax : expr) (ob : option expr) (v : nat) : option (list kentry) :=
  match ob with
  | None => Some []
  | Some b => match xhi2 k b with
              | Some bh => if (lin_ge0 k [(b, 0)] [(growmax, 0)] && expr_vars_lt v b)%bool
                           then Some [KRange (esub b (escale 8 (EVar (S v)))) 0 bh] else None
              | None => None
              end
  end.

(* [comment removed for export] *)
Definition mark_dead (dead : bool) (cs : acs) : acs := if dead then set_kn cs (KRange (ELit 1) 0 0 :: kn cs) else cs.
(* [comment removed for export] *)
Definition keep_owned_bi (bc : AX2B.bctx) (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp : expr) (v : nat) : list kentry :=
  let '(spb, spk) := split_lit sp in
  List.filter (fun K => if kentry_vars_lt v K then keep_sticky_b bc live fl top bud sp K else false) k
  ++ List.filter (fun K => if kentry_vars_lt v K then keep_content_b bc live fl top bud sp K else false) (kn_cutoutB bc spb (spk - MSTK) (ELit MSTK)).
Lemma keep_owned_bi_fe : forall k, keep_owned_bi (AX2B.mkbc k) k = keep_owned k.
Proof. intros k. reflexivity. Qed.
Definition str_keep_bi (bc : AX2B.bctx) (k : list kentry) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (sp ob : expr) (ok : Z)
           (old : option (expr * expr)) (v : nat) : list kentry :=
  let k1 := kn_cutoutM (keep_owned_bi bc k live fl top bud sp v) ob ok (ELit 24) in
  let k2 := match old with Some (od, olen) => let '(odb, odk) := split_lit od in kn_cutoutM k1 odb odk olen | None => k1 end in
  List.filter (fun K =>
     if kentry_vars_lt v K then
     match kentry_range K with
     | Some (b, off, n) =>
         if AX2B.ranges_apart_xB bc b off n ob ok (ELit 24)
         then match old with
              | Some (od, olen) => let '(odb, odk) := split_lit od in AX2B.ranges_apart_xB bc b off n odb odk olen
              | None => true
              end
         else false
     | None => true
     end else false) k2.
Lemma str_keep_bi_fe : forall k, str_keep_bi (AX2B.mkbc k) k = str_keep k.
Proof. intros k. reflexivity. Qed.
(* [comment removed for export] *)
Definition str_keep_bi2 (bc : AX2B.bctx) (ko : list kentry) (ob : expr) (ok : Z) (old : option (expr * expr)) (v : nat) : list kentry :=
  let k1 := kn_cutoutM ko ob ok (ELit 24) in
  let k2 := match old with Some (od, olen) => let '(odb, odk) := split_lit od in kn_cutoutM k1 odb odk olen | None => k1 end in
  List.filter (fun K =>
     if kentry_vars_lt v K then
     match kentry_range K with
     | Some (b, off, n) =>
         if AX2B.ranges_apart_xB bc b off n ob ok (ELit 24)
         then match old with
              | Some (od, olen) => let '(odb, odk) := split_lit od in AX2B.ranges_apart_xB bc b off n odb odk olen
              | None => true
              end
         else false
     | None => true
     end else false) k2.

(* [comment removed for export] *)
Definition perm_nonempty_b (bc : AX2B.bctx) (perm : list (expr * expr)) : list (expr * expr) :=
  List.filter (fun g : expr * expr => match AX2B.xloB bc (snd g) with Some l => Z.leb 1 l | None => false end) perm.
Lemma perm_nonempty_b_fe : forall k, perm_nonempty_b (AX2B.mkbc k) = perm_nonempty k.
Proof. intros k. unfold perm_nonempty_b, perm_nonempty. rewrite AX2B.xloB_eqf. reflexivity. Qed.
Definition kdisj_of_fact_b (bc : AX2B.bctx) (p n : expr) (K : kentry) : option kentry :=
  match kentry_range K with
  | Some (b, off, len) =>
      match b with
      | ELit _ => None                                   (* [comment removed for export] *)
      | _ => match AX2B.xloB bc len with
             | Some l => if Z.leb 1 l then Some (KDisj (SA p 0) n (SA b off) len) else None   (* [comment removed for export] *)
             | None => None
             end
      end
  | None => None
  end.
Lemma kdisj_of_fact_b_fe : forall k, kdisj_of_fact_b (AX2B.mkbc k) = kdisj_of_fact k.
Proof. intros k. unfold kdisj_of_fact_b, kdisj_of_fact. rewrite AX2B.xloB_eqf. reflexivity. Qed.
Fixpoint kdisj_of_facts_b (bc : AX2B.bctx) (p n : expr) (ks : list kentry) (acc : list kentry) : list kentry :=
  match ks with
  | [] => acc
  | K :: r => match kdisj_of_fact_b bc p n K with
              | Some D => if existsb (kentry_eqb D) acc then kdisj_of_facts_b bc p n r acc else kdisj_of_facts_b bc p n r (D :: acc)
              | None => kdisj_of_facts_b bc p n r acc
              end
  end.
Lemma kdisj_of_facts_b_fe : forall k, kdisj_of_facts_b (AX2B.mkbc k) = kdisj_of_facts k.
Proof.
  intros k. apply FunctionalExtensionality.functional_extensionality; intros p. apply FunctionalExtensionality.functional_extensionality; intros n. apply FunctionalExtensionality.functional_extensionality; intros ks.
  induction ks as [|K r IH]; apply FunctionalExtensionality.functional_extensionality; intros acc; [reflexivity|]. cbn [kdisj_of_facts_b kdisj_of_facts]. rewrite kdisj_of_fact_b_fe.
  destruct (kdisj_of_fact k p n K) as [D|]; [destruct (existsb (kentry_eqb D) acc)|]; rewrite IH; reflexivity.
Qed.
Definition block_sep_b (bc : AX2B.bctx) (k : list kentry) (p n : expr) (flr : option expr) (top : expr) (bud : Z) (live perm : list (expr * expr)) (kept : list kentry) : list kentry :=
  let '(fw, fl) := floor_win flr top bud in
  [KDisj (SA p 0) n fw fl;
   KDisj (SA p 0) n (SA (ELit 0) (g_img_lo G)) (ELit (g_img_hi G - g_img_lo G))]
  ++ disj_facts p n (live ++ perm_nonempty_b bc perm)
  ++ kdisj_of_facts_b bc p n kept [].
Lemma block_sep_b_fe : forall k, block_sep_b (AX2B.mkbc k) k = block_sep k.
Proof. intros k. unfold block_sep_b, block_sep. rewrite perm_nonempty_b_fe, kdisj_of_facts_b_fe. reflexivity. Qed.
Definition str_long_post2B (bc : AX2B.bctx) (cs : acs) (ret : Z) (ob : expr) (ok : Z) (n : expr) (nlo nhi : Z) (Alo' Ahi' : Z)
           (oldA : option expr) (bnd : list kentry) (live' : list (expr * expr)) (kept : list kentry) : acs :=
  let v := nxt cs in let d' := EVar v in let A' := EVar (S v) in let len' := escale 8 A' in
  let obj := eaddz ob ok in
  let rel := bnd ++ match oldA with
             | Some A => [KRange (esub n (escale 8 A)) 0 nhi;                                   (* [comment removed for export] *)
                          KRange (esub (eaddz (eadd n (escale 16 A)) 6) len') 0 (16 * (SMAXR / 8) + 6);  (* [comment removed for export] *)
                          KRange (esub (eaddz (escale 2 n) 8) len') 0 (2 * nhi + 8)]               (* [comment removed for export] *)
             | None => [KRange n 23 nhi; KRange (esub (eaddz n 52) len') 0 52]              (* [comment removed for export] *)
             end in
  let newf := [KRange A' Alo' Ahi'; KRange (esub len' n) 1 (8 * Ahi' - nlo)]
              ++ block_rng d' len' (8 * Alo')
              ++ [KWr (SA d' 0) len'; KUnk (SA d' 0) len' (* [comment removed for export] *);
                  KWord (SA (eadd d' n) 0) 1 (ELit 0);
                  KWord (SA ob ok) 8 (eaddz len' 1); KWord (SA ob (ok + 8)) 8 n; KWord (SA ob (ok + 16)) 8 d';
                  KWr (SA ob ok) (ELit 24); KUnk (SA ob ok) (ELit 24)]
              ++ rel ++ block_sep_b bc (kn cs) d' len' (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) live' (a_ghost cs)
                                  (keep_owned_bi bc (kn cs) (live' ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) (reg cs 2) (nxt cs)) in
                  (* [comment removed for export] *)
  ACS (mk_ss ret (ret_regs (s_regs (a_ss cs)) (S (S v)) (Some obj)) (newf ++ kept) (S (S v) + NCS)%nat)
      (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) ((d', len') :: live') (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

Lemma str_long_post2B_fe : forall cs, str_long_post2B (AX2B.mkbc (kn cs)) cs = str_long_post2 cs.
Proof. intros cs. unfold str_long_post2B, str_long_post2. rewrite block_sep_b_fe, keep_owned_bi_fe. reflexivity. Qed.
(* [comment removed for export] *)
Definition str_long_post2C (bc : AX2B.bctx) (cs : acs) (ret : Z) (ob : expr) (ok : Z) (n : expr) (nlo nhi : Z) (Alo' Ahi' : Z)
           (oldA : option expr) (bnd : list kentry) (live' : list (expr * expr)) (kept ko : list kentry) : acs :=
  let v := nxt cs in let d' := EVar v in let A' := EVar (S v) in let len' := escale 8 A' in
  let obj := eaddz ob ok in
  let rel := bnd ++ match oldA with
             | Some A => [KRange (esub n (escale 8 A)) 0 nhi;                                   (* [comment removed for export] *)
                          KRange (esub (eaddz (eadd n (escale 16 A)) 6) len') 0 (16 * (SMAXR / 8) + 6);  (* [comment removed for export] *)
                          KRange (esub (eaddz (escale 2 n) 8) len') 0 (2 * nhi + 8)]               (* [comment removed for export] *)
             | None => [KRange n 23 nhi; KRange (esub (eaddz n 52) len') 0 52]              (* [comment removed for export] *)
             end in
  let newf := [KRange A' Alo' Ahi'; KRange (esub len' n) 1 (8 * Ahi' - nlo)]
              ++ block_rng d' len' (8 * Alo')
              ++ [KWr (SA d' 0) len'; KUnk (SA d' 0) len' (* [comment removed for export] *);
                  KWord (SA (eadd d' n) 0) 1 (ELit 0);
                  KWord (SA ob ok) 8 (eaddz len' 1); KWord (SA ob (ok + 8)) 8 n; KWord (SA ob (ok + 16)) 8 d';
                  KWr (SA ob ok) (ELit 24); KUnk (SA ob ok) (ELit 24)]
              ++ rel ++ block_sep_b bc (kn cs) d' len' (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) live' (a_ghost cs)
                                  ko in
                  (* [comment removed for export] *)
  ACS (mk_ss ret (ret_regs (s_regs (a_ss cs)) (S (S v)) (Some obj)) (newf ++ kept) (S (S v) + NCS)%nat)
      (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) ((d', len') :: live') (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

Definition kentails_word_bi (bc : AX2B.bctx) (k : list kentry) (b : expr) (o : Z) (w : nat) (v : expr) : bool :=
  if AX2B.existsb_lz (fun X => kentry_eqb X (KWord (SA b o) w v)) k then true
  else if (Nat.leb 1 w && Nat.leb w 8)%bool then
         if flat_xB bc b o (ELit (Z.of_nat w)) then
           match AX2B.know_lookupB segs bc b o w false [] [] with
           | LHit v' [] _ => if expr_eqb v v' then true else expr_eqb (EExt false 0 w v) v'
           | _ => false
           end
         else false
       else false.
Lemma kentails_word_bi_fe : forall k, kentails_word_bi (AX2B.mkbc k) k = kentails_word k.
Proof.
  intros k. do 4 (apply FunctionalExtensionality.functional_extensionality; intro). unfold kentails_word_bi, kentails_word.
  rewrite AX2B.existsb_lz_fe, flat_xB_eqf, AX2B.know_lookupB_eqf.
  destruct (existsb _ k); [reflexivity|]. cbn [orb]. destruct (Nat.leb 1 _ && Nat.leb _ 8)%bool; [|reflexivity]. cbn [andb].
  destruct (flat_x k _ _ _); [|reflexivity]. cbn [andb].
  destruct (know_lookup segs k _ _ _ _ _ _) as [v' [|? ?] ?| ? ?|]; try reflexivity; destruct (expr_eqb _ v'); reflexivity.
Qed.
Definition bflat_x_bi (bc : AX2B.bctx) (b : expr) (off : Z) (n : expr) : bool :=
  match AX2B.base_rangeB bc b, AX2B.xhiB bc n with
  | Some (lo, hi), Some nh => Z.leb 0 (lo + off) && Z.ltb (hi + off) two64 && Z.leb (hi + off + nh) two64
  | _, _ => false
  end%bool.
Lemma bflat_x_bi_fe : forall k, bflat_x_bi (AX2B.mkbc k) = bflat_x k.
Proof. intros k. do 3 (apply FunctionalExtensionality.functional_extensionality; intro). unfold bflat_x_bi, bflat_x. rewrite AX2B.base_rangeB_eqf, AX2B.xhiB_eqf. reflexivity. Qed.
Definition str_obj_ok_bi (bc : AX2B.bctx) (live : list (expr * expr)) (fl : option expr) (top : expr) (bud : Z) (ob : expr) (ok : Z) : bool :=
  if owned_x_b bc live fl top bud ob ok (ELit 24) then bflat_x_bi bc ob ok (ELit 24) else false.
Lemma str_obj_ok_bi_fe : forall k, str_obj_ok_bi (AX2B.mkbc k) = str_obj_ok k.
Proof.
  intros k. do 6 (apply FunctionalExtensionality.functional_extensionality; intro). unfold str_obj_ok_bi, str_obj_ok. rewrite owned_x_b_eq, bflat_x_bi_fe.
  destruct (owned_x _ _ _ _ _ _ _ _); reflexivity.
Qed.
Fixpoint cost_hi_bi (bc : AX2B.bctx) (live : list (expr * expr)) : option Z :=
  match live with
  | [] => Some 0
  | (_, n) :: r => match AX2B.xhiB bc n, cost_hi_bi bc r with Some h, Some c => Some (h + MBLK + c) | _, _ => None end
  end.
Lemma cost_hi_bi_fe : forall k, cost_hi_bi (AX2B.mkbc k) = cost_hi k.
Proof.
  intros k. apply FunctionalExtensionality.functional_extensionality; intros live. induction live as [|[x n] r IH]; [reflexivity|].
  cbn [cost_hi_bi cost_hi]. rewrite IH, AX2B.xhiB_eqf. reflexivity.
Qed.
Definition kn_readable_x_bi (bc : AX2B.bctx) (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
  AX2B.existsb_lz (fun K => match K with
                    | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                        AX2B.xinsideB bc rb rk ne kb kk len
                    | _ => false
                    end) k.
Lemma kn_readable_x_bi_fe : forall k, kn_readable_x_bi (AX2B.mkbc k) k = kn_readable_x k.
Proof.
  intros k. do 3 (apply FunctionalExtensionality.functional_extensionality; intro). unfold kn_readable_x_bi, kn_readable_x. rewrite AX2B.existsb_lz_fe, AX2B.xinsideB_eqf.
  reflexivity.
Qed.
Definition grow_bound_bi (bc : AX2B.bctx) (growmax : expr) (ob : option expr) (v : nat) : option (list kentry) :=
  match ob with
  | None => Some []
  | Some b => match xhi2B bc b with
              | Some bh => if (AX2B.lin_ge0B bc [(b, 0)] [(growmax, 0)] && expr_vars_lt v b)%bool
                           then Some [KRange (esub b (escale 8 (EVar (S v)))) 0 bh] else None
              | None => None
              end
  end.
Lemma grow_bound_bi_fe : forall k, grow_bound_bi (AX2B.mkbc k) = grow_bound k.
Proof. intros k. do 3 (apply FunctionalExtensionality.functional_extensionality; intro). unfold grow_bound_bi, grow_bound. rewrite xhi2B_eqf, AX2B.lin_ge0B_eqf. reflexivity. Qed.
Definition node_str_resize2_ref (args : list expr) (cs : acs) : option (acs * acs) :=
  match call_ok (g_str_resize G) cs with
  | None => None
  | Some ret =>
    (* [comment removed for export] *)
    let k := kn cs in let sp := reg cs 2 in let n := reg cs 11 in
    let '(ob, ok) := split_lit (reg cs 10) in
    let '(spb, spk) := split_lit sp in
    let live := a_vis cs ++ a_ghost cs in
    (* [comment removed for export] *)
    if negb (str_obj_ok k live (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) ob ok && kwritable_x k k ob ok (ELit 24) && lin_ge0 k [(ob, ok)] [(sp, 0)]
             && ranges_apart_x k ob ok (ELit 24) spb (spk - MSTK) (ELit MSTK)
             && expr_vars_lt (nxt cs) n && Z.leb (Z.of_nat (length (a_vis cs)) + MCNT) ccap)%bool then None else
    match cost_hi k (a_vis cs) with None => None | Some ch =>
    match xlo k n, xhi k n with
    | Some nlo, Some nhi =>
      if negb (Z.leb 0 nlo && Z.leb nhi SMAXR)%bool then None else
      match args with
      | ELit 0 :: EVar sv :: rest =>
          (* [comment removed for export] *)
          let obnd := match rest with [] => Some None | [b] => Some (Some b) | _ => None end in
          match obnd, xhi k (EVar sv) with
          | Some obnd, Some shi =>
          (* [comment removed for export] *)
          if negb (kentails_word k ob ok 1 (escale 2 (EVar sv)) && Z.leb shi 22)%bool then None else
          let kept1 := str_keep k live (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp ob ok None (nxt cs) in
          let un := if kn_readable_x k ob ok (ELit 24) then [KUnk (SA ob ok) (ELit 24)] else [] in
          let newf1 := [KRange n 0 22; KWord (SA ob ok) 1 (escale 2 n); KWord (SA (eadd (eaddz ob (ok + 1)) n) 0) 1 (ELit 0);
                        KWr (SA ob ok) (ELit 24)] ++ un in
          let cs1 := with_ss cs (mk_ss ret (ret_regs (s_regs (a_ss cs)) (nxt cs) (Some (eaddz ob ok))) (newf1 ++ kept1) (nxt cs + NCS)%nat) in
          let Alo' := Z.max 6 ((Z.max nlo 23 + 8) / 8) in let Ahi' := (Z.max nhi 23 + 52) / 8 in
          if negb (Z.leb (ch + mcost (8 * Ahi')) bcap) then None else
          match grow_bound k (eaddz n 52) obnd (nxt cs) with None => None | Some bnd =>
          let kept2 := str_keep k live (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp ob ok None (nxt cs) in
          Some (mark_dead (Z.leb 23 nlo) cs1,
                mark_dead (Z.leb nhi 22) (str_long_post2 cs ret ob ok n (Z.max nlo 23) nhi Alo' Ahi' None bnd (a_vis cs) kept2))
          end
          | _, _ => None
          end
      | ELit 1 :: EVar dv :: EVar Av :: sz :: rest =>
          (* [comment removed for export] *)
          let obnd := match rest with [] => Some None | [b] => Some (Some b) | _ => None end in
          match obnd with None => None | Some obnd =>
          (* [comment removed for export] *)
          if negb (kentails_word k ob ok 8 (eaddz (escale 8 (EVar Av)) 1) && kentails_word k ob (ok + 16) 8 (EVar dv)
                   && expr_vars_lt (nxt cs) sz && kentails_word k ob (ok + 8) 8 sz
                   && lin_ge0 k [(escale 8 (EVar Av), (-1)%Z)] [(sz, 0%Z)])%bool then None else
          match remove_block (EVar dv) (a_vis cs), xlo k (EVar Av), xhi k (EVar Av) with
          | Some (olen, live'), Some Alo, Some Ahi =>
              (* [comment removed for export] *)
              if negb (expr_eqb olen (escale 8 (EVar Av)) && Z.leb 3 Alo && Z.leb Ahi (SMAXR / 8)
                       && kwritable_x k k (EVar dv) 0 olen
                       && ranges_apart_x k (EVar dv) 0 olen ob ok (ELit 24)
                       && ranges_apart_x k (EVar dv) 0 olen spb (spk - MSTK) (ELit MSTK))%bool then None else
              (* [comment removed for export] *)
              let kept1 := str_keep k (live' ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp ob ok (Some (EVar dv, olen)) (nxt cs) in
              let newf1 := [KRange (esub olen n) 1 (8 * Ahi); KWord (SA ob ok) 8 (eaddz olen 1); KWord (SA ob (ok + 8)) 8 n;
                            KWord (SA ob (ok + 16)) 8 (EVar dv); KWr (SA (EVar dv) 0) olen; KWord (SA (eadd (EVar dv) n) 0) 1 (ELit 0);
                            KWr (SA ob ok) (ELit 24); KUnk (SA ob ok) (ELit 24)]
                           ++ (if kn_readable_x k (EVar dv) 0 olen then [KUnk (SA (EVar dv) 0) olen] else []) in   (* [comment removed for export] *)
              let cs1 := ACS (mk_ss ret (ret_regs (s_regs (a_ss cs)) (nxt cs) (Some (eaddz ob ok))) (newf1 ++ kept1) (nxt cs + NCS)%nat)
                             (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
              (* [comment removed for export] *)
              let Alo' := Z.max Alo ((nlo + 8) / 8) in let Ahi' := (2 * nhi + 8) / 8 in
              match cost_hi k live' with None => None | Some ch' =>
              if negb (Z.leb (ch' + mcost (Z.min (8 * Ahi) nhi) + mcost (8 * Ahi')) bcap) then None else
              match grow_bound k (eaddz (escale 2 n) 8) obnd (nxt cs) with None => None | Some bnd =>
              let kept2 := str_keep k (live' ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp ob ok (Some (EVar dv, olen)) (nxt cs) in
              Some (mark_dead (lin_ge0 k [(n, 0)] [(olen, 0)]) cs1,                                   (* [comment removed for export] *)
                    mark_dead (lin_ge0 k [(olen, (-1)%Z)] [(n, 0)])                                    (* [comment removed for export] *)
                              (str_long_post2 cs ret ob ok n nlo nhi Alo' Ahi' (Some (EVar Av)) bnd live' kept2))
              end end
          | _, _, _ => None
          end
          end
      | _ => None
      end
    | _, _ => None
    end
    end
  end.

(* [comment removed for export] *)
Definition node_str_resize2_s2 (args : list expr) (cs : acs) : option (acs * acs) :=
  match call_ok (g_str_resize G) cs with
  | None => None
  | Some ret =>
    (* [comment removed for export] *)
    let k := kn cs in let sp := reg cs 2 in let n := reg cs 11 in
    let bc := AX2B.mkbc k in   (* [comment removed for export] *)
    let '(ob, ok) := split_lit (reg cs 10) in
    let '(spb, spk) := split_lit sp in
    let live := a_vis cs ++ a_ghost cs in
    (* [comment removed for export] *)
    if negb (str_obj_ok_bi bc live (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) ob ok && kwritable_xB bc k ob ok (ELit 24) && AX2B.lin_ge0B bc [(ob, ok)] [(sp, 0)]
             && AX2B.ranges_apart_xB bc ob ok (ELit 24) spb (spk - MSTK) (ELit MSTK)
             && expr_vars_lt (nxt cs) n && Z.leb (Z.of_nat (length (a_vis cs)) + MCNT) ccap)%bool then None else
    match cost_hi_bi bc (a_vis cs) with None => None | Some ch =>
    match AX2B.xloB bc n, AX2B.xhiB bc n with
    | Some nlo, Some nhi =>
      if negb (Z.leb 0 nlo && Z.leb nhi SMAXR)%bool then None else
      match args with
      | ELit 0 :: EVar sv :: rest =>
          (* [comment removed for export] *)
          let obnd := match rest with [] => Some None | [b] => Some (Some b) | _ => None end in
          match obnd, AX2B.xhiB bc (EVar sv) with
          | Some obnd, Some shi =>
          (* [comment removed for export] *)
          if negb (kentails_word_bi bc k ob ok 1 (escale 2 (EVar sv)) && Z.leb shi 22)%bool then None else
          let kept1 := str_keep_bi bc k live (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp ob ok None (nxt cs) in
          let un := if kn_readable_x_bi bc k ob ok (ELit 24) then [KUnk (SA ob ok) (ELit 24)] else [] in
          let newf1 := [KRange n 0 22; KWord (SA ob ok) 1 (escale 2 n); KWord (SA (eadd (eaddz ob (ok + 1)) n) 0) 1 (ELit 0);
                        KWr (SA ob ok) (ELit 24)] ++ un in
          let cs1 := with_ss cs (mk_ss ret (ret_regs (s_regs (a_ss cs)) (nxt cs) (Some (eaddz ob ok))) (newf1 ++ kept1) (nxt cs + NCS)%nat) in
          let Alo' := Z.max 6 ((Z.max nlo 23 + 8) / 8) in let Ahi' := (Z.max nhi 23 + 52) / 8 in
          if negb (Z.leb (ch + mcost (8 * Ahi')) bcap) then None else
          match grow_bound_bi bc (eaddz n 52) obnd (nxt cs) with None => None | Some bnd =>
          let kept2 := kept1 in   (* [comment removed for export] *)
          Some (mark_dead (Z.leb 23 nlo) cs1,
                mark_dead (Z.leb nhi 22) (str_long_post2B bc cs ret ob ok n (Z.max nlo 23) nhi Alo' Ahi' None bnd (a_vis cs) kept2))
          end
          | _, _ => None
          end
      | ELit 1 :: EVar dv :: EVar Av :: sz :: rest =>
          (* [comment removed for export] *)
          let obnd := match rest with [] => Some None | [b] => Some (Some b) | _ => None end in
          match obnd with None => None | Some obnd =>
          (* [comment removed for export] *)
          if negb (kentails_word_bi bc k ob ok 8 (eaddz (escale 8 (EVar Av)) 1) && kentails_word_bi bc k ob (ok + 16) 8 (EVar dv)
                   && expr_vars_lt (nxt cs) sz && kentails_word_bi bc k ob (ok + 8) 8 sz
                   && AX2B.lin_ge0B bc [(escale 8 (EVar Av), (-1)%Z)] [(sz, 0%Z)])%bool then None else
          match remove_block (EVar dv) (a_vis cs), AX2B.xloB bc (EVar Av), AX2B.xhiB bc (EVar Av) with
          | Some (olen, live'), Some Alo, Some Ahi =>
              (* [comment removed for export] *)
              if negb (expr_eqb olen (escale 8 (EVar Av)) && Z.leb 3 Alo && Z.leb Ahi (SMAXR / 8)
                       && kwritable_xB bc k (EVar dv) 0 olen
                       && AX2B.ranges_apart_xB bc (EVar dv) 0 olen ob ok (ELit 24)
                       && AX2B.ranges_apart_xB bc (EVar dv) 0 olen spb (spk - MSTK) (ELit MSTK))%bool then None else
              (* [comment removed for export] *)
              let kept1 := str_keep_bi bc k (live' ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp ob ok (Some (EVar dv, olen)) (nxt cs) in
              let newf1 := [KRange (esub olen n) 1 (8 * Ahi); KWord (SA ob ok) 8 (eaddz olen 1); KWord (SA ob (ok + 8)) 8 n;
                            KWord (SA ob (ok + 16)) 8 (EVar dv); KWr (SA (EVar dv) 0) olen; KWord (SA (eadd (EVar dv) n) 0) 1 (ELit 0);
                            KWr (SA ob ok) (ELit 24); KUnk (SA ob ok) (ELit 24)]
                           ++ (if kn_readable_x_bi bc k (EVar dv) 0 olen then [KUnk (SA (EVar dv) 0) olen] else []) in   (* [comment removed for export] *)
              let cs1 := ACS (mk_ss ret (ret_regs (s_regs (a_ss cs)) (nxt cs) (Some (eaddz ob ok))) (newf1 ++ kept1) (nxt cs + NCS)%nat)
                             (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
              (* [comment removed for export] *)
              let Alo' := Z.max Alo ((nlo + 8) / 8) in let Ahi' := (2 * nhi + 8) / 8 in
              match cost_hi_bi bc live' with None => None | Some ch' =>
              if negb (Z.leb (ch' + mcost (Z.min (8 * Ahi) nhi) + mcost (8 * Ahi')) bcap) then None else
              match grow_bound_bi bc (eaddz (escale 2 n) 8) obnd (nxt cs) with None => None | Some bnd =>
              let kept2 := kept1 in   (* [comment removed for export] *)
              Some (mark_dead (AX2B.lin_ge0B bc [(n, 0)] [(olen, 0)]) cs1,                                   (* [comment removed for export] *)
                    mark_dead (AX2B.lin_ge0B bc [(olen, (-1)%Z)] [(n, 0)])                                    (* [comment removed for export] *)
                              (str_long_post2B bc cs ret ob ok n nlo nhi Alo' Ahi' (Some (EVar Av)) bnd live' kept2))
              end end
          | _, _, _ => None
          end
          end
      | _ => None
      end
    | _, _ => None
    end
    end
  end.

Definition node_str_resize2 (args : list expr) (cs : acs) : option (acs * acs) :=
  match call_ok (g_str_resize G) cs with
  | None => None
  | Some ret =>
    (* [comment removed for export] *)
    let k := kn cs in let sp := reg cs 2 in let n := reg cs 11 in
    let bc := AX2B.mkbc k in   (* [comment removed for export] *)
    let '(ob, ok) := split_lit (reg cs 10) in
    let '(spb, spk) := split_lit sp in
    let live := a_vis cs ++ a_ghost cs in
    (* [comment removed for export] *)
    if negb (str_obj_ok_bi bc live (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) ob ok && kwritable_xB bc k ob ok (ELit 24) && AX2B.lin_ge0B bc [(ob, ok)] [(sp, 0)]
             && AX2B.ranges_apart_xB bc ob ok (ELit 24) spb (spk - MSTK) (ELit MSTK)
             && expr_vars_lt (nxt cs) n && Z.leb (Z.of_nat (length (a_vis cs)) + MCNT) ccap)%bool then None else
    match cost_hi_bi bc (a_vis cs) with None => None | Some ch =>
    match AX2B.xloB bc n, AX2B.xhiB bc n with
    | Some nlo, Some nhi =>
      if negb (Z.leb 0 nlo && Z.leb nhi SMAXR)%bool then None else
      match args with
      | ELit 0 :: EVar sv :: rest =>
          (* [comment removed for export] *)
          let obnd := match rest with [] => Some None | [b] => Some (Some b) | _ => None end in
          match obnd, AX2B.xhiB bc (EVar sv) with
          | Some obnd, Some shi =>
          (* [comment removed for export] *)
          if negb (kentails_word_bi bc k ob ok 1 (escale 2 (EVar sv)) && Z.leb shi 22)%bool then None else
          let ko := keep_owned_bi bc k live (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp (nxt cs) in   (* [comment removed for export] *)
          let kept1 := str_keep_bi2 bc ko ob ok None (nxt cs) in
          let un := if kn_readable_x_bi bc k ob ok (ELit 24) then [KUnk (SA ob ok) (ELit 24)] else [] in
          let newf1 := [KRange n 0 22; KWord (SA ob ok) 1 (escale 2 n); KWord (SA (eadd (eaddz ob (ok + 1)) n) 0) 1 (ELit 0);
                        KWr (SA ob ok) (ELit 24)] ++ un in
          let cs1 := with_ss cs (mk_ss ret (ret_regs (s_regs (a_ss cs)) (nxt cs) (Some (eaddz ob ok))) (newf1 ++ kept1) (nxt cs + NCS)%nat) in
          let Alo' := Z.max 6 ((Z.max nlo 23 + 8) / 8) in let Ahi' := (Z.max nhi 23 + 52) / 8 in
          if negb (Z.leb (ch + mcost (8 * Ahi')) bcap) then None else
          match grow_bound_bi bc (eaddz n 52) obnd (nxt cs) with None => None | Some bnd =>
          let kept2 := kept1 in   (* [comment removed for export] *)
          Some (mark_dead (Z.leb 23 nlo) cs1,
                mark_dead (Z.leb nhi 22) (str_long_post2C bc cs ret ob ok n (Z.max nlo 23) nhi Alo' Ahi' None bnd (a_vis cs) kept2 ko))
          end
          | _, _ => None
          end
      | ELit 1 :: EVar dv :: EVar Av :: sz :: rest =>
          (* [comment removed for export] *)
          let obnd := match rest with [] => Some None | [b] => Some (Some b) | _ => None end in
          match obnd with None => None | Some obnd =>
          (* [comment removed for export] *)
          if negb (kentails_word_bi bc k ob ok 8 (eaddz (escale 8 (EVar Av)) 1) && kentails_word_bi bc k ob (ok + 16) 8 (EVar dv)
                   && expr_vars_lt (nxt cs) sz && kentails_word_bi bc k ob (ok + 8) 8 sz
                   && AX2B.lin_ge0B bc [(escale 8 (EVar Av), (-1)%Z)] [(sz, 0%Z)])%bool then None else
          match remove_block (EVar dv) (a_vis cs), AX2B.xloB bc (EVar Av), AX2B.xhiB bc (EVar Av) with
          | Some (olen, live'), Some Alo, Some Ahi =>
              (* [comment removed for export] *)
              if negb (expr_eqb olen (escale 8 (EVar Av)) && Z.leb 3 Alo && Z.leb Ahi (SMAXR / 8)
                       && kwritable_xB bc k (EVar dv) 0 olen
                       && AX2B.ranges_apart_xB bc (EVar dv) 0 olen ob ok (ELit 24)
                       && AX2B.ranges_apart_xB bc (EVar dv) 0 olen spb (spk - MSTK) (ELit MSTK))%bool then None else
              (* [comment removed for export] *)
              let ko := keep_owned_bi bc k (live' ++ a_ghost cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) sp (nxt cs) in   (* [comment removed for export] *)
              let kept1 := str_keep_bi2 bc ko ob ok (Some (EVar dv, olen)) (nxt cs) in
              let newf1 := [KRange (esub olen n) 1 (8 * Ahi); KWord (SA ob ok) 8 (eaddz olen 1); KWord (SA ob (ok + 8)) 8 n;
                            KWord (SA ob (ok + 16)) 8 (EVar dv); KWr (SA (EVar dv) 0) olen; KWord (SA (eadd (EVar dv) n) 0) 1 (ELit 0);
                            KWr (SA ob ok) (ELit 24); KUnk (SA ob ok) (ELit 24)]
                           ++ (if kn_readable_x_bi bc k (EVar dv) 0 olen then [KUnk (SA (EVar dv) 0) olen] else []) in   (* [comment removed for export] *)
              let cs1 := ACS (mk_ss ret (ret_regs (s_regs (a_ss cs)) (nxt cs) (Some (eaddz ob ok))) (newf1 ++ kept1) (nxt cs + NCS)%nat)
                             (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
              (* [comment removed for export] *)
              let Alo' := Z.max Alo ((nlo + 8) / 8) in let Ahi' := (2 * nhi + 8) / 8 in
              match cost_hi_bi bc live' with None => None | Some ch' =>
              if negb (Z.leb (ch' + mcost (Z.min (8 * Ahi) nhi) + mcost (8 * Ahi')) bcap) then None else
              match grow_bound_bi bc (eaddz (escale 2 n) 8) obnd (nxt cs) with None => None | Some bnd =>
              let kept2 := kept1 in   (* [comment removed for export] *)
              Some (mark_dead (AX2B.lin_ge0B bc [(n, 0)] [(olen, 0)]) cs1,                                   (* [comment removed for export] *)
                    mark_dead (AX2B.lin_ge0B bc [(olen, (-1)%Z)] [(n, 0)])                                    (* [comment removed for export] *)
                              (str_long_post2C bc cs ret ob ok n nlo nhi Alo' Ahi' (Some (EVar Av)) bnd live' kept2 ko))
              end end
          | _, _, _ => None
          end
          end
      | _ => None
      end
    | _, _ => None
    end
    end
  end.

Lemma node_str_resize2_share : forall args cs, node_str_resize2 args cs = node_str_resize2_s2 args cs.
Proof. intros. reflexivity. Qed.
Lemma node_str_resize2_eq : forall args cs, node_str_resize2 args cs = node_str_resize2_ref args cs.
Proof.
  intros. rewrite node_str_resize2_share. unfold node_str_resize2_s2, node_str_resize2_ref. cbv zeta.
  rewrite ?str_obj_ok_bi_fe, ?kwritable_xB_eqf, ?AX2B.lin_ge0B_eqf, ?AX2B.ranges_apart_xB_eqf, ?cost_hi_bi_fe, ?AX2B.xloB_eqf,
          ?AX2B.xhiB_eqf, ?kentails_word_bi_fe, ?kn_readable_x_bi_fe, ?grow_bound_bi_fe, ?str_keep_bi_fe, ?str_long_post2B_fe.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition XBg (id : nat) (args : list expr) (cs : acs) : option (acs * acs) :=
  match id with
  | 31%nat => node_str_resize2 args cs
  | _ => None
  end.


Definition XNg (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 0 => node_imgload cs
  | 1 => node_memcpy cs
  | 2 => node_memset cs
  | 3 => node_memmove cs
  | 4 => node_strlen cs
  | 10 => None   (* [comment removed for export] *)
  | 11 => node_free cs
  | 13 => node_blkfact args cs
  | 20 => node_opnew cs
  | 21 => node_opdel cs
  | 22 => node_opdel_sized cs
  | 30 => None   (* [comment removed for export] *)
  | 40 => node_divmagic args cs
  | 41 => node_enumrange args cs
  | _ => None
  end%nat.


End WithTables.
