(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
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
      match magic_of x q, xb2B (AX2B.mkbc (kn cs)) x with   (* [comment removed for export] *)
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
      match xb2B (AX2B.mkbc (kn cs)) s with   (* [comment removed for export] *)
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
Definition SHOK_NMAX : Z := 4096.
Definition shb3 (b : expr) : expr := EAlu ALU_SRL b (ELit 3).
Definition shadow_zero_bytes (segs : list Segment) (k : list kentry) (b : expr) (off nn : Z) : bool :=
  match kread_bytes segs (Z.to_nat ((nn + 7) / 8)) k (shb3 b) (SB + off / 8) with
  | Some zs => forallb (Z.eqb 0) zs
  | None => false
  end.
Definition shadow_defined_x (k : list kentry) (b : expr) (off nn : Z) : bool :=
  existsb (fun K => match K with
                    | KUnk (SA ub uk) (ELit un) => expr_eqb ub (shb3 b) && Z.leb uk (SB + off / 8) && Z.leb (SB + off / 8 + (nn + 7) / 8) (uk + un) && Z.leb 0 un && Z.ltb un two64
                    | _ => false
                    end)%bool k.
Definition node_shok (segs : list Segment) (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b; ELit off; n] =>
      let k := kn cs in
      if kshok_entailed k k b off n then Some (add_kn cs [KShOk (SA b off) n]) else
      match xlo k b, xhi k b with
      | Some lo, Some h =>
          match n with
          | ELit nn =>
              if (Z.leb 0 (lo + off) && Z.leb 1 nn && Z.leb nn SHOK_NMAX && Z.leb (h + off + nn) two47
                  && Z.leb 3 (ealign k b) && Z.eqb (off mod 8) 0 && shadow_defined_x k b off nn && shadow_zero_bytes segs k b off nn)%bool
              then Some (add_kn cs [KShOk (SA b off) n]) else None
          | _ =>
              match xhi k n with
              | Some nh => if (Z.leb nh 0 && Z.leb 0 (lo + off) && Z.leb (h + off) two47)%bool
                           then Some (add_kn cs [KShOk (SA b off) n]) else None
              | None => None
              end
          end
      | _, _ => None
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
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable nx0 : nat.
Variable PERMc : list (Z * Z).   (* [comment removed for export] *)
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable SHC : list (Z * Z).      (* [comment removed for export] *)
Variable VSH : list (Z * Z).      (* [comment removed for export] *)
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.   (* [comment removed for export] *)
Variable KCAP : Z.
Variable FTOPc : Z.   (* [comment removed for export] *)
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ).

(* [comment removed for export] *)
Lemma add_facts_sound : forall (node : acs -> option acs),
  (forall cs cs' E fx R M model, cs_ok E cs fx R M model -> node cs = Some cs' ->
      exists K, cs' = add_kn cs K /\ know_ok SEGS E (GPS.Mr SHC VSH E cs model M) K) ->   (* [comment removed for export] *)
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
  rewrite xb2B_eqf in Hn. destruct (magic_of x q) as [[[m sh] k]|] eqn:Hmg; [|discriminate].
  destruct (xb2 (kn cs) x) as [[xl xh]|] eqn:Hxb; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc Hlh]. apply andb_prop in Hc as [Hc HS].
  apply andb_prop in Hc as [Hc Hhe]. apply andb_prop in Hc as [Hc He]. apply andb_prop in Hc as [Hd1 Hd64].
  apply Z.leb_le in Hd1. apply Z.ltb_lt in Hd64. apply Z.leb_le in He. apply Z.ltb_lt in Hhe. apply Z.leb_le in HS.
  pose proof (xb2_sound SEGS E _ (kn cs) x xl xh (co_know HC) Hxb) as Hx. fold (uE E x) in Hx.
  destruct (divmagic_facts SEGS E (GPS.Mr SHC VSH E cs model M) x q d m sh k xl xh Hmg Hx Hok Hd1 Hd64 He Hhe HS) as [F1 F2].
  eexists. split; [reflexivity|]. constructor; [exact F1|]. constructor; [exact F2 | constructor].
Qed.

Theorem node_enumrange_sound : forall args, node1_stmt always (node_enumrange args).
Proof.
  intros args. apply add_facts_sound. intros cs cs' E fx R M model HC Hn.
  unfold node_enumrange in Hn.
  destruct args as [|e [|s [|]]]; try discriminate. rewrite xb2B_eqf in Hn.
  destruct (xb2 (kn cs) s) as [[lo hi]|] eqn:Hxb; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (enum_minmax (eval_at s e) lo hi) as [[mn mx]|] eqn:Hen; [|discriminate].
  injection Hn as <-.
  pose proof (xb2_sound SEGS E _ (kn cs) s lo hi (co_know HC) Hxb) as Hs. fold (uE E s) in Hs.
  eexists. split; [reflexivity|]. constructor; [|constructor].
  exact (enumrange_fact SEGS E (GPS.Mr SHC VSH E cs model M) e s lo hi mn mx Hs Hen).
Qed.


(* [comment removed for export] *)
Lemma rdn1_defined : forall mem (a : word) b0 bs,
  rdn SEGS mem a 1 = Some bs -> mem a = Some b0 -> bs = [b0].
Proof.
  intros mem a b0 bs H Ha.
  change (rdn SEGS mem a 1) with
    (match (match mem a with Some b1 => Some b1 | None => seg_rom SEGS a end) with
     | Some b1 => match rdn SEGS mem (a + 1) 0 with Some rest => Some (b1 :: rest) | None => None end
     | None => None end) in H.
  rewrite Ha in H. cbn [rdn] in H. injection H as <-. reflexivity.
Qed.

Lemma nth_map_u8 : forall j (bs : list byte), (j < length bs)%nat -> nth j (map bv_unsigned bs) 0 = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
  induction j as [|j IH]; intros [|b0 bs] Hj; cbn [length] in Hj; try lia; cbn [map nth]; [reflexivity|]. apply IH. lia.
Qed.

Theorem node_shok_sound : forall args, node1_stmt always (node_shok SEGS args).
Proof.
  intros args. apply add_facts_sound. intros cs cs' E fx R M model HC Hn.
  unfold node_shok in Hn.
  destruct args as [|b [|[off|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?] [|n [|]]]]; try discriminate.
  cbv zeta in Hn.
  pose proof (co_know HC) as HK. set (MR := GPS.Mr SHC VSH E cs model M) in *.
  pose proof (u64_range (edenot E b)) as Rb. pose proof (u64_range (edenot E n)) as Rn.
  destruct (kshok_entailed (kn cs) (kn cs) b off n) eqn:Hent.
  { injection Hn as <-. eexists. split; [reflexivity|]. constructor; [|constructor].
    exact (kshok_entailed_sound SEGS E MR (kn cs) (kn cs) b off n HK HK Hent). }
  destruct (xlo (kn cs) b) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi (kn cs) b) as [h|] eqn:Hh; [|discriminate].
  pose proof (xlo_sound SEGS E MR (kn cs) b lo HK Hlo) as Blo.
  pose proof (xhi_sound SEGS E MR (kn cs) b h HK Hh) as Bhi.
  assert (CASEii : forall nh, xhi (kn cs) n = Some nh ->
            (Z.leb nh 0 && Z.leb 0 (lo + off) && Z.leb (h + off) two47)%bool = true ->
            kentry_ok SEGS E MR (KShOk (SA b off) n)).
  { intros nh Hnh Hc. apply andb_prop in Hc as [Hc H47]. apply andb_prop in Hc as [Hn0 H0].
    apply Z.leb_le in Hn0. apply Z.leb_le in H0. apply Z.leb_le in H47.
    pose proof (xhi_sound SEGS E MR (kn cs) n nh HK Hnh) as Nhi.
    cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_SA. unfold two47 in *. split; [lia|]. split; [lia|]. intros z Hz. lia. }
  destruct n as [nn|nv|nop na nb'|nopw naw nbw|nmd nma nmb|nmdw nmaw nmbw|nsx nso nsn nse|bsx bk bi bn];
    try (match type of Hn with context [xhi (kn cs) ?e] => destruct (xhi (kn cs) e) as [nh|] eqn:Hnh; [|discriminate] end;
         match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end;
         injection Hn as <-; eexists; split; [reflexivity|]; apply Forall_cons; [exact (CASEii nh eq_refl Hc) | apply Forall_nil]).
  (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-. eexists. split; [reflexivity|]. constructor; [|constructor].
  apply andb_prop in Hc as [Hc Hzs]. apply andb_prop in Hc as [Hc Hdef]. apply andb_prop in Hc as [Hc Hm8]. apply andb_prop in Hc as [Hc Hal].
  apply andb_prop in Hc as [Hc H47]. apply andb_prop in Hc as [Hc Hmax]. apply andb_prop in Hc as [H0 H1].
  apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in Hmax. apply Z.leb_le in H47. apply Z.leb_le in Hal. apply Z.eqb_eq in Hm8.
  unfold shadow_zero_bytes in Hzs.
  set (m := Z.to_nat ((nn + 7) / 8)) in Hzs.
  destruct (kread_bytes SEGS m (kn cs) (shb3 b) (SB + off / 8)) as [zs|] eqn:Hrb; [|discriminate].
  pose proof (ealign_sound SEGS E MR (kn cs) b HK) as [Hea Hdiv].
  assert (Hq8 : (8 | bv_unsigned (edenot E b))%Z).
  { eapply Z.divide_trans; [|exact Hdiv]. exists (2 ^ (ealign (kn cs) b - 3))%Z.
    change 8 with (2 ^ 3)%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  destruct Hq8 as [q Hq].
  assert (Hsrl : bv_unsigned (edenot E (shb3 b)) = q).
  { unfold shb3. cbn [edenot]. rewrite u_srl64. rewrite u_lit64. unfold two64. rewrite (Z.mod_small 3) by lia.
    change (3 mod 64)%Z with 3%Z. change (2 ^ 3)%Z with 8%Z. rewrite Hq. apply Z.div_mul. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (Hm : Z.of_nat m = (nn + 7) / 8) by (unfold m; rewrite Z2Nat.id; [reflexivity | lia]).
  assert (Hest : estart E (SA (shb3 b) (SB + off / 8)) = q + SB + off / 8) by (rewrite estart_SA, Hsrl; lia).
  destruct (AzAPS2.kread_bytes_sound SEGS E MR (kn cs) m _ _ zs HK Hrb) as (bs & Hlen & Hmap & Hrd).
  { rewrite Hest. unfold SB. unfold two47 in *. lia. }
  { rewrite Hest, Hm. unfold SB, two47, SHOK_NMAX in *. lia. }
  (* [comment removed for export] *)
  unfold shadow_defined_x in Hdef. apply existsb_exists in Hdef as (KU & HKUin & HKU).
  destruct KU as [| | | | | | | | |[ub uk] [un|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]| | ]; try discriminate.
  apply andb_prop in HKU as [HKU HU4]. apply andb_prop in HKU as [HKU HU3]. apply andb_prop in HKU as [HKU HU2]. apply andb_prop in HKU as [HU0 HU1].
  apply expr_eqb_eq in HU0. subst ub. apply Z.leb_le in HU1. apply Z.leb_le in HU2. apply Z.leb_le in HU3. apply Z.ltb_lt in HU4. unfold two64 in HU4.
  pose proof (proj1 (Forall_forall _ _) HK _ HKUin) as KUok. cbn [kentry_ok] in KUok. destruct KUok as [KUfl KUdef].
  rewrite estart_SA, Hsrl in KUdef. unfold elenZ in KUdef. cbn [edenot] in KUdef. rewrite u_lit64 in KUdef.
  unfold flat, elenZ in KUfl. rewrite estart_SA, Hsrl in KUfl. cbn [edenot] in KUfl. rewrite u_lit64 in KUfl.
  cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_SA. cbn [edenot]. rewrite u_lit64. unfold two64 in *. rewrite (Z.mod_small nn) by (unfold SHOK_NMAX in Hmax; lia).
  unfold two47 in *. split; [lia|]. split; [lia|].
  intros z Hz.
  (* [comment removed for export] *)
  assert (Hjr : 0 <= z / 8 - q - off / 8 < Z.of_nat m) by (rewrite Hm; lia).
  set (jz := z / 8 - q - off / 8) in Hjr.
  pose proof (Hrd (Z.to_nat jz) ltac:(lia)) as RD. rewrite Hest, Z2Nat.id in RD by lia.
  replace (q + SB + off / 8 + jz) with (SB + z / 8) in RD by (unfold jz; lia).
  assert (DEF : MR (Z_to_bv 64 (SB + z / 8)) <> None).
  { replace (SB + z / 8) with (q + uk + (SB + z / 8 - q - uk)) by lia. apply KUdef.
    rewrite (Z.mod_small un) by lia. unfold SB in *. lia. }
  destruct (MR (Z_to_bv 64 (SB + z / 8))) as [b0|] eqn:HM0; [|exfalso; exact (DEF eq_refl)].
  exists b0. split; [reflexivity|]. left.
  pose proof (rdn1_defined MR _ b0 _ RD HM0) as E1. injection E1 as E1.
  assert (Hzj : nth (Z.to_nat jz) zs 0 = bv_unsigned b0).
  { rewrite <- Hmap. rewrite nth_map_u8 by (rewrite Hlen; lia). rewrite E1. reflexivity. }
  assert (Hlz : length zs = m) by (rewrite <- Hmap, length_map; exact Hlen).
  pose proof (proj1 (forallb_forall _ _) Hzs (nth (Z.to_nat jz) zs 0) ltac:(apply nth_In; rewrite Hlz; lia)) as Z0.
  apply Z.eqb_eq in Z0. lia.
Qed.

End Sound.
