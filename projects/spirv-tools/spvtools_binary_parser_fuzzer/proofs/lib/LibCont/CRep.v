(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec SeqExec StepTac StoreOk LibIface.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition Zlen {T} (xs : list T) : Z := Z.of_nat (length xs).
Definition Znth (i : Z) (xs : list Z) : Z := nth (Z.to_nat i) xs 0.

Lemma Zlen_app1 : forall {T} (xs : list T) x, Zlen (xs ++ [x]) = Zlen xs + 1.
Proof. intros. unfold Zlen. rewrite length_app. cbn. lia. Qed.
Lemma Zlen_nil : forall {T}, Zlen (@nil T) = 0.
Proof. reflexivity. Qed.
Lemma Zlen_nonneg : forall {T} (xs : list T), 0 <= Zlen xs.
Proof. intros. unfold Zlen. lia. Qed.
Lemma Znth_app_l : forall i xs ys, 0 <= i < Zlen xs -> Znth i (xs ++ ys) = Znth i xs.
Proof. intros. unfold Znth, Zlen in *. apply app_nth1. lia. Qed.
Lemma Znth_app_r1 : forall xs x, Znth (Zlen xs) (xs ++ [x]) = x.
Proof. intros. unfold Znth, Zlen. rewrite Nat2Z.id. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma Zlen_repeat : forall (x : Z) n, 0 <= n -> Zlen (repeat x (Z.to_nat n)) = n.
Proof. intros. unfold Zlen. rewrite repeat_length. lia. Qed.
Lemma Zlen_firstn : forall (xs : list Z) n, 0 <= n <= Zlen xs -> Zlen (firstn (Z.to_nat n) xs) = n.
Proof. intros. unfold Zlen in *. rewrite length_firstn. lia. Qed.

Definition mdef (M : mem) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None.

Definition agree_on (P : Z -> Prop) (M M' : mem) : Prop :=
  forall a : Z, P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).

Lemma agree_on_of_frame_eq : forall (F P : Z -> Prop) M M',
  frame_eq F M M' -> (forall a, P a -> 0 <= a < 2 ^ 64 /\ ~ F a) -> agree_on P M M'.
Proof.
  intros F P M M' HF HP a Ha. destruct (HP a Ha) as [Hr Hn].
  apply HF. rewrite u_Z2bv by lia. exact Hn.
Qed.

Lemma agree_on_weaken : forall (P Q : Z -> Prop) M M',
  agree_on P M M' -> (forall a, Q a -> P a) -> agree_on Q M M'.
Proof. intros P Q M M' H HQ a Ha. apply H, HQ, Ha. Qed.

Lemma mdef_agree : forall M M' a n,
  mdef M a n -> agree_on (zwin a (a + n)) M M' -> mdef M' a n.
Proof.
  intros M M' a n HD HA i Hi. rewrite (HA (a + i)) by (unfold zwin; lia). apply HD. lia.
Qed.

Section WithSegs.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.

Lemma rdn_agree_win : forall M M' (a : Z) (k : nat),
  0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
  agree_on (zwin a (a + Z.of_nat k)) M M' ->
  rdn SEGS M' (Z_to_bv 64 a) k = rdn SEGS M (Z_to_bv 64 a) k.
Proof using SEGS.
  intros M M' a k Ha Hk HA. apply rdn_ext.
  - rewrite u_Z2bv by lia. lia.
  - intros x Hx. rewrite u_Z2bv in Hx by lia.
    rewrite <- (Z_to_bv_bv_unsigned 64 x). apply HA. unfold zwin. lia.
Qed.

Definition fld (M : mem) (a : Z) (k : nat) (v : Z) : Prop :=
  rdn SEGS M (Z_to_bv 64 a) k = Some (word_to_le_bytes k (Z_to_bv 64 v)).

Lemma fld_agree : forall M M' a k v,
  0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
  fld M a k v -> agree_on (zwin a (a + Z.of_nat k)) M M' -> fld M' a k v.
Proof using SEGS. intros M M' a k v Ha Hk HF HA. unfold fld. rewrite (rdn_agree_win M M' a k Ha Hk HA). exact HF. Qed.

Section WithIface.
Variable L : Layout.
Variable MI : MallocIface SEGS L.

Definition vec32 (A : AS MI) (M : mem) (v b : Z) (xs : list Z) (cap : Z) : Prop :=
  0 <= v /\ v + 24 <= 2 ^ 63 /\ mdef M v 24 /\
  0 <= Zlen xs <= cap /\
  (b = 0 /\ cap = 0 \/ 0 < b /\ b mod 16 = 0 /\ 0 < cap /\ b + 4 * cap <= 2 ^ 63 /\ In (b, 4 * cap) (live MI A)
                   /\ (v + 24 <= b \/ b + 4 * cap <= v)) /\
  fld M v 8 b /\ fld M (v + 8) 8 (b + 4 * Zlen xs) /\ fld M (v + 16) 8 (b + 4 * cap) /\
  (forall i, 0 <= i < Zlen xs -> 0 <= Znth i xs < 2 ^ 32 /\ fld M (b + 4 * i) 4 (Znth i xs)).

Definition vec32_fp (v b : Z) (xs : list Z) (a : Z) : Prop :=
  zwin v (v + 24) a \/ (b <> 0 /\ zwin b (b + 4 * Zlen xs) a).

Lemma vec32_frame : forall A M M' v b xs cap,
  vec32 A M v b xs cap -> agree_on (vec32_fp v b xs) M M' -> vec32 A M' v b xs cap.
Proof using AC SEGS L MI.
  intros A M M' v b xs cap (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2 & FE) HA.
  unfold vec32.
  assert (HAh : forall lo k, v <= lo -> lo + Z.of_nat k <= v + 24 ->
            agree_on (zwin lo (lo + Z.of_nat k)) M M').
  { intros lo k H1 H2. eapply agree_on_weaken; [exact HA|]. intros a Ha. left. unfold zwin in *. lia. }
  split; [exact Hv|]. split; [exact Hv'|].
  split; [eapply mdef_agree; [exact HD|]; eapply agree_on_weaken; [exact HA|]; intros a Ha; left; exact Ha|].
  split; [exact Hlen|]. split; [exact Hb|].
  split; [eapply fld_agree; [lia|cbn; lia|exact F0|]; apply HAh; cbn; lia|].
  split; [eapply fld_agree; [lia|cbn; lia|exact F1|]; apply HAh; cbn; lia|].
  split; [eapply fld_agree; [lia|cbn; lia|exact F2|]; apply HAh; cbn; lia|].
  intros i Hi. destruct Hb as [[-> ->]|(Hb0 & Hal & Hc0 & Hbc & HIn & Hdj)]; [lia|].
  destruct (FE i Hi) as [Hr HF]. split; [exact Hr|].
  eapply fld_agree; [lia|cbn; lia|exact HF|].
  eapply agree_on_weaken; [exact HA|]. intros a Ha. right. split; [lia|]. unfold zwin in *; cbn in Ha. lia.
Qed.

Lemma vec32_relive : forall A A' M v b xs cap,
  vec32 A M v b xs cap -> (b <> 0 -> In (b, 4 * cap) (live MI A) -> In (b, 4 * cap) (live MI A')) ->
  vec32 A' M v b xs cap.
Proof using AC SEGS L MI.
  intros A A' M v b xs cap (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2 & FE) HL.
  unfold vec32. split; [exact Hv|]. split; [exact Hv'|]. split; [exact HD|]. split; [exact Hlen|].
  split; [|exact (conj F0 (conj F1 (conj F2 FE)))].
  destruct Hb as [[-> ->]|(Hb0 & Hal & Hc0 & Hbc & HIn & Hdj)]; [left; split; reflexivity | right].
  repeat split; try lia. apply HL; [lia | exact HIn].
Qed.

Definition vec32_blocks (b cap : Z) : list (Z * Z) := if b =? 0 then [] else [(b, 4 * cap)].

Lemma vec32_blocks_live : forall A M v b xs cap,
  vec32 A M v b xs cap -> forall blk, In blk (vec32_blocks b cap) -> In blk (live MI A).
Proof using AC SEGS L MI.
  intros A M v b xs cap (Hv & Hv' & HD & Hlen & Hb & _) blk Hin. unfold vec32_blocks in Hin.
  destruct Hb as [[-> ->]|(Hb0 & Hal & Hc0 & Hbc & HIn & Hdj)].
  - cbn in Hin. destruct Hin.
  - destruct (Z.eqb_spec b 0); [lia|]. destruct Hin as [<-|[]]. exact HIn.
Qed.

Lemma vec32_nil : forall A M v,
  0 <= v -> v + 24 <= 2 ^ 63 -> mdef M v 24 ->
  fld M v 8 0 -> fld M (v + 8) 8 0 -> fld M (v + 16) 8 0 -> vec32 A M v 0 [] 0.
Proof using AC SEGS L MI.
  intros A M v Hv Hv' HD F0 F1 F2. unfold vec32. change (Zlen (@nil Z)) with 0.
  rewrite Z.mul_0_r, Z.add_0_r.
  split; [exact Hv|]. split; [exact Hv'|]. split; [exact HD|]. split; [lia|].
  split; [left; split; reflexivity|]. split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
  intros i Hi. lia.
Qed.

Definition OPND_SZ : Z := 20.

Definition vec_opnd (A : AS MI) (M : mem) (v b : Z) (n : Z) (cap : Z) : Prop :=
  0 <= v /\ v + 24 <= 2 ^ 63 /\ mdef M v 24 /\
  0 <= n <= cap /\
  (b = 0 /\ cap = 0 \/ 0 < b /\ b mod 16 = 0 /\ 0 < cap /\ b + OPND_SZ * cap <= 2 ^ 63 /\ In (b, OPND_SZ * cap) (live MI A)
                   /\ (v + 24 <= b \/ b + OPND_SZ * cap <= v)) /\
  fld M v 8 b /\ fld M (v + 8) 8 (b + OPND_SZ * n) /\ fld M (v + 16) 8 (b + OPND_SZ * cap).

Definition vec_opnd_fp (v b : Z) (n : Z) (a : Z) : Prop := zwin v (v + 24) a.

Lemma vec_opnd_frame : forall A M M' v b n cap,
  vec_opnd A M v b n cap -> agree_on (vec_opnd_fp v b n) M M' -> vec_opnd A M' v b n cap.
Proof using AC SEGS L MI.
  intros A M M' v b n cap (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2) HA.
  unfold vec_opnd, vec_opnd_fp in *.
  assert (HAh : forall lo k, v <= lo -> lo + Z.of_nat k <= v + 24 ->
            agree_on (zwin lo (lo + Z.of_nat k)) M M').
  { intros lo k H1 H2. eapply agree_on_weaken; [exact HA|]. intros a Ha. unfold zwin in *. lia. }
  split; [exact Hv|]. split; [exact Hv'|].
  split; [eapply mdef_agree; [exact HD|]; eapply agree_on_weaken; [exact HA|]; intros a Ha; exact Ha|].
  split; [exact Hlen|]. split; [exact Hb|].
  split; [eapply fld_agree; [lia|cbn; lia|exact F0|]; apply HAh; cbn; lia|].
  split; [eapply fld_agree; [lia|cbn; lia|exact F1|]; apply HAh; cbn; lia|].
  eapply fld_agree; [lia|cbn; lia|exact F2|]; apply HAh; cbn; lia.
Qed.

Lemma vec_opnd_relive : forall A A' M v b n cap,
  vec_opnd A M v b n cap ->
  (b <> 0 -> In (b, OPND_SZ * cap) (live MI A) -> In (b, OPND_SZ * cap) (live MI A')) ->
  vec_opnd A' M v b n cap.
Proof using AC SEGS L MI.
  intros A A' M v b n cap (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2) HL.
  unfold vec_opnd. split; [exact Hv|]. split; [exact Hv'|]. split; [exact HD|]. split; [exact Hlen|].
  split; [|exact (conj F0 (conj F1 F2))].
  destruct Hb as [[-> ->]|(Hb0 & Hal & Hc0 & Hbc & HIn & Hdj)]; [left; split; reflexivity | right].
  repeat split; try lia. apply HL; [lia | exact HIn].
Qed.

Definition vec_opnd_blocks (b cap : Z) : list (Z * Z) := if b =? 0 then [] else [(b, OPND_SZ * cap)].

Lemma vec_opnd_blocks_live : forall A M v b n cap,
  vec_opnd A M v b n cap -> forall blk, In blk (vec_opnd_blocks b cap) -> In blk (live MI A).
Proof using AC SEGS L MI.
  intros A M v b n cap (Hv & Hv' & HD & Hlen & Hb & _) blk Hin. unfold vec_opnd_blocks in Hin.
  destruct Hb as [[-> ->]|(Hb0 & Hal & Hc0 & Hbc & HIn & Hdj)].
  - cbn in Hin. destruct Hin.
  - destruct (Z.eqb_spec b 0); [lia|]. destruct Hin as [<-|[]]. exact HIn.
Qed.

Lemma vec_opnd_nil : forall A M v,
  0 <= v -> v + 24 <= 2 ^ 63 -> mdef M v 24 ->
  fld M v 8 0 -> fld M (v + 8) 8 0 -> fld M (v + 16) 8 0 -> vec_opnd A M v 0 0 0.
Proof using AC SEGS L MI.
  intros A M v Hv Hv' HD F0 F1 F2. unfold vec_opnd, OPND_SZ.
  rewrite Z.mul_0_r, Z.add_0_r.
  split; [exact Hv|]. split; [exact Hv'|]. split; [exact HD|]. split; [lia|].
  split; [left; split; reflexivity|]. split; [exact F0|]. split; [exact F1|]. exact F2.
Qed.

Inductive sbuf : Type := SShort | SLong (d asz : Z).

Definition SSO_CAP : Z := 22.

Definition str_data (s : Z) (m : sbuf) : Z := match m with SShort => s + 1 | SLong d _ => d end.
Definition str_cap (m : sbuf) : Z := match m with SShort => SSO_CAP | SLong _ asz => asz - 1 end.
Definition str_blocks (m : sbuf) : list (Z * Z) := match m with SShort => [] | SLong d asz => [(d, asz)] end.

Definition str_rep (A : AS MI) (M : mem) (s : Z) (m : sbuf) (cs : list Z) : Prop :=
  0 <= s /\ s + 24 <= 2 ^ 63 /\ mdef M s 24 /\
  0 <= Zlen cs <= str_cap m /\
  match m with
  | SShort => fld M s 1 (2 * Zlen cs)
  | SLong d asz => 0 < d /\ d mod 16 = 0 /\ d + asz <= 2 ^ 63 /\ asz mod 8 = 0 /\ 2 * SSO_CAP + 2 <= asz /\
                   In (d, asz) (live MI A) /\ (s + 24 <= d \/ d + asz <= s) /\
                   fld M s 8 (asz + 1) /\ fld M (s + 8) 8 (Zlen cs) /\ fld M (s + 16) 8 d
  end /\
  (forall i, 0 <= i < Zlen cs -> 0 <= Znth i cs < 256 /\ fld M (str_data s m + i) 1 (Znth i cs)) /\
  fld M (str_data s m + Zlen cs) 1 0.

Definition str_fp (s : Z) (m : sbuf) (cs : list Z) (a : Z) : Prop :=
  zwin s (s + 24) a \/
  match m with SShort => False | SLong d _ => zwin d (d + Zlen cs + 1) a end.

Lemma str_frame : forall A M M' s m cs,
  str_rep A M s m cs -> agree_on (str_fp s m cs) M M' -> str_rep A M' s m cs.
Proof using AC SEGS L MI.
  intros A M M' s m cs (Hs & Hs' & HD & Hlen & HM & HC & HZ) HA.
  assert (HAh : forall lo k, s <= lo -> lo + Z.of_nat k <= s + 24 ->
            agree_on (zwin lo (lo + Z.of_nat k)) M M').
  { intros lo k H1 H2. eapply agree_on_weaken; [exact HA|]. intros a Ha. left. unfold zwin in *. lia. }
  unfold str_rep. split; [exact Hs|]. split; [exact Hs'|].
  split; [eapply mdef_agree; [exact HD|]; eapply agree_on_weaken; [exact HA|]; intros a Ha; left; exact Ha|].
  split; [exact Hlen|].
  destruct m as [|d asz]; cbn [str_data str_cap] in *.
  - split; [|split].
    + eapply fld_agree; [lia|cbn; lia|exact HM|]. apply HAh; cbn; unfold SSO_CAP in *; lia.
    + intros i Hi. destruct (HC i Hi) as [Hr HF]. split; [exact Hr|].
      eapply fld_agree; [lia|cbn; unfold SSO_CAP in *; lia|exact HF|].
      apply HAh; cbn; unfold SSO_CAP in *; lia.
    + eapply fld_agree; [lia|cbn; unfold SSO_CAP in *; lia|exact HZ|]. apply HAh; cbn; unfold SSO_CAP in *; lia.
  - destruct HM as (Hd & Hd16 & Hd' & Hal & Hmin & HIn & Hdj & F0 & F1 & F2).
    split; [|split].
    + repeat split; try assumption.
      * eapply fld_agree; [lia|cbn; lia|exact F0|]. apply HAh; cbn; lia.
      * eapply fld_agree; [lia|cbn; lia|exact F1|]. apply HAh; cbn; lia.
      * eapply fld_agree; [lia|cbn; lia|exact F2|]. apply HAh; cbn; lia.
    + intros i Hi. destruct (HC i Hi) as [Hr HF]. split; [exact Hr|]. eapply fld_agree; [lia|cbn; lia|exact HF|].
      eapply agree_on_weaken; [exact HA|]. intros a Ha. right. unfold zwin in *; cbn in Ha. lia.
    + eapply fld_agree; [lia|cbn; lia|exact HZ|].
      eapply agree_on_weaken; [exact HA|]. intros a Ha. right. unfold zwin in *; cbn in Ha. lia.
Qed.

Lemma str_relive : forall A A' M s m cs,
  str_rep A M s m cs -> (forall blk, In blk (str_blocks m) -> In blk (live MI A) -> In blk (live MI A')) ->
  str_rep A' M s m cs.
Proof using AC SEGS L MI.
  intros A A' M s m cs (Hs & Hs' & HD & Hlen & HM & HC & HZ) HL.
  unfold str_rep. repeat (split; [assumption|]). split; [|split; assumption].
  destruct m as [|d asz]; [exact HM|].
  destruct HM as (Hd & Hd16 & Hd' & Hal & Hmin & HIn & Hdj & F0 & F1 & F2).
  repeat split; try assumption. apply HL; [left; reflexivity | exact HIn].
Qed.

Lemma str_blocks_live : forall A M s m cs,
  str_rep A M s m cs -> forall blk, In blk (str_blocks m) -> In blk (live MI A).
Proof using AC SEGS L MI.
  intros A M s m cs (Hs & Hs' & HD & Hlen & HM & _) blk Hin.
  destruct m as [|d asz]; cbn in Hin; [destruct Hin|].
  destruct Hin as [<-|[]]. destruct HM as (_ & _ & _ & _ & _ & HIn & _). exact HIn.
Qed.

Lemma str_nil : forall A M s,
  0 <= s -> s + 24 <= 2 ^ 63 -> mdef M s 24 ->
  fld M s 1 0 -> fld M (s + 1) 1 0 -> str_rep A M s SShort [].
Proof using AC SEGS L MI.
  intros A M s Hs Hs' HD F0 F1. unfold str_rep. change (Zlen (@nil Z)) with 0. cbn [str_cap str_data].
  rewrite Z.mul_0_r, Z.add_0_r.
  split; [exact Hs|]. split; [exact Hs'|]. split; [exact HD|]. split; [unfold SSO_CAP; lia|].
  split; [exact F0|]. split; [intros i Hi; lia|]. exact F1.
Qed.

Definition str_grow (m : sbuf) : Z := match m with SShort => 48 | SLong _ asz => 2 * asz end.

Definition CTX_SZ : Z := 64.

Definition ctx_rep (A : AS MI) (M : mem) (p env : Z) : Prop :=
  0 < p /\ p mod 16 = 0 /\ p + CTX_SZ <= 2 ^ 63 /\ In (p, CTX_SZ) (live MI A) /\
  fld M p 4 env /\ fld M (p + 48) 8 0.

Definition ctx_fp (p : Z) (a : Z) : Prop := zwin p (p + CTX_SZ) a.

Lemma ctx_frame : forall A M M' p env,
  ctx_rep A M p env -> agree_on (ctx_fp p) M M' -> ctx_rep A M' p env.
Proof using AC SEGS L MI.
  intros A M M' p env (Hp & Hp16 & Hp' & HIn & F0 & F1) HA. unfold ctx_rep, ctx_fp, CTX_SZ in *.
  repeat split; try assumption.
  - eapply fld_agree; [lia|cbn; lia|exact F0|]. eapply agree_on_weaken; [exact HA|]. intros a Ha; unfold zwin in *; cbn in Ha; lia.
  - eapply fld_agree; [lia|cbn; lia|exact F1|]. eapply agree_on_weaken; [exact HA|]. intros a Ha; unfold zwin in *; cbn in Ha; lia.
Qed.

Lemma ctx_relive : forall A A' M p env,
  ctx_rep A M p env -> (In (p, CTX_SZ) (live MI A) -> In (p, CTX_SZ) (live MI A')) -> ctx_rep A' M p env.
Proof using AC SEGS L MI.
  intros A A' M p env (Hp & Hp16 & Hp' & HIn & F0 & F1) HL. unfold ctx_rep. repeat split; try assumption. apply HL, HIn.
Qed.

Definition ctx_blocks (p : Z) : list (Z * Z) := [(p, CTX_SZ)].

Definition placed (A : AS MI) (v n : Z) : Prop :=
  alloc_ceiling <= v \/ exists q k, In (q, k) (live MI A) /\ q <= v /\ v + n <= q + k.

Definition obj_ok (A : AS MI) (sp STK v n : Z) : Prop :=
  placed A v n /\ forall a, zwin v (v + n) a -> ~ zwin (sp - STK) sp a.

Definition junk_ok (A : AS MI) (J : Z -> Prop) : Prop :=
  forall a, J a -> 0 < a < alloc_ceiling /\ ~ in_ranges (ly_img L) a /\
                   (forall q k, In (q, k) (live MI A) -> ~ (q <= a < q + k)).

Lemma live_add_keeps : forall p n lv lv' blk, live_add p n lv lv' -> In blk lv -> In blk lv'.
Proof using. intros p n lv lv' blk [-> _] Hin. right. exact Hin. Qed.

Lemma live_add_new : forall p n lv lv', live_add p n lv lv' -> In (p, n) lv'.
Proof using. intros p n lv lv' [-> _]. left. reflexivity. Qed.

Lemma live_del_keeps : forall p lv lv' q k, live_del p lv lv' -> In (q, k) lv -> q <> p -> In (q, k) lv'.
Proof using. intros p lv lv' q k HD Hin Hne. apply (proj2 (HD q k)). split; assumption. Qed.

End WithIface.
End WithSegs.

Arguments fld SEGS M a k v /.
Arguments vec32 {AC SEGS L} MI A M v b xs cap.
Arguments vec32_fp v b xs a /.
Arguments vec_opnd {AC SEGS L} MI A M v b n cap.
Arguments vec_opnd_fp v b n a /.
Arguments str_rep {AC SEGS L} MI A M s m cs.
Arguments str_fp s m cs a /.
Arguments ctx_rep {AC SEGS L} MI A M p env.
Arguments placed {AC SEGS L} MI A v n.
Arguments obj_ok {AC SEGS L} MI A sp STK v n.
Arguments junk_ok {AC SEGS L} MI A J.
Arguments vec32_frame {AC SEGS L} MI.
Arguments vec32_relive {AC SEGS L} MI.
Arguments vec32_blocks_live {AC SEGS L} MI.
Arguments vec32_nil {AC SEGS L} MI.
Arguments vec_opnd_frame {AC SEGS L} MI.
Arguments vec_opnd_relive {AC SEGS L} MI.
Arguments vec_opnd_blocks_live {AC SEGS L} MI.
Arguments vec_opnd_nil {AC SEGS L} MI.
Arguments str_frame {AC SEGS L} MI.
Arguments str_relive {AC SEGS L} MI.
Arguments str_blocks_live {AC SEGS L} MI.
Arguments str_nil {AC SEGS L} MI.
Arguments ctx_frame {AC SEGS L} MI.
Arguments ctx_relive {AC SEGS L} MI.
