(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec StoreOk SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Transport.
Variable segs : list Segment.

(* [comment removed for export] *)
Variables (spi : nat) (so sc : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (hiv : list nat) (img : list (Z * Z)).
(* [comment removed for export] *)
Variable wimg : list (Z * Z).

Fixpoint find_nz (i : nat) (l : list (nat * Z)) : option Z :=
  match l with
  | [] => None
  | (j, z) :: l' => if Nat.eqb i j then Some z else find_nz i l'
  end.

(* [comment removed for export] *)
Definition rng_keep_b (b : expr) (k n : Z) : bool :=
  (0 <=? n) &&
  match b with
  | EVar i =>
      if Nat.eqb i spi
      then (- 2 ^ 23 <=? k) && (k + n <=? 0) && ((k + n <=? so - sc) || (so <=? k))
      else match find_nz i bls with
           | Some nb => (0 <=? k) && (k + n <=? nb)
           | None => existsb (Nat.eqb i) hiv && (0 <=? k) && (k + n <=? 2 ^ 20)
           end
  | ELit z => (z =? 0) && existsb (fun iv => (fst iv <=? k) && (k + n <=? snd iv)) img
  | _ => false
  end.

(* [comment removed for export] *)
Definition rng_wr_b (b : expr) (k n : Z) : bool :=
  match b with
  | EVar i => if Nat.eqb i spi then (0 <=? n) && (- 2 ^ 23 <=? k) && (k + n <=? 0) else rng_keep_b b k n
  | _ => rng_keep_b b k n
  end.

(* [comment removed for export] *)
Definition len_hi (n : expr) : option Z :=
  match n with
  | ELit z => if (0 <=? z) && (z <? 2 ^ 64) then Some z else None
  | EVar v => find_nz v vbnd
  | _ => None
  end.

Definition kkeep_b (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => rng_keep_b b k (Z.of_nat w)
  | KZero (SA b k) n => match len_hi n with Some h => rng_keep_b b k h | None => false end
  | KBlob (SA b k) n _ => match len_hi n with Some h => rng_keep_b b k h | None => false end
  | KImg l h => existsb (fun iv => (fst iv <=? l) && (h <=? snd iv)) img || (h <=? l)
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => rng_wr_b b k n
                      || match b with
                         | ELit z => (z =? 0) && (0 <=? n) && existsb (fun iv => (fst iv <=? k) && (k + n <=? snd iv)) wimg
                         | _ => false
                         end
  end.

Definition kn_keep (kn : list kentry) : list kentry := List.filter kkeep_b kn.

(* [comment removed for export] *)
Variables (E : env) (CP SC : Z -> Prop).

Record regions_ok : Prop := REG {
  rg_sp0 : 0x7fff80000000 <= bv_unsigned (ev E spi) <= 2 ^ 47;
  rg_so : - 2 ^ 23 <= so - sc /\ 0 <= sc;
  rg_stack : forall z, - 2 ^ 23 <= z < 0 -> ~ (so - sc <= z < so) -> CP (bv_unsigned (ev E spi) + z);
  rg_scratch : forall z, so - sc <= z < so -> CP (bv_unsigned (ev E spi) + z) \/ SC (bv_unsigned (ev E spi) + z);
  rg_blocks : forall i nb, find_nz i bls = Some nb ->
                bv_unsigned (ev E i) + nb <= 2 ^ 64 /\ forall z, 0 <= z < nb -> CP (bv_unsigned (ev E i) + z);
  rg_vbnd : forall v b, find_nz v vbnd = Some b -> bv_unsigned (ev E v) <= b;
  rg_hiv : forall i, In i hiv -> bv_unsigned (ev E spi) <= bv_unsigned (ev E i) /\ bv_unsigned (ev E i) + 2 ^ 20 <= 2 ^ 64
             /\ forall z, 0 <= z < 2 ^ 20 -> CP (bv_unsigned (ev E i) + z);
  rg_img : forall lo hi, In (lo, hi) img -> 0 <= lo /\ hi <= 2 ^ 64 /\ forall a, lo <= a < hi -> CP a;
  rg_wimg : forall lo hi, In (lo, hi) wimg -> 0 <= lo /\ hi <= 2 ^ 64 /\
              forall (Mx : word -> option byte) d (m : nat), lo <= d -> d + Z.of_nat m <= hi -> store_ok segs Mx (Z_to_bv 64 d) m = true
}.

Hypothesis RG : regions_ok.
Variables (M M' : word -> option byte).
Hypothesis PRES : forall a, 0 <= a < 2 ^ 64 -> CP a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis SDEF : forall a, SC a -> M' (Z_to_bv 64 a) <> None.

Lemma existsb_nat_in : forall i l, existsb (Nat.eqb i) l = true -> In i l.
Proof.
  intros i l H. apply existsb_exists in H as (j & Hj & Ej). apply Nat.eqb_eq in Ej. subst j. exact Hj.
Qed.

Lemma existsb_iv : forall (f : Z * Z -> bool) l, existsb f l = true -> exists lo hi, In (lo, hi) l /\ f (lo, hi) = true.
Proof.
  intros f l H. apply existsb_exists in H as ([lo hi] & Hin & Hf). exists lo, hi. auto.
Qed.

(* [comment removed for export] *)
Lemma rng_keep_sound : forall b k n,
  rng_keep_b b k n = true ->
  0 <= n /\ 0 <= bv_unsigned (edenot E b) + k /\ bv_unsigned (edenot E b) + k + n <= 2 ^ 64
  /\ forall i, 0 <= i < n -> CP (bv_unsigned (edenot E b) + k + i).
Proof.
  intros b k n H. unfold rng_keep_b in H. apply andb_prop in H as [Hn H]. apply Z.leb_le in Hn.
  destruct RG as [S0 SO ST _ BL _ HV IM].
  destruct b as [z|i| | | | | |]; try discriminate.
  - apply andb_prop in H as [Hz H]. apply Z.eqb_eq in Hz. subst z.
    apply existsb_iv in H as (lo & hi & Hin & Hf). apply andb_prop in Hf as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2.
    destruct (IM lo hi Hin) as (L0 & Hhi & Icp).
    cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    split; [lia|]. split; [lia|]. split; [lia|].
    intros j Hj. apply Icp. lia.
  - cbn [edenot]. destruct (Nat.eqb i spi) eqn:Ei.
    + apply Nat.eqb_eq in Ei. subst i.
      apply andb_prop in H as [H Hor]. apply andb_prop in H as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2.
      split; [lia|]. split; [lia|]. split; [lia|].
      intros j Hj. replace (bv_unsigned (ev E spi) + k + j) with (bv_unsigned (ev E spi) + (k + j)) by lia.
      apply ST; [lia|]. apply orb_prop in Hor. intros [A B].
      destruct Hor as [Hor|Hor]; apply Z.leb_le in Hor; lia.
    + destruct (find_nz i bls) as [nb|] eqn:Fb.
      * apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
        destruct (BL i nb Fb) as [Bnw Bcp]. pose proof (u64_range (ev E i)).
        split; [lia|]. split; [lia|]. split; [lia|].
        intros j Hj. replace (bv_unsigned (ev E i) + k + j) with (bv_unsigned (ev E i) + (k + j)) by lia.
        apply Bcp. lia.
      * apply andb_prop in H as [H H2]. apply andb_prop in H as [H H1].
        apply existsb_nat_in in H. apply Z.leb_le in H1. apply Z.leb_le in H2.
        destruct (HV i H) as (V1 & V2 & V3). pose proof (u64_range (ev E i)).
        split; [lia|]. split; [lia|]. split; [lia|].
        intros j Hj. replace (bv_unsigned (ev E i) + k + j) with (bv_unsigned (ev E i) + (k + j)) by lia.
        apply V3. lia.
Qed.

(* [comment removed for export] *)
Lemma rng_wr_sound : forall b k n,
  rng_wr_b b k n = true ->
  0 <= n /\ 0 <= bv_unsigned (edenot E b) + k /\ bv_unsigned (edenot E b) + k + n <= 2 ^ 64
  /\ forall i, 0 <= i < n -> CP (bv_unsigned (edenot E b) + k + i) \/ SC (bv_unsigned (edenot E b) + k + i).
Proof.
  intros b k n H. unfold rng_wr_b in H.
  assert (KEEP : rng_keep_b b k n = true ->
     0 <= n /\ 0 <= bv_unsigned (edenot E b) + k /\ bv_unsigned (edenot E b) + k + n <= 2 ^ 64
     /\ forall i, 0 <= i < n -> CP (bv_unsigned (edenot E b) + k + i) \/ SC (bv_unsigned (edenot E b) + k + i)).
  { intros HK. destruct (rng_keep_sound b k n HK) as (A & B & C & D). repeat split; try assumption.
    intros i Hi. left. apply D. exact Hi. }
  destruct b as [z|i| | | | | |]; try (apply KEEP; exact H).
  destruct (Nat.eqb i spi) eqn:Ei; [|apply KEEP; exact H].
  apply Nat.eqb_eq in Ei. subst i. destruct RG as [S0 SO ST SCR _ _ _ _].
  apply andb_prop in H as [H H2]. apply andb_prop in H as [Hn H1].
  apply Z.leb_le in Hn. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [edenot].
  split; [lia|]. split; [lia|]. split; [lia|].
  intros j Hj. replace (bv_unsigned (ev E spi) + k + j) with (bv_unsigned (ev E spi) + (k + j)) by lia.
  destruct (Z.lt_ge_cases (k + j) (so - sc)) as [L|G]; [left; apply ST; lia|].
  destruct (Z.lt_ge_cases (k + j) so) as [L2|G2]; [apply SCR; lia | left; apply ST; lia].
Qed.

Lemma len_hi_sound : forall n h, len_hi n = Some h -> 0 <= elenZ E n <= h.
Proof.
  intros n h H. unfold len_hi in H. unfold elenZ.
  destruct n as [z|v| | | | | |]; try discriminate.
  - destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:B; [|discriminate]. injection H as <-.
    apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
    cbn [edenot]. rewrite u_small by lia. lia.
  - cbn [edenot]. pose proof (rg_vbnd RG v h H). pose proof (u64_range (ev E v)). lia.
Qed.

Lemma kentry_keep_sound : forall K,
  kentry_ok segs E M K -> kkeep_b K = true -> kentry_ok segs E M' K.
Proof.
  intros K HK Hb.
  destruct K as [[b k] w v|[b k] n|[b k] n bk|l h|e m|e l h|[b k] n|a1 n1 a2 n2]; cbn [kkeep_b] in Hb;
    cbn [kentry_ok] in HK |- *; try exact HK.
  - (* [comment removed for export] *)
    destruct HK as (Hw8 & Hfl & Hr). split; [exact Hw8|]. split; [exact Hfl|].
    destruct (rng_keep_sound b k (Z.of_nat w) Hb) as (A & B & C & D).
    rewrite <- Hr. symmetry. apply rdn_agree. intros j Hj.
    pose proof (flat_u E _ _ Hfl) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu. rewrite Hu.
    symmetry. replace (bv_unsigned (edenot E b) + k + Z.of_nat j) with (bv_unsigned (edenot E b) + k + Z.of_nat j) by lia.
    apply PRES; [lia|]. apply D. lia.
  - (* [comment removed for export] *)
    destruct (len_hi n) as [h|] eqn:Hh; [|discriminate].
    pose proof (len_hi_sound n h Hh) as Hle.
    destruct HK as (Hfl & Hz). split; [exact Hfl|]. intros i Hi.
    destruct (rng_keep_sound b k h Hb) as (A & B & C & D).
    unfold estart. cbn [a_base a_off]. rewrite PRES; [apply Hz; exact Hi | lia |]. apply D. lia.
  - (* [comment removed for export] *)
    destruct (len_hi n) as [h|] eqn:Hh; [|discriminate].
    pose proof (len_hi_sound n h Hh) as Hle.
    destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct (rng_keep_sound b k h Hb) as (A & B & C & D).
    unfold estart. cbn [a_base a_off]. rewrite PRES; [apply Hz; exact Hi | lia |]. apply D. lia.
  - (* [comment removed for export] *)
    destruct HK as (H0 & H64 & Hnone). split; [exact H0|]. split; [exact H64|].
    apply orb_prop in Hb. destruct Hb as [Hb|Hb].
    + apply existsb_iv in Hb as (lo & hi & Hin & Hf). apply andb_prop in Hf as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2.
      destruct (rg_img RG lo hi Hin) as (L0 & Lhi & Icp).
      intros i Hi. rewrite PRES; [apply Hnone; exact Hi | lia |]. apply Icp. lia.
    + apply Z.leb_le in Hb. intros i Hi. lia.
  - (* [comment removed for export] *)
    destruct HK as [Hfl Hst]. split; [exact Hfl|].
    apply orb_prop in Hb. destruct Hb as [Hb|Hw].
    2:{ destruct b as [z| | | | | | |]; try discriminate.
        apply andb_prop in Hw as [Hw Hex]. apply andb_prop in Hw as [Hz Hn0]. apply Z.eqb_eq in Hz. subst z.
        apply Z.leb_le in Hn0.
        apply existsb_iv in Hex as (lo & hi & Hin & Hf). apply andb_prop in Hf as [H1 H2].
        apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2.
        destruct (rg_wimg RG lo hi Hin) as (L0 & Lhi & W).
        intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0.
        apply W; lia. }
    destruct (rng_wr_sound b k n Hb) as (A & B & C & D).
    intros d m Hd Hm. destruct m as [|m']; [reflexivity|]. set (m := S m') in *.
    assert (HU : bv_unsigned (Z_to_bv 64 (estart E (SA b k) + d)) = bv_unsigned (edenot E b) + k + d).
    { unfold estart. cbn [a_base a_off]. rewrite u_small by lia. reflexivity. }
    apply store_ok_of_all; [rewrite HU; lia|].
    intros x Hx. rewrite HU in Hx.
    pose proof (store_ok_all segs M m (Z_to_bv 64 (estart E (SA b k) + d)) ltac:(rewrite HU; lia)
                  (Hst d m Hd Hm) x ltac:(rewrite HU; lia)) as W.
    destruct (D (bv_unsigned x - (bv_unsigned (edenot E b) + k))) as [HC|HS]; [lia| |].
    + replace (bv_unsigned (edenot E b) + k + (bv_unsigned x - (bv_unsigned (edenot E b) + k))) with (bv_unsigned x) in HC by lia.
      rewrite (wview_ext segs M M' x); [exact W|].
      rewrite <- (Z_to_bv_bv_unsigned 64 x). apply PRES; [pose proof (u64_range x); lia | exact HC].
    + replace (bv_unsigned (edenot E b) + k + (bv_unsigned x - (bv_unsigned (edenot E b) + k))) with (bv_unsigned x) in HS by lia.
      apply SDEF in HS. rewrite Z_to_bv_bv_unsigned in HS.
      unfold wview. destruct (M' x); [discriminate | exfalso; apply HS; reflexivity].
Qed.

Theorem know_keep_sound : forall kn,
  know_ok segs E M kn -> know_ok segs E M' (kn_keep kn).
Proof.
  intros kn HK. unfold know_ok in *. induction kn as [|K rest IH]; [constructor|].
  apply Forall_cons_iff in HK as [HK1 HK2].
  change (kn_keep (K :: rest)) with (if kkeep_b K then K :: kn_keep rest else kn_keep rest).
  destruct (kkeep_b K) eqn:Hb.
  - constructor; [|apply IH; exact HK2]. eapply kentry_keep_sound; eauto.
  - apply IH. exact HK2.
Qed.

(* [comment removed for export] *)
Definition is_kwr (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
Definition kn_keep_g (kn : list kentry) : list kentry := List.filter (fun K => is_kwr K || kkeep_b K) kn.

Theorem know_keep_g_sound : forall kn,
  mem_grows M M' -> know_ok segs E M kn -> know_ok segs E M' (kn_keep_g kn).
Proof.
  intros kn Hg HK. unfold know_ok in *. induction kn as [|K rest IH]; [constructor|].
  apply Forall_cons_iff in HK as [HK1 HK2].
  change (kn_keep_g (K :: rest)) with (if is_kwr K || kkeep_b K then K :: kn_keep_g rest else kn_keep_g rest).
  destruct (is_kwr K || kkeep_b K) eqn:Hb.
  - constructor; [|apply IH; exact HK2].
    destruct (is_kwr K) eqn:Hw.
    + destruct K as [| | | | | |[b k] n|]; try discriminate.
      cbn [kentry_ok] in HK1 |- *. destruct HK1 as [Hfl Hst]. split; [exact Hfl|].
      intros d m Hd Hm. eapply store_ok_mono; [exact Hg | apply Hst; assumption].
    + cbn [orb] in Hb. apply (kentry_keep_sound K HK1 Hb).
  - apply IH. exact HK2.
Qed.

End Transport.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section LogFrame.
Variable segs : list Segment.
Variables (spi : nat) (so sc : Z) (bls vbnd : list (nat * Z)) (hiv : list nat) (img : list (Z * Z)).
Variables (E : env) (CP SC : Z -> Prop).
Variable wimg : list (Z * Z).
Hypothesis RG : regions_ok segs spi so sc bls vbnd hiv img wimg E CP SC.

Definition sentry_in_b (se : sentry) : bool :=
  match se with SE (SA b k) w _ => (Nat.leb w 8) && rng_keep_b spi so sc bls hiv img b k (Z.of_nat w) end.

Definition log_in_b (log : list sentry) : bool := forallb sentry_in_b log.

Lemma mem_denot_frame : forall M log (x : word),
  log_in_b log = true -> ~ CP (bv_unsigned x) -> mem_denot E M log x = M x.
Proof.
  intros M log x Hb Hx. induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_in_b forallb] in Hb. apply andb_prop in Hb as [He Hrest]. cbn [sentry_in_b] in He.
  apply andb_prop in He as [Hw He]. apply Nat.leb_le in Hw.
  destruct (rng_keep_sound segs spi so sc bls vbnd hiv img wimg E CP SC RG b k (Z.of_nat w) He) as (A & B & C & D).
  cbn [mem_denot]. destruct w as [|w'].
  { change (word_to_le_bytes 0 (edenot E v)) with (@nil byte). cbn [wbytes]. apply IH. exact Hrest. }
  set (w := S w') in *.
  rewrite wbytes_out.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia.
    pose proof (u64_range x).
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k)) as [L|G]; [left; lia|].
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k + Z.of_nat w)) as [L2|G2]; [|right; lia].
    exfalso. apply Hx. replace (bv_unsigned x) with (bv_unsigned (edenot E b) + k + (bv_unsigned x - (bv_unsigned (edenot E b) + k))) by lia.
    apply D. lia.
Qed.

Lemma mem_denot_frame_Z : forall M log (a : Z),
  log_in_b log = true -> 0 <= a < 2 ^ 64 -> ~ CP a -> mem_denot E M log (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros M log a Hb Ha Hx. apply mem_denot_frame; [exact Hb|]. rewrite u_small by lia. exact Hx.
Qed.
End LogFrame.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kentry_eqb (K K' : kentry) : bool :=
  match K, K' with
  | KWord a w v, KWord a' w' v' => saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v'
  | KZero a n, KZero a' n' => saddr_eqb a a' && expr_eqb n n'
  | KBlob a n k, KBlob a' n' k' => saddr_eqb a a' && expr_eqb n n' && Nat.eqb k k'
  | KImg l h, KImg l' h' => (l =? l') && (h =? h')
  | KAlign e m, KAlign e' m' => expr_eqb e e' && (m =? m')
  | KRange e l h, KRange e' l' h' => expr_eqb e e' && (l =? l') && (h =? h')
  | KWr a n, KWr a' n' => saddr_eqb a a' && (n =? n')
  | KDisj a n b m, KDisj a' n' b' m' => saddr_eqb a a' && (n =? n') && saddr_eqb b b' && (m =? m')
  | _, _ => false
  end.

Lemma kentry_eqb_eq : forall K K', kentry_eqb K K' = true -> K = K'.
Proof.
  intros K K' H;
  destruct K as [[b1 k1] w v|[b1 k1] n|[b1 k1] n kk|l h|e m|e l h|[b1 k1] n|[b1 k1] n1 [b2 k2] n2];
  destruct K' as [[b1' k1'] w' v'|[b1' k1'] n'|[b1' k1'] n' kk'|l' h'|e' m'|e' l' h'|[b1' k1'] n'|[b1' k1'] n1' [b2' k2'] n2'];
    cbn [kentry_eqb saddr_eqb a_base a_off] in H; try discriminate;
    repeat (apply andb_prop in H; destruct H as [H ?]);
    repeat match goal with
      | X : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in X
      | X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X; cbn [a_base a_off] in X
      | X : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in X
      | X : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in X; cbn [a_base a_off] in X
      end; subst; congruence.
Qed.

(* [comment removed for export] *)
Definition ksub_b (kn : list kentry) (K : kentry) : bool :=
  existsb (kentry_eqb K) kn
  || match K with
     | KImg lo hi => existsb (fun K' => match K' with KImg l h => (l <=? lo) && (hi <=? h) | _ => false end) kn
     | _ => false
     end.

Lemma ksub_sound : forall segs E M kn K,
  know_ok segs E M kn -> ksub_b kn K = true -> kentry_ok segs E M K.
Proof.
  intros segs E M kn K HK Hb. unfold ksub_b in Hb. apply orb_prop in Hb. destruct Hb as [Hb|Hb].
  - apply existsb_exists in Hb as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'.
    exact (proj1 (Forall_forall _ _) HK K Hin).
  - destruct K as [| | |lo hi| | | |]; try discriminate.
    apply existsb_exists in Hb as (K' & Hin & Hm). destruct K' as [| | |l h| | | |]; try discriminate.
    apply andb_prop in Hm as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HK'. cbn [kentry_ok] in HK' |- *.
    destruct HK' as (A & B & C). split; [lia|]. split; [lia|]. intros i Hi. apply C. lia.
Qed.

Definition ksubl_b (kn kn' : list kentry) : bool := forallb (ksub_b kn) kn'.

Lemma ksubl_sound : forall segs E M kn kn',
  know_ok segs E M kn -> ksubl_b kn kn' = true -> know_ok segs E M kn'.
Proof.
  intros segs E M kn kn' HK Hb. unfold know_ok. apply Forall_forall. intros K Hin.
  unfold ksubl_b in Hb. rewrite forallb_forall in Hb. eapply ksub_sound; [exact HK | apply Hb; exact Hin].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint expr_blobs_lt (bb : nat) (e : expr) : bool :=
  match e with
  | ELit _ | EVar _ => true
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_blobs_lt bb x && expr_blobs_lt bb y
  | EExt _ _ _ x => expr_blobs_lt bb x
  | EBlob _ k _ _ => Nat.ltb k bb
  end.
Definition kentry_blobs_lt (bb : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => expr_blobs_lt bb (a_base a) && expr_blobs_lt bb v
  | KZero a n => expr_blobs_lt bb (a_base a) && expr_blobs_lt bb n
  | KBlob a n k => expr_blobs_lt bb (a_base a) && expr_blobs_lt bb n && Nat.ltb k bb
  | KImg _ _ => true
  | KAlign e _ => expr_blobs_lt bb e
  | KRange e _ _ => expr_blobs_lt bb e
  | KWr a _ => expr_blobs_lt bb (a_base a)
  | KDisj a1 _ a2 _ => expr_blobs_lt bb (a_base a1) && expr_blobs_lt bb (a_base a2)
  end.
Definition kn_blobs_lt (bb : nat) (kn : list kentry) : bool := forallb (kentry_blobs_lt bb) kn.
Definition sr_blobs_lt (bb : nat) (sr : list expr) : bool := forallb (expr_blobs_lt bb) sr.

Definition blob_agree (bb : nat) (E E' : env) : Prop :=
  (forall n, ev E n = ev E' n) /\ (forall k, (k < bb)%nat -> eb E k = eb E' k).

Lemma edenot_bagree : forall bb E E' e,
  blob_agree bb E E' -> expr_blobs_lt bb e = true -> edenot E e = edenot E' e.
Proof.
  intros bb E E' e [Hv Hb]. induction e; cbn [expr_blobs_lt edenot]; intros H;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    try reflexivity;
    try (rewrite IHe1, IHe2 by assumption; reflexivity);
    try (rewrite IHe by assumption; reflexivity).
  - apply Hv.
  - apply Nat.ltb_lt in H. rewrite (Hb _ H). reflexivity.
Qed.

Lemma regs_ok_bagree : forall bb E E' sr R,
  blob_agree bb E E' -> sr_blobs_lt bb sr = true -> regs_ok E sr R -> regs_ok E' sr R.
Proof.
  intros bb E E' sr R Ha Hsr HR r. rewrite (HR r). apply (edenot_bagree bb E E'); [exact Ha|].
  unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
  unfold sr_blobs_lt in Hsr. rewrite forallb_forall in Hsr.
  destruct (nth_error sr (ridx r)) as [e|] eqn:He.
  - rewrite (nth_error_nth _ _ _ He). apply Hsr. eapply nth_error_In; exact He.
  - rewrite nth_overflow; [reflexivity|]. apply (proj1 (nth_error_None _ _)). exact He.
Qed.

Lemma know_ok_bagree : forall segs bb E E' base kn,
  blob_agree bb E E' -> kn_blobs_lt bb kn = true -> know_ok segs E base kn -> know_ok segs E' base kn.
Proof.
  intros segs bb E E' base kn Ha Hkn HK. unfold know_ok in *. unfold kn_blobs_lt in Hkn. rewrite forallb_forall in Hkn.
  apply Forall_forall. intros K HinK. pose proof (proj1 (Forall_forall _ _) HK K HinK) as Hk. specialize (Hkn K HinK).
  pose proof Ha as [Hv Hb].
  assert (AD : forall a, expr_blobs_lt bb (a_base a) = true -> adenot E a = adenot E' a).
  { intros a H. unfold adenot. rewrite (edenot_bagree bb E E' _ Ha H). reflexivity. }
  assert (ES : forall a, expr_blobs_lt bb (a_base a) = true -> estart E a = estart E' a).
  { intros a H. unfold estart. rewrite (edenot_bagree bb E E' _ Ha H). reflexivity. }
  assert (FL : forall a n, expr_blobs_lt bb (a_base a) = true -> flat E a n -> flat E' a n).
  { intros a n H F. unfold flat in *. rewrite <- (ES a H). exact F. }
  destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2]; cbn [kentry_blobs_lt kentry_ok] in *;
    repeat match goal with | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
  - destruct Hk as (A & B & C). split; [exact A|]. split; [apply FL; assumption|].
    rewrite <- (AD a), <- (edenot_bagree bb E E' v Ha) by assumption. exact C.
  - destruct Hk as [A B]. unfold elenZ in *. rewrite <- (edenot_bagree bb E E' n Ha) by assumption.
    split; [apply FL; assumption|]. intros i Hi. rewrite <- (ES a) by assumption. apply B. exact Hi.
  - destruct Hk as (A & B & C). unfold elenZ in *. rewrite <- (edenot_bagree bb E E' n Ha) by assumption.
    apply Nat.ltb_lt in H0. rewrite <- (Hb _ H0).
    split; [apply FL; assumption|]. split; [exact B|]. intros i Hi. rewrite <- (ES a) by assumption. apply C. exact Hi.
  - exact Hk.
  - rewrite <- (edenot_bagree bb E E' ae Ha) by assumption. exact Hk.
  - rewrite <- (edenot_bagree bb E E' re Ha) by assumption. exact Hk.
  - destruct Hk as [A B]. split; [apply FL; assumption|]. intros d m Hd Hm. rewrite <- (ES wa) by assumption. apply B; assumption.
  - rewrite <- (ES da1), <- (ES da2) by assumption. exact Hk.
Qed.

Lemma blob_agree_app : forall vals bl extra,
  blob_agree (length bl) (Env vals (blobs_ev bl)) (Env vals (blobs_ev (bl ++ extra))).
Proof.
  intros vals bl extra. split; [reflexivity|]. intros k Hk. cbn [eb]. unfold blobs_ev. rewrite app_nth1 by exact Hk. reflexivity.
Qed.

End FPX_1.
