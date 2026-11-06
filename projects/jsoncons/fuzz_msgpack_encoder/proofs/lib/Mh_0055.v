(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module DrvKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveH4.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

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
      then (- 2 ^ 23 <=? k) && (k + n <=? 2 ^ 40) && ((k + n <=? so - sc) || (so <=? k))
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
  | EVar i => if Nat.eqb i spi then (0 <=? n) && (- 2 ^ 23 <=? k) && (k + n <=? 2 ^ 40) else rng_keep_b b k n
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
  rg_stack : forall z, - 2 ^ 23 <= z < 2 ^ 40 -> ~ (so - sc <= z < so) -> CP (bv_unsigned (ev E spi) + z);
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

End DrvKit.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.
Module ShapeEF.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX.

Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCfg.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma srealizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  srealizes0 segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply srealizes_no_error; eassumption. Qed.

Lemma srealizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  srealizes0 segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply srealizes_obs_iff. assumption. Qed.

Lemma realizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  realizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply realizes_no_error; eassumption. Qed.

Lemma realizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  realizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply realizes_obs_iff. assumption. Qed.

Theorem shape_strong_equiv_efs :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  srealizes0 source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes0 target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  split; [| split].
  - eapply srealizes_error_free; exact Hsource.
  - eapply srealizes_error_free; exact Htarget.
  - intro tr.
    rewrite (srealizes_traces_iff source_segs _ _ _ _ _ _ _ _ T tr Hsource).
    rewrite (srealizes_traces_iff target_segs _ _ _ _ _ _ _ _ T tr Htarget).
    reflexivity.
Qed.

(* [comment removed for export] *)
Corollary shape_strong_equiv_efs_eq :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  srealizes0 source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes0 target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until T'. intros inp Hs Ht Heq.
  eapply shape_strong_equiv_efs; [| exact Ht].
  eapply srz0_conseq; [exact Hs | exact Heq].
Qed.

(* [comment removed for export] *)
Theorem shape_strong_equiv_ef :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until T. intros inp Hs Ht.
  apply (shape_strong_equiv_efs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T);
    apply srealizes0_of_realizes; assumption.
Qed.

Corollary shape_strong_equiv_ef_eq :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  realizes source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until T'. intros inp Hs Ht Heq.
  eapply shape_strong_equiv_ef; [| exact Ht].
  eapply rz_conseq; [exact Hs | exact Heq].
Qed.

(* [comment removed for export] *)
Corollary srealizes_strong_equiv_error_free_scfg :
  forall (SRC TGT : Image) (en_s en_t : ExecEntry) (T : TSet) (inp : ProcInput),
  srealizes0 (img_segments SRC) scfg
    (init_config (img_segments SRC) (img_init_pc SRC) (img_phdrs SRC)
                 (en_sp en_s) (en_brk en_s) (en_mmap_base en_s) (en_draw en_s) source_alloc_limit inp) T ->
  srealizes0 (img_segments TGT) scfg
    (init_config (img_segments TGT) (img_init_pc TGT) (img_phdrs TGT)
                 (en_sp en_t) (en_brk en_t) (en_mmap_base en_t) (en_draw en_t) target_alloc_limit inp) T ->
  strong_equiv_error_free_scfg scfg SRC TGT en_s en_t inp.
Proof.
  intros [ssegs spc sph] [tsegs tpc tph] [ssp sbrk smb srnd] [tsp tbrk tmb trnd] T inp Hs Ht.
  unfold strong_equiv_error_free_scfg. cbn [img_segments img_init_pc img_phdrs en_sp en_brk en_mmap_base en_draw] in Hs, Ht.
  exact (shape_strong_equiv_efs ssegs spc sph ssp sbrk smb srnd source_alloc_limit
           tsegs tpc tph tsp tbrk tmb trnd target_alloc_limit T inp Hs Ht).
Qed.

End WithCfg.

End ShapeEF.
Module KillFree.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.ShapeEF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.BigintSpec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ev_not_kill (e : event) : Prop :=
  match e with KillEv _ _ => False | _ => True end.

Definition kill_free (T : TSet) : Prop := forall tr, T tr -> Forall ev_not_kill tr.

Lemma Forall_prefix {A} (P : A -> Prop) : forall (l1 l2 : list A),
  is_prefix l1 l2 -> Forall P l2 -> Forall P l1.
Proof.
  induction l1 as [|x l1 IH]; intros l2 Hp Hl2; [constructor|].
  destruct l2 as [|y l2]; cbn in Hp; [contradiction|].
  destruct Hp as [-> Hp]. inversion Hl2; subst. constructor; [assumption | eapply IH; eassumption].
Qed.

Lemma kill_free_nil : kill_free t_nil.
Proof. intros tr ->. constructor. Qed.

Lemma kill_free_emit : forall evs T,
  Forall ev_not_kill evs -> kill_free T -> kill_free (t_emit evs T).
Proof.
  intros evs T Hevs HT tr [Hp | (tr' & -> & Htr')].
  - eapply Forall_prefix; eassumption.
  - apply Forall_app. split; [exact Hevs | exact (HT _ Htr')].
Qed.

Lemma kill_free_alt2 : forall A B, kill_free A -> kill_free B -> kill_free (t_alt2 A B).
Proof. intros A B HA HB tr [H | H]; [exact (HA _ H) | exact (HB _ H)]. Qed.

Lemma kill_free_exit : forall code fs, kill_free (t_exit code fs).
Proof.
  intros code fs. unfold t_exit. apply kill_free_emit; [| apply kill_free_nil].
  constructor; [exact I | constructor].
Qed.

Lemma Forall_not_kill_writes : forall ch (s : list byte), Forall ev_not_kill (map (WriteEv ch) s).
Proof. intros ch s. induction s as [|b s IH]; cbn; constructor; [exact I | exact IH]. Qed.

Section FPX_1.
Context {fx : PropExec.FPState}.

Lemma kill_free_W_emit : forall ch s T, kill_free T -> kill_free (t_emit (W ch s) T).
Proof. intros ch s T HT. apply kill_free_emit; [apply Forall_not_kill_writes | exact HT]. Qed.

Lemma kill_free_die : forall msg fs, kill_free (t_die msg fs).
Proof. intros msg fs. unfold t_die. apply kill_free_W_emit. apply kill_free_exit. Qed.

Lemma kill_free_t_body : forall data fs, kill_free (BigintSpec.t_body data fs).
Proof.
  intros data fs. unfold BigintSpec.t_body.
  repeat first [ apply kill_free_die
               | apply kill_free_W_emit
               | apply kill_free_exit
               | match goal with |- kill_free (if ?c then _ else _) => destruct c end
               | match goal with |- kill_free (match ?c with _ => _ end) => destruct c end ].
Qed.

Lemma kill_free_spec : forall argv fs, kill_free (BigintSpec.spec argv fs).
Proof.
  intros argv fs. unfold BigintSpec.spec.
  repeat first [ apply kill_free_die
               | apply kill_free_t_body
               | apply kill_free_alt2
               | apply kill_free_exit
               | match goal with |- kill_free (if ?c then _ else _) => destruct c end
               | match goal with |- kill_free (match ?c with _ => _ end) => destruct c end ].
Qed.

(* [comment removed for export] *)
Lemma srealizes_not_dies_by_signal : forall scfg segs pc ph sp brk0 mb rnd lim inp T,
  srealizes0 segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  kill_free T ->
  ~ dies_by_signal (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros scfg segs pc ph sp brk0 mb rnd lim inp T Hs HK (tr & sig & fs & Htr & Hin).
  apply (srealizes_traces_iff scfg segs pc ph sp brk0 mb rnd lim inp T tr Hs) in Htr.
  pose proof (HK _ Htr) as HF.
  apply Forall_forall with (x := KillEv sig fs) in HF; [exact HF | exact Hin].
Qed.

Lemma srealizes_error_free_unkilled : forall scfg segs pc ph sp brk0 mb rnd lim inp T,
  srealizes0 segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  kill_free T ->
  error_free_unkilled (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros. split; [eapply srealizes_error_free; eassumption | eapply srealizes_not_dies_by_signal; eassumption].
Qed.

End FPX_1.

End KillFree.
From Stdlib Require ZArith NArith List Lia Bool Classical. From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence MustExit.
Module HaltsKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.BigintSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.KillFree.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition exit_codes_in (S : list word) (T : TSet) : Prop :=
  forall tr, T tr -> forall code fs, In (ExitEv code fs) tr -> In code S.

Lemma exit_codes_in_t_eq : forall S T T', t_eq T T' -> exit_codes_in S T -> exit_codes_in S T'.
Proof. intros S T T' Heq H tr Htr code fs Hin. refine (H tr _ code fs Hin). apply Heq; exact Htr. Qed.

Lemma kill_free_t_eq : forall T T', t_eq T T' -> kill_free T -> kill_free T'.
Proof. intros T T' Heq H tr Htr. apply H. apply Heq. exact Htr. Qed.

Lemma exit_codes_in_branch : forall S (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  exit_codes_in S (t_alt (fun i => t_emit (evs i) (T i))) -> exit_codes_in S (T i).
Proof.
  intros S I evs T i H tr Htr code fs Hin.
  refine (H (evs i ++ tr) _ code fs _); [| apply in_app_iff; right; exact Hin].
  exists i. right. exists tr. split; [reflexivity | exact Htr].
Qed.

Lemma kill_free_branch : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  kill_free (t_alt (fun i => t_emit (evs i) (T i))) -> kill_free (T i).
Proof.
  intros I evs T i H tr Htr.
  assert (HF : Forall ev_not_kill (evs i ++ tr)).
  { apply H. exists i. right. exists tr. split; [reflexivity | exact Htr]. }
  apply Forall_app in HF as [_ HF]. exact HF.
Qed.

(* [comment removed for export] *)
Lemma node_evs_trace : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  T i [] -> t_alt (fun i => t_emit (evs i) (T i)) (evs i).
Proof.
  intros I evs T i H0. exists i. right. exists []. split; [rewrite app_nil_r; reflexivity | exact H0].
Qed.

Lemma exit_codes_in_t_exit : forall S code fs, In code S -> exit_codes_in S (t_exit code fs).
Proof.
  intros S code fs Hin tr Htr c' fs' Hc.
  unfold t_exit, t_emit, t_nil in Htr.
  assert (Hc' : In (ExitEv c' fs') [ExitEv code fs]).
  { destruct Htr as [Hp | (tr' & -> & ->)].
    - exact (in_is_prefix _ _ _ Hp Hc).
    - rewrite app_nil_r in Hc. exact Hc. }
  destruct Hc' as [Hc' | []]. injection Hc' as -> _. exact Hin.
Qed.

Lemma exit_codes_in_emit_writes : forall S ch s T,
  exit_codes_in S T -> exit_codes_in S (t_emit (Spec.W ch s) T).
Proof.
  intros S ch s T H tr Htr code fs Hin.
  destruct Htr as [Hp | (tr' & -> & HT)].
  - exfalso. assert (Hin' : In (ExitEv code fs) (Spec.W ch s)) by exact (in_is_prefix _ _ _ Hp Hin).
    unfold Spec.W in Hin'. apply in_map_iff in Hin' as (b & Hb & _). discriminate Hb.
  - apply in_app_iff in Hin as [Hin | Hin].
    + exfalso. unfold Spec.W in Hin. apply in_map_iff in Hin as (b & Hb & _). discriminate Hb.
    + exact (H tr' HT code fs Hin).
Qed.

Lemma exit_codes_in_alt2 : forall S A B, exit_codes_in S A -> exit_codes_in S B -> exit_codes_in S (t_alt2 A B).
Proof. intros S A B HA HB tr [Htr | Htr]; [exact (HA tr Htr) | exact (HB tr Htr)]. Qed.

Lemma exit_codes_in_die : forall S msg fs, In (Spec.exit_code 2) S -> exit_codes_in S (Spec.t_die msg fs).
Proof. intros S msg fs H2. unfold Spec.t_die. apply exit_codes_in_emit_writes. apply exit_codes_in_t_exit. exact H2. Qed.

(* [comment removed for export] *)
Section SpecCodes.
Context {fx : PropExec.FPState} {bmK : BMode}.
Definition codes02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma in02_0 : In (Spec.exit_code 0) codes02. Proof. left. reflexivity. Qed.
Lemma in02_2 : In (Spec.exit_code 2) codes02. Proof. right. left. reflexivity. Qed.

Lemma exit_codes_in_t_body : forall data fs, exit_codes_in codes02 (BigintSpec.t_body data fs).
Proof.
  intros data fs. unfold BigintSpec.t_body.
  repeat first [ apply exit_codes_in_die; apply in02_2
               | apply exit_codes_in_emit_writes
               | apply exit_codes_in_t_exit; apply in02_0
               | match goal with |- exit_codes_in _ (if ?c then _ else _) => destruct c end
               | match goal with |- exit_codes_in _ (match ?c with _ => _ end) => destruct c end ].
Qed.

Lemma exit_codes_in_spec : forall argv fs, exit_codes_in codes02 (BigintSpec.spec argv fs).
Proof.
  intros argv fs. unfold BigintSpec.spec.
  repeat first [ apply exit_codes_in_die; apply in02_2
               | apply exit_codes_in_t_body
               | apply exit_codes_in_alt2
               | apply exit_codes_in_t_exit; apply in02_0
               | match goal with |- exit_codes_in _ (if ?c then _ else _) => destruct c end
               | match goal with |- exit_codes_in _ (match ?c with _ => _ end) => destruct c end ].
Qed.
End SpecCodes.

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

Lemma m_halted_of_proc : forall m m', m_proc m' = m_proc m -> m_halted m' = m_halted m.
Proof. intros m m' H. unfold m_halted. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_into_halted : forall cfg c evs c' code,
  sstep_cfg segs cfg c evs (SNext c') ->
  m_halted (cfg_model c') = Some code ->
  (m_killed (cfg_model c') = None /\ exists evs0 fs, evs = evs0 ++ [ExitEv code fs])
  \/ (exists evs0 sig fs, evs = evs0 ++ [KillEv sig fs]).
Proof.
  intros cfg c evs c' code Hss Hh.
  inversion Hss; subst; cbn [cfg_model] in Hh.
  - (* [comment removed for export] *) exfalso.
    match goal with [ H : mi_account_step _ _ _ = MachineOk _ |- _ ] =>
      pose proof (mi_account_step_model_frame _ _ _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _) end.
    rewrite (m_halted_of_proc _ _ Hp) in Hh. congruence.
  - (* [comment removed for export] *) exfalso.
    match goal with [ H : materialize_model_accesses _ _ = Some _ |- _ ] =>
      pose proof (materialize_model_accesses_frame _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _) end.
    rewrite (m_halted_of_proc _ _ Hp) in Hh. congruence.
  - (* [comment removed for export] *) left. split; [assumption |].
    match goal with [ H : m_halted ?m = Some ?c0 |- _ ] => idtac end.
    assert (code0 = code) by congruence. subst. eexists _, _. reflexivity.
  - (* [comment removed for export] *) right. eexists _, _, _. reflexivity.
Qed.

(* [comment removed for export] *)
Definition reach_fo (c0 c : config) : Prop := exists tr, star_cfg segs forced_only_cfg c0 tr c.

Lemma reach_fo_refl : forall c0, reach_fo c0 c0.
Proof. intros c0. exists []. apply star_cfg_refl. Qed.

Lemma star_cfg_snoc : forall cfg c0 tr c evs c',
  star_cfg segs cfg c0 tr c -> sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c0 (tr ++ evs) c'.
Proof.
  intros cfg c0 tr c evs c' Hstar Hss. induction Hstar as [c1 | c1 evs1 c2 tr2 c3 Hs Hst IH].
  - cbn. rewrite <- (app_nil_r evs). eapply star_cfg_step; [exact Hss | apply star_cfg_refl].
  - rewrite <- app_assoc. eapply star_cfg_step; [exact Hs | exact (IH Hss)].
Qed.

Lemma reach_fo_step : forall c0 c evs c',
  reach_fo c0 c -> sstep_cfg segs forced_only_cfg c evs (SNext c') -> reach_fo c0 c'.
Proof. intros c0 c evs c' (tr & Hstar) Hss. exists (tr ++ evs). eapply star_cfg_snoc; eassumption. Qed.

(* [comment removed for export] *)
Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m Hoff.
  destruct (classic (exists eff' m' evs', syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false)) as [H | H].
  - left. exact H.
  - right. intros eff' m' evs' Hspec.
    destruct (refusal_b i m (eff_ret eff')) eqn:Hr; [reflexivity |].
    exfalso. apply H. eexists _, _, _. split; [exact Hspec | exact Hr].
Qed.

Lemma fo_progress : forall cfg c evs st,
  sstep_cfg segs cfg c evs st -> exists evs' st', sstep_cfg segs forced_only_cfg c evs' st'.
Proof.
  intros cfg [ms model] evs st Hss.
  eapply sstep_cfg_progress; [| eapply sstep_cfg_sub; exact Hss].
  intros x8 _. apply refusal_decided_classic.
Qed.

(* [comment removed for export] *)
Section Master.
Variable scfgD : SpuriousCfg.          (* [comment removed for export] *)
Context {fx : PropExec.FPState} {bmK : BMode}.
(* [comment removed for export] *)
Variable S : list word.
Variable c0 : config.
Hypothesis NOREFUSE : forall c, reach_fo c0 c -> ~ budget_refused_at segs c.

Theorem srealizes_must_exit_fo : forall c T,
  srealizes0 segs scfgD c T ->
  reach_fo c0 c ->
  exit_codes_in S T ->
  kill_free T ->
  (forall code, m_halted (cfg_model c) = Some code -> In code S /\ m_killed (cfg_model c) = None) ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh Hmode | c T T' H IH Heq | c T Hon Hbr HT0];
    intros Hreach HE HK Hhalt.
  - (* [comment removed for export] *)
    destruct Hnode as [Hcomp Hsound].
    assert (Hnh : m_halted (cfg_model c) = None).
    { exact (sstep_cfg_not_halted _ _ _ _ _ (Hcomp i0)). }
    apply must_exit_in_at_cfg_running.
    + exact Hnh.
    + destruct (fo_progress _ _ _ _ (Hcomp i0)) as (evs' & st' & Hfo). eexists _, _. exact Hfo.
    + intros evs' Herr.
      destruct (Hsound evs' SError (sstep_cfg_mono _ _ _ _ _ _ (forced_only_cfg_least scfgD) Herr)) as (i & _ & Habs).
      discriminate Habs.
    + intros evs' c' Hfo.
      destruct (Hsound evs' (SNext c') (sstep_cfg_mono _ _ _ _ _ _ (forced_only_cfg_least scfgD) Hfo)) as (i & -> & Hc').
      injection Hc' as Ec. subst c'.
      apply (IH i).
      * eapply reach_fo_step; eassumption.
      * eapply exit_codes_in_branch; exact HE.
      * eapply kill_free_branch; exact HK.
      * intros code Hcode.
        pose proof (srealizes0_nonempty _ _ _ _ (Hcont i)) as H0.
        pose proof (node_evs_trace I evs T i H0) as Htr.
        destruct (sstep_cfg_into_halted _ _ _ _ _ Hfo Hcode) as [(Hk & evs0 & fs & Hevs) | (evs0 & sig & fs & Hevs)].
        { split; [| exact Hk]. apply (HE (evs i) Htr code fs). rewrite Hevs. apply in_app_iff. right. left. reflexivity. }
        { exfalso. pose proof (HK (evs i) Htr) as HF. rewrite Hevs in HF.
          apply Forall_app in HF as [_ HF]. inversion HF as [| x l Hx _]; subst. exact Hx. }
  - (* [comment removed for export] *)
    destruct (m_halted (cfg_model c)) as [code |] eqn:Hc; [| congruence].
    destruct (Hhalt code eq_refl) as [Hin Hk].
    eapply must_exit_in_at_cfg_halted; eassumption.
  - (* [comment removed for export] *)
    exfalso. exact Hmode.
  - (* [comment removed for export] *)
    apply IH; [exact Hreach | eapply exit_codes_in_t_eq; [apply t_eq_sym; exact Heq | exact HE]
              | eapply kill_free_t_eq; [apply t_eq_sym; exact Heq | exact HK] | exact Hhalt].
  - (* [comment removed for export] *)
    exfalso. exact (NOREFUSE c Hreach Hbr).
Qed.
End Master.
End WithSegs.

(* [comment removed for export] *)
Section Top.
Context {fx : PropExec.FPState} {bmK : BMode}.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma noref_of_within_budget : forall segs pc ph sp brk0 mb rnd lim inp,
  ~ run_scfg_budget_refused forced_only_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp ->
  forall c, reach_fo segs (init_config segs pc ph sp brk0 mb rnd lim inp) c -> ~ budget_refused_at segs c.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp Hnb c (tr & Hstar) Hbr.
  apply Hnb. cbn [run_scfg_budget_refused]. exists tr, c. split; [exact Hstar | exact Hbr].
Qed.

Theorem srealizes_init_must_exit : forall scfgD segs pc ph sp brk0 mb rnd lim inp S T,
  srealizes0 segs scfgD (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  exit_codes_in S T -> kill_free T ->
  ~ run_scfg_budget_refused forced_only_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp ->
  must_exit_in_scfg forced_only_cfg S (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros scfgD segs pc ph sp brk0 mb rnd lim inp S T Hs HE HK Hnb.
  cbn [must_exit_in_scfg].
  eapply (srealizes_must_exit_fo segs scfgD S _ (noref_of_within_budget _ _ _ _ _ _ _ _ _ Hnb)).
  - exact Hs.
  - apply reach_fo_refl.
  - exact HE.
  - exact HK.
  - intros code Hh. exfalso. unfold init_config in Hh. cbn [cfg_model] in Hh. rewrite m_halted_init_model in Hh. discriminate Hh.
Qed.
End Top.

End HaltsKit.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module LibAtomic.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.
Ltac2 kr_t_LibAtomic () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem3Run<in_is_prefixc59OSSVerify5KrLib7Mh_00558KillFree=Forall_prefixC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consI46Stdlib5Lists4List6Exists00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00558HaltsKitDexit_codes_in_branchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg5t_altC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00558HaltsKit@kill_free_branchC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00558HaltsKit>node_evs_traceC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK59OSSVerify5KrLib7Mh_00367SpinAlg:srealizes001C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr0DK47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4prod01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes3nat02C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec4v_lwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics5Riscv3Sem5is_x0K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv3Sem3eff06C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff07C56Stdlib6ZArith6BinInt1Z3eqbC49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8b_lw_valC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9le_word_vC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6ov_rdnC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec=bv_eqb0_is_x0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepc59OSSVerify5KrLib7Mh_00559LibAtomic6mkst_rC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C45stdpp9bitvector;definitions:bv_extractK47Corelib4Init9Datatypes4list02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr6awidth01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib4Init5Logic4True01I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00C45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsCbv_wrap_bv_unsignedC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitionsCbv_extract_unsignedK4ELinuxProcessSemantics5Riscv5Instr6awidth02I47Corelib4Init5Logic3and00K4ELinuxProcessSemantics5Riscv5Instr5instr0EC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32K4ELinuxProcessSemantics5Riscv3Sem3eff08C59OSSVerify5KrLib7Mh_00387SeqExecAstore_bytes_low32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflK47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics5Riscv3Sem9amo_bytesI4ELinuxProcessSemantics5Riscv5Instr6awidth00K4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem<branch_takenC49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00C49OSSVerify5KrLib8PropExec4c_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00559LibAtomic@step_branch_tk_rC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c59OSSVerify5KrLib7Mh_00559LibAtomic@step_branch_ft_rC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5instr08C4ELinuxProcessSemantics5Riscv3Sem5alu64I4ELinuxProcessSemantics5Riscv5Instr5aluop00K4ELinuxProcessSemantics5Riscv5Instr5instr0:".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition mkst_r (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (r : word)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := Some r; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Lemma mkst_r_svc : forall regs pc mem rom r, ms_svc_pending (mkst_r regs pc mem rom r) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_1"] "h03memh12pch21rh34regsh43romp;1p;2p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0p1006Gp4p710R0p8p1006ep4p710R6P3p8P6P0p8p1007Bp4p70R7P1p8P7p10080p4p7210p8P7P3p8P7p1008Lp4p710R1p8P7P6p8P7P4p8P7P5p8P7p1009Bp4p710R6p8P7P0p8P7p1009cp4p710p8P7p100:@p4p710p8P7p100;9p6051001R8p8P7p100<<p4p7210p8P7p100<Yp4p710p8g00=6R7p4p7210R9P3p8P9P4p8P9P5p8P9P0p8P9p100=bp4p710p8P2P0p8P8P3p8P8P1p8P8P4p8P8P5p8P8P6p8P8P0p8P8p100>ip4p710p8p100?Kp60521000R8p100@Up4p710R6p8p100APp6051000R1P6p8p100BVp6051000R2P6p8p100CZp4p70R6P3p8P6P4p8P6P5p8P6P0p8p100DPp4p7511110R0P8p8P0P1p8P0P2p8g00EQj10Tg00F6j17Tg00F[j11Tg00G9j12TP7j26Tg00G\j13Tg00H>j15Tg00H`j24Tg00I:#0R7#7#1%07#0R7#0#0#0#1#2R2'6%17#2#3\2R7%32%52'4X22X47W0X12W3o"). Qed.
End FPX_1.


Ltac atomic_pipeline Hfetch Hecall Hdecode :=
  unfold mkst_r;
  step_pipeline Hfetch Hecall Hdecode;
  cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
  rewrite ?bv_eqb0_is_x0.

(* [comment removed for export] *)
Ltac norm_pc_r :=
  try lazymatch goal with
      | |- CatSim.msteps _ (mkst_r _ ?p _ _ _) _ => wlit p
      end.
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_lr_w : forall segs regs pc mem rom w aq rl rd rs bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr AW aq rl rd rs, 4%Z) ->
  (bv_unsigned (getr regs rs) mod 4 = 0)%Z ->
  rdn segs mem (getr regs rs) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
                    (v_addi pc 4) mem rom (getr regs rs)).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "p'0h01bi001bh11vi011vh21mh31oh41ti021th53Halh67Hdecodeh76Hecallh86Hfetchh95Hreadh:2Hvh;2aqh<2bsi032bsh=3memh>2pch?2rdh@4regshA2rlhB3romhC2rshD4segshE1wi041whF1zi051ai061ci076c_fcsri087c_fregsi094c_pci0:6c_regsi0;6c_resvi0<1ii0=Cinterp_eff_accessesi0>3iszi0?1ki0@2m'i0A1ni0B1pi0C2p0i0D2p1i0E2p2i0F2p3i0G2p4i0H2p5i0I2p6i0J1ri0K6reporti0L3st'i0M1xp%0p&0p;1p;2p;3p;5p;4p;8p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0g006GR0p4p710R6p8p1006ep4p710R7P3p8P7P6p8p1007Bp4p70R8P1p8P8p10080p4p7210p8P8P3p8P8p1008Lp4p710R1p8P8P7p8P8P4p8P8P5p8P8p1009Bp4p710R7p8P8P6p8P8p1009cp4p710p8P8p100:@p4p710p8P8p100;9p6051001R9p8P8p100<<p4p7210p8P8p100<Yp4p710p8g00=6R8p4p7210R:P3p8P:P4p8P:P5p8P:P6p8P:g00=bR:p4p710p8P2P6p8P9P3p8P9P1p8P9P4p8P9P5p8P9P7p8P9P6p8P9p100>ip4p710p8p100?Kp60521000R9p100@Up4p710R7p8p100APp6051000R1P7p8p100BVp6051000R2P7p8p100CZp4p70R7P3p8P7P4p8P7P5p8P7P6p8p100DPp4p7511110R6P9p8P6P1p8P6P2p8g00I_j1yTg00EQj1FTg00F6j1qTg00F[j1STg00G9j1YTP8k20DTg00G\R8j1HTg00J?j2`Tg00KAj23Tg00Kcj31Tg00L=j1vTg00M=R2j2\Tg00M]j1ZTg00NNj5|Tg00O:j1{Tg00OXj4PTg00P8j2CTg00Pjj2TTg00QTj2xTg00R4j1:Tg00RSj4wTg00SDk10<Tg00TAR6j1aTP:j1sTg00UIj5@Tg00V;j3hTg00WGj1RTg00XEj3oTg00YJj3nTg00ZPj3mTg00[Uk104Tg00\5j1bTg00]=j1fTg00^Ej2]Tg00_Oj3lTg00`2j3kTg00`_j1JTg00aQj3jTg00bEj1}Tg00c:j2LTg00H>k10GTg00cnk10FTg00dbj1WTg00eaj1=Tg00faj1VTg00gbk20ETg00h`j1QTg00i_j1BTg00j^j1UTg00k\j85Tg00lcj2eTg00mIj50Tg00n2j3dTg00nYj3cTg00odj2GTg010hk10CTg011Qk10BTg012;k10ATg012bk10@Tg013Kk10=Tg0144j2KTg015;j1uTg0164j1ITg016\j2>Tg017dj4_Tg018ij1gTg019ij4rTg01:ik208Tg01;fk307Tg01<jj2^Tg01=Tj2pTg01>Bj1[Tg01>`j1MTg01?Hj3NTg01?mj3DTg01@Xj54Tg01AHj1OTg01B0j3XTg01BXk206Tg00H`j2zTg01C5k10:TP0j66Tg01Cik10;Tg01D_k303Tg01EVk402Tg01FJk101Tg01GEk100Tg01HBk20>Tg01I>k60?Tg01J;j3?Tg01KBj4~Tg01Kkj3iTf2R0g01LKR:f1R1f0R93?'>p=<f7R7f6R5f5R4f4R3f3R;P0P1P9G5,>:p=81>:9p=tg01MRR<P;P0P1CP=?39p=2P0g01N;P1P9C~p=AP0g01NYR=P1P9CPp=EAi0199?3;p>091K199i;0p=71G01=?;9p>051G431K199i;05?5,G7p=;1G01=?;9,K39?:4,>5p=9g01O8#yg00I:#FR>#q#SR?%F>R>#FR@#F#FRA#F#SRB#YRC+0DRD%S@#YRE#H\CRF%SARA#YRGg01P7RH%Y?S00Q00%yERE%HGRIf;RJf9RK'`13G531%v7g01PWS0151Hg01Q7S02g01QcRL'\RM#HRNf8RO#ZQ02PLg01RARPP7P5P4P3D|%{>R>CP,3M31f=RQ/C4,TB/x>g01RnRR51L%HERSf?RTf<RUf>RV/C5g01SLRW#:RX#:RY#:#:RZCw13E431&0<51TB451LPI13GU%a:R[P8PG%s:R\#aR]P9fCR^p,2fxR_fBR`fARaf@RbPTD@;h9RcP8PGP]P_PaPbPTPVD@Rd#RRe=o`bPcP8PGP]An`ebPcP6P:P]Am`ebg01Sk$04Rc9<\9S03%b\Rf%f\Rgn10110M00031010L0000n10110M00021010400n10110M00021010400n10110M00021010400,]:PHPDf:Rhg01U0Ri9l?RS045k?Pa%J7S059jahRjn0100000020000%}_Rk1Lb>Rl&0GCRm1CaKRn,3CRo&0F_RpPTPVG8Rq31X3IPHQ01P6P\P[PHP]P9%Wd%=d%Vd%q@#{=l?i-0Ed,3C%Qd%BdPe%UdG5=<\cP8PMP]%ZQP2Q02PLP]P9P61\<FRe#sRiP]fES061eB9S07P_fDR@P^P`PaD@RI#W%=I%VI%BI%QID07d1%RI3cP2P<PFP]1Ge9RI&0C1S08&0B1S09&0A1S0:Pm&0@1S0;&0=1S0<P9P_fGS0=fFS0>Q06P@D@#UG51Ke0Rr5<\n200110M00012010610@PfPgn10110M00031010K0000n200110B00012010<10>RsPHP]%uQPfPgn0100000020000Rtn10110M00021110B00n01000000200011G:9#tRu%b:Rv%f:Rwn10110J00031010K0000=1[qX0HPNQ02PLPPPJPhPKPOD|S0?P>CP,3MP6P\P[P8PMP]P9PsPtn10110M00021110B00PuPvPwn10110J00031010K0000=1[qX3NPH%IKRNP6P\P[P6PiP]g01ULRq%aiRt^2F]4S0@PqPtP1PePFP9P1PcD2,>iS0A%fiRs%biRxPsPxPxP8PEPtfHS0BP;P1g01V4RyP=P0PWg01VRRzP=P9PWPzP=P9PWPzP=P9PWPzP=P9PWPzP=P9PWPzP=P9PWPzP=P9PWPW%:Z#:#:#:n0110H00031010I1010I00PZn0110G00031010H1010H00PYn0110F00031010G1010G00PXn0110E00031010F1010F00PWn0110D00031010E1010E00PWn0110C00031010D1010D00PWn0110B00031010C1010C00RXn0110A0002001010BS0CC_P6PiPtP5P1%g9RY9AB;O1P3O2PePI1\C=RzPyP=P3PWPXn0110A0002001010B9EC;1Ke9I09,>iR{PxPsn10110M00031010K0000S0DPxn10110M00021110300PHPtfIP3P0PyP=P;PWPXn0110A0002001010BS0ECrP6PiPtP5P9Q0E1T;1+08:0730O2P{PxPsn10110M00031010K0000S0FPxn0100000020100n0110200081010610106101061010610106101063110A10510?4110A10510110?X2FX4qp?100010=R{PHPqPHPCPN1eBRS0G1^aKn0100000020000S0H,pP#[PaPaPkPbPmPmPpPTPVG5RX#=S0IPb%BXS0JPmD0#MQ0HP<PDPHP<%IJRXP`P`PkPaPmPmPpPbPTG5RW#=R=1eB>Ry9NBaR|%BWRWPmD0P?PCPJADAB9S0KP`D4R}P=P|PWPmD0n0100000020000RWP3n0110600015010:10810910710;P<PDPWP;n0110600015010:10810910710;P<PCPWP0n0110600015010:10810910710;P<PGPWP1n0110600015010:10810910710;PHPC%IhRWQ0G1^`hn0100000020000,3CD0#OX1G5XAn0100000020001PTO2P2P<PFP]PIP<PDP1P3n0110600015010:10810910710;S0LP<PDP1P;n0110600015010:10810910710;S0MP<PCP1P0n0110600015010:10810910710;S0NPmP<%HCP1P9n0110600015010:10810910710;S0OP<PGP1P1n0110600015010:10810910710;S0PP9PaG5S0Q=<\rn200110M00012010610@R=PfPgn10110M00031010K0000PuPvPwn10110J00031010K0000PHPDP9PaPjn0100000020000PkPlPmPoPpPTPVG851[X0HPLPRP6P\P[P6PiP]P{PHPq2069R#[PaPkPbPpPmD0#MP<PDPHP<PXP`PkP|PpPmD0S0RP}PkP|PpPmD0n0100000020000R}P3n0110600015010:10810910710;P<PDP}P;n0110600015010:10810910710;P<PCP}P0n0110600015010:10810910710;P<PGP}P1n0110600015010:10810910710;1C`hR},3CRRD0#OX1G9XAnn0100000020001PTO2P=PfPgn10110M00031010K0000PuPvPwn10110J00031010K0000PHPDPWPaPjn0100000020000PkPlPmPoPpPTPVG8Rj51[XFLPSPaPV1CbOR{PZCwS0SP6P\P[P6PiP]P8PEPtP9PePePePFP<PDPHP<PXQ0RP?PCPJAABAY9DABP`D4PkP|PpPmD0n0100000020000RYP3n0110600015010:10810910710;P<PDPYP;n0110600015010:10810910710;P<PCPYP0n0110600015010:10810910710;P<PGPYP1n0110600015010:10810910710;PRD0PbPcD2RYPzAEC}ZS0TPePYC7H05,>iPxn10110M00021110300P=PfPgn10110M00031010K0000PuPvPwn10110J00031010K0000=1[jX3SR=PS13E7P=PCP5P6P\P[P2P<PFP]PePePePePFP<PDPHP<PWPaPkANBbyR=PpPmD0S0UP?PCPhAABA99DABPaD4PkP=PpPmD0n0100000020000RSP3n0110600015010:10810910710;P<PDPSP;n0110600015010:10810910710;P<PCPSP0n0110600015010:10810910710;P<PGPSP1n0110600015010:10810910710;PoD0PTPcD2RSPzAECnZRnPePSG;P\Q0LQ0MQ0NPmQ0OQ0PP9PbG5RSPePePePePFP<PDPHP<%IUS0VP^PkANB`yS0WPpPmD0S0XP?PCPUAABA09DABP^D4PkQ0WPpPmD0n0100000020000RYP3n0110600015010:10810910710;P<PDPYP;n0110600015010:10810910710;P<PCPYP0n0110600015010:10810910710;P<PGPYP1n0110600015010:10810910710;1C^JRY,3CR}D0PaPcD2R~PzAECYZRYPeP~C7F9n200110M00012110610@PuPvPwn10110J00031010K0000=1[jX0CPC%J5S0YP6P\P[P2P<PFP]PePePePePFP<PDPHP<PWQ0UP?PCPhP9PaD4PkP=PpPmD0n0100000020000R~P3n0110600015010:10810910710;P<PDP~P;n0110600015010:10810910710;P<PCP~P0n0110600015010:10810910710;P<PGP~P1n0110600015010:10810910710;PoD0PTPcD2R~PzPnPeP~G;P\PSPePePePePFP<PDPHP<Q0VQ0XP?PCPUP0P^D4PkQ0WPpPmD0n0100000020000R~P3n0110600015010:10810910710;P<PDP~P;n0110600015010:10810910710;P<PCP~P0n0110600015010:10810910710;P<PGP~P1n0110600015010:10810910710;P}D0PaPcD2R~PzPYPeP~C7F9n200110M00012110610@PuPvPwn10110J00031010K0000=1[jX0CPC1LT>R~P6P\P[P2P<PFP]PePePePePFP<PDPHP<PWPaPkP9PpPmD0P?PCPhQ05PaD4S05PkP9PpPmD0n0100000020000S0WP3n0110600015010:10810910710;P<PDQ0WP;n0110600015010:10810910710;P<PCQ0WP0n0110600015010:10810910710;P<PGQ0WP1n0110600015010:10810910710;PoD0PTPcD2S0WPzPnPeQ0WG;P\PSPePePePePFP<PDPHP<Q0VP^PkP0PpPmD0P?PCPU%JKP^D4S0VPkP0PpPmD0n0100000020000S0WP3n0110600015010:10810910710;P<PDQ0WP;n0110600015010:10810910710;P<PCQ0WP0n0110600015010:10810910710;P<PGQ0WP1n0110600015010:10810910710;P}D0PaPcD2S0WPzPYPeQ0WC7F9n200110M00012110610@PuPvPwn10110J00031010K0000=1[jX0CPNPHPHP6P\P[P2P<PFP]PePePePePFP<PDPHP<P9P`Pk1La>S0WPpPmD0S0XP?PCPJ%JOP`D4S0ZPkQ0WPpPmD0S0[n0100000020000RjP3n0110600015010:10810910710;P<PDPjP;n0110600015010:10810910710;P<PCPjP0n0110600015010:10810910710;P<PGPjP1n0110600015010:10810910710;PRD0PbPcD2RjPzQ0TPePjG;P\Q0QPePePePePFP<PDPHP<P0P@Pk1L^>RjPpPmD0P?PCPQ%JhP@D4PkPjPpPmD0n0100000020000RjP3n0110600015010:10810910710;P<PDPjP;n0110600015010:10810910710;P<PCPjP0n0110600015010:10810910710;P<PGPjP1n0110600015010:10810910710;1C@URj,3CD0P`PcD2S0QPzAECjZPeQ0QC7F9n200110M00012110610@PuPvPwn10110J00031010K0000PHPDP9P`Q0Zn0100000020000PkQ0WPmPRPpPbPTG851[P9PaPkPlPmPoPpPTPVG8Rj,z[P6P\P[P2P<PFP]PePePePePFPaPkPlPpPoD0PTPcD2S0WPzPnPeQ0WG;P\PSPePePePePFP^Pk1L`>S0WPpP}D0PaPcD2S0ZPzPYPeQ0ZC7F9n200110M00012110610@PuPvPwn10110J00031010K0000=1[jeQ05PkPlPmPoPpPTPVG8Rj,z[P6P\P[P2P<PFP]PePePePePFQ05PkPlPpPoD0PTPcD2RlPzPnPePlG;P\PSPePePePePFQ0VPkQ0WPpP}D0PaPcD2R}PzPYPeP}C7F9n200110M00012110610@PuPvPwn10110J00031010K0000=1[jen0110001020101b0P6P\P[P2P<PFP]PePePePePFP<PDPHP<PNPbPkP~PpPmD0P?PCPKQ0YPbD4PkP~PpPmD0n0100000020000RjP3n0110600015010:10810910710;P<PDPjP;n0110600015010:10810910710;P<PCPjP0n0110600015010:10810910710;P<PGPjP1n0110600015010:10810910710;13C{RjD0PVPcD2R}PzAEC{ZS0WPeP}G;P\Q0LQ0MQ0NPmQ0OQ0PP9PTG5R}PePePePePFP<PDPHP<PXQ0XQ0[n0100000020000RYP3n0110600015010:10810910710;P<PDPYP;n0110600015010:10810910710;P<PCPYP0n0110600015010:10810910710;P<PGPYP1n0110600015010:10810910710;PRD0PbPcD2RYPzQ0TPePYC7F9n200110M00012110610@PuPvPwn10110J00031010K0000PHPDPNPbQ0Y9jbKS0Yn0100000020000PkP~PmPjPpPVPQG8RY51[eANBTyRl&0:TE6AABA59DAB&0;5E6%g7RnB03759E6P6P\P[P2P<PFP]PePePePePFP<PDPHP<PNPbPkPlPpPmD0P?PCPKAABAn9DABPbD4PkPlPpPmD0n0100000020000RlP3n0110600015010:10810910710;P<PDPlP;n0110600015010:10810910710;P<PCPlP0n0110600015010:10810910710;P<PGPlP1n0110600015010:10810910710;PjD0PVPcD2RlPzQ0WPePlG;P\P}PePePePePFP<PDPHP<PXQ0RP?PCPJ%gK9ABA9DABP`D4PkP|PpPmD0n0100000020000R|P3n0110600015010:10810910710;P<PDP|P;n0110600015010:10810910710;P<PCP|P0n0110600015010:10810910710;P<PGP|P1n0110600015010:10810910710;PRD0PbPcD2RcPzQ0TPePcC7F9n200110M00012110610@PuPvPwn10110J00031010K0000=1[YeQ0SP1E6PaPVP{PZC_PaPVPZP{H02E6P6P\P[P6PiP]Q0@PqPtP1Q0APsPxPsPxPxP8PEPtQ0=P;P1Q0CC_Q0DPxn10110M00021110300PHPtQ0BP3P0Q0ECrQ0FPxn0100000020100n0110200081010610106101061010610106101063110A10510?4110A10510110?X2FX4qp?100010=RxPHPqQ01PbPkPTPpPmD0#MP<PDPHP<PWQ0UP?PCPhQ0KPaD4RhPkP=PpPmD0n0100000020000RtP3n0110600015010:10810910710;P<PDPtP;n0110600015010:10810910710;P<PCPtP0n0110600015010:10810910710;P<PGPtP1n0110600015010:10810910710;PoD0#OX1G9XA{n0100000020001PVO2P2P<PFP]PIA<\Srn200110M00012010610@RSPfPgn10110M00031010K0000PuPvPwn10110J00031010K0000=1[Ye1TB{/x>P0E6P6P\P[P6PiP]PxPHPqPHPC%IOQ0G1^bOn0100000020000RO,pP#[PbPbPkPTPmPmPpPVPQG5RP#=PT%BPPmD0#MP<PDPHP<PWPaQ0IP=Q0JPmD0PhQ0IP=Q0JPmD0n0100000020000R=P3n0110600015010:10810910710;P<PDP=P;n0110600015010:10810910710;P<PCP=P0n0110600015010:10810910710;P<PGP=P1n0110600015010:10810910710;Q0H,3CD0#OX1G9XAOn0100000020001PVO2PSPfPgn10110M00031010K0000PuPvPwn10110J00031010K0000=1[YeQ049k?KR?&01KE6P6P\P[P6PiP]Q0?P_PbPTPVPQD@RK#W%=K%VK%BK%QKD05dy%RKRy5caP2P<PFP]PIQ08Q09Q0:PmQ0;Q0<P9P_P^P`PaPbD@RY#UG5=<\rn200110M00012010610@PfPgn10110M00031010K0000PuPvPwn10110J00031010K0000PHPDP?PbQ0Yn0100000020000RbPkP~PmPjPpPVPQG8Rp51[e%ZURjP;E6P6P\P[P8PMP]PjP2Q02PLP]P9P6PiP]Q07%WY%=Y%VY%BY%QYD07d1%RY5c@P2P<PFP]PIQ08Q09Q0:PmQ0;Q0<P9P_Q0>Q06P@P^D@#UG5=<\rn200110M00012010610@PfPgn10110M00031010K0000n200110B00012010<10>PHP]%uUPfPgn0100000020000n10110M00021110B00PuPvPwn10110J00031010K0000=1[pe%vUP3E6AhaKU,]:=1[pRUePUe1`aTP4E6P8PGP]&00KR4,`aAh`d9RdP8PGP]Aoay4PdP8PGP]Anay4PdP6P:P]Amay4Q03PfPgn10110M00031010L0000n10110M00021010400n10110M00021010400n10110M00021010400,]:=1[pe20>aKRK=1[peP_PbP~PVPQP{J0?#t91[KeW:W9W5W6W7W8X1CW<WCW?XAHW;WEXBFW=X>CW@WDo"). Qed.

Lemma step_lr_d : forall segs regs pc mem rom w aq rl rd rs bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr AD aq rl rd rs, 4%Z) ->
  (bv_unsigned (getr regs rs) mod 8 = 0)%Z ->
  rdn segs mem (getr regs rs) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs else regupd regs rd v)
                    (v_addi pc 4) mem rom (getr regs rs)).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "p'0h01bi001bh11vi011vh21mh31oh41ti021th51zh62b1h72b2h81ni031nh91Hh:3Halh;7Hdecodeh<6Hecallh=6Hfetchh>5Hreadh?2Hvh@2HzhA2aqhB2bsi042bshC3memhD2pchE2rdhF4regshG2rlhH3romhI2rshJ4segshK1wi051wi061ai071ci086c_fcsri097c_fregsi0:4c_pci0;6c_regsi0<6c_resvi0=1ii0>Cinterp_eff_accessesi0?3iszi0@1ki0A2m'i0B1pi0C2p0i0D2p1i0E2p2i0F2p3i0G2p4i0H2p5i0I2p6i0J1ri0K6reporti0L3st'i0M1xp%0p&0p;1p;2p;3p;5p;4p;6p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0g006GR0p4p710R6p8p1006ep4p710R7P3p8P7P6p8p1007Bp4p70R8P1p8P8p10080p4p7210p8P8P3p8P8p1008Lp4p710R1p8P8P7p8P8P4p8P8P5p8P8p1009Bp4p710R7p8P8P6p8P8p1009cp4p710p8P8p100:@p4p710p8P8p100;9p6051001R9p8P8p100<<p4p7210p8P8p100<Yp4p710p8g00=6R8p4p7210R:P3p8P:P4p8P:P5p8P:P6p8P:g00=bR:p4p710p8P2P6p8P9P3p8P9P1p8P9P4p8P9P5p8P9P7p8P9P6p8P9p100>ip4p710p8p100?Kp60521000R9p100@Up4p710R7p8p100APp6051000R1P7p8p100BVp6051000R2P7p8p100CZp4p70R7P3p8P7P4p8P7P5p8P7P6p8p100DPp4p7511110R6P9p8P6P1p8P6P2p8g00I_j1wTg00EQj1HTg00F6j1sTg00F[j1MTg00G9j18TP8k20JTg00G\R8j1JTg00J?j2_Tg00KAj23Tg00Kcj31Tg00L=j1yTg00M=R2j2cTg00M]j1XTg00NNj5|Tg00O:j1eTg00OXj4WTg00P8j2BTg00Pjj27Tg00QTj2vTg00R4j1:Tg00RSj4tTg00SDk10FTg01W7k30ATg01W[k10=Tg01X9j2pTg01XYj2oTg01Y?k209Tg01Z1k106TP0j65Tg01ZUk405Tg00TAR0j1^TP:j1rTg00UIj5@Tg00V;j3`Tg00WGj1UTg00XEj3lTg00YJj3jTg00ZPj3iTg00[Uj1}Tg00\5j1hTg00]=j1gTg00^Ej2fTg00_Oj3{Tg00`2j3zTg00aQj3xTg00bEk10KTg00c:j2LTg00H>k10ITg00cnk10HTg00dbj1TTg00eaj1ATg00faj1VTg00gbk20GTg00h`j1STg00i_j1ETg00j^j1RTg00k\j86Tg00lcj2bTg00mIj50Tg00n2j3aTg00nYj3]Tg00odj2GTg010hk10ETg011Qk10DTg012;k10@Tg012bk10?Tg013Kk10>Tg0144j2ITg015;j1qTg0164j1KTg016\j2?Tg017dj4\Tg018ij1dTg019ij4kTg01:ik20;Tg01;fk308Tg01<jj2ZTg01=Tj2nTg01>Bj1[Tg01>`j1QTg01?Hj3OTg01@Xj54Tg01AHj1PTg01B0j3NTg01BXk207Tg00H`j2mTg01C5k104Tg01D_k303Tg01EVk402Tg01FJk101Tg01GEk10BTg01HBk20CTg01I>k600Tg01KBj4~Tg01J;j3DTg01Kkj3YTf2R:g01N;R6f1R1f0R9C~p=<g01LKR7?D19,?:p=Cf7R5f6R4f5R3f4R;f3R<P:P1P9G6,?7p==1?79p=ug01MRR=P<P:P1CW=D;9p=2P:g01NYR>P1P9CWp=FAY:199D;<p>0<1I199Y<:p=91G:1=D<9p>0:1G3;1I199Y<:5D4,G5p=;1G:1=D<9,I;9D73,?4p=>g01O8#wg00I:#HR?#s#MR@%H?R?#HRA#H#HRB#H#MRC#8RD+0JRE%MA#8RF#J\DRG%MB#8RBg01P7RH%8@S00Q00%wFRF%JBRIf;RJf9RK'_13B431%y5g01PWS0151Hg01Q7S02g01QcRL'cRM#JRNf8RO#XQ02PLg01[GRPP5P4P3P;D|%e?R?CW,3M31f=RQ/B3,7C%eAS03'vg01RnRR51L%JFRSf?RTf<RUf>RV/B4g01SLRW#:RX#:RY#:#:RZ#:#:#:#:R[Ct13F331&0F417C351Lg01V4R\%89R]%81R^g01\4%8:?11917<:17<1R_51LR`[17:117:951L%8<?1:1[Ra%8;?1<:\`B0A:19P9n2001000000120000000W7W6W8Pa^7^^6]^8\P9PCA<CC5S04P5PL17C5R]&0=6'p,oC17COR^91L9X5LPLP]1oC9=1L^X5L209C51p]R&06]E5Q04,7CPCP6PCP5H05E5O4b9A<CC4=1D4PI13BQ%^7R6P8PB%r7R]#^R^P9fDRap,2fxR`fCRbfBRcfARdf@ReD@;`9RfP8PBP^P`PcPdPePTD@Rg#URh=lbdPfP8PBP^AjbhdPfP0P7P^Aibhdg01Sk#}Rf9C]9S05%h]Ri%g]Rjn10110M00031010L0000n10110M00021010500n10110M00021010500n10110M00021010500,f7PHPEg01U0Rk9{@RS069z@JPcAxcJORln0100000020000&0K`Rm1Ld?Rn&0IDRof:Rp,BcRq,3DRr&0H`RsPePTG=Rt31X3IPHQ01P0P]P6PHP^P9%Tg%Ag%Vg%sA#e={@k-0Gg,3D%Sg%EgPh%RgG6=C]fP8PMP^%XVP2Q02PLP^P9P01c=GRh#rRkP^fFS071bC9S08P`fERAPaPbPcD@RI#T%AI%VI%EI%SID07a1%UI3]P2P=PGP^1Gh9RI&0E1S09&0D1S0:&0@1S0;Po&0?1S0<&0>1S0=P9P`fHS0>fGS0?Q07PAD@#RG61Ih:Ru5C]n200110M00012010710APiPjn10110M00031010K0000n200110B00012010=10?RvPHP^%qVPiPjn0100000020000Rwn10110M00021110B00n01000000200011G79#uRx%h7Ry%g7Rzn10110J00031010K0000=16tX0HPNQ02PLPPPUPJPpPKD|S0@P?CW,3MP0P]P6P8PMP^P9PvPwn10110M00021110B00PxPyPzn10110J00031010K0000=16tX3NPH%KpRNP0P]P6P0PkP^g01ULRt%^kRw^2G]4S0APtPwP1PhPGP9P1PfD2,?kS0B%gkRv%hkR{PvP{P{P8PFPwfIS0CP<P1P\P>P:PWg01VRR|P>P9PWP|P>P9PWP|P>P9PWP|P>P9PWP|P>P9PWP|P>P9PWP|P>P9PWPWP[n0110H00031010I1010I00PZn0110G00031010H1010H00PYn0110F00031010G1010G00PXn0110E00031010F1010F00PWn0110D00031010E1010E00PWn0110C00031010D1010D00PWn0110B00031010C1010C00RXn011030002001010BS0DC\P0PkPwP4P1%d9RY9<C<O1P;O2PhPI1cD>RZP\P>P;PWPXn011030002001010B9FD<1Ih9I0<,?kR|P{Pvn10110M00031010K0000S0EP{n10110M00021110400PHPwfJP;P:P\P>P<PWPXn011030002001010BS0FCkP0PkPwP4P9Q0F00;_:08;:O2P|P{Pvn10110M00031010K0000S0GP{n0100000020100n0110200081010710107101071010710107101073110310610@4110310610110@X2GX4tp?100010>R|PHPtPHPDPN1bCRS0H1Zcpn0100000020000S0I,nP#[PcPcPmPdPoPoPsPePTG6R_#AS0JPd%E_S0KPoD0#QQ0IP=PEPHP=%KUR_PbPbPmPcPoPoPsPdPeG6RX#ARW1bC?R>9OCcR\%EXRXPoD0P@PDPUP9PbD4R}PWP\PXPoD0n0100000020000RXP;n0110700015010;10910:10810<P=PEPXP<n0110700015010;10910:10810<P=PDPXP:n0110700015010;10910:10810<P=PBPXP1n0110700015010;10910:10810<PHPD%KJRXQ0H1ZbJn0100000020000,3DD0#PX1D5NCn0100000020001PeO2P2P=PGP^PIP=PEP1P;n0110700015010;10910:10810<S0LP=PEP1P<n0110700015010;10910:10810<S0MP=PDP1P:n0110700015010;10910:10810<S0NPoP=%JDP1P9n0110700015010;10910:10810<S0OP=PBP1P1n0110700015010;10910:10810<S0PP9PcG6S0Q=C]un200110M00012010710ARWPiPjn10110M00031010K0000PxPyPzn10110J00031010K0000PHPEP9PcPln0100000020000PmPnPoPrPsPePTG=516X0HPLPRP0P]P6P0PkP^P|PHPt2079R#[PcPmPdPsPoD0#QP=PEPHP=P_PbPmP\PsPoD0S0RP}PmP\PsPoD0n0100000020000R}P;n0110700015010;10910:10810<P=PEP}P<n0110700015010;10910:10810<P=PDP}P:n0110700015010;10910:10810<P=PBP}P1n0110700015010;10910:10810<1BbJR},3DRRD0#PX1D9NCqn0100000020001PeO2PWPiPjn10110M00031010K0000PxPyPzn10110J00031010K0000PHPEPXPcPln0100000020000PmPnPoPrPsPePTG=Rl516X5LPSPcPT1BdKR|P[CtS0SP0P]P6P0PkP^P8PFPwP9PhPhPhPGP=PEPHP=P_Q0RP@PDPUA<CCYPbD4PmP\PsPoD0n0100000020000RYP;n0110700015010;10910:10810<P=PEPYP<n0110700015010;10910:10810<P=PDPYP:n0110700015010;10910:10810<P=PBPYP1n0110700015010;10910:10810<PRD0PdPfD2RYPZAFD}[S0TPhPYC9H0:,?kP{n10110M00021110400PWPiPjn10110M00031010K0000PxPyPzn10110J00031010K0000=16lX3SRWPS13FOPWPDP5P0P]P6P2P=PGP^PhPhPhPhPGP=PEPHP=PXPcPmAOCd>RWPsPoD0S0UP@PDPJA<CC9PcD4PmPWPsPoD0n0100000020000RSP;n0110700015010;10910:10810<P=PEPSP<n0110700015010;10910:10810<P=PDPSP:n0110700015010;10910:10810<P=PBPSP1n0110700015010;10910:10810<PrD0PePfD2RSPZAFDq[RqPhPSG;P]Q0LQ0MQ0NPoQ0OQ0PP9PdG6RSPhPhPhPhPGP=PEPHP=%KQS0VPaPmAOCb>S0WPsPoD0S0XP@PDPQA<CC:PaD4PmQ0WPsPoD0n0100000020000RYP;n0110700015010;10910:10810<P=PEPYP<n0110700015010;10910:10810<P=PDPYP:n0110700015010;10910:10810<P=PBPYP1n0110700015010;10910:10810<1BaURY,3DR}D0PcPfD2R~PZAFDY[RYPhP~C9F>n200110M00012110710APxPyPzn10110J00031010K0000=16lX0DPDP5P0P]P6P2P=PGP^PhPhPhPhPGP=PEPHP=PXQ0UP@PDPJP9PcD4S0UPmPWPsPoD0n0100000020000R~P;n0110700015010;10910:10810<P=PEP~P<n0110700015010;10910:10810<P=PDP~P:n0110700015010;10910:10810<P=PBP~P1n0110700015010;10910:10810<PrD0S0YPePfD2R~PZPqPhP~G;P]PSPhPhPhPhPGP=PEPHP=Q0VQ0XP@PDPQP:PaD4PmQ0WPsPoD0n0100000020000R~P;n0110700015010;10910:10810<P=PEP~P<n0110700015010;10910:10810<P=PDP~P:n0110700015010;10910:10810<P=PBP~P1n0110700015010;10910:10810<P}D0PcPfD2R~PZPYPhP~C9F>n200110M00012110710APxPyPzn10110J00031010K0000=16lX0DPD1Le?R~P0P]P6P2P=PGP^PhPhPhPhPGP=PEPHP=PXPcPmP9PsPoD0P@PDPJPOPcD4S0WPmP9PsPoD0n0100000020000S0XP;n0110700015010;10910:10810<P=PEQ0XP<n0110700015010;10910:10810<P=PDQ0XP:n0110700015010;10910:10810<P=PBQ0XP1n0110700015010;10910:10810<PrD0PePfD2S0XPZPqPhQ0XG;P]PSPhPhPhPhPGP=PEPHP=Q0VPaPmP:PsPoD0P@PDPQPpPaD4S0VPmP:PsPoD0n0100000020000S0XP;n0110700015010;10910:10810<P=PEQ0XP<n0110700015010;10910:10810<P=PDQ0XP:n0110700015010;10910:10810<P=PBQ0XP1n0110700015010;10910:10810<P}D0PcPfD2S0XPZPYPhQ0XC9F>n200110M00012110710APxPyPzn10110J00031010K0000=16lX0DPNPHPHP0P]P6P2P=PGP^PhPhPhPhPGP=PEPHP=P9PbPm1Lc?S0XPsPoD0S0ZP@PDPUPKPbD4S0[PmQ0XPsPoD0S0\n0100000020000RlP;n0110700015010;10910:10810<P=PEPlP<n0110700015010;10910:10810<P=PDPlP:n0110700015010;10910:10810<P=PBPlP1n0110700015010;10910:10810<PRD0PdPfD2RlPZQ0TPhPlG;P]Q0QPhPhPhPhPGP=PEPHP=P:PAPm1La?RlPsPoD0P@PDPVPJPAD4PmPlPsPoD0n0100000020000RlP;n0110700015010;10910:10810<P=PEPlP<n0110700015010;10910:10810<P=PDPlP:n0110700015010;10910:10810<P=PBPlP1n0110700015010;10910:10810<1BAQRl,3DD0PbPfD2RJPZAFDl[PhPJC9F>n200110M00012110710APxPyPzn10110J00031010K0000PHPEP9PbQ0[n0100000020000PmQ0XPoPRPsPdPeG=516P9PcPmPnPoPrPsPePTG=RJ,m6P0P]P6P2P=PGP^PhPhPhPhPGPcPmPnPsPrD0PePfD2RlPZPqPhPlG;P]PSPhPhPhPhPGPaPm1Lb?R?PsP}D0PcPfD2RlPZPYPhPlC9F>n200110M00012110710APxPyPzn10110J00031010K0000=16JeQ0WPmPnPoPrPsPePTG=RJ,m6P0P]P6P2P=PGP^PhPhPhPhPGQ0WPmPnPsPrD0PePfD2RrPZPqPhPrG;P]PSPhPhPhPhPGQ0VPmP?PsP}D0PcPfD2R}PZPYPhP}C9F>n200110M00012110710APxPyPzn10110J00031010K0000=16Jen0110001020101b0P0P]P6P2P=PGP^PhPhPhPhPGP=PEPHP=PNPdPmP~PsPoD0P@PDPpP5PdD4PmP~PsPoD0n0100000020000RJP;n0110700015010;10910:10810<P=PEPJP<n0110700015010;10910:10810<P=PDPJP:n0110700015010;10910:10810<P=PBPJP1n0110700015010;10910:10810<13D|RJD0PTPfD2R}PZAFD|[RYPhP}G;P]Q0LQ0MQ0NPoQ0OQ0PP9PeG6R}PhPhPhPhPGP=PEPHP=P_Q0ZQ0\n0100000020000R?P;n0110700015010;10910:10810<P=PEP?P<n0110700015010;10910:10810<P=PDP?P:n0110700015010;10910:10810<P=PBP?P1n0110700015010;10910:10810<PRD0PdPfD2R?PZQ0TPhP?C9F>n200110M00012110710APxPyPzn10110J00031010K0000PHPEPNPdAxdp5R?n0100000020000PmP~PoPJPsPTPVG=Rr516eAOCe>Rq&04eE5Q04P9E5%dORnB03O51E5P0P]P6P2P=PGP^PhPhPhPhPGP=PEPHP=PNPdPmPqPsPoD0P@PDPpA<CCnPdD4PmPqPsPoD0n0100000020000RqP;n0110700015010;10910:10810<P=PEPqP<n0110700015010;10910:10810<P=PDPqP:n0110700015010;10910:10810<P=PBPqP1n0110700015010;10910:10810<PJD0PTPfD2RqPZPYPhPqG;P]P}PhPhPhPhPGP=PEPHP=P_Q0RP@PDPU%dp9<CCPbD4PmP\PsPoD0n0100000020000R\P;n0110700015010;10910:10810<P=PEP\P<n0110700015010;10910:10810<P=PDP\P:n0110700015010;10910:10810<P=PBP\P1n0110700015010;10910:10810<PRD0PdPfD2RfPZQ0TPhPfC9F>n200110M00012110710APxPyPzn10110J00031010K0000=16reQ0SP:E5PcPTP|P[C\PcPTP[P|H02E5P0P]P6P0PkP^Q0APtPwP1Q0BPvP{PvP{P{P8PFPwQ0>P<P1Q0DC\Q0EP{n10110M00021110400PHPwQ0CP;P:Q0FCkQ0GP{n0100000020100n0110200081010710107101071010710107101073110310610@4110310610110@X2GX4tp?100010>R{PHPtQ01PdPmPePsPoD0#QQ0Y#PX1D9NC|n0100000020001PTO2P2P=PGP^PIAC]Sun200110M00012010710ARSPiPjn10110M00031010K0000PxPyPzn10110J00031010K0000=16re17C|Q03'vP<E5P0P]P6P0PkP^P{PHPtPHPD%KKQ0H1ZdKn0100000020000RK,nP#[PdPdPmPePoPoPsPTPVG6RP#APe%EPPoD0#QP=PEPHP=PXPcQ0JPWQ0KPoD0Q0UQ0JPWQ0KPoD0n0100000020000RWP;n0110700015010;10910:10810<P=PEPWP<n0110700015010;10910:10810<P=PDPWP:n0110700015010;10910:10810<P=PBPWP1n0110700015010;10910:10810<Q0I,3DD0#PX1D9NCKn0100000020001PTO2PSPiPjn10110M00031010K0000PxPyPzn10110J00031010K0000=16reQ069z@pR@&01pE5P0P]P6P0PkP^Q0@P`PdPePTPVD@Rp#T%Ap%Vp%Ep%SpD05a>%UpR>5]cP2P=PGP^PIQ09Q0:Q0;PoQ0<Q0=P9P`PaPbPcPdD@Rr#RG6=C]un200110M00012010710APiPjn10110M00031010K0000PxPyPzn10110J00031010K0000PHPEP@PdP?n0100000020000R?PmP~PoPJPsPTPVG=Rs516e%XQRJP;E5P0P]P6P8PMP^PJP2Q02PLP^P9P0PkP^Q08%Tr%Ar%Vr%Er%SrD07a1%Ur5]AP2P=PGP^PIQ09Q0:Q0;PoQ0<Q0=P9P`Q0?Q07PAPaD@#RG6=C]un200110M00012010710APiPjn10110M00031010K0000n200110B00012010=10?PHP^%qQPiPjn0100000020000n10110M00021110B00PxPyPzn10110J00031010K0000=16se%yQP3E5A`cpQ,f7=16sRQePQe1_ceP4E5P8PBP^&0BpR4,_cA`bg9RgP8PBP^Alc>4PgP8PBP^Ajc>4PgP0P7P^Aic>4Q05PiPjn10110M00031010L0000n10110M00021010500n10110M00021010500n10110M00021010500,f7=16se20CcpRp=16seP`P?P~PTPVP|J00#u916peb@W?W>W:W;W<W=X1DWBWIWEXGHWAWKXHGWCXDDWFWJo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_sc_w_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc AW aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 4 = 0)%Z ->
  r = getr regs rs1 ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 4%nat = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
                  (wbytes mem (getr regs rs1) (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "p'0h01bi001bh11mh21oh31ti011th41ri021rh53Halh67Hdecodeh76Hecallh86Hfetchh93Hokh:2Hrh;2aqh<1lh=3memh>2pch?2rdh@4regshA2rlhB3romhC3rs1hD3rs2hE4segshF1wi031whG1zi041ai052bsi061ci076c_fcsri087c_fregsi094c_pci0:6c_regsi0;6c_resvi0<1ii0=Cinterp_eff_accessesi0>3iszi0?1ki0@2m'i0A1ni0B2oki0C1pi0D2p0i0E2p1i0F2p2i0G2p3i0H2p4i0I2p5i0J2p6i0K6reporti0L3st'i0M1vi0N1xp%0p&0p;1p;2p;3p;6p;4p;8p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0g006GR0p4p710R6p8p1006ep4p710R7P3p8P7P6p8p1007Bp4p70R8P1p8P8p10080p4p7210p8P8P3p8P8p1008Lp4p710R1p8P8P7p8P8P4p8P8P5p8P8p1009Bp4p710R7p8P8P6p8P8p1009cp4p710p8P8p100:@p4p710p8P8p100;9p6051001R9p8P8p100<<p4p7210p8P8p100<Yp4p710p8g00=6R8p4p7210R:P3p8P:P4p8P:P5p8P:P6p8P:g00=bR:p4p710p8P2P6p8P9P3p8P9P1p8P9P4p8P9P5p8P9P7p8P9P6p8P9p100>ip4p710p8p100?Kp60521000R9p100@Up4p710R7p8p100APp6051000R1P7p8p100BVp6051000R2P7p8p100CZp4p70R7P3p8P7P4p8P7P5p8P7P6p8p100DPp4p7511110R6P9p8P6P1p8P6P2p8g00I_j1yTg00EQj1DTg00F6j1sTg00F[j1MTg00G9j1^TP8k20CTg00G\R8j1VTg00J?j2jTg00KAj26Tg00Kcj31Tg00L=j1vTg00M=R2j2cTg00M]j1_Tg01\Oj6}Tg00O:j1kTg00OXj4]Tg00P8j24Tg00Pjj25Tg00QTj2xTg00R4j1>Tg019ij4UTg00TAR6j1fTP:j1qTg00bEk108Tg00H>k106Tg00cnk105Tg00k\j82Tg00V;j3dTg00WGj1TTg00XEj3wTg00YJj3{Tg00ZPj3nTg00[Uj1~Tg00\5j1bTg00]=j1aTg00^Ej2`Tg00_Oj3mTg00`2j3lTg00lcj2LTg00aQj3|Tg00c:j2KTg01];j2JTg01^Cj3?Tg00UIj5zTg00dbj1\Tg00eaj1[Tg00faj1PTg00gbk20BTg00h`j1ZTg00i_j1YTg00j^j1XTg00mIj50Tg00n2j3iTg00nYj3hTg00odj27Tg010hk10ATg011Qk10@Tg012;k10?Tg012bk10>Tg013Kk10=Tg0144j2ITg015;j1uTg0164j1ETg016\j2ATg017dj4rTg018ik10:Tg01KBk409Tg01:ij2STg01;fj3NTg01<jj2WTg01=Tj2pTg01>Bj1eTg01>`j1RTg01BXj2CTg01_>j1HTg01?Hj3QTg01@Xj5BTg01AHj1=Tg01_fj4OTg00H`j2oTg01C5k104TP0j68Tg01`Nk103Tg01aTk302Tg01b\k10;Tg01FJk10<Tg01GEk101Tg01HBj2tTg01I>k600Tg01J;j3GTg01Kkj3gTf2R0g01LKR:f1R1f0R93G'Ap=@1A:9p=:f4R7g01MRR5f3R4P0P1C];G9p=3P0g01NYR3P1P9C]p=FAg0199G74p>07f6R;f5R</771I199g403Gp=91I199g40p=;1701=G49,I79G:<,A;p=<g01O8#yg00I:S00#DR=#s#MR>%D=R=#DR?#D#DR@#D#MRA#^RB+0CRC%M?#^RD#V\BRE%M@R@#^RFg01P7RG%^>S01Q01Q01%VFRHf;RIf9RJ'j16F;31f7RK#vg01PWS0251Gg01Q7S03g01QcRL'cRM#VRNf8RO#_Q03PLg01RARPPKP;P<P7P4E}%k=R=C],6M31f=RQ/4<,5A/x=g01RnRR51Lf>RS/4;91B7f@RTPQf?RU/4Kg01SLRV#>RW#>RX#>#>RYCUg01c>S0451GPHf<RZ,6F%f:R[P8PF%q:R\#fR]P9fCR^fBR_p,2fxR`$08RafARb&06BRc16BO&05`RdPTPUG2;d9ReP8PFP]PbPaPTPc16BKRfPdPUPSG2Rg#TRh=w_TPeP8PFP]A{_hTPeP6P:P]An_hTg01Sk#~Re9@\9S05%b\Ri%a\Rjn10110N00031010L0000n10110N00021010300n10110N00021010300n10110N00021010301,`:P`PGPCf:Rkg01U0Rl9m>RS065l>Pb1LARRm9|bkS07n01000000200001KT=Rn14bJRo14bORp,JY5?URqPSDz#:Rr31X2HPGQ02P6P\P[PGP]P9%\g%[gRH%Pg%s?#k=m>l-0Bg,6B%Zg%YgRlPh%XgG2=@\eP8PMP]%_QP2Q03PLP]P9P61c5ERh#qR?P]fES081LA9S09fDRsPaP^Pc16BkPdP_PbG2Rt#\%[t%Pt%Yt%ZtD07i1%Tt3hP2P5PEP]17h9Rt&0A1S0:&0@1S0;&0?1S0<Pc&0>1S0=&0=1S0>P9fGS0?PafFS0@Pc16BQPdQ08PsG2#XG21Ih0Ru5@\n200110N00012010610@PiPjn10110N00031010K0000n200110C00012110<10>RvPGP]%uQPiPjn0100000020000Rwn10110N00021110C00n010000002010117:9#:Rx%b:Ry%a:Rzn10110200031010K0000=1[rX0GPNQ03PLPPPIPkPJPOPKE}S0AP=C],6MP6P\P[P8PMP]P9PvPwn10110N00021110C00PxPyPzn10110200031010K0000=1[rX2NPG%EJRNP6P\P[P6P?P]g01ULRr%f?Rw^1E]3S0BPrPwP1PhPEP9P1PeD3,A?S0C%a?Rv%b?R{PvP{P{P8%yDRDPwfHS0DP4P1g01V4R|P3P0PVg01VRR}P3P9PVP}P3P9PVP}P3P9PVP}P3P9PVP}P3P9PVP}P3P9PVP}P3P9PVPV%>Y#>#>#>n0110I00031010J1010J00PYn0110H00031010I1010I00PXn0110G00031010H1010H00PWn0110F00031010G1010G00PVn0110E00031010F1010F00PVn0110D00031010E1010E00PVn0110C00031010D1010D00RWn0110A0002001010CS0ECrP6P?PwP;P1PAg01N;P4&0:9H09O1P7O2PhPt1cB3RXP|P3P7PVPWn0110A0002001010C9FB41Ih9I07,A?R}P{Pvn10110N00031010K0000S0FP{n10110N00021110500PGPwfIP7P0P|P3P4PVPWn0110A0002001010CS0GCUP6P?PwP;P9Q0G1541'S9N70O2P}P{Pvn10110N00031010K0000S0HP{n0100000020100n0110100081010610106101061010610106101063110A10410?4110A10410M10?X1EX3rp?100010=R}PGPrPGPBPNPm1WbJn0100000020000RW,pP#ePbPHPTPlPfD0#RPGPr15AKRV15AW'CP@PWPGPB%EOS0IPm1WbOn0100000020000#HPGP5%EkRWPbPH1LA=R39QATR|PlPcD0S0JP>PBPkPmPbDBR~PHP|PlPcD0n0100000020000#=COPGP5PWQ0JP>PBPkQ00#k,LAS00PbDBS0JPHP|PlPcD0n0100000020000#=n0110B00020101n0100000020001PUO2P2P5PEP]PtP5PCP1P7n0110600015010:10810910710;S0KP5PCP1P4n0110600015010:10810910710;S0LP5PBP1P0n0110600015010:10810910710;S0MPcP5%VBP1P9n0110600015010:10810910710;S0NP5PFP1P1n0110600015010:10810910710;S0OP9PbG2S0P=@\un200110N00012010610@RlPiPjn10110N00031010K0000PxPyPzn10110200031010K0000PGPCP9PbQ07n0100000020000PaPnPcPcPdPqPSG2#:51[X0GPLPRP6P\P[P6P?P]P}PGPr1C9R#ePbPaPTPdPfD0#RPGPr15AoRf,CVP@Po%HpRpPGP5PWPbPaP|PdPcD0RVP~PaP|PdPcD0n0100000020000S0Q#=CORRPGP5PWPVQ0JPaP|PdPcD0n0100000020000#=R|n0110B00020000n0100000020001PUO2PlPiPjn10110N00031010K0000PxPyPzn10110200031010K0000PGPCPWPbQ07n0100000020000PaPnPcPcPdPqPSG2#:RV51[XGLPB14TORHP6P\P[P6P?P]P}PGPr15A9/CfPRP|n0110B00020000PUO2PlPiPjn10110N00031010K0000PxPyPzn10110200031010K0000=1[VX4BPGQ04P6P\P[P6P?P]P}PGPrP9PRP|n0110B00020000PUO2PlPiPjn10110N00031010K0000PxPyPzn10110200031010K0000=1[VX0GPGQ04P6P\P[P6P?P]PGPwP9PhPhPhPEQ0Q15@p,SY9NUoPeD3RpPXAFBoYR|PhPpF9,A?P{n0100000020100PlPiPjn10110N00031010K0000PxPyPzn10110200031010K0000=1[VX0GPE14TKRl#HS04,5@,SYRp9?SHP6P\P[P2P5PEP]PhPhPhPEQ0QP9PeD3RRPXP|PhPRF9,7hP\Q0KQ0LQ0MPcQ0NQ0OP9PTG2RRPhPhPhPhPEPGP5%EZS07P^PaAQA_3R}PdPcD0P>PBPZPmP^DBS0JPaP}PdPcD0n0100000020000S0RP0PeD3S0SPX14^IR}=FBYRfPhQ0SC;F<n200110N00012110610@PxPyPzn10110200031010K0000=1[VX2EPD1JYlS0SP6P\P[P2P5PEP]PhPhPhPEQ0QA?Uo9PeD3RoPXP|PhPoF9,7hP\PRPhPhPhPhPEQ0RA?b}0PeD3RoPXPfPhPoC;F<n200110N00012110610@PxPyPzn10110200031010K0000=1[VX<DPB1KU=RoP6P\P[P2P5PEP]PhPhPhPEPGP5PWPbPaP9PdPcD0P~PaP9PdPcD0n0100000020000PqPeD3RWPXP|PhPWF9,7hP\PRPhPhPhPhPEPGP5Q07P^PaP0PdPcD0Q0JPaP0PdPcD0n010000002000014^k,JY9?b}R}PeD3RWPXPfPhPWC;F<n200110N00012110610@PxPyPzn10110200031010K0000=1[VX0BPNPGPGP6P\P[P2P5PEP]PhPhPhPEPGP5P9P_Pa1Kb=RVPdPcD0S07P>PBPIPmP_DBS0RPaPVPdPcD0S0Qn010000002000014_kRk14_JS0T,JY5?TS0UPeD3RWPXAFBkYS0VPhPWF9,7hP\Q0PPhPhPhPhPEPGP5P0PsPa1K^=RWPdPcD0P>PBPQPmPsDBPaPWPdPcD0n010000002000014sZRW14sI,JY5?_PeD3S0PPXAFBWYPhQ0PC;F<n200110N00012110610@PxPyPzn10110200031010K0000PGPCP9P_Q0Rn0100000020000PaPVPcPcPdQ0UPUG2#:51[P9PbPaPnPcPcPdPqPSG2#:RV,o[P6P\P[P2P5PEP]PhPhPhPEPbPaPnPdPcD0PqPeD3RWPXP|PhPWF9,7hP\PRPhPhPhPhPEP^Pa1K_=S0PPdPcD0P}PeD3RWPXPfPhPWC;F<n200110N00012110610@PxPyPzn10110200031010K0000=1[VeP~PaPnPcPcPdPqPSG2#:RV,o[P6P\P[P2P5PEP]PhPhPhPEP~PaPnPdPcD0PqPeD3RqPXP|PhPqF9,7hP\PRPhPhPhPhPEQ0JPaQ0PPdPcD0P}PeD3R}PXPfPhP}C;F<n200110N00012110610@PxPyPzn10110200031010K0000=1[Ven0110001020101b0P6P\P[P2P5PEP]PhPhPhPEPGP5PNPTPaPoPdPcD0P>PBPJPmPTDBRVPaPoPdPcD0n0100000020000Q0S9?SHR}PeD3RfPXAFBHYRqPhPfF9,7hP\Q0KQ0LQ0MPcQ0NQ0OP9PUG2RfPhPhPhPhPEPGP5%EIRIQ07Q0Qn0100000020000Q0UPeD3R|PXQ0VPhP|C;F<n200110N00012110610@PxPyPzn10110200031010K0000PGPCPNPTA|TJmR|n0100000020000PaPoPcPcPdP}PQG2#:Rn51[eAQAU3R~&04UE8Pp&03lE8ANSHpRlB02pSHE8P6P\P[P2P5PEP]PhPhPhPEPGP5PNPTPaP~PdPcD0RpPVPaP~PdPcD0n0100000020000RWPlPeD3RlPXPqPhPlF9Rl,7hP\PfPhPhPhPhPEPGP5PIP_PaAQAb3RIPdPcD0Q0RPaPIPdPcD0n0100000020000Q0T#H,5@,SY9NTkPeD3RePXQ0VPhPeC;F<n200110N00012110610@PxPyPzn10110200031010K0000=1[nePbPSPHPYCURYP9E8P6P\P[P6P?P]PGPwPY1A?lP{n0100000020100P2P5PEP]PtA@\Run200110N00012010610@RRPiPjn10110N00031010K0000PxPyPzn10110200031010K0000=1[ne15AHRl/Cl&0;lE8P;P1E8P6P\P[P6P?P]Q0BPrPwP1Q0CPvP{PvP{P{P8PDPwQ0?P4P1Q0ECrQ0FP{n10110N00021110500PGPwQ0DP7P0Q0GCUQ0HP{n0100000020100n0110100081010610106101061010610106101063110A10410?4110A10410M10?X1EX3rp?100010=R{PGPrQ02PTPaPUPd16B;RwD0#RPGPr15A;RD/ClP@PHQ04%=WCOPGP5PNPpP>PBPJQ00PTDBRpPaP~PdPcD0n0100000020000#=n0110B00020000n0100000020001PSO2PRPiPjn10110N00031010K0000PxPyPzn10110200031010K0000=1[ne1xl=P0E8P6P\P[P6P?P]P{PGPrPGPBQ0IPm1WTOn0100000020000RO,pP#ePTPTPaPUPcPwPdPSPQG2RP#[R{PU%YPR0PwD0#RPGPr15AO,CDP@POPGPB%EKPm1WTKn0100000020000#HPGP5PNPTP{P~P0PcD0RKPVP{P~P0PcD0n0100000020000#=COPGP5PNPKPpP{P~P0PcD0n0100000020000#=n0110B00020101n0100000020001PSO2PRPiPjn10110N00031010K0000PxPyPzn10110200031010K0000=1[neQ069l>JR>&0<JE8P6P\P[P6P?P]Q0A%\PP{%PPP0%ZPD05i3%TPR35hbP2P5PEP]PtQ0:Q0;Q0<PcQ0=Q0>P9P^PaP_Pc16BJPdPbPTG2RJ#XG2=@\un200110N00012010610@PiPjn10110N00031010K0000PxPyPzn10110200031010K0000P`PGPCP>PTP|n0100000020000PoP}PQDz#:R}51[e%_ZRoP4E8P6P\P[P8PMP]PoP2Q03PLP]P9P6P?P]Q09%\J%[J%PJ%YJ%ZJD07i1%TJ5hsP2P5PEP]PtQ0:Q0;Q0<PcQ0=Q0>P9Q0@PaQ08Pc16BZPdPsP^G2#XG2=@\un200110N00012010610@PiPjn10110N00031010K0000n200110C00012110<10>PGP]%uZPiPjn0100000020000n10110N00021110C00PxPyPzn10110200031010K0000=1[}e%vZP7E8AdbPZ,`:=1[}RZePZe1jbUP<E8P8PFP]&01PR<,jbAd_g9RgP8PFP]Awb3<PgP8PFP]A{b3<PgP6P:P]Anb3<Q05PiPjn10110N00031010L0000n10110N00021010300n10110N00021010301n10110N00021010301,`:=1[}e1tbP=1[}eP`PTPUPSPQP;J00,tb=1[}eW9W:W5W6W7W8X4BWDWCW?XAGW;WFXBEW=X>BW@WEo"). Qed.

(* [comment removed for export] *)
Lemma step_sc_d_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc AD aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod 8 = 0)%Z ->
  r = getr regs rs1 ->
  RiscvSemantics.store_ok segs mem (getr regs rs1) 8%nat = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
                  (wbytes mem (getr regs rs1) (word_to_le_bytes 8 (getr regs rs2))) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "p'0h01bi001bh11mh21oh31ti011th41ri021rh53Halh67Hdecodeh76Hecallh86Hfetchh93Hokh:2Hrh;2aqh<3memh=2pch>2rdh?4regsh@2rlhA3romhB3rs1hC3rs2hD4segshE1wi031whF1zi041ai052bsi061ci076c_fcsri087c_fregsi094c_pci0:6c_regsi0;6c_resvi0<1ii0=Cinterp_eff_accessesi0>3iszi0?1ki0@2m'i0A1ni0B2oki0C1pi0D2p0i0E2p1i0F2p2i0G2p3i0H2p4i0I2p5i0J2p6i0K6reporti0L3st'i0M1vi0N1xp%0p&0p;1p;2p;3p;6p;4p;8p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0g006GR0p4p710R6p8p1006ep4p710R7P3p8P7P6p8p1007Bp4p70R8P1p8P8p10080p4p7210p8P8P3p8P8p1008Lp4p710R1p8P8P7p8P8P4p8P8P5p8P8p1009Bp4p710R7p8P8P6p8P8p1009cp4p710p8P8p100:@p4p710p8P8p100;9p6051001R9p8P8p100<<p4p7210p8P8p100<Yp4p710p8g00=6R8p4p7210R:P3p8P:P4p8P:P5p8P:P6p8P:g00=bR:p4p710p8P2P6p8P9P3p8P9P1p8P9P4p8P9P5p8P9P7p8P9P6p8P9p100>ip4p710p8p100?Kp60521000R9p100@Up4p710R7p8p100APp6051000R1P7p8p100BVp6051000R2P7p8p100CZp4p70R7P3p8P7P4p8P7P5p8P7P6p8p100DPp4p7511110R6P9p8P6P1p8P6P2p8g00I_j1vTg00EQj1DTg00F6j1pTg00F[j1HTg00G9j1[TP8k20?Tg00G\R8j1PTg00J?j2cTg00KAj28Tg00Kcj31Tg00L=j1iTg00M=R2j2`Tg00M]j1\Tg01\Oj6zTg00O:j1YTg00OXj4WTg00P8j27Tg00Pjj26Tg00QTj2uTg00R4j1=Tg019ij4OTg00TAR6j1bTP:j1nTg00bEk104Tg00H>k102Tg00cnk101Tg00k\j82Tg00V;j3fTg00WGj1NTg00XEj3sTg00YJj3tTg00ZPj3kTg00[Uj1{Tg00\5j1_Tg00]=j1^Tg00^Ej2]Tg00_Oj3hTg00`2j3gTg00lcj2STg00aQj3yTg00c:j2GTg01];j2xTg01^Cj3ATg00UIj5wTg00dbj1RTg00eaj1QTg00faj1ITg00gbk20>Tg00h`j1VTg00i_j1UTg00j^j1TTg00mIj50Tg00n2j3eTg00nYj3dTg00odj2:Tg010hk10=Tg011Qk10<Tg012;k10;Tg012bk10:Tg013Kk109Tg0144j29Tg015;j1rTg0164j1CTg016\j2FTg017dj4oTg018ik106Tg01KBk405Tg01:ij2ETg01;fj3ZTg01<jj2XTg01=Tj2mTg01>Bj1aTg01>`j1MTg01BXj2@Tg01?Hj3LTg01@Xj5?Tg01AHj1>Tg01_fj4KTg00H`j2lTg01C5k100TP0j6;Tg01aTj3~Tg01b\j1}Tg01FJk107Tg01GEk108Tg01HBj2qTg01I>j6|Tg01J;j3JTg01Kkj3jTf2R0g01LKR:f1R1f0R93J'Fp=51F:9p=<f4R7g01MRR5f3R4P0P1CW;J9p=3P0g01NYR3P1P9CWp=BAj0199J74p>03f6R;f5R</:719199j403Jp=4g01O8#vg00I:S00#DR=#p#HR>%D=R=#DR?#D#DR@#D#HRA#[RB+0?RC%H?#[RD#P\BRE%H@#[R@g01P7RF%[>RG%P@RHf;RIf9RJ'c18@;31f7RK#ig01PWS0151Fg01Q7RLg01QcRM'`RN#PROf8RP#\PLPMg01[GRQPKP;P<P7P4Ez%Y=R=CW,8N31f=RR/7<,6A%Y?S02'ug01RnRS51Mf>RT/7;91B7f@RUPRf?RV/7Kg01SLRW#=RX#=RY#=#=RZ#=#=#=#=R[COg01c>S0351FPHf<R\,8@%b:R]P8P@%n:R^#bR_P9fCR`fBRap,2fxRb$04RcfARd&02BRe18BP&01bRfPUPVG2;f9RgP8P@P_PdPcPUPe18BKS04PfPVPTG2Rh#NRi=saUPgP8P@P_AtaiUPgP6P:P_AkaiUg01Sk#{Rg95^9S05%_^Rj%^^Rkn10110N00031010L0000n10110N00021010300n10110N00021010300n10110N00021010301,]:PbPFPCf:Rlg01U0Rm9h>SS065g>Pd1SASRn9ydlS07n01000000200001GU=Ro17dJRp17dPRq,x[5AVRrPTDw#<Rs31X2HPFQ01P6P^P]PFP_P9%Rh%QhRH%Ih%p?#Y=h>m-0>h,8B%Vh%UhRmPi%ThG2=5^gP8PNP_%\RP2PLPMP_P9P61`5ERi#nR?P_fES081SA9S09fDRtPcP`Pe18BlPfPaPdG2Ru#R%Qu%Iu%Uu%VuD07e1%Nu3dP2P5PEP_1:i9Ru&0=1S0:&0<1S0;&0;1S0<Pe&0:1S0=&091S0>P9fGS0?PcfFS0@Pe18BRPfQ08PtG2#TG219i0Rv55^n200110N00012010610@PjPkn10110N00031010K0000n200110C00012110<10>RwPFP_%rRPjPkn0100000020000Rxn10110N00021110C00n01000000201011::9#<Ry%_:Rz%^:R{n10110200031010K0000=1]sX0FPOPLPMPQPIPlPJPPPKEzS0AP=CW,8NP6P^P]P8PNP_P9PwPxn10110N00021110C00PyPzP{n10110200031010K0000=1]sX2OPF%CJROP6P^P]P6P?P_g01ULRs%b?Rx^1E]3S0BPsPxP1PiPEP9P1PgD3,F?S0C%^?Rw%_?R|PwP|P|P8%vDS0DPxfHS0EP4P1g01V4RDP3P0PWg01VRR}P3P9PWP}P3P9PWP}P3P9PWP}P3P9PWP}P3P9PWP}P3P9PWP}P3P9PWPWP[n0110I00031010J1010J00PZn0110H00031010I1010I00PYn0110G00031010H1010H00PXn0110F00031010G1010G00PWn0110E00031010F1010F00PWn0110D00031010E1010E00PWn0110C00031010D1010D00RXn0110A0002001010CS0FCoP6P?PxP;P1PAg01N;P4&069H05O1P7O2PiPu1`B3RYPDP3P7PWPXn0110A0002001010C9BB419i9I03,F?RZP|Pwn10110N00031010K0000S0GP|n10110N00021110500PFPxfIP7P0PDP3P4PWPXn0110A0002001010CRXCOP6P?PxP;P91641,EX9Z70O2PZP|Pwn10110N00031010K0000S0HP|n0100000020100n0110100081010610106101061010610106101063110A10410?4110A10410M10?X1EX3sp?100010=RZPFPsPFPBPOPn1XdJn0100000020000RW,mQ#aPdPHPUPmQ04D0#MPFPs16AKR316AW'@PAPWPFPB%CPS0IPn1XdPn0100000020000PFP5%ClRWPdPH1SA=RD9LAUR}PmPeD0S0JP>PBPlPnPdD?R~PHP}PmPeD0n0100000020000#>CKPFP5PWQ0JP>PBPlQ00#Y,SAS00PdD?S0JPHP}PmPeD0n0100000020000#>n0110B00020101n0100000020001PVO2P2P5PEP_PuP5PCP1P7n0110600015010:10810910710;S0KP5PCP1P4n0110600015010:10810910710;S0LP5PBP1P0n0110600015010:10810910710;S0MPeP5%PBP1P9n0110600015010:10810910710;S0NP5P@P1P1n0110600015010:10810910710;S0OP9PdG2S0P=5^vn200110N00012010610@RmPjPkn10110N00031010K0000PyPzP{n10110200031010K0000PFPCP9PdQ07n0100000020000PcPoPePePfPrPTG2#<51]X0FPMPSP6P^P]P6P?P_PZPFPs1@9S#aPdPcPUPfQ04D0#MPFPs16ApRS,@3PAPpPqPFP5PWPdPcP}PfPeD0R3P~PcP}PfPeD0n0100000020000S04#>CKRHPFP5PWP3Q0JPcP}PfPeD0n0100000020000#>R}n0110B00020000n0100000020001PVO2PmPjPkn10110N00031010K0000PyPzP{n10110200031010K0000PFPCPWPdQ07n0100000020000PcPoPePePfPrPTG2#<Rr51]XFMPB17UPR3P6P^P]P6P?P_PZPFPs16A9/@SPHP}n0110B00020000PVO2PmPjPkn10110N00031010K0000PyPzP{n10110200031010K0000=1]rX4BPFQ03P6P^P]P6P?P_PZPFPsP9PHP}n0110B00020000PVO2PmPjPkn10110N00031010K0000PyPzP{n10110200031010K0000=1]rX0FPFQ03P6P^P]P6P?P_PFPxP9PiPiPiPEQ0416Aq,E[S039ZVpPgD3RqPYABBp[R}PiPqF4,F?P|n0100000020100PmPjPkn10110N00031010K0000PyPzP{n10110200031010K0000=1]rX0FPE17UKRm,6A,E[Rq9AT3S07P6P^P]P2P5PEP_PiPiPiPEQ04P9PgD3RHPYP}PiPHF4,:iQ0KQ0LQ0MPeQ0NQ0OP9PUG2RHPiPiPiPEPFP5%C\S04P`PcALAaDRZPfPeD0P>PBP\PnP`D?S0JPcPZPfPeD0n0100000020000P0PgD3RZPY17`IS0Q=BB[RSPiPZF4,9i55^n200110N00012110610@PyPzP{n10110200031010K0000=1]rX2EPB1GV=RZP6P^P]P2P5PEP_PiPiPiPEPFP5PWPdPcP9PfPeD0P~PcP9PfPeD0n0100000020000Q039AVpRpPgD3RWPYP}PiPWF4,:iPiPiPiPEPFP5Q04P`PcP0PfPeD0Q0JPcP0PfPeD0n0100000020000Q0Q17`l,6A,E[5AdS0QPgD3RWPYPSPiPWF4,9i95^Hn200110N00012110610@PyPzP{n10110200031010K0000=1]rX0BPOPFPFP6P^P]P2P5PEP_PiPiPiPEPFP5P9PaPc1Gd=RrPfPeD0S04P>PBPIPnPaD?S03PcPrPfPeD0S0Rn010000002000017alRl17aJ,6A,E[S0S5AUS0TPgD3RWPYABBl[S0UPiPWF4,:iQ0PPiPiPiPEPFP5P0PtPc1G`=RWPfPeD0P>PBPRPnPtD?PcPWPfPeD0n010000002000017t\RW17tI,6A,E[5AaPgD3S0VPYABBW[PiQ0VF4,9i55^n200110N00012110610@PyPzP{n10110200031010K0000PFPCP9PaQ03n0100000020000PcPrPePePfQ0TPVG2#<51]P9PdPcPoPePePfPpPTG2#<Rr,l]P6P^P]P2P5PEP_PiPiPiPEPdPcPoPfPeD0PpPgD3RWPYP}PiPWF4,:iPiPiPiPEP`Pc1Ga=R=PfPeD0Q0QPgD3RWPYPSPiPWF4,9i95^Hn200110N00012110610@PyPzP{n10110200031010K0000=1]reP~PcPoPePePfPpPTG2#<Rr,l]P6P^P]P2P5PEP_PiPiPiPEP~PcPoPfPeD0PpPgD3RpPYP}PiPpF4,:iPiPiPiPEQ0JPcP=PfPeD0Q0QPgD3R=PYPSPiP=F4,9i95^Hn200110N00012110610@PyPzP{n10110200031010K0000=1]ren0110001020101b0P6P^P]P2P5PEP_PiPiPiPEPFP5POPUPcPZPfPeD0P>PBPJPnPUD?RrPcPZPfPeD0n0100000020000Q07PgD3R=PYABB3[RSPiP=F4,:iQ0KQ0LQ0MPeQ0NQ0OP9PVG2R=PiPiPiPEPFP5%CIRIQ04Q0Rn0100000020000Q0TPgD3RpPYQ0UPiPpF4,9i55^n200110N00012110610@PyPzP{n10110200031010K0000PFPCPOPUAyUJnS0Tn0100000020000PcPZPePePf1x[m9AT3RpPRG2#<R}51]eALAVDRo&00VE;AZT3qR~A~qT3E;P6P^P]P2P5PEP_PiPiPiPEPFP5POPUPcPoPfPeD0RqPrPcPoPfPeD0n0100000020000RWP~PgD3R~PYPSPiP~F4R~,:iPiPiPiPEPFP5PIPaPcALAdDRIPfPeD0Q03PcPIPfPeD0n0100000020000Q0S9ZUlPgD3RgPYQ0UPiPgF4,9i95^=n200110N00012110610@PyPzP{n10110200031010K0000=1]}ePdPTP3P[COR[P9E;P6P^P]P6P?P_PFPxP[1F?~P|n0100000020100P2P5PEP_PuA5^Hvn200110N00012010610@RHPjPkn10110N00031010K0000PyPzP{n10110200031010K0000=1]}e16A3R~/@~%}~E;P;P1E;P6P^P]P6P?P_Q0BPsPxP1Q0CPwP|PwP|P|P8Q0DPxQ0?P4P1Q0FCoQ0GP|n10110N00021110500PFPxQ0EP7P0PXCOQ0HP|n0100000020100n0110100081010610106101061010610106101063110A10410?4110A10410M10?X1EX3sp?100010=R|PFPsQ01PUPcPVPf18B;RXD0#MPFPs16A;Rx/@~PAP3Pm%>WCKPFP5POPqP>PBPJQ00PUD?RqPcPoPfPeD0n0100000020000#>n0110B00020000n0100000020001PTO2PHPjPkn10110N00031010K0000PyPzP{n10110200031010K0000=1]}eQ02,u~P0E;P6P^P]P6P?P_P|PFPsPFPBQ0IPn1XUPn0100000020000RP,mQ#aPUPUPcPVPePXPfPTPRG2RQ#QR|PV%UQR0PXD0#MPFPs16AP,@xPAPPPFPB%CKPn1XUKn0100000020000PFP5POPUP|PoP0PeD0RKPrP|PoP0PeD0n0100000020000#>CKPFP5POPKPqP|PoP0PeD0n0100000020000#>n0110B00020101n0100000020001PTO2PHPjPkn10110N00031010K0000PyPzP{n10110200031010K0000=1]}eQ069g>JR>&07JE;P6P^P]P6P?P_Q0A%RQP|%IQP0%VQD05eD%NQRD5ddP2P5PEP_PuQ0:Q0;Q0<PeQ0=Q0>P9P`PcPaPe18BJPfPdPUG2RJ#TG2=5^vn200110N00012010610@PjPkn10110N00031010K0000PyPzP{n10110200031010K0000PbPFPCP>PUQ0Tn0100000020000PZPpPRDw#<Rp51]e%\\RZP4E;P6P^P]P8PNP_PZP2PLPMP_P9P6P?P_Q09%RJ%QJ%IJ%UJ%VJD07e1%NJ5dtP2P5PEP_PuQ0:Q0;Q0<PeQ0=Q0>P9Q0@PcQ08Pe18B\PfPtP`G2#TG2=5^vn200110N00012010610@PjPkn10110N00031010K0000n200110C00012110<10>PFP_%r\PjPkn0100000020000n10110N00021110C00PyPzP{n10110200031010K0000=1]pe%i\P7E;AfdQ\,]:=1]pR\eP\e1cdVP<E;P8P@P_&08QR<,cdAfah9RhP8P@P_AsdD<PhP8P@P_AtdD<PhP6P:P_AkdD<Q05PjPkn10110N00031010L0000n10110N00021010300n10110N00021010301n10110N00021010301,]:=1]pe1qdQ=1]pePbPUPVPTPRP;E|,qd=1]peW9W:W5W6W7W8X4BXCGXBGW>X@FW;WEXAEW<X=BW?WDo"). Qed.

(* [comment removed for export] *)
Lemma step_sc_fail : forall segs regs pc mem rom w wd aq rl rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 1)) (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "p'0h01bi001bh11mh21ti011th31oh43Halh57Hdecodeh66Hecallh76Hfetchh82aqh93memh:2pch;2rdh<4regsh=2rlh>3romh?3rs1h@3rs2hA4segshB1wi021whC2wdi032wdhD1zi041ai052bsi061ci076c_fcsri087c_fregsi094c_pci0:6c_regsi0;6c_resvi0<1ii0=Cinterp_eff_accessesi0>3iszi0?1ki0@2m'i0A1ni0B1pi0C2p0i0D2p1i0E2p2i0F2p3i0G2p4i0H2p5i0I2p6i0J1ri0K6reporti0L3st'i0M1vi0N1xp%0p&0p;1p;2p;3p;6p;4p;5p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0g006GR0p4p710R6p8p1006ep4p710R7P3p8P7P6p8p1007Bp4p70R8P1p8P8p10080p4p7210p8P8P3p8P8p1008Lp4p710R1p8P8P7p8P8P4p8P8P5p8P8p1009Bp4p710R7p8P8P6p8P8p1009cp4p710p8P8p100:@p4p710p8P8p100;9p6051001R9p8P8p100<<p4p7210p8P8p100<Yp4p710p8g00=6R8p4p7210R:P3p8P:P4p8P:P5p8P:P6p8P:g00=bR:p4p710p8P2P6p8P9P3p8P9P1p8P9P4p8P9P5p8P9P7p8P9P6p8P9p100>ip4p710p8p100?Kp60521000R9p100@Up4p710R7p8p100APp6051000R1P7p8p100BVp6051000R2P7p8p100CZp4p70R7P3p8P7P4p8P7P5p8P7P6p8p100DPp4p7511110R6P9p8P6P1p8P6P2p8g00I_j1oTg00EQj1:Tg00F6j1dTg00F[j1CTg00G9j1NTP8k206Tg00G\R8j1KTg00J?j2VTg00KAj2?Tg00Kcj31Tg00L=j1`Tg00M=R2j2QTg00M]j1PTg01\Oj6pTg00O:j1MTg00OXj4LTg00P8j2nTg00Pjj2YTg01c^j1~Tg00QTj2kTg00TAR6j1XTP:j1hTg00UIj55Tg00V;j3WTg00WGj1HTg00XEj3bTg00YJj3aTg00ZPj3mTg00[Uj1rTg00\5j1TTg00]=j1STg00^Ej2RTg00_Oj3_Tg00`2j3^Tg00lcj2BTg00aQj3]Tg00c:j2>Tg00dbj1DTg00eaj1=Tg00faj1OTg00gbk207Tg00h`j1ITg00i_j1;Tg00j^j1JTg00k\j82Tg00mIj50Tg00n2j3\Tg00nYj3ZTg00odj28Tg010hk105Tg011Qk104Tg012;k103Tg00H>k101Tg012bj1}Tg013Kj1|Tg0144j29Tg015;j1jTg0164j1@Tg016\j2GTg00R4j17Tg017dj4iTg018ij1{Tg01KBj4zTg01Kkj3yTg01J;j3UTg019ij4gTg01:ij2wTg01;fj3vTg01<jj2fTg01=Tj2cTg01>Bj1[Tg00bEj1uTg00cnj1xTg01>`j1ETg01?Hj3eTg01@Xj5ATg01AHj1FTg01BXj2tTg00H`j2lTg01C5j1sTP0j6<Tg01FJk100Tg01GEj1qTg01HBk202Tf2R0g01LKR:f1R1f0R93U'Gp=31G:9p=6f4R7g01MRR5f3R4P0P1CL;U9p=4g01O8#og00I:R3#:R;#d#CR<%:;R;#:R=#:#:R>#:#CR?#NR@+06RA%C=#NRB#K\@RC%C>#NR>g01dJS00g01P7RD%N<RE%K>RFf;RGf9RH'Vf6RI,?>31f7RJ#`g01PWRK51Dg01Q7RLg01QcRM'QRN#KROf8RP#PPLPMPJPIf5RQP7P4P0Ep%M;R;CL,?N31f=RR/n7,Y?%~P'kg01RnRS51MPFf:RT,?>%X:RUP8P>%h:RV#XRWP9fARXp,2fxRYf@RZf?R[f>R\PRD5;W9R]P8P>PWPYP[P\PRf<R^D5R_#HR`=bZ\P]P8P>PWAaZ`\P]P6P:PWAmZ`\g01Sk#rR]93V9S01%TVRa%SVRbn10110N00031010L0000n10110N00021010200n10110N00021010200n10110N00021010200,R:PYPDPAg01U0Rc9_<SRd9^<JP[%M3,B?R39][JRen01000000200001>\;RfPRP^D5#6Rg31X3FPDPKP6PVPUPDPWP9%D_%=_%O_%d=#M=_<c-07_,?@%I_%;_P`%J_G2=3V]P8PNPW%PGP2PLPMPWP9P61Q5CR`#hRcPWfCS021B?9S03PYfBRFPXPZP[D5Rh#D%=h%Oh%;h%IhD07\1%Hh3ZP2P5PCPW18`9Rh&051S04&041S05&031S06&01@Ri%}1Rj%|1RkP9PYfES07fDS08Q02PFD5#JG219`0Rl53Vn200110N00012010610@PaPbn10110N00031010K0000n200110B00012010<10>RmPDPW%jGPaPbn0100000020000Rnn10110N00021110B00n010000002000118:9#6Ro%T:Rp%S:Rqn10110J00031010K0000=1UgX0DPOPLPMPHPPPJPIPQP7EpRrP;CL,?NP6PVPUP8PNPWP9PmPnn10110N00021110B00PoPpPqn10110J00031010K0000=1UgX3OPD%@IROP6PVPUP6PcPWg01ULRg%XcRn^1C]2S09PgPnP1P`PCP9P1P]D4,GcS0:%ScRm%TcRsPmPsPsP8%oBS0;PnfFS0<P4P1g01V4RBg01NYRtP0g01SLRug01VRRvPtP9PuPvPtP9PuPvPtP9PuPvPtP9PuPvPtP9PuPvPtP9PuPvPtP9PuPu%7uRv#7Rw#7#7Rx#7#7#7#7n0110H00031010I1010I00Pxn0110G00031010H1010H00Pwn0110F00031010G1010G00Pvn0110E00031010F1010F00Pun0110D00031010E1010E00Pun0110C00031010D1010D00Pun0110B00031010C1010C00Rvn0110A0002001010BS0=CiP6PcPnPIP1P?g01N;P4%{9CzO1P7O21Q@tP@PtP4PBPtP7PuPvn0110A0002001010BCL19`93y9U`h,GcRwPsPmn10110N00031010K0000S0>Psn10110N00021110500PDPnfGP7P0PBPtP4PuPvn0110A0002001010BRvCgP6PcPnPIP91Y41,wv9v70O2PwPsPmn10110N00031010K0000S0?Psn0100000020100n0110100081010610106101061010610106101063110A10410?4110A10410M10?X1CX2gp?100010=S0@PDPgPDP@PO1B?SS0A1f[In0100000020000,cT#[P[P[%uYRwP\PiPi%xYRuPRP^G2Rt#=RBP\%;tRtPiD0#EPDP5%@JRxP[PB1B?;Ry9e?\RzPtPiD0P<P@PJP3P[DARJPBPzPtPiD0n0100000020000#Fn0100000020001PRO2P2P5PCPWPhP5PAP1P7n0110600015010:10810910710;RtP5PAP1P4n0110600015010:10810910710;RBP5P@P1P0n0110600015010:10810910710;R{PiP5%K@P1P9n0110600015010:10810910710;R|P5P>P1P1n0110600015010:10810910710;R}P9P[G2R~=3Vln200110N00012010610@S0BPaPbn10110N00031010K0000PoPpPqn10110J00031010K0000PDPAP9P[Pen0100000020000PwPfPiPiPuPRP^G2#651UX0DPMPSP6PVPUP6PcPWQ0@PDPg1t9S#[P[PwP\PuPiD0#EPDP5PxP[PwPzPuPiD0PJPwPzPuPiD0n0100000020000#Fn0100000020000PRO2Q0BPaPbn10110N00031010K0000PoPpPqn10110J00031010K0000PDPAPxP[Pen0100000020000PwPfPiPiPuPRP^G2#6Re51UXDMP@1>R;RzP6PVPUP2P5PCPWP`PCPDP5PxP[PwP9PuPiD0PJPwP9PuPiD0n0100000020000PRP]D4,8`PtPBP{PiP|P}P9P\G2RxP`PCPDP5%@HPXPwP0PuPiD0P<P@PHP3PXDAS0BPwP0PuPiD0n0100000020000P[P]D4,9`53Vn200110N00012110610@PoPpPqn10110J00031010K0000=1UeX0@POPDPDP6PVPUP2P5PCPWP`PCPDP5P9PZPw1>[;RePuPiD0S0@P<P@PPP3PZDAS0CPwPePuPiD0S0Dn0100000020000P\P]D4,8`P`PCPDP5P0PFPw1>X;RSPuPiD0P<P@PTP3PFDAPwPSPuPiD0n0100000020000PZP]D4,9`93V~n200110N00012110610@PoPpPqn10110J00031010K0000PDPAP9PZQ0Cn0100000020000PwPePiPiPuP\PRG2#651UP9P[PwPfPiPiPuPRP^G2#6Re,lUP6PVPUP2P5PCPWP`PCP[PwPfPuPiD0PRP]D4,8`P`PCPXPw1>Z;R~PuPiD0P[P]D4,9`93Vxn200110N00012010610@PoPpPqn10110J00031010K0000=1UeePJPwPfPiPiPuPRP^G2#6Re,lUP6PVPUP2P5PCPWP`PCPJPwPfPuPiD0PRP]D4,8`P`PCQ0BPwP~PuPiD0P[P]D4,9`93Vxn200110N00012110610@PoPpPqn10110J00031010K0000=1Ueen0110001020101b0P6PVPUP2P5PCPWP`PCPDP5POP\PwPzPuPiD0P<P@PIP3P\DARePwPzPuPiD0n0100000020000P^P]D4,8`PtPBP{PiP|P}P9PRG2P`PCPDP5%@PQ0@Q0Dn0100000020000P\P]D4,9`53Vn200110N00012110610@PoPpPqn10110J00031010K0000PDPAPOP\A]\I3R3n0100000020000PwPzPiPiPuP^PGG2#6R`51UeAe?RyR]%sRE<P6PVPUP6PcPWQ09PgPnP1Q0:PmPsPmPsPsP8Q0;PnQ07P4P1Q0=CiQ0>Psn10110N00021110500PDPnQ0<P7P0PvCgQ0?Psn0100000020100n0110100081010610106101061010610106101063110A10410?4110A10410M10?X1CX2gp?100010=RsPDPgPKP\PwPRPuPiD0#EPDP5POP\PwP]PuPiD0PePwP]PuPiD0n0100000020000#Fn0100000020000P^O2P2P5PCPWPhA3Vxln200110N00012010610@RxPaPbn10110N00031010K0000PoPpPqn10110J00031010K0000=1U`e1n\Q,Y?Q00PMPHP;%M=n0110300020000'kP9E<P6PVPUP6PcPWPsPDPgPDP@%@QQ0A1f\Qn0100000020000,cH#[P\P\PwPRPiPiPuP^PGG2Ru#=RwPR%;uRuPiD0#EPDP5POP\PwP]PuPiD0PePwP]PuPiD0n0100000020000#Fn0100000020001P^O2PxPaPbn10110N00031010K0000PoPpPqn10110J00031010K0000=1U`eA^<IdRd&00IE<P6PVPUP6PcPWPYP\PRP^PGD5RI#D%=I%OI%;I%IID09\yr%HIRy5Z[P2P5PCPWPhQ04Q05Q06PiPjPkP9PYPXPZP[P\D5Rr#JG2=3Vln200110N00012010610@PaPbn10110N00031010K0000PoPpPqn10110J00031010K0000PYPDPAPdP\P3n0100000020000PzP^PGD5#6RG51Ue%PTR^P1E<P6PVPUP8PNPWP^P2PLPMPWP9P6PcPWQ03%Dr%=r%Or%;r%IrD07\1%Hr5ZFP2P5PCPWPhQ04Q05Q06PiPjPkP9PYQ08Q02PFPXD5#JG2=3Vln200110N00012010610@PaPbn10110N00031010K0000n200110B00012010<10>PDPW%jTPaPbn0100000020000n10110N00021110B00PoPpPqn10110J00031010K0000=1UGe%`TP0E<AW[IT,R:=1UGRTePTe1V[RP4E<P8P>PW%qIR4,V[AWZ_9R_P8P>PWAb[y4P_P8P>PWAa[y4P_P6P:PWAm[y4Q01PaPbn10110N00031010L0000n10110N00021010200n10110N00021010200n10110N00021010200,R:=1UGe202[I=1UGRGePGeW4W5W6W7X@EX?EW;X=DW8WCWBX>CW9X:@W<WAo"). Qed.

(* [comment removed for export] *)
Lemma step_sc_mismatch : forall segs regs pc mem rom w wd aq rl rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
  (bv_unsigned r =? bv_unsigned (getr regs rs1))%Z = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 1)) (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "p'0h01bi001bh11mh21ti011th31oh43Halh57Hdecodeh66Hecallh76Hfetchh83Hneh92aqh:1ki021kh;3memh<2pch=1ri031rh>2rdh?4regsh@2rlhA3romhB3rs1hC3rs2hD4segshE1wi041whF2wdi052wdhG1zi061ai072bsi081ci096c_fcsri0:7c_fregsi0;4c_pci0<6c_regsi0=6c_resvi0>1ii0?Cinterp_eff_accessesi0@3iszi0A2m'i0B1ni0C2oki0D1pi0E2p0i0F2p1i0G2p2i0H2p3i0I2p4i0J2p5i0K2p6i0L6reporti0M3st'i0N1vi0O1xp%0p&0p;1p;2p;3p;6p;4p;8p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0g006GR0p4p710R6p8p1006ep4p710R7P3p8P7P6p8p1007Bp4p70R8P1p8P8p10080p4p7210p8P8P3p8P8p1008Lp4p710R1p8P8P7p8P8P4p8P8P5p8P8p1009Bp4p710R7p8P8P6p8P8p1009cp4p710p8P8p100:@p4p710p8P8p100;9p6051001R9p8P8p100<<p4p7210p8P8p100<Yp4p710p8g00=6R8p4p7210R:P3p8P:P4p8P:P5p8P:P6p8P:g00=bR:p4p710p8P2P6p8P9P3p8P9P1p8P9P4p8P9P5p8P9P7p8P9P6p8P9p100>ip4p710p8p100?Kp60521000R9p100@Up4p710R7p8p100APp6051000R1P7p8p100BVp6051000R2P7p8p100CZp4p70R7P3p8P7P4p8P7P5p8P7P6p8p100DPp4p7511110R6P9p8P6P1p8P6P2p8g00I_j1pTg00EQj1ATg00F6j1iTg00F[j1ETg00G9j1PTP8k209Tg00G\R8j1KTg00J?j2\Tg00KAj25Tg00Kcj31Tg00L=j1cTg00M=R2j2XTg00M]j1TTg01\Oj6tTg00O:j1RTg00OXj4JTg00P8j2OTg00Pjj26Tg01c^k108Tg00QTj2mTg01BXj2@Tg00TAR6j1^TP:j1jTg00bEj1~Tg00H>j1|Tg00cnj1zTg00k\j82Tg00V;j3]Tg00WGj1HTg00XEj3oTg00YJj3eTg00ZPj3dTg00[Uj1uTg00\5j1WTg00]=j1VTg00^Ej2UTg00_Oj3bTg00`2j3aTg00lcj2CTg00aQj3sTg00c:j2BTg00UIj5rTg00dbj1QTg00eaj1ITg00faj1GTg00gbk20:Tg00h`j1NTg00i_j1LTg00j^j1DTg00mIj50Tg00n2j3`Tg00nYj3_Tg00odj28Tg010hk107Tg011Qk106Tg012;k105Tg012bk104Tg013Kk103Tg0144j2:Tg015;j1lTg0164j1?Tg016\j2MTg00R4j19Tg017dj4kTg018ik102Tg01KBk401Tg01Kkk300Tg01J;j3YTg019ij4hTg01:ij2}Tg01;fj3{Tg01<jj2FTg01=Tj2gTg01>Bj1ZTg01>`j1STg01_>j1fTg01_fj3;Tg01?Hj3[Tg01@Xj5>Tg01AHj1<Tg00H`j2qTg01C5j1yTP0j6=Tg01FJj1xTg01GEj1wTg01HBj2nTg01I>j6vTf2R0g01LKR:f1R1f0R93Y'Mp=41M:9p=7f4R7g01MRR5f3R4P0P1CJ;Y9p=3g01O8#pg00I:R3#AR;#i#ER<%A;R;#AR=#A#AR>#A#ER?#PR@+09RA%E=#PRB#K\@RC%E>R>#PRDg01dJREg01P7RF%P<RG%KDRHf<RIf:RJ'\f7RK,5D31f8RL#cg01PWRM51Fg01Q7RNg01QcRO'XRP#KRQf9RR#TPNPOPLPKf6RSf5RTP7P4Et%R;R;CJ,5P31f>RU/OT,6?&08R'mg01RnRV51O16?7f?RW/OS,6?'@=1FMPH15DI%^:RXP8PD%j:RY#^RZP9fCR[fBR\p,2fxR]#~R^fAR_%|@R`15@K%z]Raf@RbPWG2;]9RcP8PDPZP_P^PbP`15@SS00PaPWPUG2Rd#HRe=o\bPcP8PDPZAe\ebPcP6P:PZAd\ebg01Sk#uRc94Y9S01%WYRf%VYRgn10110O00031010M0000n10110O00021010400n10110O00021010400n10110O00021010401,U:P]PFPAg01U0Rh9b<VS029a<RP_%R3,C?R39s_RS03n01000000200001Bb;RiPWPUDr#7Rj31X3HPFPMP6PYPXPFPZP9%Qd%IdRH%Gd%i=#R=b<h-0:d,5@%Nd%LdRhPe%DdG2=4YcP8PPPZf=Re#TP2PNPOPZP9P61X5CRk#jRlPZfES041C?9S05fDRmP^P[P`15@RPaP\P_G2Rn#Q%In%Gn%Ln%NnD07`1%Hn3_P2P5PCPZ18k9Rn&071S06&061S07&051S08P`&041S09&031S0:P9fGS0;P^fFS0<P`15@IPaQ04PmG2#DG21:k0Ro54Yn200110O00012010810APfPgn10110O00031010L0000n200110D00012110>10@RpPFPZ%lePfPgn0100000020000Rqn10110O00021110D00n010000002010118:9#7Rr%W:Rs%V:Rtn10110300031010L0000=1XjX0FPQPNPOf;RuPJPRPLPKPSEtS0=P;CJ,5PP6PYPXP8PPPZP9PpPqn10110O00021110D00PrPsPtn10110300031010L0000=1XjX3QPF%?LRQP6PYPXP6PlPZg01ULRj%^lRq^1C]2S0>PjPqP1PkPCP9P1PcD3,MlS0?%VlRp%WlRvPpPvPvP8%pBS0@PqfHS0AP4P1g01V4RBg01NYRwP0g01SLRxg01VRRyPwP9PxPyPwP9PxPyPwP9PxPyPwP9PxPyPwP9PxPyPwP9PxPyPwP9PxPx%9xRy#9Rz#9#9R{#9#9#9#9n0110J00031010K1010K00P{n0110I00031010J1010J00Pzn0110H00031010I1010I00Pyn0110G00031010H1010H00Pxn0110F00031010G1010G00Pxn0110E00031010F1010F00Pxn0110D00031010E1010E00Ryn0110B0002001010DS0BCkP6PlPqPSP1P?g01N;P4&029H01O1P7O21X@wP@PwP4PBPwP7PxPyn0110B0002001010DCJ1:k94009Ykn,MlRzPvPpn10110O00031010L0000S0CPvn10110O00021110700PFPqfIP7P0PBPwP4PxPyn0110B0002001010DRyChP6PlPqPSP91641,}y9{70O2PzPvPpn10110O00031010L0000S0DPvn0100000020100n0110100081010810108101081010810108101083110B1061024110B10610N102X1CX2jp?100010?S0EPFPjPFP@PQ1C?VRz1F_Ln0100000020000Rx,gI#ZP_PHPbPhQ00D0#SPFPj16?SRw16?x'@PEPj^:jRBPIPFP@%?KS0FPz1F_Kn0100000020000R{#fR|9;>xA;?x{n0110500020000PFP5%?RRxP_PH1C?;R}9[?bR~PhP`D0S0GP<P@PRPzP_D>S0HPHP~PhP`D0n0100000020000#<O1PFP5PxQ0GP<P@PRP3P_D>RRPHP~PhP`D0n0100000020000#<n0110C00020101n0100000020001PWO2P2P5PCPZPnP5PAP1P7n0110800015010<10:10;10910=S0GP5PAP1P4n0110800015010<10:10;10910=S0IP5P@P1P0n0110800015010<10:10;10910=S0JP`P5%K@P1P9n0110800015010<10:10;10910=S0KP5PDP1P1n0110800015010<10:10;10910=S0LP9P_G2Rh=4Yon200110O00012010810ARHPfPgn10110O00031010L0000PrPsPtn10110300031010L0000PFPAP9P_Q03n0100000020000P^PiP`P`PaPWPUG2#751XX0FPOPVP6PYPXP6PlPZQ0EPFPj1@9V#ZP_P^PbPaQ00D0#SPFPj1O_LRV,6?,@wPEPBPIA;>V|A;?V{n0110500020000PFP5PxP_P^P~PaP`D0RVQ0HP^P~PaP`D0n0100000020000#<O1R{PFP5PxPVPRP^P~PaP`D0n0100000020000#<R~n0110C00020100n0100000020001PWO2PHPfPgn10110O00031010L0000PrPsPtn10110300031010L0000PFPAPxP_Q03n0100000020000P^PiP`P`PaPWPUG2#7RV51XXGOPFPMP6PYPXP6PlPZQ0EPFPjP9P{P~n0110C00020100PWO2PHPfPgn10110O00031010L0000PrPsPtn10110300031010L0000=1XVX0FP@1BW;RHP6PYPXP2P5PCPZPkPCPFP5PxP_P^P9PaP`D0PRP^P9PaP`D0n0100000020000PWPcD3,8kQ0GQ0IQ0JP`Q0KQ0LP9PbG2RxPkPCPFP5%?uP[P^P0PaP`D0P<P@PuP3P[D>R~P^P0PaP`D0n0100000020000P_PcD3,:k54Yn200110O00012110810APrPsPtn10110300031010L0000=1XVX0@PQPFPFP6PYPXP2P5PCPZPkPCPFP5P9P\P^1B_;RVPaP`D0S0EP<P@PJP3P\D>R{P^PVPaP`D0R|n0100000020000PbPcD3,8kPkPCPFP5P0PmP^1B[;RwPaP`D0P<P@PIP3PmD>P^PwPaP`D0n0100000020000P\PcD3,:k94Yhn200110O00012110810APrPsPtn10110300031010L0000PFPAP9P\P{n0100000020000P^PVP`P`PaPbPWG2#751XP9P_P^PiP`P`PaPWPUG2#7RV,qXP6PYPXP2P5PCPZPkPCP_P^PiPaP`D0PWPcD3,8kPkPCP[P^1B\;RhPaP`D0P_PcD3,:k94Yxn200110O00012010810APrPsPtn10110300031010L0000=1XVePRP^PiP`P`PaPWPUG2#7RV,qXP6PYPXP2P5PCPZPkPCPRP^PiPaP`D0PWPcD3,8kPkPCP~P^PhPaP`D0P_PcD3,:k94Yxn200110O00012110810APrPsPtn10110300031010L0000=1XVen0110001020101b0P6PYPXP2P5PCPZPkPCPFP5PQPbP^PHPaP`D0P<P@PLP3PbD>RVP^PHPaP`D0n0100000020000PUPcD3,8kQ0GQ0IQ0JP`Q0KQ0LP9PWG2RhPkPCPFP5%?JRJQ0EP|n0100000020000PbPcD3,:k54Yn200110O00012110810APrPsPtn10110300031010L0000PFPAPQPbAsbL3R3n0100000020000P^PHP`P`PaPUPeG2#7R|51XeA[?W}R~%yWE=P6PYPXP2P5PCPZPkPCPFP5PQPbP^P~PaP`D0RiPVP^P~PaP`D0n0100000020000RRPUPcD3,8kPkPCPFP5PJP\P^A[?_}RJPaP`D0P{P^PJPaP`D0n0100000020000PbPcD3,:k94Yhn200110O00012110810APrPsPtn10110300031010L0000=1X|e16?TRh1ObKRk,6?Rc'@RJP9E=P6PYPXP6PlPZQ0>PjPqP1Q0?PpPvPpPvPvP8Q0@PqQ0;P4P1Q0BCkQ0CPvn10110O00021110700PFPqQ0AP7P0PyChQ0DPvn0100000020100n0110100081010810108101081010810108101083110B1061024110B10610N102X1CX2jp?100010?RvPFPjPMPbP^PWPa15@TRMD0#SPFPjPJPEPBPuPFP@%?SPz1FbSn0100000020000RS#fRJ9;>kA;?kSn0110500020000PFP5PQPiP<P@PLPzPbD>RiP^P~PaP`D0n0100000020000#<O1%<Rn0110C00020100n0100000020001PUO2P2P5PCPZPnA4Yxon200110O00012010810ARxPfPgn10110O00031010L0000PrPsPtn10110300031010L0000=1X|ePEPOPuP;%R=n0110500020000,mcP1E=P6PYPXP6PlPZPvPFPjPFP@Q0FPz1FbKn0100000020000RK,gu#ZPbPbP^PWP`PMPaPUPeG2Rz#IRvPW%LzRcPMD0#SPFPj16?K,@hPEPBPuA;>KJA;?KSn0110500020000PFP5PQPbPvP~PcP`D0RKPiPvP~PcP`D0n0100000020000#<O1PFP5PQPKPVPvP~PcP`D0n0100000020000#<n0110C00020101n0100000020001PUO2PxPfPgn10110O00031010L0000PrPsPtn10110300031010L0000=1X|eQ029a<LR<%xLE=P6PYPXP6PlPZQ0=%QzPv%GzPc%NzD05`}%HzR}5__P2P5PCPZPnQ06Q07Q08P`Q09Q0:P9P[P^P\P`15@LPaP_PbG2RL#DG2=4Yon200110O00012010810APfPgn10110O00031010L0000PrPsPtn10110300031010L0000P]PFPAP<PbP3n0100000020000PHPUPeDr#7RH51Xe%TIR3P0E=P6PYPXP8PPPZP3P2PNPOPZP9P6PlPZQ05%QL%IL%GL%LL%NLD07`1%HL5_mP2P5PCPZPnQ06Q07Q08P`Q09Q0:P9Q0<P^Q04P`15@uPaPmP[G2#DG2=4Yon200110O00012010810APfPgn10110O00031010L0000n200110D00012110>10@PFPZ%lIPfPgn0100000020000n10110O00021110D00PrPsPtn10110300031010L0000=1XHe%cIP4E=A]_zI,U:=1XHRIePIe1\_WP7E=P8PDPZ%wzR7,\_A]\d9RdP8PDPZAo_}7PdP8PDPZAe_}7PdP6P:PZAd_}7Q01PfPgn10110O00031010M0000n10110O00021010400n10110O00021010401n10110O00021010401,U:=1XHe1n_z=1XHeP]PbPWPUPePTEv,n_=1XHeW8W4W5W6W7X=@XCGXBGW>X@FW9WFWEXACW;X<@W?WDo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_branch_tk_r : forall segs regs pc mem rom r w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (btgt pc (bv_signed imm)) mem rom r).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "p'0h02Hch11bi001bh21oh37Hdecodeh46Hecallh56Hfetchh61ci011ch73immh83memh92pch:1ri021rh;4regsh<3romh=3rs1h>3rs2h?4segsh@1wi031wi046c_fcsri057c_fregsi064c_pci076c_regsi086c_resvi091ii0:3iszi0;2m'i0<1pi0=6reporti0>3st'i0?1xp%0p;1p;2p;3p;4p;8p;5p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0g0050R3p4p710R4p8P0p1005Lp4p710R5p8P0p1005jp4p7210R6p8P0g006GR0p4p710R7p8p1006ep4p710R8P4p8P8P7p8p1007Bp4p70R9P1p8P9p10080p4p7210p8P9P4p8P9p1008Lp4p710R1p8P9P8p8P9P5p8P9P6p8P9p1009Bp4p710R8p8P9P7p8P9p1009cp4p710p8P9p100:@p4p710p8P9p100;9p6051001R:p8P9p100<<p4p7210p8P9p100<Yp4p710p8g00=6R9p4p7210R;P4p8P;P5p8P;P6p8P;P7p8P;g00=bR;p4p710p8P2P7p8P:P4p8P:P1p8P:P5p8P:P6p8P:P8p8P:P7p8P:p100>ip4p710p8p100?Kp60521000R:p100@Up4p710R8p8p100APp6051000R1P8p8p100BVp6051000R2P8p8p100CZp4p70R8P4p8P8P5p8P8P6p8P8P7p8p100DPp4p7511110R7P:p8P7P1p8P7P2p8g00I_j1}Tg00EQj1<Tg00F6j1MTg00F[j1?Tg00G9j1ETP9j2{Tg00G\R9j1JTg00J?j2YTg00KAj25Tg00Kcj30Tg00L=j1]Tg00M=R2j2ZTg00M]j1PTg01e7j4kTg00O:j1jTg00OXj4WTg00P8j2iTg00TAR7j1fTP;j1bTg00bEj1tTg00H>j1sTg00cnj1rTg00k\j83Tg00V;j3UTg00WGj1ITg00XEj3`Tg00YJj3_Tg00ZPj3^Tg00[Uj1mTg00\5j1\Tg00]=j1[Tg00^Ej2QTg01ecj2>Tg01fKj2ATg00dbj1HTg00eaj1CTg00faj1KTg00_Oj3lTg00gbj2|Tg00h`j1OTg00i_j1BTg00j^j1NTg00lcj2XTg00mIj5GTg00n2j3STg00nYj3RTg00odj2VTg010hj1zTg011Qj1yTg012;j1xTg012bj1wTg013Kj1vTg0144j2eTg015;j1cTg00`2j3dTg01<jj22Tg0164j1:Tg01FJj1uTP3j6aTg01g=j34Tg01?mj3;Tg01?Hj37Tg00c:j2qTg00H`j2pTg01glj3oTP0j6DTg01GEj1nTg01HBj2gTg01I>j6hTg01J;j3FTg016\j2TTg01P7R0f2R3f1R;f0R134g01c>R:30p=6g01LKR8?F;1,T3p=@1T81p==g01MRR6f6R5f5R4f4R<f3R=P3P;DGP1CWp=1AF3;1,V=p=9AF3;1,e=9F8<,T4p=8P0P:P=P3P;P1EDp=Lg01O8#}g00I:R:#<R>#M#?R?%<>R>#<R@#<#<RA#<#?RB#ERC'{RD%?@#E#J\CRE%?A#ERAg01hc%E?S00Q00%M:#<#M#?R:#E%JARFf:RGf8RH'Y15A<30%]4g01PWRI500g01Q7RJg01QcRK'ZRL#JRM%P5PJPKP4P<P=P3Ck%j>R>CW,5L30f<RN/i41iN<565PF15AH%f8ROP9PA%b8RP#fRQP1f@RRf?RSp,2fxRT#tRUf>RV%sCRWf;RX,5CS01%rTRYf=RZPNG3R[;U1R\P9PAPQPVPUPZPW15CGR]PYPNPXG3R^#IR_=`SZP\P9PAPQA_S_ZP\P7P8PQA^S_Zg01Sk#mR\9@P1S02%\PR`%[PRan10110?00031010>0000n10110?00021010300n10110?00021010300n10110?00021010301,Q8PVPU1>:4,AZPWP]PYPNPXG3#=R]30X2FP0PIP7PPPOP0PQP1%H^%C^%K^%M@#jg01U0R@5l?,|^,5C%O^%B^P_%N^G3=@P\P9PLPQf9R_#PP2PJPKPQP1P71Z6ERI#bS03PQfBRF1XB1S04fARbPUPRPW15CZPYPSPVG3Rc#H%Cc%Kc%Bc%OcDG7S;%Ic3RP2P6PEPQ1VI1S05%z;S06%y;S07%x;S08PW%w;S09%v;S0:P1fDRcPUfCRdPW15CRRePYPFPbG3#NG31eI3Rf5@Pn200110?00012010110;P`Pan10110?00031010=0000n200110<00012110910:RgP0PQ%c_P`Pan0100000020000Rhn10110?00021110<00n01000000201011V81#=Ri%\8Rj%[8Rkn10110200031010=0000=0O]X10PMPJPKf7RlP5P4P<CkS0;P>CW,5LP7PPPOP9PLPQP1PgPhn10110?00021110<00PiPjPkn10110200031010=0000=0O]X2MP0g01RnRM=l?@R@9d?5R]P0PCP11XBMRM12VlRhn0100000020000P0PCP]PM12V5Rgn010000002000056HX10P1%:5Rm%u5RnEaP0PCPmPM12Z5n0100000020000S0<P0PCAd?4@PM12Z4S0=n010000002000056lP0P]P0PC%:HR]PM12SHn0100000020000S0>P0PCP1PM12SlS0?n010000002000056_X10P1PmPnEaP0PC%:lS0@PMPhn0100000020000P0PCPmPMPgn010000002000056HP]P0P0P0PCP1PM12bGn0100000020000P0PC%:_S0APM12b_n010000002000056XP7PPPOP2P6PEPQPIPIPEPFPUP0PCP0PCP;PM12FXRgn0100000020000P0PC%:GPM12FGRmn010000002000054NA;:B_97Bb1XB>R>97Bbn0100000020000PY15CVRhPRF1P\C9PPP6PDP;P<n01101000150107105106104108S0BP6PDP;P=n01101000150107105106104108S0CP6PCP;P3n01101000150107105106104108RDPWP6%JCP;P1n01101000150107105106104108RnP6PAP;P;n01101000150107105106104108R@P1PbG3PIPIPEPcPUP0PCP0PCP=PM12cZS0Dn0100000020000P0PC%:NPM12cNR?n010000002000054VA;:BX97BdRoA7Bd>Rpn0100000020000PYPePFF1P\E8n200110?00012110110;PiPjPkn10110200031010=0000PFPU1>:_,AbPWPhPYPRPSG3#=50O]0P1P0PCP]PM12RHn0100000020000R]96GMQ0AP0P0P0PCP1PM12dXRhn0100000020000S0E96ZMP7PPPOP2P6PEPQPIPIPEPcPUP0PCP0PCP;PMP?n0100000020000S0F94VMPoPpn0100000020000PYPePFF1P\C9PPQ0BQ0CPDPWPnP@P1PdG3R?PIPIPEfFRqPUP0PCP0PCP=PM12qVn0100000020000S0G94RMfERrA;:BZ57BS0HA7Br>S0In0100000020000PY15CFRsPcF1P\E8n200110?00012110110;PiPjPkn10110200031010=0000PcPU1>:X,AdPWPePYPFPbG3#=Rt50O]0P1A6NMMP7PPPOP2P6PEPQPIPIPEPcPUP0PCP1PoPpn0100000020000PYPePFF1P\C9PPP?PIPIPEPqPUP0PCP3Q0HQ0In0100000020000PYPsPcF1P\E8n200110?00012110110;PiPjPkn10110200031010=0000=0OtX10RuPC1>:GRv,qFP7PPPOP2P6PEPQPIPIPEPcPUP1PYPePFF1P\C9PPP?PIPIPEPqPUP3PYPsPcF1P\E8n200110?00012010110;PiPjPkn10110200031010=0000=0OtX1CPdPU1AFvPW15CSRvPYPbPRG3#=Rw,pOA;:BG97BFRxAoF:GEDP7PPPOP2P6PEPQPIPIPEPdPUPxPYPvPbF1P\C9PPQ0BQ0CPDPWPnP@P1PFG3RyPIPIPEPrPUA;:BN97BcRzPY15CbR{PdF1P\E8n200110?00012110110;PiPjPkn10110200031010=0000=0OweR|A4ZMMR}P1CLP7PPPOP2P6PEPQPIPIPEPdPUP0PCP}PxA7BF>R}n0100000020000PYPvPbF1P\C9PPPyPIPIPEPrPUP0PCA4SMMPzA7Bc>R~n0100000020000PYP{PdF1P\E8n200110?00012110110;PiPjPkn10110200031010=0000=0OweW0A6NMmPuP|A4ZMhS0JP1CLP7PPPOP2P6PEPQPIPIPEPdPUP0PCQ0JPxP}n0100000020000PYPvPbF1P\C9PPPyPIPIPEPrPUP0PC12rZS0J94SMPzP~n0100000020000PYP{PdF1P\E8n200110?00012110110;PiPjPkn10110200031010=0000=0OweW0n0110001020101P;O1b1W012R_=6G]Q0AP0P012dNR]Q0E56ZP7PPPOP2P6PEPQPIPIPEPcPUP0PCQ0DQ0F54VPoPpn0100000020000PYPePFF1P\C9PPP?PIPIPEPqPUP0PC12qSQ0G54RQ0HQ0In0100000020000PYPsPcF1P\E8n200110?00012110110;PiPjPkn10110200031010=0000=0Ot]0P1A6NgMPuP|A4Z]MRtP1CLP7PPPOP2P6PEPQPIPIPEPdPUP0PCPtPxP}n0100000020000PYPvPbF1P\C9PPPyPIPIPEPrPUP0PC12rVRt=4SMPzP~n0100000020000PYP{PdF1P\E8n200110?00012110110;PiPjPkn10110200031010=0000=0OweW0A6NgmPuP|A4Z]hR]P1CLP7PPPOP2P6PEPQPIPIPEPdPUP0PCP]PxP}n0100000020000PYPvPbF1P\C9PPPyPIPIPEPrPUP0PCQ0J94StPzP~n0100000020000PYP{PdF1P\E8n200110?00012110110;PiPjPkn10110200031010=0000=0OweW0n0110001020101P;O1b1W0n0110001020101P;O1b1b0b0P7PPPOP2P6PEPQPIPIPEPZPZPUPNPW15C_RwPYPXPGG3R{#CR~P0PCQ0<P0PC%:4PMQ0=n010000002000054lA;:B<97BNA7BN>n0100000020000%B{RlPwPXF1P\C9PPQ0BQ0CPDPWPnP@P1PNG3PIPIPEPS%C[P0PCQ0>P0PCQ0@PMQ0?n010000002000054_A;:B597BVA7BV>n0100000020000%B[Q01PZF1P\E8n200110?00012110110;PiPjPkn10110200031010=0000PZPU1>:<,ANR:PWPwPYPXPGG3#=Rw50OeP7PPPOP7Q03PQQ0;%H{P~%K{Pl%O{DG5S>%I{R>5RVP2P6PEPQQ05Q06Q07Q08PWQ09Q0:P1PRPUPSPW15CNPYPVPZG3Rl#NG3=@Pfn200110?00012010110;P`Pan10110?00031010=0000PiPjPkn10110200031010=0000=0Owe%PHR~P;EDP7PPPOP9PLPQP~P2PJPKPQP1P7Q03PQQ04%Hl%Cl%Kl%Bl%OlDG7S;%Il5RbP2P6PEPQQ05Q06Q07Q08PWQ09Q0:P1PdPUPFPWPvPYPbPRG3#NG3=@Pfn200110?00012010110;P`Pan10110?00031010=0000n200110<00012110910:P0PQ%cHP`Pan0100000020000n10110?00021110<00PiPjPkn10110200031010=0000=0Owe%]HP3EDAUV{H,Q8=0OwRHePHe1YVNP=EDP9PAPQ%n{R=,YVAUS^1R^P9PAPQA`V>=P^P9PAPQA_V>=P^P7P8PQA^V>=Q02P`Pan10110?00031010>0000n10110?00021010300n10110?00021010301n10110?00021010301,Q8=0Owe1gV{=0OwePTPZPNPXPGP_Eh,gVPTPZP:PXPGP_Eh#=50OeW0W3W4W5W7W>W=W6W@X:CX<EW8X9CW;W?o"). Qed.

Lemma step_branch_ft_r : forall segs regs pc mem rom r w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "p'0h02Hch11bi001bh21oh37Hdecodeh46Hecallh56Hfetchh61ci011ch73immh83memh92pch:1ri021rh;4regsh<3romh=3rs1h>3rs2h?4segsh@1wi031wi046c_fcsri057c_fregsi064c_pci076c_regsi086c_resvi091ii0:3iszi0;2m'i0<1pi0=6reporti0>3st'i0?1xp%0p;1p;2p;3p;4p;8p;5p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0g0050R3p4p710R4p8P0p1005Lp4p710R5p8P0p1005jp4p7210R6p8P0g006GR0p4p710R7p8p1006ep4p710R8P4p8P8P7p8p1007Bp4p70R9P1p8P9p10080p4p7210p8P9P4p8P9p1008Lp4p710R1p8P9P8p8P9P5p8P9P6p8P9p1009Bp4p710R8p8P9P7p8P9p1009cp4p710p8P9p100:@p4p710p8P9p100;9p6051001R:p8P9p100<<p4p7210p8P9p100<Yp4p710p8g00=6R9p4p7210R;P4p8P;P5p8P;P6p8P;P7p8P;g00=bR;p4p710p8P2P7p8P:P4p8P:P1p8P:P5p8P:P6p8P:P8p8P:P7p8P:p100>ip4p710p8p100?Kp60521000R:p100@Up4p710R8p8p100APp6051000R1P8p8p100BVp6051000R2P8p8p100CZp4p70R8P4p8P8P5p8P8P6p8P8P7p8p100DPp4p7511110R7P:p8P7P1p8P7P2p8g00I_j1|Tg00EQj1<Tg00F6j1KTg00F[j1>Tg00G9j1BTP9j2zTg00G\R9j1ITg00J?j2RTg00KAj25Tg00Kcj30Tg00L=j1]Tg00M=R2j2YTg00M]j1XTg01e7j4jTg00O:j1iTg00OXj4STg00P8j2hTg00TAR7j1cTP;j1bTg00bEj1rTg00H>j1qTg00cnj1nTg00k\j82Tg00V;j3QTg00WGj1JTg00XEj3`Tg00YJj3_Tg00ZPj3^Tg00[Uj1mTg00\5j1\Tg00]=j1ZTg00^Ej2OTg00c:j2DTg00dbj1ETg00eaj1ATg00faj1MTg00_Oj3kTg00gbj2{Tg00h`j1NTg00i_j1@Tg00j^j1FTg00lcj2WTg00mIj5GTg00n2j3UTg00nYj3PTg00odj2TTg010hj1yTg011Qj1xTg012;j1wTg012bj1vTg013Kj1uTg0144j2fTg015;j1eTg00`2j3dTg01<jj23Tg0164j1;Tg01FJj1sTP3j6[Tg01g=j34Tg01?mj3=Tg01?Hj36Tg00H`j2pTg01C5j1oTP0j6LTg01GEj1tTg01HBj2aTg01I>j6gTg01J;j3HTg016\j2VTg01P7R0f0R3g01PWR;30p=lf2R1f1R:;43=00;p=7g01LKR8?H:3,V1p=C1V83p=:g01MRR6f6R5f5R4f4R<f3R=P1P:DGP3CSp=1AH1:3,T=p=9AH1:3,f=9H8<,V4p=8P0P;P=P1P:P3ELp=?g01O8#|g00I:R;#<R>#K#>R?%<>R>#<R@#<#<RA#<#>RB#BRC'zRD%>@#B#I\CRE%>A#BRAg01hc%B?S00Q00%K;#<#K#>R;#B%IARFf:RGf8RH'R15A<30%]4#lg01Q7RIg01QcRJ'YRK#IRL%X5PIPJP4P<P=P1Cj%i>R>CS,5K30f<RM/h41hM<575PF15AH%c8RNP9PA%b8RO#cRPP3f@RQf?RRp,2fxRS#rRTf>RU%qCRVf;RW,5CS01%nSRXf=RYPMG2RZ;Q3R[P9PAPPPUPTPYPV15CGR\PXPMPWG2R]#JR^=`RYP[P9PAPPA_R^YP[P7P8PPA^R^Yg01Sk#mR[9CO3S02%\OR_%ZOR`n10110?00031010>0000n10110?00021010300n10110?00021010300n10110?00021010301,O8PUPT1DY>PVP\PXPMPWG2#:R\30X2FP7POPNP0PPP3%E]%A]%M]%K@#ig01U0R@5k?,{],5C%N]%@]P^%F]G2=CO[P9PKPPf9R^#XP2PIPJPPP3P71Y6ERF#bS03PPfBRa1WB3S04fARbPTPQPV15CYPXPRPUG2Rc#E%Ac%Mc%@c%NcDG7U:%Jc3PP2P6PEPP1TF3S05%y:S06%x:S07%w:S08PV%v:S09%u:S0:P3fDRcPTfCRdPV15CQRePXPaPbG2#FG21fF1Rf5COn200110?00012010110;P_P`n10110?00031010=0000n200110<00012110910:RgP0PP%e^P_P`n0100000020000Rhn10110?00021110<00n01000000201011T83#:Ri%\8Rj%Z8Rkn10110200031010=0000=0N\X10PLPIPJf7RlP5P4P<CjS0;P>CS,5KP7POPNP9PKPPP3PgPhn10110?00021110<00PiPjPkn10110200031010=0000=0N\X2LP0g01RnRL=k?@R@9d?5R\P0PCP31WBLRL13UlRhn0100000020000P0PCP\PL13U5Rgn010000002000057HX10P3%;5Rm%s5RnE[P0PCPmPL13Y5n0100000020000S0<P0PCAd?4@PL13Y4S0=n010000002000057lP0P\P0PC%;HR\PL13RHn0100000020000S0>P0PCP3PL13RlS0?n010000002000057^X10P3PmPnE[P0PC%;lS0@PLPhn0100000020000P0PCPmPLPgn010000002000057HP\P0P0P0PCP3PL13bGn0100000020000P0PC%;^S0APL13b^n010000002000057WP7POPNP2P6PEPPPFPFPEPaPTP0PCP0PCP:PL13aWRgn0100000020000P0PC%;GPL13aGRmn010000002000054MA=;B^96Bb1WB>Rh96Bbn0100000020000PX15CURnPQF1P[C9POP6PDP:P<n01101000150107105106104108S0BP6PDP:P=n01101000150107105106104108S0CP6PCP:P1n01101000150107105106104108S0DPVP6%ICP:P3n01101000150107105106104108RDP6PAP:P:n01101000150107105106104108R@P3PbG2PFPFPEPcPTP0PCP0PCP=PL13cYS0En0100000020000P0PC%;MPL13cMR?n010000002000054UA=;BW96BdRoA6BdhRpn0100000020000PXPePaF1P[E8n200110?00012110110;PiPjPkn10110200031010=0000PaPT1Db>PVPnPXPQPRG2#:50N]0P3P0PCP\PL13QHn0100000020000R\97GLQ0AP0P0P0PCP3PL13dWRnn0100000020000S0F97YLP7POPNP2P6PEPPPFPFPEPcPTP0PCP0PCP:PLP?n0100000020000S0G94ULPoPpn0100000020000PXPePaF1P[C9POQ0BQ0CQ0DPVPDP@P3PdG2R?PFPFPEfFRqPTP0PCP0PCP=PL13qUn0100000020000S0H94QLfERrA=;BY56BS0IA6BrhS0Jn0100000020000PX15CaRsPcF1P[E8n200110?00012110110;PiPjPkn10110200031010=0000PcPT1Dd>PVPePXPaPbG2#:Rt50N]0P3A7MLLP7POPNP2P6PEPPPFPFPEPcPTP0PCP3PoPpn0100000020000PXPePaF1P[C9POP?PFPFPEPqPTP0PCP1Q0IQ0Jn0100000020000PXPsPcF1P[E8n200110?00012110110;PiPjPkn10110200031010=0000=0NtX10RuPC1Da>RvP7POPNP2P6PEPPPFPFPEPcPTP3PXPePaF1P[C9POP?PFPFPEPqPTP1PXPsPcF1P[E8n200110?00012010110;PiPjPkn10110200031010=0000=0NtX1CPdPTPvPV15CRRvPXPbPQG2#:Rw,pNA6BahRx%oaELP7POPNP2P6PEPPPFPFPEPdPTPxPXPvPbF1P[C9POQ0BQ0CQ0DPVPDP@P3PaG2RyPFPFPEPrPTA6BchRzPX15CbR{PdF1P[E8n200110?00012110110;PiPjPkn10110200031010=0000=0NweR|A4YLLR}P3C?P7POPNP2P6PEPPPFPFPEPdPTP0PCP}A=;BG96BaR}Pxn0100000020000PXPvPbF1P[C9POPyPFPFPEPrPTP0PCA4RLLA=;BM96BcR~Pzn0100000020000PXP{PdF1P[E8n200110?00012110110;PiPjPkn10110200031010=0000=0NweW0A7MLmPuP|A4YLnS0KP3C?P7POPNP2P6PEPPPFPFPEPdPTP0PCQ0KP}Pxn0100000020000PXPvPbF1P[C9POPyPFPFPEPrPTP0PC13rYS0K94RLP~Pzn0100000020000PXP{PdF1P[E8n200110?00012110110;PiPjPkn10110200031010=0000=0NweW0n0110001020101P:O1b1W013Q^=7G\Q0AP0P013dMR\Q0F57YP7POPNP2P6PEPPPFPFPEPcPTP0PCQ0EQ0G54UPoPpn0100000020000PXPePaF1P[C9POP?PFPFPEPqPTP0PC13qRQ0H54QQ0IQ0Jn0100000020000PXPsPcF1P[E8n200110?00012110110;PiPjPkn10110200031010=0000=0Nt]0P3A7MgLPuP|A4Y\LRtP3C?P7POPNP2P6PEPPPFPFPEPdPTP0PCPtP}Pxn0100000020000PXPvPbF1P[C9POPyPFPFPEPrPTP0PC13rURt=4RLP~Pzn0100000020000PXP{PdF1P[E8n200110?00012110110;PiPjPkn10110200031010=0000=0NweW0A7MgmPuP|A4Y\nR\P3C?P7POPNP2P6PEPPPFPFPEPdPTP0PCP\P}Pxn0100000020000PXPvPbF1P[C9POPyPFPFPEPrPTP0PCQ0K94RtP~Pzn0100000020000PXP{PdF1P[E8n200110?00012110110;PiPjPkn10110200031010=0000=0NweW0n0110001020101P:O1b1W0n0110001020101P:O1b1b0b0P7POPNP2P6PEPPPFPFPEPYPYPTPMPV15C^RwPXPWPGG2R{#ARzP0PCQ0<P0PC%;4PLQ0=n010000002000054lA=;B<96BMA6BMhn0100000020000%@{R<PwPWF1P[C9POQ0BQ0CQ0DPVPDP@P3PMG2PFPFPEPR%AZP0PCQ0>P0PCQ0@PLQ0?n010000002000054^A=;B596BUA6BUhn0100000020000%@ZQ01PYF1P[E8n200110?00012110110;PiPjPkn10110200031010=0000PYPT1DM>R>PVPwPXPWPGG2#:Rw50NeP7POPNP7Q03PPQ0;%E{Pz%M{P<%N{DG5Uh%J{Rh5PUP2P6PEPPQ05Q06Q07Q08PVQ09Q0:P3PQPTPRPV15CMPXPUPYG2R<#FG2=COfn200110?00012010110;P_P`n10110?00031010=0000PiPjPkn10110200031010=0000=0Nwe%XHRzP:ELP7POPNP9PKPPPzP2PIPJPPP3P7Q03PPQ04%E<%A<%M<%@<%N<DG7U:%J<5PbP2P6PEPPQ05Q06Q07Q08PVQ09Q0:P3PdPTPaPVPvPXPbPQG2#FG2=COfn200110?00012010110;P_P`n10110?00031010=0000n200110<00012110910:P0PP%eHP_P`n0100000020000n10110?00021110<00PiPjPkn10110200031010=0000=0Nwe%]HP1C?AQU{H,O8=0NwRHePHe1RUMP=ELP9PAPP%t{R=,RUAQR]3R]P9PAPPA`Uh=P]P9PAPPA_Uh=P]P7P8PPA^Uh=Q02P_P`n10110?00031010>0000n10110?00021010300n10110?00021010301n10110?00021010301,O8=0Nwe1aU{=0NwePSPYPMPWPGP^Eg,aUPSPYP>PWPGP^Eg#:50NeW0W3W4W5W7W>W=W6W@X:CX<EW8X9CW;W?o"). Qed.

Lemma step_bne_tk_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (btgt pc (bv_signed imm)) mem rom r).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "h02Hch12Hdh22Heh32Hfh41bh53immh63memh72pch81rh94regsh:3romh;3rs1h<3rs2h=4segsh>1wp;1p;2p;3p;4p;6p;?p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0g006GR0p4p710R6p8p1006ep4p710R7P3p8P7P6p8p1007Bp4p70R8P1p8P8p10080p4p7210p8P8P3p8P8p1008Lp4p710R1p8P8P7p8P8P4p8P8P5p8P8p1009Bp4p710R7p8P8P6p8P8p1009cp4p710p8P8p100:@p4p710p8P8p100;9p6051001R9p8P8p100<<p4p7210p8P8p100<Yp4p710p8g00=6R8p4p7210R:P3p8P:P4p8P:P5p8P:P6p8P:p100=bp4p710p8P2P6p8P9P3p8P9P1p8P9P4p8P9P5p8P9P7p8P9P6p8P9p100>ip4p710p8p100?Kp60521000R9p100@Up4p710R7p8p100APp6051000R1P7p8p100BVp6051000R2P7p8p100CZp4p70R7P3p8P7P4p8P7P5p8P7P6p8p100DPp4p7511110R6P9p8P6P1p8P6P2p8g00I_j1GTg00EQj10Tg00F6j16Tg00F[j12Tg00G9j13TP8j2@Tg00G\j15Tg00J?j2<Tg00KAj27Tg00Kcj31Tg00L=j18Tg00M=j29Tg00M]j1:Tg01e7j4FTg00O:j1ETg00OXj4DTg00P8j24Tg01iUj2?Tg01>Bj1>Tg00H`j2=Tg00`2j3ATP0j6BTg01g=j3;Tg01jGl?CTg01O8#Gg00I:R0#0R8#6#2R2%08R8#0R6#0#0R1#0#2R9#3R7'@%26#3#5\7R6%21#3R1%32R2%60#0#6#2#3%51f9R0f7R5'<f3R4,7131g01P7R1f4R3#8g01PWR:31g01Q7R;g01QcR<'9R=#5f5R>#:P;P<g01kNR<P3P4f2R;CF%E8CD,7=31f;R=/4>14=3'?=11:f=f<R8P=f:P0f8P5P<f6R5P>P3P4P;f1P1P:f0R:#>g01c>R;511X411=1;1485R5148>R85A9P:EBA;<58=11;eM?CW0W1W2W3W5X<2W;W>X87X:6W6X77W9W=o"). Qed.

Lemma step_bne_ft_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "h02Hch12Hdh22Heh32Hfh41bh53immh63memh72pch81rh94regsh:3romh;3rs1h<3rs2h=4segsh>1wp;1p;2p;3p;4p;6p;?p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0g006GR0p4p710R6p8p1006ep4p710R7P3p8P7P6p8p1007Bp4p70R8P1p8P8p10080p4p7210p8P8P3p8P8p1008Lp4p710R1p8P8P7p8P8P4p8P8P5p8P8p1009Bp4p710R7p8P8P6p8P8p1009cp4p710p8P8p100:@p4p710p8P8p100;9p6051001R9p8P8p100<<p4p7210p8P8p100<Yp4p710p8g00=6R8p4p7210R:P3p8P:P4p8P:P5p8P:P6p8P:p100=bp4p710p8P2P6p8P9P3p8P9P1p8P9P4p8P9P5p8P9P7p8P9P6p8P9p100>ip4p710p8p100?Kp60521000R9p100@Up4p710R7p8p100APp6051000R1P7p8p100BVp6051000R2P7p8p100CZp4p70R7P3p8P7P4p8P7P5p8P7P6p8p100DPp4p7511110R6P9p8P6P1p8P6P2p8g00I_j1HTg00EQj10Tg00F6j17Tg00F[j11Tg00G9j12TP8j2@Tg00G\j16Tg00J?j2<Tg00KAj28Tg00Kcj33Tg00L=j19Tg00M=j2:Tg00M]j1GTg01e7j4FTg00O:j1ETg00OXj4?Tg00P8j24Tg01iUj2>Tg01>Bj1=Tg00H`j2ATg00`2j3BTP0j6;Tg01g=j3CTg01l@l?DTg01P7R0f0R8g01PWR233p=5g01O8#Hg00I:R6#0R1#7#1R9%01R1#0R7#0#0R5#0#1R4#2R3'@%17#2#6\3R7%15#2R5%29R9%76#0#7#1#2%65f9R6f7R:'<f3R;,8533f4R5#9#5g01Q7R<g01QcR=':R>#6f5R?#GP<P=g01kNR=P5P;f2R<CF%E1C?,8>33f;R>/4?14>5'>g01c>R1530f=f<R@P>f:P6f8P:P=f6R:P?P5P;P<f1P0P1%=8#5X401A0214@:R:14@?R@5B4P8E;AC=:@#5eM?DW0W1W2W3W5X<9W;W>X83X:7W6X73W9W=o"). Qed.

Lemma step_beq_tk_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (btgt pc (bv_signed imm)) mem rom r).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "h02Hch12Hdh22Heh32Hfh43immh53memh62pch71rh84regsh93romh:3rs1h;3rs2h<4segsh=1wp;1p;2p;3p;4p;?p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0p1006Gp4p710R0p8p1006ep4p710R6P3p8P6P0p8p1007Bp4p70R7P1p8P7p10080p4p7210p8P7P3p8P7p1008Lp4p710R1p8P7P6p8P7P4p8P7P5p8P7p1009Bp4p710R6p8P7P0p8P7p1009cp4p710p8P7p100:@p4p710p8P7p100;9p6051001R8p8P7p100<<p4p7210p8P7p100<Yp4p710p8g00=6R7p4p7210R9P3p8P9P4p8P9P5p8P9P0p8P9p100=bp4p710p8P2P0p8P8P3p8P8P1p8P8P4p8P8P5p8P8P6p8P8P0p8P8p100>ip4p710p8p100?Kp60521000R8p100@Up4p710R6p8p100APp6051000R1P6p8p100BVp6051000R2P6p8p100CZp4p70R6P3p8P6P4p8P6P5p8P6P0p8p100DPp4p7511110R0P8p8P0P1p8P0P2p8g00I_j1BTg00EQj10Tg00F6j14Tg00F[j11Tg00G9j12TP7j2<Tg00G\j15Tg00J?j2;Tg00KAj26Tg00Kcj33Tg00L=j18Tg00M=j29Tg00M]j1:Tg01e7j4ATg00O:j1@Tg00OXj4?Tg00P8j27Tg01iUj2=Tg01jGl?>Tg01O8#Bg00I:R7#0R2#4#1R0%02R2#0R1#0#0R8#0#1#2R6'<%11#2#5\6R1%18#2R8%20R0%47#0#4#1#2%58f9R7f7R5';f3R4,6833g01P7R8f4R3#8g01PW33g01Q7R9g01QcR:'9R;#5f5R<#:P9P:g01mGR:P3P4f2R9CA%@2C?,6;33f;R;/7<17;3'=g01c>538f=f<P;f:P7f8P5P:f6P<P3P4P9f1f0M?>W0W1W2W3W4X;0W:W=X76X91W5X66W8W<o"). Qed.

Lemma step_beq_ft_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "h02Hch12Hdh22Heh32Hfh43immh53memh62pch71rh84regsh93romh:3rs1h;3rs2h<4segsh=1wp;1p;2p;3p;4p;?p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0p1006Gp4p710R0p8p1006ep4p710R6P3p8P6P0p8p1007Bp4p70R7P1p8P7p10080p4p7210p8P7P3p8P7p1008Lp4p710R1p8P7P6p8P7P4p8P7P5p8P7p1009Bp4p710R6p8P7P0p8P7p1009cp4p710p8P7p100:@p4p710p8P7p100;9p6051001R8p8P7p100<<p4p7210p8P7p100<Yp4p710p8g00=6R7p4p7210R9P3p8P9P4p8P9P5p8P9P0p8P9p100=bp4p710p8P2P0p8P8P3p8P8P1p8P8P4p8P8P5p8P8P6p8P8P0p8P8p100>ip4p710p8p100?Kp60521000R8p100@Up4p710R6p8p100APp6051000R1P6p8p100BVp6051000R2P6p8p100CZp4p70R6P3p8P6P4p8P6P5p8P6P0p8p100DPp4p7511110R0P8p8P0P1p8P0P2p8g00I_j1BTg00EQj10Tg00F6j14Tg00F[j11Tg00G9j12TP7j2<Tg00G\j15Tg00J?j2;Tg00KAj26Tg00Kcj33Tg00L=j18Tg00M=j29Tg00M]j1:Tg01e7j4ATg00O:j1@Tg00OXj4?Tg00P8j27Tg01iUj2=Tg01l@l?>Tg01O8#Bg00I:R7#0R2#4#1R0%02R2#0R1#0#0R8#0#1#2R6'<%11#2#5\6R1%18#2R8%20R0%47#0#4#1#2%58f9R7f7R5';f3R4,6833g01P7R8f4R3#8g01PWR933g01Q7R:g01QcR;'9R<#5f5R=#:P:P;g01mGR;P3P4f2R:CA%@2C?,6<33f;R</7=17<3'==389f=f<P<f:P7f8P5P;f6P=P3P4P:f1f0M?>W0W1W2W3W4X;0W:W=X76X91W5X66W8W<o"). Qed.

(* [comment removed for export] *)
Lemma step_opimm_r : forall segs regs pc mem rom r w op rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs
                     else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                    (v_addi pc 4) mem rom r).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "p'0h01bi001bh11oh27Hdecodeh36Hecallh46Hfetchh53immh63memh72oph82pch91ri011rh:2rdh;4regsh<3romh=2rsh>4segsh?1wi021wi031ci046c_fcsri057c_fregsi064c_pci076c_regsi086c_resvi091ii0:3iszi0;2m'i0<1pi0=6reporti0>3st'i0?1xp%0p&0p;1p;2p;3p;4p;8p;5p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0g006GR0p4p710R6p8p1006ep4p710R7P3p8P7P6p8p1007Bp4p70R8P1p8P8p10080p4p7210p8P8P3p8P8p1008Lp4p710R1p8P8P7p8P8P4p8P8P5p8P8p1009Bp4p710R7p8P8P6p8P8p1009cp4p710p8P8p100:@p4p710p8P8p100;9p6051001R9p8P8p100<<p4p7210p8P8p100<Yp4p710p8g00=6R8p4p7210R:P3p8P:P4p8P:P5p8P:P6p8P:g00=bR:p4p710p8P2P6p8P9P3p8P9P1p8P9P4p8P9P5p8P9P7p8P9P6p8P9p100>ip4p710p8p100?Kp60521000R9p100@Up4p710R7p8p100APp6051000R1P7p8p100BVp6051000R2P7p8p100CZp4p70R7P3p8P7P4p8P7P5p8P7P6p8p100DPp4p7511110R6P9p8P6P1p8P6P2p8g00I_k100Tg00EQj19Tg00F6j1\Tg00F[j1HTg00G9j1CTP8j2}Tg00G\R8j1LTg00J?j2XTg00KAj24Tg00Kcj32Tg00L=j1bTg00M=R2j2`Tg00M]j1TTg01n9j4pTg00O:j1oTg00OXj4GTg00TAR6j1nTP:j1mTg00bEj1yTg00H>j1vTg00cnj1tTg00k\j81Tg00V;j3YTg00WGj1OTg00XEj3iTg00YJj3fTg00ZPj3eTg00[Uj1qTg00\5j1dTg00]=j1cTg00^Ej2WTg00_Oj3aTg00`2j3VTg00P8j2_Tg01?mj3?Tg01nej3ITg00aQj3KTg00c:j2MTg00dbj1STg00eaj1JTg00faj1RTg00gbj2~Tg00h`j1QTg00i_j1FTg00j^j1PTg00lcj2^Tg00mIj50Tg00n2j3]Tg00nYj3UTg00odj2NTg010hj1|Tg011Qj1{Tg012;j1zTg012bj1xTg013Kj1wTg0144j2[Tg015;j1hTg0164j1>Tg01?Hj3<Tg01<jj2@Tg00H`j2ZTg01C5j1sTP0j6:Tg01@Xj5gTg01FJj1jTg01GEj1rTg01HBj2kTg01I>j6lTg01J;j3;Tg016\j2=Tf2R0g01LKR:f1R1f0R93;'=p=Bf7R7f6R5f5R4f4R3f3R;P0P1P9G1,=:p=A1=:9p=uP5P4P3AI;01P9Dgp=3g01MRR<P;P0P1CG=;39,N4p=6P<P;P0P1CG=;39,[49;:5,=7p=81=:99201p=5P<P5P4P3P;P0P1D0P9CGp=7A;019,N;p=DA;019,[;9;:3,=4p=Eg01O8$00g00I:R=#9R>#\#HR?%9>R>#9R@#9#9RA#9#HRB#CRC'}RD%H@#C#L\CRE%HA#CRAg01oM%C?S00Q00%\=#9#9#HR=#C%LARFf:RGf8RH'X14A332g01P7RI%b4g01PWRJ32g01Q7RKg01QcRL'`RM#LRN%T5PKPLP4P3P;P0Cp%o>R>CG,4M32PF14A7%n:ROP8PA%m:RP#nRQP9f?RRf>RSp,2fxRT#yRUf=RV%vCRW14CGRX%tTRYf<RZf;R[G1R\;Y9R]P8PAPQPVPUPZPWf9R^,4CR_PYP[PGG1R`#ORa=iSZP]P8PAPQAfSaZP]P6P:PQAeSaZg01Sk#qR]9BP9S01%dPRb%cPRcn10110?00031010>0000n10110?00021010200n10110?00021010200n10110?00021010201,W:PIPDg01RnRdg01U0Re5a?Rf9V?5PV1_V4A?=B3Rg5I79KV5Rhn0100000020000PU1MZ>RiPWP_PYP[PGGARj32X1FPIPJP6PPPOPIPQP9%S`%J`RJ%R`%\@#o=a?e,~`,4C%Q`%F`RePa%P`G1=BP]P8PMPQ%THP2PKPLPQP9P61`<ERa#mS02PQfAR@1^B9S03f@RFPUPRPW14CZRkPYPSPVG1Rl#S%Jl%Rl%Fl%QlD07]1%Ol3UP2P<PEPQ1Na9S04%|1S05%{1S06%z1S07PW%x1S08%w1S09P9fCPUfBS0:PW14CRPYP@PFG1#PG11[a0Rl5BPn200110?00012010310;PbPcn10110?00031010=0000n200110<00012110910:RmPIPQ%hHPbPcn0100000020000Rnn10110?00021110<00n01000000201011N:9#uRo%d:Rp%c:Rqn10110100031010=0000=2OjX0IPNPKPLP5P4P3P;CpS0;P>CG,4MP6PPPOP8PMPQP9PmPnn10110?00021110<00PoPpPqn10110100031010=0000=2OjX1NPI%>4RNP6PPPOP2P<PEPQPaPaPEPIP<%>5RjPVPJ1^B>Rn9<BZRmPeP_D0P?PCP5P7PIPCPN1^BdRd1@V4S0<n0100000020000PgPVF3RrPJPmPeP_D0n0100000020000P[P]E6PPP<PDP1P3n01103000150107105106104108S0=P<PDP1P;n01103000150107105106104108S0>P<PCP1P0n01103000150107105106104108S0?PWP<%LCP1P9n01103000150107105106104108S0@P<PAP1P1n01103000150107105106104108S0AP9PZG1RePaPaPEPIP<%>HRJPRPRPUPSPW14C[RsPYPVPZG1Rt#JS0BA<BSnRu%FtS0CPsD0P?PCPHP^PIPC%>7RvPd1@R7S0Dn0100000020000A?=B5S0EPRF3RwQ0BPuQ0CPsD0n0100000020000PVP]G8n200110?00012110310;PoPpPqn10110100031010=0000PIPDP9PVPhn0100000020000PUPiPWP_PYP[PGG155OX0IPI%>3S0FP6PPPOP2P<PEPQPaPaPEPIP<PjPVPUPmPYP_D0S0GPrPUPmPYP_D0n0100000020000P[P]E6PPPePaPaPEPIP<PJPRPUPuPYPsD0RrPwPUPuPYPsD0n0100000020000PVP]G8n200110?00012110310;PoPpPqn10110100031010=0000PIPDPjPVPIPCP9PdQ0<n0100000020000=I7g9KV5n0100000020000PUPiPWP_PYP[PGG155OX0IQ0FPIPIP6PPPOP2P<PEPQPaPaPEPIP<PvPSPUA<BVnRwPYPXD0S0HP?PCP7PHPIPCP9Pd1@S5S0In0100000020000A?=B4RhPSF3RxPUPwPYPXD0n0100000020000PZP]E6PPQ0=Q0>Q0?PWQ0@Q0AP9PVG1RyPaPaPEPIP<%>^PFPUA<BRnRzPYPkD0S0JP?PCP^PGPIPCP0Pd1@FHS0Kn0100000020000A?=B7S0LPFF3PUPzPYPkD0n0100000020000PSP]G8n200110?00012110310;PoPpPqn10110100031010=0000PIPDPvPSPxn0100000020000PU1MV>RxPWPXPYPZP[G155OP9PjPIPIP6PPPOP2P<PEPQPaPaPEPIP<P9PrP?PCPHP^PdQ0EPRF3R{PUPuPYPsD0S0Mn0100000020000PVP]E6PPQ0=Q0>Q0?PWQ0@Q0AP9PSG1R|PaPaPEPIP<P0P@PUA<BFnS0NPY14CVR}D0S0OP?PCPGP[PdA?=BHS0PP@F3S0QPUQ0NPYP}D0n0100000020000PRP]G8n200110?00012110310;PoPpPqn10110100031010=0000PIPDP9PRP{n0100000020000PU1MS>R~PWPsPYPVPZG155OP9PCPxP6PPPOP2P<PEPQPaPaPEPRPUP9PYPsPVF7P]CDPPP|PaPaPEP@PUP0PYP}PRF7P]EEn200110?00012010310;PoPpPqn10110100031010=0000PRPUP~PWPsPYPVPZG155OX0CPSPUPxPWPXPYPZP[GAS0R,ZOPw%sVS0SE:P6PPPOP2P<PEPQPaPaPEQ0HPZP]E6PPPyPaPaPEQ0JPSP]G8n200110?00012110310;PoPpPqn10110100031010=0000Q0R52OeS0RPCPxP6PPPOP2P<PEPQPaPaPEP{PUP9PYPsPVF7P]CDPPP|PaPaPEQ0QPUP0PYP}PRF7P]EEn200110?00012110310;PoPpPqn10110100031010=0000P{PUP~PWPsPYPVPZG155OX0CP?PCP7PHPdPhPSF3S0QPUPxPWPXPYPZP[GAR{,ZOPwQ0SE:P6PPPOP2P<PEPQPaPaPEQ0QPUPwPYPXPZF7P]CDPPPyPaPaPEP?PCP^PGPdQ0LPFF3PUPzPYPkPSF7P]EEn200110?00012110310;PoPpPqn10110100031010=0000=2O{en0110001020101b0P6PPPOP2P<PEPQPaPaPEPIP<PjQ0GP?PCP5P7PdPgPVF3R{PUPmPYP_D0n0100000020000P[P]E6PPPePaPaPEPIP<PJPrQ0Mn0100000020000PVP]G8n200110?00012110310;PoPpPqn10110100031010=0000PIPDPjPVP{n0100000020000PUPiPWP_PYP[PGG155OePjPIPIP6PPPOP2P<PEPQPaPaPEPIP<P9PrP?PCPHP^Q0DQ0EPRF3R{PUPuPYPsD0S0En0100000020000PVP]E6PPP|PaPaPEPIP<P0Q0OP?PCPGP[1@@^Q0PP@F3RuPUQ0NPYP}D0n0100000020000PRP]G8n200110?00012110310;PoPpPqn10110100031010=0000PIPDP9PRP{n0100000020000PUP~PWPsPYPVPZG155OP9Q0RPCPxP6PPPOP2P<PEPQPaPaPEP{PUP9PYPsPVF7P]CDPPP|PaPaPEPuPUP0PYP}PRF7P]EEn200110?00012110310;PoPpPqn10110100031010=0000P{PUP~PWPsPYPVPZG155OX0CP?PCP7PHQ0IPhPSF3RsPUPxPWPXPYPZP[GARx,ZOPwQ0SE:P6PPPOP2P<PEPQPaPaPEPsPUPwPYPXPZF7P]CDPPPyPaPaPEP?PCP^PGQ0KQ0LPFF3PUPzPYPkPSF7P]EEn200110?00012110310;PoPpPqn10110100031010=0000=2Oxen0110001020101b0P6PPPOP2P<PEPQPaPaPEPIP<PjQ0GP?PCP5P7Q0<PgPVF3RgPUPmPYP_D0n0100000020000P[P]E6PPPePaPaPEPIP<PJPrQ0En0100000020000PVP]G8n200110?00012110310;PoPpPqn10110100031010=0000PIPDPjPVPgn0100000020000PUPiPWP_PYP[PGG155Oen0110001020101b0P6PPPOP2P<PEPQPaPaPEPIP<PNPZPUA<B[nR_PY14CHRiD0P?PCP4PIPCQ0FPd1@Z3n0100000020000A?=B;R=5I5RBPZDgR;PUP_PYPiD0n0100000020000PGP]E6PPQ0=Q0>Q0?PWQ0@Q0AP9P[G1RgPaPaPEPIP<PvQ0HP?PCP7PHPIPCPjPdQ0In0100000020000PhPSF3RhPUPwPYPXD0n0100000020000PZP]G8n200110?00012110310;PoPpPqn10110100031010=0000RdPIPDPNPZAKZ4Bn0100000020000PU1M[>R>PWPiPYPGP^G155OeAV?3f%j3E:PIPDPNPZ1_Z3=I5=9KZ4R=n0100000020000PUP>PWPiPYPGP^GAR592OdeP6PPPOP2P<PEPQPaPaPEPIP<PNPZPZPUP[PWPiPYPGP^G1RN#JRdP_%FNR3PiD0P;PdP_P3PiD0n0100000020000PGP]E6PPPgPaPaPEPIP<PvPS%J\RvPw%F\R\PXD0PhPvPwP\PXD0n0100000020000PZP]G8n200110?00012110310;PoPpPqn10110100031010=0000=2O5eAV?4fRf%j4E:P6PPPOP6Q02PQQ0;%SNPd%RNP3%QND05]n%ONRn5UVP2P<PEPQQ04Q05Q06Q07PWQ08Q09P9%PtG1=BPln200110?00012010310;PbPcn10110?00031010=0000PoPpPqn10110100031010=0000PIPDPfPZP=n0100000020000R=PUP>PWPiPYPGP^GARi52Oe%T7RfP9E:P6PPPOP8PMPQPfP2PKPLPQP9P6Q02PQQ03%StQ0B%RtQ0C%QtD07]1%Ot5UFP2P<PEPQQ04Q05Q06Q07PWQ08Q09P9Q0:PUP@PW14CSPYPFPRG1#PG1=BPln200110?00012010310;PbPcn10110?00031010=0000n200110<00012110910:PIPQ%h7PbPcn0100000020000n10110?00021110<00PoPpPqn10110100031010=0000=2Oie%b7P1E:AYVN7,W:=2OiR7eP7e1XV[P0E:P8PAPQ%rNR0,XVAYS`9R`P8PAPQAiVn0P`P8PAPQAfVn0P`P6P:PQAeVn0Q01PbPcn10110?00031010>0000n10110?00021010200n10110?00021010201n10110?00021010201,W:=2Oie1kVN=2OiePTPZP[PGP^PHEl,kVPTP=P>PGP^PHEl55OeW2W3W4W5W=W:W7W?X9CX<EW6X8CW;W>o"). Qed.

(* [comment removed for export] *)
Lemma step_op_r : forall segs regs pc mem rom r w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs
                     else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                    (v_addi pc 4) mem rom r).
Proof.
ltac2:(KReplay.run1 (kr_t_LibAtomic ()) ["FPX_2"] "p'0h01bi001bh11oh27Hdecodeh36Hecallh46Hfetchh53memh62oph72pch81ri011rh92rdh:4regsh;3romh<3rs1h=3rs2h>4segsh?1wi021wi031ci046c_fcsri057c_fregsi064c_pci076c_regsi086c_resvi091ii0:3iszi0;2m'i0<1pi0=6reporti0>3st'i0?1xp%0p;1p;2p;3p;4p;8p;5p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Up4p710R1p8P0p1002lR2p4p710p8P0P2p4p7210p8P0p1003Ip4p710R2p8P0p1003dp4p710p8p1004@p4p70R0p10050p4p710R3p8P0p1005Lp4p710R4p8P0p1005jp4p7210R5p8P0g006GR0p4p710R6p8p1006ep4p710R7P3p8P7P6p8p1007Bp4p70R8P1p8P8p10080p4p7210p8P8P3p8P8p1008Lp4p710R1p8P8P7p8P8P4p8P8P5p8P8p1009Bp4p710R7p8P8P6p8P8p1009cp4p710p8P8p100:@p4p710p8P8p100;9p6051001R9p8P8p100<<p4p7210p8P8p100<Yp4p710p8g00=6R8p4p7210R:P3p8P:P4p8P:P5p8P:P6p8P:g00=bR:p4p710p8P2P6p8P9P3p8P9P1p8P9P4p8P9P5p8P9P7p8P9P6p8P9p100>ip4p710p8p100?Kp60521000R9p100@Up4p710R7p8p100APp6051000R1P7p8p100BVp6051000R2P7p8p100CZp4p70R7P3p8P7P4p8P7P5p8P7P6p8p100DPp4p7511110R6P9p8P6P1p8P6P2p8g00I_j1~Tg00EQj1ATg00F6j1fTg00F[j1MTg00G9j1TTP8j2|Tg00G\R8j1QTg00J?j2[Tg00KAj29Tg00Kcj34Tg00L=j1aTg00M=R2j2_Tg00M]j1VTg0209j4oTg00O:j1nTg00OXj4HTg00TAR6j1mTP:j1lTg00bEj1wTg00H>j1uTg00cnj1sTg00k\j81Tg00V;j3YTg00WGj1PTg00XEj3iTg00YJj3eTg00ZPj3dTg00[Uj1pTg00\5j1cTg00]=j1bTg00^Ej2WTg00_Oj3`Tg00`2j3OTg00P8j2LTg01nej3CTg00aQj3FTg00c:j2ITg00dbj1KTg00eaj1JTg00faj1UTg00gbj2}Tg00h`j1STg00i_j1GTg00j^j1RTg00lcj2^Tg00mIj50Tg00n2j3]Tg00nYj3\Tg00odj2NTg010hj1{Tg011Qj1zTg012;j1yTg012bj1xTg013Kj1vTg0144j2XTg015;j1hTg0164j1=Tg01?Hj3@Tg01<jj28Tg00H`j2ETg01C5j1rTP0j6:Tg01@Xj5gTg01FJj1ZTg01GEj1qTg01HBj2kTg01I>j6jTg01J;j3?Tg016\j2BTf2R0g01LKR:f1R1f0R93?'Bp=Df7R7f6R5f5R4f4R3f3R;P0P1P9G1,B:p=>1B:9p=tP5P4P3AC;01P9Dgp=2g01MRR<P;P0P1CH=?39,N4p=6P<P;P0P1CH=?39,X49?:5,B7p=71B:99401p=3P<P5P4P3P;P0P1D0P9CHp=5A?019,N;p=;A?019,X;9?:3,B4p=<g01O8#~g00I:#AR=#f#MR>%A=R=#AR?#A#AR@#A#MRA#TRB'|RC%M?#T#Q\BRD%M@#TR@g01oM%T>S00Q00Q00%Q@REf:RFf8RG'[19@334g01P7RH%a4g01PWRI34g01Q7S01g01QcS02'_RJ#QRK%V5Q01Q02P4P3P;P0Co%n=R=CH,9J34PE19@7%m:RLP8P@%l:RM#mRNP9f?ROf>RPp,2fxS03#wRQf=RR%uBRS19BFRTQ03#sRUf<RVf;RWG1S04;Y9RXP8P@PNPRPQPVPSf9RY,9BRZPUPWPFG1R[#PR\=iPVPXP8P@PNAeP\VPXP6P:PNAdP\Vg01Sk#pRX9DM9S05%cMR]%bMR^n10110?00031010>0000n10110?00021010200n10110?00021010200n10110?00021010201,W:PHPCg01RnR_g01U0R`5`>Ra9O>5PR1LR41LR35C79FR5Rbn0100000020000PQ1IV=RcPSPZPUPWPFG>Rd34X1EPHPIP6PMPLPHPNP9%K[%J[RI%U[%f?#n=`>`,}[,9B%S[%G[R`P\%R[G1=DMXP8PJPN%VGP2Q01Q02PNP9P61_<DR\#lS06PNfAR?1^A9S07f@REPQPOPS19BVRePUPPPRG1Rf#K%Jf%Uf%Gf%SfD07]1%Pf3\P2P<PDPN1N\9S08%{1S09%z1S0:%y1S0;PS%x1S0<%v1S0=P9fCPQfBRfPS19BOPUP?PEG1#RG11X\0S0>5DMn200110?00012010310;P]P^n10110?00031010=0000n200110<00012110910:RgPHPN%hGP]P^n0100000020000Rhn10110?00021110<00n01000000201011N:9#tRi%c:Rj%b:Rkn10110100031010=0000=4LdX0HPKQ01Q02P5P4P3P;CoS0?P=CH,9JP6PMPLP8PJPNP9PgPhn10110?00021110<00PiPjPkn10110100031010=0000=4LdX1KPH%=4RKP6PMPLP2P<PDPNP\P\PDPHP<%=5RdPRPI1^A=Rh9@AVRgP`PZD0P>PBP5P7PHPBPK1^A_R_18R4S0@n0100000020000RlPHPB%=3RmP_18R3Rnn0100000020000S0APRF2RoPIPgP`PZD0n0100000020000PWPXE6PMP<PCP1P3n01103000150107105106104108S0BP<PCP1P;n01103000150107105106104108S0CP<PBP1P0n01103000150107105106104108S0DPSP<%QBP1P9n01103000150107105106104108S0EP<P@P1P1n01103000150107105106104108S0FP9PVG1S0GP\P\PDPHP<%=GR`POPOPQPPPS19BWRIPUPRPVG1Rp#JS0HA@APhRq%GpS0IPID0P>PBPGPYPHPB%=7RrP_18O7S0Jn0100000020000PHPBPdP_18O5S0Kn0100000020000S0LPOF2RsQ0HPqQ0IPID0n0100000020000PRPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCP9PRPbn0100000020000PQPcPSPZPUPWPFG153LX0HPHPmP6PMPLP2P<PDPNP\P\PDPHP<PdPRPQPgPUPZD0S0MPoPQPgPUPZD0n0100000020000PWPXE6PMQ0GP\P\PDPHP<P`POPQPqPUPID0RoPsPQPqPUPID0n0100000020000PRPXG7n200110?00012110310;PiPjPkn10110100031010=0000RsPHPCPdPRPHPBP9P_Q0@n0100000020000PHPBAO>3aS0NP_Pnn01000000200005C79FR5n0100000020000PQPcPSPZPUPWPFG153LX0HPH%=;S0OPHPCPdPRPHPBP9P_Pnn01000000200009C7l9FR5n0100000020000PQPcPSPZPUPWPFG193LsX0HPmPHPHP6PMPLP2P<PDPNP\P\PDPHP<PrPPPQA@ARhRsPUPTD0RlP>PBP7PGPHPBP9P_18P5S0Pn0100000020000PHPBPKP_18P4S0Qn0100000020000S0RPPF2RnPQPsPUPTD0n0100000020000PVPXE6PMQ0BQ0CQ0DPSQ0EQ0FP9PRG1S0SP\P\PDPHP<%=YRbPEPQA@AOhRtPUPeD0RuP>PBPYPFPHPBP0P_18EGS0Tn0100000020000PHPBPrP_18E7S0Un0100000020000PEF2PQPtPUPeD0n0100000020000PPPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCPrPPPnn0100000020000PQ1IR=RnPSPTPUPVPWG153LP9PmPHPHP6PMPLP2P<PDPNP\P\PDPHP<P`PoP>PBPGPYP_PHPBP9P_Q0Kn0100000020000S0VPOF2RvPQPqPUPID0n0100000020000PRPXE6PMQ0BQ0CQ0DPSQ0EQ0FP9PPG1RwP\P\PDPHP<%=FS0WP?PQA@AEhRxPU19BRRyD0S0XP>PBPFPWP_PHPBP0P_18?GS0Yn0100000020000S0ZP?F2PQPxPUPyD0n0100000020000POPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCP`POPvn0100000020000PQ1IP=RvPSPIPUPRPVG153LP9PrPHPHP6PMPLP2P<PDPNP\P\PDPHP<P9PuP>PBPYPFP_P_PEF2S0[PQPtPUPeD0S0\n0100000020000PPPXE6PMQ0BQ0CQ0DPSQ0EQ0FP9POG1RzP\P\PDPHP<P0PfPQA@A?hR{PU19BPR|D0S0]P>PBPWPVP_P_PfF2S0^PQP{PUP|D0n0100000020000PEPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCP9PEQ0[n0100000020000PQ1IO=R}PSPePUPPPRG153LP9PBPvP6PMPLP2P<PDPNP\P\PDPEPQP9PUPePPF5PXC;PMPzP\P\PDPfPQP0PUP|PEF5PXE<n200110?00012010310;PiPjPkn10110100031010=0000PEPQP}PSPePUPPPRG153LX0BPOPQPvPSPIPUPRPVG>S0_,ELPq%rPR~E:P6PMPLP2P<PDPNP\P\PDPoPRPXE6PMPwP\P\PDQ0XPOPXG7n200110?00012110310;PiPjPkn10110100031010=0000Q0_54LeS0_PBPvP6PMPLP2P<PDPNP\P\PDQ0[PQP9PUPePPF5PXC;PMPzP\P\PDQ0^PQP0PUP|PEF5PXE<n200110?00012110310;PiPjPkn10110100031010=0000Q0[PQP}PSPePUPPPRG153LX0BP>PBPGPYP_P_POF2S0[PQPvPSPIPUPRPVG>S0^,ELPqP~E:P6PMPLP2P<PDPNP\P\PDQ0[PQPqPUPIPRF5PXC;PMPwP\P\PDP>PBPFPWP_P_P?F2PQPxPUPyPOF5PXE<n200110?00012110310;PiPjPkn10110100031010=0000Q0^54Len0110001020101b0P6PMPLP2P<PDPNP\P\PDPHP<PrPlP>PBP7PGP_P_PPF2S0^PQPsPUPTD0n0100000020000PVPXE6PMQ0SP\P\PDPHP<PbPuQ0\n0100000020000PPPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCPrPPQ0^n0100000020000PQPnPSPTPUPVPWG153LePrPHPHP6PMPLP2P<PDPNP\P\PDPHP<P9PuP>PBPYPFP_Q0UPEF2S0^PQPtPUPeD0S0\n0100000020000PPPXE6PMPzP\P\PDPHP<P0Q0]P>PBPWPVP_18fYS0[PfF2S0`PQP{PUP|D0n0100000020000PEPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCP9PEQ0^n0100000020000PQP}PSPePUPPPRG153LP9Q0_PBPvP6PMPLP2P<PDPNP\P\PDQ0^PQP9PUPePPF5PXC;PMPzP\P\PDQ0`PQP0PUP|PEF5PXE<n200110?00012110310;PiPjPkn10110100031010=0000Q0^PQP}PSPePUPPPRG153LX0BP>PBPGPYP_Q0KPOF2S0^PQPvPSPIPUPRPVG>S0`,ELPqP~E:P6PMPLP2P<PDPNP\P\PDQ0^PQPqPUPIPRF5PXC;PMPwP\P\PDP>PBPFPWP_Q0YP?F2PQPxPUPyPOF5PXE<n200110?00012110310;PiPjPkn10110100031010=0000Q0`54Len0110001020101b0P6PMPLP2P<PDPNP\P\PDPHP<PrPlP>PBP7PGP_Q0QPPF2S0`PQPsPUPTD0n0100000020000PVPXE6PMQ0SP\P\PDPHP<PbPuQ0\n0100000020000PPPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCPrPPQ0`n0100000020000PQPnPSPTPUPVPWG153Len0110001020101b0P6PMPLP2P<PDPNP\P\PDPHP<PdQ0MP>PBP5P7P_Q0APRF2S0`PQPgPUPZD0n0100000020000PWPXE6PMQ0GP\P\PDPHP<P`PoP>PBPGPYP_Q0LPOF2PQPqPUPID0n0100000020000PRPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCPdPRQ0`n0100000020000PQPcPSPZPUPWPFG153LePmPHPHP6PMPLP2P<PDPNP\P\PDPHP<P`PoP>PBPGPYQ0JQ0VPOF2S0VPQPqPUPID0n0100000020000PRPXE6PMPwP\P\PDPHP<Q0WQ0XP>PBPFPW18?YS0XQ0ZP?F2PQPxPUPyD0n0100000020000POPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCP`POQ0Vn0100000020000PQPvPSPIPUPRPVG153LP9PrPHPHP6PMPLP2P<PDPNP\P\PDPHP<P9PuP>PBPYPFQ0TP_PEF2S0VPQPtPUPeD0S0Zn0100000020000PPPXE6PMPzP\P\PDPHP<P0Q0]P>PBPWPV18fFS0WP_PfF2S0`PQP{PUP|D0n0100000020000PEPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCP9PEQ0Vn0100000020000PQP}PSPePUPPPRG153LP9Q0_PBPvP6PMPLP2P<PDPNP\P\PDQ0VPQP9PUPePPF5PXC;PMPzP\P\PDQ0`PQP0PUP|PEF5PXE<n200110?00012110310;PiPjPkn10110100031010=0000Q0VPQP}PSPePUPPPRG153LX0BP>PBPGPYQ0JP_POF2S0VPQPvPSPIPUPRPVG>S0`,ELPqP~E:P6PMPLP2P<PDPNP\P\PDQ0VPQPqPUPIPRF5PXC;PMPwP\P\PDP>PBPFPWQ0XP_P?F2PQPxPUPyPOF5PXE<n200110?00012110310;PiPjPkn10110100031010=0000Q0`54Len0110001020101b0P6PMPLP2P<PDPNP\P\PDPHP<PrPlP>PBP7PGQ0PP_PPF2S0`PQPsPUPTD0n0100000020000PVPXE6PMQ0SP\P\PDPHP<PbPuQ0Zn0100000020000PPPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCPrPPQ0`n0100000020000PQPnPSPTPUPVPWG153LePrPHPHP6PMPLP2P<PDPNP\P\PDPHP<P9PuP>PBPYPFQ0TQ0UPEF2S0UPQPtPUPeD0S0Tn0100000020000PPPXE6PMPzP\P\PDPHP<P0Q0]P>PBPWPVQ0WQ0[PfF2RtPQP{PUP|D0n0100000020000PEPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCP9PEQ0Un0100000020000PQP}PSPePUPPPRG153LP9Q0_PBPvP6PMPLP2P<PDPNP\P\PDQ0UPQP9PUPePPF5PXC;PMPzP\P\PDPtPQP0PUP|PEF5PXE<n200110?00012110310;PiPjPkn10110100031010=0000Q0UPQP}PSPePUPPPRG153LX0BP>PBPGPYQ0JQ0KPOF2RePQPvPSPIPUPRPVG>Rv,ELPqP~E:P6PMPLP2P<PDPNP\P\PDPePQPqPUPIPRF5PXC;PMPwP\P\PDP>PBPFPWQ0XQ0YP?F2PQPxPUPyPOF5PXE<n200110?00012110310;PiPjPkn10110100031010=0000=4Lven0110001020101b0P6PMPLP2P<PDPNP\P\PDPHP<PrPlP>PBP7PGQ0PQ0QPPF2RvPQPsPUPTD0n0100000020000PVPXE6PMQ0SP\P\PDPHP<PbPuQ0Tn0100000020000PPPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCPrPPPvn0100000020000PQPnPSPTPUPVPWG153Len0110001020101b0P6PMPLP2P<PDPNP\P\PDPHP<PdQ0MP>PBP5P7Q0@Q0APRF2RnPQPgPUPZD0n0100000020000PWPXE6PMQ0GP\P\PDPHP<P`PoP>PBPGPYQ0JQ0LPOF2PQPqPUPID0n0100000020000PRPXG7n200110?00012110310;PiPjPkn10110100031010=0000PHPCPdPRPnn0100000020000PQPcPSPZPUPWPFG153Len0110001020101b0P6PMPLP2P<PDPNP\P\PDPHP<PKPVPQA@AWhRAPU19BGRZD0P>PBP4PHPBPmP_18V3n0100000020000PHPBQ0OP_18V;n01000000200005C5RmPVDgRcPQPAPUPZD0n0100000020000PFPXE6PMQ0BQ0CQ0DPSQ0EQ0FP9PWG1RnP\P\PDPHP<PrPlP>PBP7PGPHPBPdP_Q0Pn0100000020000Q0RPPF2R_PQPsPUPTD0n0100000020000PVPXG7n200110?00012110310;PiPjPkn10110100031010=0000RdPHPCPKPVAFV4mn0100000020000PQ1IW=R=PSPZPUPFPYG153LeAO>;a%Z;E:Q0N%Z3E:PHPCPKPV1LV31LV;5C59FV4R5n0100000020000PQP=PSPZPUPFPYG>R;94LdeP6PMPLP2P<PDPNP\P\PDPHP<PKPVPVPQPWPSPZPUPFPYG1RK#JRdPA%GKR3PZD0PcPdPAP3PZD0n0100000020000PFPXE6PMPnP\P\PDPHP<PrPPQ04#JRrPsQ04#GR\PTD0P_PrPsP\PTD0n0100000020000PVPXG7n200110?00012110310;PiPjPkn10110100031010=0000=4L;eAO>4aRa%Z4E:P6PMPLP6Q06PNQ0?%KKPd%UKP3%SKD05]h%PKRh5\RP2P<PDPNQ08Q09Q0:Q0;PSQ0<Q0=P9%RpG1Q0>5DMn200110?00012010310;P]P^n10110?00031010=0000PiPjPkn10110100031010=0000PHPCPaPVP5n0100000020000R5PQP=PSPZPUPFPYG>RZ54Le%V7RaP9E:P6PMPLP8PJPNPaP2Q01Q02PNP9P6Q06PNQ07%KpQ0H%UpQ0I%SpD07]1%Pp5\EP2P<PDPNQ08Q09Q0:Q0;PSQ0<Q0=P9PfPQP?PSP|PUPEPOG1#RG1Q0>5DMn200110?00012010310;P]P^n10110?00031010=0000n200110<00012110910:PHPN%h7P]P^n0100000020000n10110?00021110<00PiPjPkn10110100031010=0000=4LZe%a7P1E:AYRK7,W:=4LZR7eP7e1[RWP0E:P8P@PN%qKR0,[RAYP[9R[P8P@PNAiRh0P[P8P@PNAeRh0P[P6P:PNAdRh0Q05P]P^n10110?00031010>0000n10110?00021010200n10110?00021010201n10110?00021010201,W:=4LZe1kRK=4LZeQ03PVPWPFPYPGEj,kRQ03P5P=PFPYPGEj53LeW2W3W4W=W<W9W6W?X8BX;DW5X7BW:W>o"). Qed.

End FPX_2.

End LibAtomic.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.
Module LibKnowFrame.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition apart_b (allkn : list kentry) (ub : expr) (uk un : Z) (b : expr) (k n : Z) : bool :=
  if expr_eqb b ub then (Z.leb (k + n) uk || Z.leb (uk + un) k)%bool
  else ranges_apart allkn ub uk un b k n.

Lemma apart_b_sound : forall segs E M allkn ub uk un b k n,
  know_ok segs E M allkn -> apart_b allkn ub uk un b k n = true ->
  ((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z).
Proof.
  intros segs E M allkn ub uk un b k n HK H. unfold apart_b in H.
  destruct (expr_eqb b ub) eqn:Heq.
  - apply expr_eqb_eq in Heq. subst b. unfold estart. cbn [a_base a_off].
    apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
  - eapply ranges_apart_sound; [exact HK | exact H].
Qed.

(* [comment removed for export] *)
Definition kn_frame1 (allkn : list kentry) (ub : expr) (uk un : Z) (K : kentry) : list kentry :=
  match K with
  | KWord (SA b k) w _ => if apart_b allkn ub uk un b k (Z.of_nat w) then [K] else []
  | KZero (SA b k) (ELit l) =>
      if (Z.leb 0 l && Z.ltb l (2 ^ 64))%bool then
        if apart_b allkn ub uk un b k l then [K]
        else if expr_eqb b ub then
          (if Z.ltb k uk then [KZero (SA b k) (ELit (Z.min l (uk - k)))] else [])
          ++ (if Z.ltb (uk + un) (k + l) then [KZero (SA b (Z.max k (uk + un))) (ELit (k + l - Z.max k (uk + un)))] else [])
        else []
      else []
  | KZero _ _ => []
  | KBlob (SA b k) (ELit l) _ => if (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b allkn ub uk un b k l)%bool then [K] else []
  | KBlob _ _ _ => []
  | KImg lo hi => if (Z.leb 0 lo && Z.ltb lo hi && Z.leb hi (2 ^ 64) && apart_b allkn ub uk un (ELit 0) lo (hi - lo))%bool then [K] else []
  | KAlign _ _ => [K]
  | KRange _ _ _ => [K]
  | KDisj _ _ _ _ => [K]
  | KWr _ _ => [K]
  end.

Definition kn_frame (kn : list kentry) (ub : expr) (uk un : Z) : list kentry :=
  flat_map (kn_frame1 kn ub uk un) kn.

Lemma edenot_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma know_ok_frame : forall segs E M M' kn ub uk un,
  know_ok segs E M kn -> flat E (SA ub uk) un ->
  (forall x : word,
     (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + un <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok segs E M' (kn_frame kn ub uk un).
Proof.
  intros segs E M M' kn ub uk un HK Hfl OUT GR.
  pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  unfold know_ok, kn_frame. apply Forall_forall. intros K' HinF.
  apply in_flat_map in HinF as (K & Hin & Hb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  assert (APART : forall b k n, apart_b kn ub uk un b k n = true ->
            ((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z)).
  { intros b k n H. eapply apart_b_sound; [exact HK | exact H]. }
  destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
    cbn [kn_frame1] in Hb.
  - (* [comment removed for export] *)
    destruct (apart_b kn ub uk un b k (Z.of_nat w)) eqn:Hap; [|destruct Hb].
    destruct Hb as [<-|[]]. cbn [kentry_ok] in HKK |- *.
    destruct HKK as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
    rewrite <- Hr. apply rdn_agree. intros j Hj.
    pose proof (flat_u E _ _ Hf) as Hub. destruct Hf as (G1 & G2 & G3 & G4).
    apply OUT. rewrite u_small by lia. destruct (APART b k (Z.of_nat w) Hap); lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
    destruct (Z.leb 0 l && Z.ltb l (2 ^ 64))%bool eqn:Hl; [|destruct Hb].
    apply andb_prop in Hl as [Hl0 Hl1]. apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    cbn [kentry_ok] in HKK. destruct HKK as (Hf & Hz).
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. pose proof Hf as Hf0. destruct Hf as (G1 & G2 & G3 & G4).
    destruct (apart_b kn ub uk un b k l) eqn:Hap.
    + destruct Hb as [<-|[]]. cbn [kentry_ok]. rewrite El. split; [exact Hf0|].
      intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
      rewrite u_small by lia. destruct (APART b k l Hap); lia.
    + destruct (expr_eqb b ub) eqn:Heq; [|destruct Hb].
      apply expr_eqb_eq in Heq. subst b.
      unfold estart in G1, G2, G4, OUT, Hz |- *. cbn [a_base a_off] in G1, G2, G4, OUT, Hz |- *.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      * destruct (Z.ltb k uk) eqn:Hlt; [|destruct Hb]. apply Z.ltb_lt in Hlt.
        destruct Hb as [<-|[]]. cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off edenot].
        rewrite u_small by lia. split; [split; [exact G1 | split; [exact G2 | split; lia]]|].
        intros i Hi. rewrite OUT; [apply Hz; lia|]. rewrite u_small by lia. lia.
      * destruct (Z.ltb (uk + un) (k + l)) eqn:Hlt; [|destruct Hb]. apply Z.ltb_lt in Hlt.
        destruct Hb as [<-|[]]. cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off edenot].
        rewrite u_small by lia. split; [split; [lia | split; [lia | split; lia]]|].
        intros i Hi. rewrite OUT; [|rewrite u_small by lia; lia].
        replace (bv_unsigned (edenot E ub) + Z.max k (uk + un) + i)%Z
          with (bv_unsigned (edenot E ub) + k + (Z.max k (uk + un) - k + i))%Z by lia.
        apply Hz. lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
    destruct (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b kn ub uk un b k l)%bool eqn:Hl; [|destruct Hb].
    destruct Hb as [<-|[]].
    apply andb_prop in Hl as [Hl Hap]. apply andb_prop in Hl as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    cbn [kentry_ok] in HKK |- *. destruct HKK as (Hf & Hlen & Hz). split; [exact Hf|]. split; [exact Hlen|].
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. destruct Hf as (G1 & G2 & G3 & G4).
    intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
    rewrite u_small by lia. destruct (APART b k l Hap); lia.
  - (* [comment removed for export] *)
    destruct (Z.leb 0 lo && Z.ltb lo hi && Z.leb hi (2 ^ 64) && apart_b kn ub uk un (ELit 0) lo (hi - lo))%bool eqn:Hl; [|destruct Hb].
    destruct Hb as [<-|[]].
    apply andb_prop in Hl as [Hl Hap]. apply andb_prop in Hl as [Hl Hhi]. apply andb_prop in Hl as [Hlo Hlh].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hlh. apply Z.leb_le in Hhi.
    cbn [kentry_ok] in HKK |- *. destruct HKK as (H0 & H1 & Hnone). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite OUT; [apply Hnone; exact Hi|].
    pose proof (APART (ELit 0) lo (hi - lo)%Z Hap) as AP. unfold estart in AP |- *. cbn [a_base a_off] in AP |- *.
    rewrite edenot_lit0 in AP. rewrite u_small by lia. lia.
  - (* [comment removed for export] *) destruct Hb as [<-|[]]. exact HKK.
  - (* [comment removed for export] *) destruct Hb as [<-|[]]. exact HKK.
  - (* [comment removed for export] *)
    destruct Hb as [<-|[]]. cbn [kentry_ok] in HKK |- *.
    destruct HKK as (Hf & Hst). split; [exact Hf|].
    intros d m Hd Hm. eapply store_ok_mono; [exact GR | apply Hst; assumption].
  - (* [comment removed for export] *) destruct Hb as [<-|[]]. exact HKK.
Qed.

(* [comment removed for export] *)

Lemma zfill_inside : forall (a n : word) M (x : word),
  (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z ->
  zfill a n M x = Some (Z_to_bv 8 0).
Proof.
  intros a n M x H. unfold zfill, zmem.
  rewrite (proj2 (Z.leb_le _ _) (proj1 H)). rewrite (proj2 (Z.ltb_lt _ _) (proj2 H)). reflexivity.
Qed.

Lemma zfill_outside : forall (a n : word) M (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  zfill a n M x = M x.
Proof. intros a n M x H. apply zfill_out. exact H. Qed.

(* [comment removed for export] *)
Lemma know_ok_zfill : forall segs E M kn ub uk un,
  know_ok segs E M kn -> flat E (SA ub uk) un -> (0 < un)%Z -> (un < 2 ^ 64)%Z ->
  know_ok segs E (zfill (adenot E (SA ub uk)) (Z_to_bv 64 un) M)
          (KZero (SA ub uk) (ELit un) :: kn_frame kn ub uk un).
Proof.
  intros segs E M kn ub uk un HK Hfl Hpos Hun.
  pose proof (flat_u E _ _ Hfl) as Hu. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in F1, F2, F3, F4. cbn [a_base a_off] in F1, F2, F3, F4.
  apply know_ok_cons.
  - eapply (kzero_intro segs E _ ub (edenot E ub) uk (ELit un) un); [reflexivity | | exact F1 | exact Hpos | exact F4 |].
    + cbn [edenot]. apply u_small. clear -Hpos Hun. lia.
    + intros i Hi. apply zfill_inside. rewrite Hu, !u_small by lia. unfold estart. cbn [a_base a_off]. lia.
  - eapply know_ok_frame; [exact HK | exact Hfl | |].
    + intros x Hx. apply zfill_outside. rewrite Hu, u_small by lia. exact Hx.
    + intros x Hx. unfold zfill, zmem. destruct (_ && _)%bool; [discriminate | exact Hx].
Qed.

(* [comment removed for export] *)

Lemma know_ok_wblob : forall segs E M kn ub uk (k : nat) (bs : list byte),
  know_ok segs E M kn -> flat E (SA ub uk) (Z.of_nat (length bs)) ->
  eb E k = bs -> (0 < length bs)%nat -> (Z.of_nat (length bs) < 2 ^ 64)%Z ->
  know_ok segs E (wbytes M (adenot E (SA ub uk)) bs)
          (KBlob (SA ub uk) (ELit (Z.of_nat (length bs))) k :: kn_frame kn ub uk (Z.of_nat (length bs))).
Proof.
  intros segs E M kn ub uk k bs HK Hfl Hb Hpos Hsmall.
  pose proof (flat_u E _ _ Hfl) as Hu. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in F1, F2, F3, F4. cbn [a_base a_off] in F1, F2, F3, F4.
  apply know_ok_cons.
  - eapply (kblob_intro segs E _ ub (edenot E ub) uk _ k bs); [reflexivity | exact Hb | | exact F1 | exact F2 | exact F4 |].
    + cbn [edenot]. apply u_small. clear -Hsmall. lia.
    + intros i Hi.
      rewrite MemSplit.wbytes_inside by (rewrite Hu; unfold estart; cbn [a_base a_off]; rewrite ?u_small by lia; lia).
      f_equal. f_equal. rewrite Hu, u_small by lia. unfold estart. cbn [a_base a_off]. lia.
  - eapply know_ok_frame; [exact HK | exact Hfl | |].
    + intros x Hx. apply MemSplit.wbytes_outside; rewrite Hu; [unfold estart; cbn [a_base a_off]; lia | exact Hx].
    + apply wbytes_grows.
Qed.

(* [comment removed for export] *)
Lemma wbytes_nil_id : forall M (a : word), wbytes M a [] = M.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)

Lemma rdn_1_of_mem : forall segs M (a : word) (b : byte),
  M a = Some b -> rdn segs M a 1 = Some [b].
Proof. intros segs M a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma kword1_of_mem : forall segs E M (e : expr) (a : word) off (z : Z),
  edenot E e = a -> (0 <= z < 256)%Z ->
  (0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + 1 <= 2 ^ 64)%Z ->
  M (Z_to_bv 64 (bv_unsigned a + off)) = Some (Z_to_bv 8 z) ->
  kentry_ok segs E M (KWord (SA e off) 1 (ELit z)).
Proof.
  intros segs E M e a off z He Hz H1 H2 Hm.
  eapply (kword_intro segs E M e a off 1 (ELit z) (Z_to_bv 64 z)); try assumption; try reflexivity; try lia.
  rewrite (rdn_1_of_mem segs M _ _ Hm). cbn. rewrite u_small by lia. reflexivity.
Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End LibKnowFrame.
From Stdlib Require ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs State Monad Specs Run.
Module SumWalkTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_to_Z_4 : forall v : word, (bv_unsigned v < 2^32)%Z ->
  bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
  intros v Hv. rewrite bytes_le_N.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z.
  apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

Lemma v_lw_small : forall z, (0 <= z < 2147483648)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lw. f_equal. rewrite u_Z2bv by lia.
  apply (bv_swrap_small 32). change (bv_half_modulus 32) with 2147483648%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma v_lw_m1 : v_lw (Z_to_bv 64 4294967295) = Z_to_bv 64 (-1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma c_eq_Z : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma c_eq_refl : forall x : word, c_eq x x = true.
Proof. intros x. unfold c_eq. apply bv_eqb_refl. Qed.
End FPX_1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac zsimp := rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; u_norm.

(* [comment removed for export] *)
Ltac sok_stack SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 144%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac lia_fast := first [ solve [ clear_disj; lia ] | lia ].
Ltac rdn_peel1 := rewrite rdn_wbytes_out by (zsimp; lia_fast).  (* [comment removed for export] *)
Ltac rdn_by H := repeat rdn_peel1; exact H.
(* [comment removed for export] *)
Ltac rdn_hyp :=
  match goal with
  | H : rdn _ _ ?a ?n = Some _ |- rdn _ _ ?a ?n = Some _ => exact H
  end.
Ltac rdn_solve :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (rdn_peel1; rdn_solve)
  | |- _ => rdn_hyp
  end.

(* [comment removed for export] *)
Ltac zbv_target x i :=
  lazymatch x with
  | Z_to_bv 64 (?a - ?b)%Z => let d := eval cbv in (b - i)%Z in constr:(Z_to_bv 64 (a - d))
  | Z_to_bv 64 (?a + ?b)%Z => let d := eval cbv in (b + i)%Z in constr:(Z_to_bv 64 (a + d))
  | Z_to_bv 64 ?a =>
      lazymatch i with
      | Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (a - d))
      | _ => constr:(Z_to_bv 64 (a + i))
      end
  | _ =>
      lazymatch i with
      | Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (bv_unsigned x - d))
      | _ => constr:(Z_to_bv 64 (bv_unsigned x + i))
      end
  end.

(* [comment removed for export] *)
Ltac addr_norm :=
  match goal with
  | |- context [v_addi ?x ?i] =>
      let e := constr:(v_addi x i) in
      tryif check_closed_term e then wlit_closed e
      else first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac sp_renorm :=
  match goal with
  | |- context [regupd _ 2 (v_addi ?x ?i)] =>
      let e := constr:(v_addi x i) in
      first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  end.

(* [comment removed for export] *)
Ltac getr_hyps :=
  repeat match goal with
         | H : getr ?rs ?n = _ |- context [getr ?rs ?n] => rewrite H
         end.
Ltac addr_tac := getr_hyps; unfold v_addi; u_norm; first [reflexivity | f_equal; lia | apply bv_eq; u_norm; lia].
Ltac val_tac := first [reflexivity | assumption | symmetry; assumption].

(* [comment removed for export] *)
Ltac stepST F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac
        | reflexivity | oktac ]
    end
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepLD F D bsv vv rdtac vtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac | vtac ]
  | step_simpl ]; vnorm.

(* [comment removed for export] *)
Ltac stepLD8 F D vv := stepLD F D (word_to_le_bytes 8 vv) vv ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).

(* [comment removed for export] *)
Ltac stepLBU F D bb rdtac :=
  chain_step;
  [ reflexivity
  | eapply step_lbu with (b := bb);
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac ]
  | step_simpl ]; vnorm.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (u_Z2bv z) by lia
      end
  end.

(* [comment removed for export] *)
Ltac addi_renorm :=
  match goal with
  | |- context [regupd _ _ (v_addi (Z_to_bv 64 ?x) ?i)] =>
      let t := zbv_target (Z_to_bv 64 x) i in
      replace (v_addi (Z_to_bv 64 x) i) with t by (unfold v_addi; unorm; f_equal; lia)
  end.
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)



Lemma rdn_img : forall segs mem (a : Z) (n : nat) (lo hi : Z),
  (forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
  (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z -> (0 <= lo)%Z -> (hi < 2^64)%Z ->
  rdn segs mem (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros segs mem a n lo hi Himg Hlo Hhi H0 H64.
  apply rdn_ext; [u_norm; lia|].
  intros x Hx. revert Hx. u_norm. intros Hx.
  rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Himg. lia.
Qed.
End FPX_2.


(* [comment removed for export] *)
Ltac img_exists :=
  lazymatch goal with |- exists bs, ?l = Some bs =>
    let v := eval vm_compute in l in
    lazymatch v with Some ?bs => exists bs; vm_compute; reflexivity end
  end.

(* [comment removed for export] *)
Ltac enum_nat k N tac :=
  let rec go n := lazymatch n with
    | O => lia
    | S ?m => destruct k as [|k]; [tac | go m]
    end in go N.


(* [comment removed for export] *)
Ltac zaddr H :=
  repeat match type of H with
  | context [Z_to_bv 64 (?a + ?b)%Z] =>
      let c := eval cbv in (a + b)%Z in change (a + b)%Z with c in H
  end.

(* [comment removed for export] *)
Ltac zaddr_goal :=
  repeat match goal with
  | |- context [Z_to_bv 64 (?a + ?b)%Z] =>
      let c := eval cbv in (a + b)%Z in
      lazymatch c with
      | Zpos _ => change (a + b)%Z with c
      end
  end.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End SumWalkTac.
From Ltac2 Require Ltac2. From Ltac2 Require Constr Control Ltac1 Array.
Module RdnPeelKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Ltac1 Array.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Fixpoint wchainZ (m : word -> option byte) (ws : list (Z * list byte)) : word -> option byte :=
  match ws with
  | [] => m
  | (x, bs) :: r => wbytes (wchainZ m r) (Z_to_bv 64 x) bs
  end.

Fixpoint wch_ok (y : Z) (n : nat) (ws : list (Z * list byte)) : Prop :=
  match ws with
  | [] => True
  | (x, bs) :: r =>
      (0 <= x < 2 ^ 64 /\ x + Z.of_nat (length bs) <= 2 ^ 64 /\ (y + Z.of_nat n <= x \/ x + Z.of_nat (length bs) <= y))
      /\ wch_ok y n r
  end.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Lemma rdn_wchainZ_out : forall segs m ws y n,
  0 <= y < 2 ^ 64 -> y + Z.of_nat n <= 2 ^ 64 -> wch_ok y n ws ->
  rdn segs (wchainZ m ws) (Z_to_bv 64 y) n = rdn segs m (Z_to_bv 64 y) n.
Proof.
  intros segs m ws y n Hy Hyn. induction ws as [|[x bs] r IH]; cbn [wchainZ wch_ok]; [reflexivity|].
  intros [(Hx & Hxl & Hd) Hr]. rewrite rdn_wbytes_out.
  - exact (IH Hr).
  - rewrite !u_Z2bv by lia. exact Hd.
  - rewrite u_Z2bv by lia. exact Hyn.
  - rewrite u_Z2bv by lia. exact Hxl.
Qed.
End FPX_1.

(* [comment removed for export] *)
Ltac2 rec chain_split (m : constr) (b : constr) : constr * constr :=
  match Constr.Unsafe.kind m with
  | Constr.Unsafe.App h args =>
      if Bool.and (Constr.equal h '@wbytes) (Int.equal (Array.length args) 3) then
        let a := Array.get args 1 in
        if Constr.equal a b then ('(@nil (Z * list byte)), m)
        else
          match Constr.Unsafe.kind a with
          | Constr.Unsafe.App ha aargs =>
              if Bool.and (Constr.equal ha '@Z_to_bv) (Int.equal (Array.length aargs) 2) then
                if Constr.equal (Array.get aargs 0) '64%N then
                  let x := Array.get aargs 1 in
                  let bs := Array.get args 2 in
                  let (r, base) := chain_split (Array.get args 0) b in
                  ('(@cons (Z * list byte) ($x, $bs) $r), base)
                else ('(@nil (Z * list byte)), m)
              else ('(@nil (Z * list byte)), m)
          | _ => ('(@nil (Z * list byte)), m)
          end
      else ('(@nil (Z * list byte)), m)
  | _ => ('(@nil (Z * list byte)), m)
  end.

Ltac wch_solve side :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; [ side | wch_solve side ]
  end.

(* [comment removed for export] *)
Ltac2 rdn_peel_many (side : Ltac1.t) : unit :=
  lazy_match! Control.goal () with
  | @eq _ (rdn ?segs ?m (Z_to_bv 64 ?y) ?n) _ =>
      let b := '(Z_to_bv 64 $y) in
      let (ws, base) := chain_split m b in
      lazy_match! ws with
      | nil => Control.zero (Tactic_failure None)
      | _ =>
          ltac1:(segs m base ws y n side |-
                 change_no_check m with (wchainZ base ws);
                 rewrite (rdn_wchainZ_out segs base ws y n); [ | side | side | cbn [wch_ok]; wch_solve side ])
            (Ltac1.of_constr segs) (Ltac1.of_constr m) (Ltac1.of_constr base) (Ltac1.of_constr ws) (Ltac1.of_constr y) (Ltac1.of_constr n) side
      end
  end.
Ltac rdn_peel_many side := let f := ltac2:(side |- Control.enter (fun () => rdn_peel_many side)) in f side.

End RdnPeelKit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.
Module SymAux.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Frame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sregion : Type := (saddr * Z)%type.

Definition rdenot (E : env) (r : sregion) : word * Z :=
  (Z_to_bv 64 (estart E (fst r)), snd r).

(* [comment removed for export] *)
Fixpoint entry_covered (rs : list sregion) (a : saddr) (w : nat) : bool :=
  match rs with
  | [] => false
  | (SA rb rk, n) :: rest =>
      (expr_eqb (a_base a) rb && Z.leb rk (a_off a) && Z.leb (a_off a + Z.of_nat w) (rk + n))%bool
      || entry_covered rest a w
  end.

Fixpoint log_covered (rs : list sregion) (log : list sentry) : bool :=
  match log with
  | [] => true
  | SE a w _ :: rest => entry_covered rs a w && log_covered rs rest
  end.

Definition regions_flat (E : env) (rs : list sregion) : Prop :=
  forall r, In r rs -> flat E (fst r) (snd r).

Lemma entry_covered_in : forall E rs a w (x : word),
  entry_covered rs a w = true -> regions_flat E rs -> flat E a (Z.of_nat w) ->
  (estart E a <= bv_unsigned x < estart E a + Z.of_nat w)%Z ->
  ~ outside x (map (rdenot E) rs).
Proof.
  intros E rs a w x. induction rs as [|[[rb rk] n] rest IH]; cbn [entry_covered map outside]; intros Hc Hrf Hfa Hx.
  - discriminate.
  - apply orb_prop in Hc as [Hc|Hc].
    + apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
      apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
      intros [Hno _]. apply Hno. unfold in_rng, rdenot. cbn [fst snd].
      pose proof (Hrf _ (or_introl eq_refl)) as Hfr. cbn [fst snd] in Hfr.
      unfold flat, estart in *. cbn [a_base a_off] in *. rewrite <- H1 in *.
      rewrite u64_lit by lia. lia.
    + intros [_ Hout]. apply (IH Hc); [| exact Hfa | exact Hx | exact Hout].
      intros r Hr. apply Hrf. right. exact Hr.
Qed.

Lemma frame_layer : forall E rs m a w (v : word),
  entry_covered rs a w = true -> regions_flat E rs -> flat E a (Z.of_nat w) ->
  frame_mod m (wbytes m (adenot E a) (word_to_le_bytes w v)) (map (rdenot E) rs).
Proof.
  intros E rs m a w v Hc Hrf Hfa.
  pose proof (flat_u E a _ Hfa) as Hu.
  eapply frame_mod_weaken.
  2:{ apply frame_mod_wbytes. rewrite length_N_to_le_bytes, Hu. destruct Hfa as (?&?&?&?). lia. }
  intros x Hout. cbn [outside]. split; [|exact I].
  intros Hin. unfold in_rng in Hin. rewrite length_N_to_le_bytes, Hu in Hin.
  exact (entry_covered_in E rs a w x Hc Hrf Hfa Hin Hout).
Qed.

Theorem log_covered_frame : forall E base rs log,
  log_covered rs log = true -> regions_flat E rs -> log_flat E log ->
  frame_mod base (mem_denot E base log) (map (rdenot E) rs).
Proof.
  intros E base rs log. induction log as [|[a w v] rest IH]; cbn [log_covered mem_denot log_flat]; intros Hc Hrf Hlf.
  - apply frame_mod_refl.
  - apply andb_prop in Hc as [H1 H2]. destruct Hlf as (Hw & Hfa & Hlf').
    eapply frame_mod_trans_same; [apply IH; assumption|].
    apply frame_layer; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma regs_ok_same : forall E sr sr' R R' (r : reg),
  regs_ok E sr R -> regs_ok E sr' R' -> sr_get sr' r = sr_get sr r -> getr R' r = getr R r.
Proof. intros E sr sr' R R' r HR HR' Hs. rewrite (HR r), (HR' r), Hs. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint same_regs (sr sr' : list expr) (rs : list reg) : bool :=
  match rs with
  | [] => true
  | r :: rest => expr_eqb (sr_get sr' r) (sr_get sr r) && same_regs sr sr' rest
  end.

Lemma same_regs_sound : forall E sr sr' R R' rs,
  same_regs sr sr' rs = true -> regs_ok E sr R -> regs_ok E sr' R' ->
  forall r, In r rs -> getr R' r = getr R r.
Proof.
  intros E sr sr' R R' rs. induction rs as [|r0 rest IH]; cbn [same_regs]; intros Hs HR HR' r Hin.
  - destruct Hin.
  - apply andb_prop in Hs as [H1 H2]. destruct Hin as [<-|Hin].
    + apply (regs_ok_same E sr sr' R R' r0 HR HR'). apply expr_eqb_eq. exact H1.
    + apply IH; assumption.
Qed.

Lemma keeps_cs_of_same : forall E sr sr' R R',
  same_regs sr sr' callee_saved = true -> regs_ok E sr R -> regs_ok E sr' R' -> keeps_cs R R'.
Proof. intros E sr sr' R R' Hs HR HR' r Hin. eapply same_regs_sound; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem run_sound_log : forall segs fuel stops scr pc sr log kn nx ss' scs scr' E base rom regs,
  sym_exec segs fuel true stops scr (SS pc sr log kn nx) [] = (ss', scs, scr') ->
  regs_ok E sr regs -> log_flat E log -> know_ok segs E base kn ->
  scs_denot segs base E scs ->
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ msteps segs (mkst regs (Z_to_bv 64 pc) (mem_denot E base log) rom)
                        (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
  intros segs fuel stops scr pc sr log kn nx ss' scs scr' E base rom regs Hex HR Hlf HK Hsc.
  eapply sym_exec_ex; [exact Hex | exact Hsc |].
  exists regs. cbn [s_pc s_log s_regs s_know].
  split; [reflexivity|]. split; [exact HR|]. split; [exact Hlf | exact HK].
Qed.

End FPX_1.

End SymAux.
