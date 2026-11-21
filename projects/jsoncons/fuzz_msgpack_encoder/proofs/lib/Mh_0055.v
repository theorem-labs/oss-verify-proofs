(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed noref_of_within_budget, realizes_error_free, realizes_traces_iff and 24 more; added m_halted_with_vdso; removed step_sc_fail, step_sc_mismatch; taken in part from projects/jsoncons/fuzz_bson_parser_max/proofs/lib/LibAtomic.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, 80 lines within its lines 28-289. *)
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
  srealizes0 (run_segments segs inp sp mb) scfg (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply srealizes_no_error; eassumption. Qed.

Lemma srealizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  srealizes0 (run_segments segs inp sp mb) scfg (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply srealizes_obs_iff. assumption. Qed.

Lemma realizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  realizes (run_segments segs inp sp mb) scfg (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply realizes_no_error; eassumption. Qed.

Lemma realizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  realizes (run_segments segs inp sp mb) scfg (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply realizes_obs_iff. assumption. Qed.

Theorem shape_strong_equiv_efs :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  srealizes0 (run_segments source_segs inp rsp rmb) scfg
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes0 (run_segments target_segs inp asp amb) scfg
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
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
  srealizes0 (run_segments source_segs inp rsp rmb) scfg
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes0 (run_segments target_segs inp asp amb) scfg
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T' ->
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
  realizes (run_segments source_segs inp rsp rmb) scfg
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (run_segments target_segs inp asp amb) scfg
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
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
  realizes (run_segments source_segs inp rsp rmb) scfg
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (run_segments target_segs inp asp amb) scfg
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T' ->
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
  srealizes0 (run_segments (img_segments SRC) inp (en_sp en_s) (en_mmap_base en_s)) scfg
    (init_config (run_segments (img_segments SRC) inp (en_sp en_s) (en_mmap_base en_s)) (img_init_pc SRC) (img_phdrs SRC)
                 (en_sp en_s) (en_brk en_s) (en_mmap_base en_s) (en_draw en_s) source_alloc_limit inp) T ->
  srealizes0 (run_segments (img_segments TGT) inp (en_sp en_t) (en_mmap_base en_t)) scfg
    (init_config (run_segments (img_segments TGT) inp (en_sp en_t) (en_mmap_base en_t)) (img_init_pc TGT) (img_phdrs TGT)
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
  srealizes0 (run_segments segs inp sp mb) scfg (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  kill_free T ->
  ~ dies_by_signal (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros scfg segs pc ph sp brk0 mb rnd lim inp T Hs HK (tr & sig & fs & Htr & Hin).
  apply (srealizes_traces_iff scfg segs pc ph sp brk0 mb rnd lim inp T tr Hs) in Htr.
  pose proof (HK _ Htr) as HF.
  apply Forall_forall with (x := KillEv sig fs) in HF; [exact HF | exact Hin].
Qed.

Lemma srealizes_error_free_unkilled : forall scfg segs pc ph sp brk0 mb rnd lim inp T,
  srealizes0 (run_segments segs inp sp mb) scfg (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
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
  - (* [comment removed for export] *)
    exfalso.
    rewrite (m_halted_of_proc _ _ (m_proc_with_vdso_bump _)) in Hh.
    match goal with [ H : materialize_model_accesses _ _ = Some _ |- _ ] =>
      pose proof (materialize_model_accesses_frame _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _) end.
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
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c Hspin Hh Hmode | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
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
  forall c, reach_fo (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) c ->
    ~ budget_refused_at (run_segments segs inp sp mb) c.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp Hnb c (tr & Hstar) Hbr.
  apply Hnb. cbn [run_scfg_budget_refused]. exists tr, c. split; [exact Hstar | exact Hbr].
Qed.

Lemma m_halted_with_vdso : forall v m, m_halted (with_vdso v m) = m_halted m.
Proof. reflexivity. Qed.

Theorem srealizes_init_must_exit : forall scfgD segs pc ph sp brk0 mb rnd lim inp S T,
  srealizes0 (run_segments segs inp sp mb) scfgD
    (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  exit_codes_in S T -> kill_free T ->
  ~ run_scfg_budget_refused forced_only_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp ->
  must_exit_in_scfg forced_only_cfg S (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros scfgD segs pc ph sp brk0 mb rnd lim inp S T Hs HE HK Hnb.
  cbn [must_exit_in_scfg].
  eapply (srealizes_must_exit_fo (run_segments segs inp sp mb) scfgD S _ (noref_of_within_budget _ _ _ _ _ _ _ _ _ Hnb)).
  - exact Hs.
  - apply reach_fo_refl.
  - exact HE.
  - exact HK.
  - intros code Hh. exfalso. unfold init_config in Hh. cbn [cfg_model] in Hh.
    rewrite m_halted_with_vdso, m_halted_init_model in Hh. discriminate Hh.
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
  intros segs regs pc mem rom w aq rl rd rs bs v Hfetch Hecall Hdecode Hal Hread Hv.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

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
  intros segs regs pc mem rom w aq rl rd rs bs v Hfetch Hecall Hdecode Hal Hread Hv.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

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
  intros segs regs pc mem rom w aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  subst r. rewrite Z.eqb_refl. cbv beta iota.
  rewrite Hok. cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
  unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

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
  intros segs regs pc mem rom w aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  subst r. rewrite Z.eqb_refl. cbv beta iota.
  rewrite Hok. cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4.
  unfold regupd, word_to_le_bytes.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

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
  intros segs regs pc mem rom r w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

Lemma step_branch_ft_r : forall segs regs pc mem rom r w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom r w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

Lemma step_bne_tk_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (btgt pc (bv_signed imm)) mem rom r).
Proof.
  intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_r segs regs pc mem rom r w BC_NE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

Lemma step_bne_ft_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_r segs regs pc mem rom r w BC_NE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

Lemma step_beq_tk_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (btgt pc (bv_signed imm)) mem rom r).
Proof.
  intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_r segs regs pc mem rom r w BC_EQ rs1 rs2 imm Hf He Hd). exact Hc.
Qed.

Lemma step_beq_ft_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_r segs regs pc mem rom r w BC_EQ rs1 rs2 imm Hf He Hd). exact Hc.
Qed.

(* [comment removed for export] *)
Lemma step_opimm_r : forall segs regs pc mem rom r w op rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs
                     else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                    (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom r w op rd rs imm Hfetch Hecall Hdecode.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_op_r : forall segs regs pc mem rom r w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
  MachineOk (mkst_r (if bv_eqb rd 0 then regs
                     else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                    (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom r w op rd rs1 rs2 Hfetch Hecall Hdecode.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

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
