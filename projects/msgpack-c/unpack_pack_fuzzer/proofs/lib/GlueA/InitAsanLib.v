(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Mem Cells Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainExport.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import LinZ.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St LinZ.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module InitAsanLib.
Module MX := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainExport.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells.
Module AS_ := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma nth_error_Z_to_le_bytes : forall n z i, (i < n)%nat ->
  nth_error (Z_to_le_bytes n z) i = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat i))).
Proof.
  induction n as [|n IH]; intros z i Hi; [lia|]. destruct i as [|i]; cbn [Z_to_le_bytes nth_error].
  - rewrite Z.shiftr_0_r. reflexivity.
  - rewrite (IH (Z.shiftr z 8) i) by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma rb_mrd : forall m a, rb segs m a = AM.mrd segs m (AM.wa a).
Proof. reflexivity. Qed.

Lemma bytes_at_word_rb : forall m A (w : nat) z,
  AM.bytes_at segs m A (word_to_le_bytes w (Z_to_bv 64 z)) ->
  forall i, 0 <= i < Z.of_nat w -> rb segs m (A + i) = Some (byte_of (Z_to_bv 64 z) i).
Proof.
  intros m A w z (_ & _ & H) i Hi. rewrite rb_mrd.
  unfold word_to_le_bytes in H. rewrite length_Z_to_le_bytes in H.
  specialize (H (Z.to_nat i)). rewrite Z2Nat.id in H by lia. rewrite H by lia.
  rewrite nth_error_Z_to_le_bytes by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Section Facts.
Variables (V : nat -> Z) (m : word -> option byte).
Variable kv : list (nat * Z).
Hypothesis Hkv : kv_ok V kv.
Variable E : env.

Variable B : list (int * lin).
Hypothesis HB : Forall (fun kb => bv_unsigned (ev E (fst kb)) = leval V (snd kb)) B.

Fixpoint base_of (T : list (int * lin)) (k : int) : option lin :=
  match T with [] => None | kb :: r => if PrimInt63.eqb k (fst kb) then Some (snd kb) else base_of r k end.
Lemma base_of_sound0 : forall T, Forall (fun kb => bv_unsigned (ev E (fst kb)) = leval V (snd kb)) T ->
  forall k b, base_of T k = Some b -> bv_unsigned (ev E k) = leval V b.
Proof.
  intros T HT k b. induction HT as [|[k0 b0] r H0 Hr IH]; cbn [base_of fst snd]; [discriminate|].
  destruct (PrimInt63.eqb k k0) eqn:Ek; [|exact IH].
  intros [= <-]. apply Uint63.eqb_correct in Ek. subst k0. exact H0.
Qed.
Lemma base_of_sound : forall k b, base_of B k = Some b -> bv_unsigned (ev E k) = leval V b.
Proof. exact (base_of_sound0 B HB). Qed.

Definition lin_sv (v : sv) : option lin :=
  match v with
  | VL w => Some (lconst (w2Z w))
  | VP k off => match base_of B k with Some b => Some (ladd b (lconst (w2Zs off))) | None => None end
  | _ => None
  end.

Lemma Z_to_bv_mod64 : forall a b, a mod MX.two64 = b mod MX.two64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. exact H. Qed.

Lemma lin_sv_sound : forall v p, lin_sv v = Some p -> den E v = Z_to_bv 64 (leval V p).
Proof.
  intros v p H. destruct v; cbn [lin_sv] in H; try discriminate.
  - injection H as <-. rewrite leval_lconst. reflexivity.
  - destruct (base_of B k) as [b|] eqn:Eb; [|discriminate]. injection H as <-.
    rewrite leval_ladd, leval_lconst. cbn [den]. apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, (base_of_sound k b Eb), Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. cbn [Z.of_N]. unfold w2Zs. destruct (wt off); [|reflexivity].
    rewrite two64_eq. replace (leval V b + (w2Z off - 2 ^ 64)) with (leval V b + w2Z off + (-1) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

Inductive nkind := NWord | NZero | NZeroS | NImg | NOther.
Record nfact := NF { nf_kind : nkind; nf_a : lin; nf_n : Z; nf_v : lin }.

Definition norm_fact (f : MX.mfact) : nfact :=
  match f with
  | MX.MCell a w v | MX.MRo a w v =>
      match lin_of kv a, lin_of kv v with
      | Some la, Some lv => if MX.is_cellw w then NF NWord la (Z.of_nat w) lv else NF NOther la 0 lv
      | _, _ => NF NOther (lconst 0) 0 (lconst 0)
      end
  | MX.MZeroC a n | MX.MZero a n =>
      match lin_of kv a with Some la => NF NZero la n (lconst 0) | None => NF NOther (lconst 0) 0 (lconst 0) end
  | MX.MImg lo hi => NF NImg (lconst lo) (hi - lo) (lconst 0)
  | MX.MZeroS a n =>
      match lin_of kv a, lin_of kv n with Some la, Some ln => NF NZeroS la 0 ln | _, _ => NF NOther (lconst 0) 0 (lconst 0) end
  | _ => NF NOther (lconst 0) 0 (lconst 0)
  end.

Definition nfact_ok (f : nfact) : Prop :=
  match nf_kind f with
  | NWord => forall i, 0 <= i < nf_n f -> rb segs m (leval V (nf_a f) + i) = Some (byte_of (Z_to_bv 64 (leval V (nf_v f))) i)
  | NZero => forall i, 0 <= i < nf_n f -> rb segs m (leval V (nf_a f) + i) = Some (Z_to_bv 8 0)
  | NZeroS => forall i, 0 <= i < leval V (nf_v f) -> rb segs m (leval V (nf_a f) + i) = Some (Z_to_bv 8 0)
  | NImg => forall i, 0 <= i < nf_n f -> m (Z_to_bv 64 (leval V (nf_a f) + i)) = None
  | NOther => True
  end.

Lemma cellw_bytes_at : forall a w z, MX.is_cellw w = true ->
  AS_.rw_cells segs m a [MX.cellw w z] -> AM.bytes_at segs m a (word_to_le_bytes w (Z_to_bv 64 z)).
Proof.
  intros a w z Hw [[_ H] _]. destruct (MX.cellw_bytes w z Hw) as (Eb & _ & _).
  cbn [AC.cells_bytes] in H. rewrite app_nil_r, Eb in H. exact H.
Qed.

Lemma zeros_rb : forall A n, AM.bytes_at segs m A (MX.zeros n) -> forall i, 0 <= i < n -> rb segs m (A + i) = Some (Z_to_bv 8 0).
Proof.
  intros A n (_ & _ & H) i Hi. rewrite rb_mrd. unfold MX.zeros in *. rewrite repeat_length in H.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H.
  apply nth_error_repeat. lia.
Qed.

Lemma norm_fact_sound : forall f, MX.mfact_ok segs V m f -> nfact_ok (norm_fact f).
Proof.
  intros f Hf. destruct f as [a w v|a n|a w v|a n|a n c|lo hi|a n|a n|a n]; cbn [norm_fact]; try exact I.
  -   destruct (lin_of kv a) as [la|] eqn:Ea; [|exact I]. destruct (lin_of kv v) as [lv|] eqn:Ev; [|exact I].
    destruct (MX.is_cellw w) eqn:Hw; [|exact I]. unfold nfact_ok. cbn [nf_kind nf_a nf_n nf_v]. cbn [MX.mfact_ok] in Hf.
    rewrite <- (lin_of_sound V kv Hkv a la Ea), <- (lin_of_sound V kv Hkv v lv Ev).
    exact (bytes_at_word_rb m _ w _ (cellw_bytes_at _ w _ Hw Hf)).
  -   destruct (lin_of kv a) as [la|] eqn:Ea; [|exact I]. unfold nfact_ok. cbn [nf_kind nf_a nf_n nf_v]. cbn [MX.mfact_ok] in Hf.
    rewrite <- (lin_of_sound V kv Hkv a la Ea). destruct Hf as [[_ H] _]. cbn [AC.cells_bytes AC.cbytes] in H. rewrite app_nil_r in H.
    exact (zeros_rb _ n H).
  -   destruct (lin_of kv a) as [la|] eqn:Ea; [|exact I]. destruct (lin_of kv v) as [lv|] eqn:Ev; [|exact I].
    destruct (MX.is_cellw w) eqn:Hw; [|exact I]. unfold nfact_ok. cbn [nf_kind nf_a nf_n nf_v]. cbn [MX.mfact_ok] in Hf.
    rewrite <- (lin_of_sound V kv Hkv a la Ea), <- (lin_of_sound V kv Hkv v lv Ev).
    exact (bytes_at_word_rb m _ w _ Hf).
  -   destruct (lin_of kv a) as [la|] eqn:Ea; [|exact I]. unfold nfact_ok. cbn [nf_kind nf_a nf_n nf_v]. cbn [MX.mfact_ok] in Hf.
    rewrite <- (lin_of_sound V kv Hkv a la Ea). intros i Hi. unfold rb. unfold AM.wa in Hf. rewrite (Hf i Hi). reflexivity.
  -   unfold nfact_ok. cbn [nf_kind nf_a nf_n nf_v]. cbn [MX.mfact_ok] in Hf. intros i Hi. rewrite leval_lconst.
    apply (Hf (lo + i)). lia.
  -   destruct (lin_of kv a) as [la|] eqn:Ea; [|exact I]. destruct (lin_of kv n) as [ln|] eqn:En; [|exact I].
    unfold nfact_ok. cbn [nf_kind nf_a nf_n nf_v]. cbn [MX.mfact_ok] in Hf.
    rewrite <- (lin_of_sound V kv Hkv a la Ea), <- (lin_of_sound V kv Hkv n ln En). intros i Hi. unfold rb. unfold AM.wa in Hf. rewrite (Hf i Hi). reflexivity.
Qed.

Definition img_chk (ca w cv : Z) : bool :=
  forallb (fun i => match img_byte segs (ca + Z.of_nat i) with
                    | Some b => bv_unsigned b =? bv_unsigned (byte_of (Z_to_bv 64 cv) (Z.of_nat i))
                    | None => false end) (seq 0 (Z.to_nat w)).
Definition fact_cell (a : lin) (w : Z) (v : lin) (f : nfact) : bool :=
  match nf_kind f with
  | NWord => lin_eqb (nf_a f) a && (nf_n f =? w) && lin_eqb64 (nf_v f) v
  | NZero => match ldiff a (nf_a f) with
             | Some d => (0 <=? d) && (d + w <=? nf_n f) && lin_eqb64 v (lconst 0)
             | None => false
             end
  | NImg => match is_const a, is_const (nf_a f), is_const v with
            | Some ca, Some lo, Some cv => (lo <=? ca) && (ca + w <=? lo + nf_n f) && img_chk ca w cv
            | _, _, _ => false
            end
  | _ => false
  end.

Lemma byte_of_zero : forall i, 0 <= i -> byte_of (Z_to_bv 64 0) i = Z_to_bv 8 0.
Proof. intros i Hi. unfold byte_of. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Z.shiftr_0_l. reflexivity. Qed.

Lemma fact_cell_sound : forall a w v f, nfact_ok f -> fact_cell a w v f = true ->
  forall i, 0 <= i < w -> rb segs m (leval V a + i) = Some (byte_of (Z_to_bv 64 (leval V v)) i).
Proof.
  intros a w v f Hf H i Hi. unfold fact_cell in H. unfold nfact_ok in Hf. destruct (nf_kind f).
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H2.
    rewrite <- (lin_eqb_sound V _ _ H1). rewrite (Hf i ltac:(lia)).
    rewrite (Z_to_bv_mod64 _ _ (lin_eqb64_sound V _ _ H3)). reflexivity.
  - destruct (ldiff a (nf_a f)) as [d|] eqn:D; [|discriminate]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1, H2. rewrite (ldiff_sound V _ _ d D).
    replace (leval V (nf_a f) + d + i) with (leval V (nf_a f) + (d + i)) by lia. rewrite (Hf (d + i) ltac:(lia)).
    pose proof (lin_eqb64_sound V _ _ H3) as Hz. rewrite leval_lconst in Hz.
    rewrite (Z_to_bv_mod64 _ 0 Hz). rewrite byte_of_zero by lia. reflexivity.
  - discriminate.
  -
    destruct (is_const a) as [ca|] eqn:CA; [|discriminate]. destruct (is_const (nf_a f)) as [lo|] eqn:CL; [|discriminate].
    destruct (is_const v) as [cv|] eqn:CV; [|discriminate].
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
    rewrite (is_const_sound V _ _ CA), (is_const_sound V _ _ CV). rewrite (is_const_sound V _ _ CL) in Hf.
    unfold img_chk in H3. pose proof (proj1 (forallb_forall _ _) H3 (Z.to_nat i) ltac:(apply in_seq; lia)) as X. cbv beta in X.
    rewrite Z2Nat.id in X by lia.
    specialize (Hf (ca - lo + i) ltac:(lia)). replace (lo + (ca - lo + i)) with (ca + i) in Hf by lia.
    unfold rb. rewrite Hf. unfold img_byte in X. destruct (rom_of segs (Z_to_bv 64 (ca + i))) as [b|]; [|discriminate X].
    apply Z.eqb_eq in X. f_equal. apply bv_eq. exact X.
  - discriminate.
Qed.

Variable NFS : list nfact.
Hypothesis HNF : Forall nfact_ok NFS.

Definition cell_chk (k : int) (g : int) (c : cell) : bool :=
  let idx := to_Z (c_idx c) in let w := to_Z (c_w c) in
  (0 <=? idx) && (0 <? w) && (idx + w <=? 8) &&
  match base_of B k, lin_sv (c_v c) with
  | Some b, Some v => existsb (fact_cell (ladd b (lconst (8 * keyZ g + idx))) w v) NFS
  | _, _ => false
  end.

Lemma cell_chk_sound : forall k g c, cell_chk k g c = true -> cell_ok segs E m (bv_unsigned (ev E k) + 8 * keyZ g) c.
Proof.
  intros k g c H. unfold cell_chk in H. cbv zeta in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1, H3. apply Z.ltb_lt in H2.
  destruct (base_of B k) as [b|] eqn:Eb; [|discriminate]. destruct (lin_sv (c_v c)) as [v|] eqn:Ev; [|discriminate].
  apply existsb_exists in H4 as (f & Hin & Hf).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. intros i Hi.
  pose proof (fact_cell_sound _ _ _ f (proj1 (Forall_forall _ _) HNF f Hin) Hf i Hi) as R.
  rewrite leval_ladd, leval_lconst, <- (base_of_sound k b Eb) in R.
  rewrite (lin_sv_sound _ _ Ev). rewrite <- R. f_equal. lia.
Qed.

Fixpoint slot_sortedb (s : slot) : bool :=
  match s with
  | [] => true
  | c :: s' => match s' with [] => true | c' :: _ => to_Z (c_idx c) + to_Z (c_w c) <=? to_Z (c_idx c') end && slot_sortedb s'
  end.
Lemma slot_sortedb_sound : forall s, slot_sortedb s = true -> slot_sorted s.
Proof.
  induction s as [|c s IH]; intros H; [exact I|]. cbn [slot_sortedb] in H. apply andb_prop in H as [H1 H2].
  cbn [slot_sorted]. split; [|exact (IH H2)]. destruct s as [|c' s']; [exact I| apply Z.leb_le; exact H1].
Qed.

Definition gran_chk (k : int) (g : int) (gr : gran) : bool := slot_sortedb (g_cells gr) && forallb (cell_chk k g) (g_cells gr).
Lemma gran_chk_sound : forall k g gr, gran_chk k g gr = true -> slot_ok segs E m (bv_unsigned (ev E k) + 8 * keyZ g) (g_cells gr).
Proof.
  intros k g gr H. apply andb_prop in H as [H1 H2]. split; [exact (slot_sortedb_sound _ H1)|].
  apply Forall_forall. intros c Hc. apply cell_chk_sound. exact (proj1 (forallb_forall _ _) H2 c Hc).
Qed.

Definition bytes_chk (P : Z -> bool) (o w : Z) : bool := forallb (fun i => P (o + Z.of_nat i)) (seq 0 (Z.to_nat w)).
Lemma bytes_chk_sound : forall P o w, bytes_chk P o w = true -> forall i, 0 <= i < w -> P (o + i) = true.
Proof.
  intros P o w H i Hi. pose proof (proj1 (forallb_forall _ _) H (Z.to_nat i)) as X. cbv beta in X. rewrite Z2Nat.id in X by lia.
  apply X. apply in_seq. lia.
Qed.

Definition in_priv_Zb (priv : list (int * int)) (a : Z) : bool := existsb (fun iv => (to_Z (fst iv) <=? a) && (a <? to_Z (snd iv))) priv.
Lemma in_priv_Zb_spec : forall priv a, in_priv_Zb priv a = false -> ~ in_priv priv a.
Proof.
  intros priv a H X. unfold in_priv in X. apply Exists_exists in X as (iv & Hin & Hiv).
  assert (Y : in_priv_Zb priv a = true).
  { apply existsb_exists. exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  congruence.
Qed.

Definition seg_at (a : Z) : bool := match find_segment segs a 1 with Some _ => true | None => false end.

Section Region0.
Variable priv : list (int * int).
Variable r : region.
Hypothesis Hbst : IMap.bst (rg_cells r).
Hypothesis Hbg : rg_bg r = BGImage.
Hypothesis Hev0 : ev E 0%uint63 = Z_to_bv 64 0.
Hypothesis Hminv : AM.mem_inv segs m.

Definition cell_in0 (g : int) (c : cell) : bool :=
  let o := 8 * keyZ g + to_Z (c_idx c) in let w := to_Z (c_w c) in
  (0 <=? o) && (o + w <=? two63 / 2) && bytes_chk seg_at o w && bytes_chk (fun a => negb (in_priv_Zb priv a)) o w.
Definition gran0_chk (gg : int * gran) : bool := gran_chk 0%uint63 (fst gg) (snd gg) && forallb (cell_in0 (fst gg)) (g_cells (snd gg)).
Hypothesis Hcells : forallb gran0_chk (IMap.elements (rg_cells r)) = true.

Lemma gran0_of_find : forall g gr, IMap.find g (rg_cells r) = Some gr -> gran0_chk (g, gr) = true.
Proof.
  intros g gr F. apply (proj1 (forallb_forall _ _) Hcells). apply (proj2 (IMap.elements_spec g gr (rg_cells r) Hbst)). exact F.
Qed.

Lemma cell_in0_sound : forall g c, cell_in0 g c = true -> forall i, 0 <= i < to_Z (c_w c) ->
  let o := 8 * keyZ g + to_Z (c_idx c) + i in
  0 <= o < two63 / 2 /\ (exists seg, find_segment segs o 1 = Some seg) /\ ~ in_priv priv o.
Proof.
  intros g c H i Hi. cbv zeta in *. unfold cell_in0 in H. cbv zeta in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1, H2. split; [lia|]. split.
  - pose proof (bytes_chk_sound _ _ _ H3 i Hi) as X. unfold seg_at in X.
    destruct (find_segment segs (8 * keyZ g + to_Z (c_idx c) + i) 1) as [seg|]; [exists seg; reflexivity| discriminate].
  - apply in_priv_Zb_spec. pose proof (bytes_chk_sound _ _ _ H4 i Hi) as X. cbv beta in X. apply negb_true_iff in X. exact X.
Qed.

Inductive ctag := TImg | TPriv | TGran (g : int) | TCell (g : int) (j : nat).
Record civ := CIV { ci_lo : Z; ci_hi : Z; ci_tag : ctag }.

Definition civ_ok (c : civ) : bool :=
  match ci_tag c with
  | TImg => existsb (fun f => match nf_kind f, is_const (nf_a f) with
                              | NImg, Some lo => (lo <=? ci_lo c) && (ci_hi c <=? lo + nf_n f)
                              | _, _ => false end) NFS
  | TPriv => existsb (fun iv => (to_Z (fst iv) <=? ci_lo c) && (ci_hi c <=? to_Z (snd iv))) priv
  | TGran g => match IMap.find g (rg_cells r) with
               | Some gr => g_dirty gr && (ci_lo c =? 8 * keyZ g) && (ci_hi c =? 8 * keyZ g + 8)
               | None => false end
  | TCell g j => match IMap.find g (rg_cells r) with
                 | Some gr => match nth_error (g_cells gr) j with
                              | Some cl => (ci_lo c =? 8 * keyZ g + to_Z (c_idx cl)) && (ci_hi c =? ci_lo c + to_Z (c_w cl))
                                           && (0 <=? to_Z (c_idx cl)) && (to_Z (c_idx cl) + to_Z (c_w cl) <=? 8)
                              | None => false end
                 | None => false end
  end.

Fixpoint sweep (cur : Z) (ivs : list civ) : Z :=
  match ivs with
  | [] => cur
  | c :: rest => if ci_lo c <=? cur then sweep (Z.max cur (ci_hi c)) rest else cur
  end.
Lemma sweep_cover : forall ivs cur o, cur <= o < sweep cur ivs -> exists c, In c ivs /\ ci_lo c <= o < ci_hi c.
Proof.
  induction ivs as [|c rest IH]; intros cur o Ho; cbn [sweep] in Ho; [lia|].
  destruct (Z.leb_spec (ci_lo c) cur) as [Hle|Hgt]; [|lia].
  destruct (Z.lt_ge_cases o (ci_hi c)) as [Hin|Hout].
  - exists c. split; [left; reflexivity| lia].
  - destruct (IH (Z.max cur (ci_hi c)) o ltac:(lia)) as (c' & Hc' & Ho'). exists c'. split; [right; exact Hc'| exact Ho'].
Qed.

Variable cover : list civ.
Hypothesis Hcover_ok : forallb civ_ok cover = true.
Hypothesis Hcover : forallb (fun seg => if seg_writable seg
                                       then Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? sweep (Z.of_N (seg_base seg)) cover
                                       else true) segs = true.

Lemma find_segment_in : forall sgs a n seg, find_segment sgs a n = Some seg ->
  In seg sgs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction sgs as [|s0 rest IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:Eb.
  - injection H as <-. apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1, E2. split; [left; reflexivity| lia].
  - destruct (IH a n seg H) as (X & Y). split; [right; exact X| exact Y].
Qed.

Lemma bg0 : forall o, 0 <= o < two63 / 2 -> (exists bs, memory_read segs (Z_to_bv 64 o) 1 = Some bs) -> ~ in_priv priv o ->
  uncovered r o -> forall b, img_byte segs o = Some b -> rb segs m o = Some b.
Proof.
  intros o Ho (bs & Hrd) Hnp Hunc b Hb.
  assert (Eo : bv_unsigned (Z_to_bv 64 o) = o).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_small. rewrite two63_eq in Ho. lia. }
  unfold memory_read in Hrd. rewrite Eo in Hrd. change (Z.of_N 1) with 1 in Hrd.
  destruct (find_segment segs o 1) as [seg|] eqn:F; [|discriminate].
  assert (Hnone : m (Z_to_bv 64 o) = None -> rb segs m o = Some b).
  { intros Hn. unfold rb. rewrite Hn. exact Hb. }
  destruct (seg_writable seg) eqn:W.
  - destruct (find_segment_in _ _ _ _ F) as (Hin & Hlo & Hhi).
    pose proof (proj1 (forallb_forall _ _) Hcover seg Hin) as C. cbv beta in C. rewrite W in C. apply Z.leb_le in C.
    destruct (sweep_cover cover (Z.of_N (seg_base seg)) o ltac:(lia)) as (c & Hc & Hoc).
    pose proof (proj1 (forallb_forall _ _) Hcover_ok c Hc) as K. unfold civ_ok in K. destruct (ci_tag c) as [| |g|g j].
    + apply existsb_exists in K as (f & Hf & Kf). pose proof (proj1 (Forall_forall _ _) HNF f Hf) as Of. unfold nfact_ok in Of.
      destruct (nf_kind f); try discriminate. destruct (is_const (nf_a f)) as [lo|] eqn:Ec; [|discriminate].
      apply andb_prop in Kf as [K1 K2]. apply Z.leb_le in K1, K2. apply Hnone.
      specialize (Of (o - lo) ltac:(lia)). rewrite (is_const_sound V _ lo Ec) in Of. replace (lo + (o - lo)) with o in Of by lia. exact Of.
    + exfalso. apply Hnp. apply existsb_exists in K as (iv & Hiv & Kiv). apply andb_prop in Kiv as [K1 K2]. apply Z.leb_le in K1, K2.
      apply Exists_exists. exists iv. split; [exact Hiv| lia].
    + exfalso. destruct (IMap.find g (rg_cells r)) as [gr|] eqn:Fg; [|discriminate].
      apply andb_prop in K as [K K3]. apply andb_prop in K as [K1 K2]. apply Z.eqb_eq in K2, K3.
      assert (Hg : keyZ g = o / 8). { apply (Z.div_unique o 8 (keyZ g) (o - 8 * keyZ g)); lia. }
      destruct (Hunc g gr Hg Fg) as [D _]. congruence.
    + exfalso. destruct (IMap.find g (rg_cells r)) as [gr|] eqn:Fg; [|discriminate].
      destruct (nth_error (g_cells gr) j) as [cl|] eqn:Nj; [|discriminate].
      apply andb_prop in K as [K K4]. apply andb_prop in K as [K K3]. apply andb_prop in K as [K1 K2].
      apply Z.eqb_eq in K1, K2. apply Z.leb_le in K3, K4.
      assert (Hg : keyZ g = o / 8). { apply (Z.div_unique o 8 (keyZ g) (o - 8 * keyZ g)); lia. }
      assert (Hm : o mod 8 = o - 8 * keyZ g). { symmetry. apply (Z.mod_unique o 8 (keyZ g) (o - 8 * keyZ g)); lia. }
      destruct (Hunc g gr Hg Fg) as [_ NC]. apply (proj1 (Forall_forall _ _) NC cl (nth_error_In _ _ Nj)).
      unfold covers. rewrite Hm. lia.
  - apply Hnone. destruct (m (Z_to_bv 64 o)) as [b0|] eqn:Em; [|reflexivity]. exfalso.
    pose proof (Hminv _ _ Em) as R. unfold AM.ro_addr in R. rewrite Eo, F, W in R. discriminate R.
Qed.

Theorem region0_ok : region_ok segs priv E m 0%uint63 r.
Proof.
  constructor.
  - exact Hbst.
  - intros K. discriminate K.
  - intros K. discriminate K.
  - intros g gr F. pose proof (gran0_of_find g gr F) as G. apply andb_prop in G as [G _]. cbn [fst snd] in G.
    pose proof (gran_chk_sound _ _ _ G) as S. rewrite Hev0 in S. rewrite Hev0. exact S.
  - intros g gr c i F Hc Hi. cbv zeta. split; [intros K; discriminate K|]. intros _.
    pose proof (gran0_of_find g gr F) as G. apply andb_prop in G as [_ G]. cbn [fst snd] in G.
    exact (cell_in0_sound g c (proj1 (forallb_forall _ _) G c Hc) i Hi).
  - intros o _ H0 Hunc. destruct (H0 eq_refl) as (Ho & Hrd & Hnp). unfold bg_byte. rewrite Hbg.
    destruct (img_byte segs o) as [b|] eqn:Eb; [|exact I].
    rewrite Hev0. replace (bv_unsigned (Z_to_bv 64 0) + o) with o by (rewrite Z_to_bv_unsigned; reflexivity).
    exact (bg0 o Ho Hrd Hnp Hunc b Eb).
Qed.

Lemma cells_public0 : forall g gr c, IMap.find g (rg_cells r) = Some gr -> In c (g_cells gr) ->
  forall i, 0 <= i < to_Z (c_w c) -> ~ in_priv priv (8 * keyZ g + to_Z (c_idx c) + i).
Proof.
  intros g gr c F Hc i Hi. pose proof (gran0_of_find g gr F) as G. apply andb_prop in G as [_ G]. cbn [fst snd] in G.
  exact (proj2 (proj2 (cell_in0_sound g c (proj1 (forallb_forall _ _) G c Hc) i Hi))).
Qed.

End Region0.

Definition cell_inb (lo hi : Z) (g : int) (c : cell) : bool :=
  (lo <=? 8 * keyZ g + to_Z (c_idx c)) && (8 * keyZ g + to_Z (c_idx c) + to_Z (c_w c) <=? hi).
Definition granb_chk (k : int) (lo hi : Z) (gg : int * gran) : bool :=
  gran_chk k (fst gg) (snd gg) && forallb (cell_inb lo hi (fst gg)) (g_cells (snd gg)).

Theorem based_region_ok : forall priv k r (lo hi : Z),
  PrimInt63.eqb k 0%uint63 = false -> IMap.bst (rg_cells r) ->
  loZ r = lo -> hiZ E r = hi ->
  0 <= bv_unsigned (ev E k) + lo -> bv_unsigned (ev E k) + hi < two64 ->
  (forall a, bv_unsigned (ev E k) + lo <= a < bv_unsigned (ev E k) + hi ->
     rb segs m a <> None /\ (rg_w r = true -> wb segs m a = true) /\ find_segment segs a 1 = None) ->
  forallb (granb_chk k lo hi) (IMap.elements (rg_cells r)) = true ->
  (forall o, lo <= o < hi -> uncovered r o ->
     match bg_byte segs E k r o with Some b => rb segs m (bv_unsigned (ev E k) + o) = Some b | None => True end) ->
  region_ok segs priv E m k r.
Proof.
  intros priv k r lo hi K Hbst Hlo Hhi R1 R2 Hval Hc Hbgp.
  assert (G : forall g gr, IMap.find g (rg_cells r) = Some gr -> granb_chk k lo hi (g, gr) = true).
  { intros g gr F. apply (proj1 (forallb_forall _ _) Hc). apply (proj2 (IMap.elements_spec g gr (rg_cells r) Hbst)). exact F. }
  constructor.
  - exact Hbst.
  - intros _. rewrite Hlo, Hhi. split; assumption.
  - intros _ a Ha. rewrite Hlo, Hhi in Ha. exact (Hval a Ha).
  - intros g gr F. pose proof (G g gr F) as X. apply andb_prop in X as [X _]. exact (gran_chk_sound _ _ _ X).
  - intros g gr c i F Hin Hi. cbv zeta. split; [|intros K'; rewrite K in K'; discriminate K'].
    intros _. pose proof (G g gr F) as X. apply andb_prop in X as [_ X]. cbn [fst snd] in X.
    pose proof (proj1 (forallb_forall _ _) X c Hin) as Y. unfold cell_inb in Y. apply andb_prop in Y as [Y1 Y2].
    apply Z.leb_le in Y1, Y2. rewrite Hlo, Hhi. lia.
  - intros o Ho _ Hunc. rewrite Hlo, Hhi in Ho. exact (Hbgp o (Ho K) Hunc).
Qed.

Definition covered_b (r : region) (o : Z) : bool :=
  existsb (fun gg => (keyZ (fst gg) =? o / 8) &&
                     existsb (fun c => (to_Z (c_idx c) <=? o mod 8) && (o mod 8 <? to_Z (c_idx c) + to_Z (c_w c))) (g_cells (snd gg)))
          (IMap.elements (rg_cells r)).
Lemma covered_rb : forall k r lo hi, forallb (granb_chk k lo hi) (IMap.elements (rg_cells r)) = true ->
  forall o, covered_b r o = true -> rb segs m (bv_unsigned (ev E k) + o) <> None.
Proof.
  intros k r lo hi Hc o H. unfold covered_b in H. apply existsb_exists in H as ([g gr] & Hin & H). cbn [fst snd] in H.
  apply andb_prop in H as [Hg H]. apply Z.eqb_eq in Hg. apply existsb_exists in H as (c & Hcin & H).
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (proj1 (forallb_forall _ _) Hc (g, gr) Hin) as X. unfold granb_chk in X. apply andb_prop in X as [X _]. cbn [fst snd] in X.
  destruct (gran_chk_sound _ _ _ X) as [_ S]. pose proof (proj1 (Forall_forall _ _) S c Hcin) as (C1 & C2 & C3 & C4).
  specialize (C4 (o mod 8 - to_Z (c_idx c)) ltac:(lia)).
  replace (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx c) + (o mod 8 - to_Z (c_idx c))) with (bv_unsigned (ev E k) + o) in C4
    by (rewrite Hg; pose proof (Z.div_mod o 8 ltac:(lia)); lia).
  rewrite C4. discriminate.
Qed.
Definition range_covered_b (r : region) (lo : Z) (n : nat) : bool := forallb (fun i => covered_b r (lo + Z.of_nat i)) (seq 0 n).
Lemma range_covered_rb : forall k r lo hi, forallb (granb_chk k lo hi) (IMap.elements (rg_cells r)) = true ->
  forall lo' n, range_covered_b r lo' n = true -> forall o, lo' <= o < lo' + Z.of_nat n -> rb segs m (bv_unsigned (ev E k) + o) <> None.
Proof.
  intros k r lo hi Hc lo' n H o Ho. apply (covered_rb k r lo hi Hc).
  pose proof (proj1 (forallb_forall _ _) H (Z.to_nat (o - lo'))) as X. cbv beta in X. rewrite Z2Nat.id in X by lia.
  replace (lo' + (o - lo')) with o in X by lia. apply X. apply in_seq. lia.
Qed.

Lemma wb_of_rb_noseg : forall a, 0 <= a < 2 ^ 64 -> rb segs m a <> None -> find_segment segs a 1 = None -> wb segs m a = true.
Proof.
  intros a Ha Hr Hs. unfold wb, wview. unfold rb in Hr. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [reflexivity|].
  exfalso. apply Hr. unfold rom_of, memory_read. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite Z.mod_small by lia. change (Z.of_N 1) with 1. rewrite Hs. reflexivity.
Qed.

Lemma bg_unk_ok : forall k r o, rg_bg r = BGUnk ->
  (forall o', eg E k o' = match rb segs m (bv_unsigned (ev E k) + o') with Some b => b | None => Z_to_bv 8 0 end) ->
  rb segs m (bv_unsigned (ev E k) + o) <> None ->
  match bg_byte segs E k r o with Some b => rb segs m (bv_unsigned (ev E k) + o) = Some b | None => True end.
Proof.
  intros k r o Hbg Heg Hr. unfold bg_byte. rewrite Hbg. rewrite Heg. destruct (rb segs m (bv_unsigned (ev E k) + o)); [reflexivity| contradiction].
Qed.

Lemma word_is_sv : forall v p z, lin_sv v = Some p -> (leval V p) mod MX.two64 = z mod MX.two64 -> Z_to_bv 64 z = den E v.
Proof. intros v p z Hv Hz. rewrite (lin_sv_sound v p Hv). symmetry. apply Z_to_bv_mod64. exact Hz. Qed.

Definition zlen (f : nfact) : Z := match nf_kind f with NZero => nf_n f | NZeroS => leval V (nf_v f) | _ => 0 end.
Lemma zero_fact_rb : forall f, nfact_ok f -> forall i, 0 <= i < zlen f -> rb segs m (leval V (nf_a f) + i) = Some (Z_to_bv 8 0).
Proof. intros f Hf i Hi. unfold zlen in Hi. unfold nfact_ok in Hf. destruct (nf_kind f); try lia; exact (Hf i Hi). Qed.

Theorem zero_region_ok : forall priv k r (lo hi : Z) f,
  PrimInt63.eqb k 0%uint63 = false -> In f NFS ->
  rg_bg r = BGZero -> IMap.bst (rg_cells r) -> IMap.elements (rg_cells r) = [] -> rg_w r = false ->
  loZ r = lo -> hiZ E r = hi ->
  0 <= bv_unsigned (ev E k) + lo -> bv_unsigned (ev E k) + hi < two64 ->
  leval V (nf_a f) <= bv_unsigned (ev E k) + lo -> bv_unsigned (ev E k) + hi <= leval V (nf_a f) + zlen f ->
  (forall a, bv_unsigned (ev E k) + lo <= a < bv_unsigned (ev E k) + hi -> find_segment segs a 1 = None) ->
  region_ok segs priv E m k r.
Proof.
  intros priv k r lo hi f K Hin Hbg Hbst Hel Hw Hlo Hhi R1 R2 I1 I2 Hns.
  pose proof (proj1 (Forall_forall _ _) HNF f Hin) as Hf.
  assert (Z0 : forall a, bv_unsigned (ev E k) + lo <= a < bv_unsigned (ev E k) + hi -> rb segs m a = Some (Z_to_bv 8 0)).
  { intros a Ha. pose proof (zero_fact_rb f Hf (a - leval V (nf_a f)) ltac:(lia)) as X.
    replace (leval V (nf_a f) + (a - leval V (nf_a f))) with a in X by lia. exact X. }
  apply (based_region_ok priv k r lo hi K Hbst Hlo Hhi R1 R2).
  - intros a Ha. split; [rewrite (Z0 a Ha); discriminate|]. split; [intros W; rewrite Hw in W; discriminate W| exact (Hns a Ha)].
  - rewrite Hel. reflexivity.
  - intros o Ho _. unfold bg_byte. rewrite Hbg. apply Z0. lia.
Qed.

End Facts.

Theorem region_ok_transfer : forall priv priv' E E' m m' k r,
  PrimInt63.eqb k 0%uint63 = false ->
  region_ok segs priv E m k r ->
  ev E' k = ev E k -> hiZ E' r = hiZ E r ->
  (forall g gr c, IMap.find g (rg_cells r) = Some gr -> In c (g_cells gr) -> den E' (c_v c) = den E (c_v c)) ->
  (forall o, loZ r <= o < hiZ E r -> bg_byte segs E' k r o = bg_byte segs E k r o) ->
  (forall a, bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r ->
     rb segs m' a = rb segs m a /\ (wb segs m a = true -> wb segs m' a = true)) ->
  region_ok segs priv' E' m' k r.
Proof.
  intros priv priv' E E' m m' k r K RO Hev Hhi Hden Hbg Hag.
  constructor.
  - exact (ro_bst _ _ _ _ _ _ RO).
  - intros _. rewrite Hev, Hhi. exact (ro_range _ _ _ _ _ _ RO K).
  - intros _ a Ha. rewrite Hev, Hhi in Ha. destruct (ro_valid _ _ _ _ _ _ RO K a Ha) as (V1 & V2 & V3).
    destruct (Hag a Ha) as [A1 A2]. split; [rewrite A1; exact V1|]. split; [intros W; exact (A2 (V2 W))| exact V3].
  - intros g gr F. destruct (ro_cells _ _ _ _ _ _ RO g gr F) as [S1 S2]. split; [exact S1|].
    apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) S2 c Hc) as (C1 & C2 & C3 & C4).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros i Hi.
    destruct (ro_cells_in _ _ _ _ _ _ RO g gr c i F Hc Hi) as [In1 _]. specialize (In1 K).
    rewrite Hev, (Hden g gr c F Hc). rewrite <- (C4 i Hi).
    apply (Hag (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx c) + i)). lia.
  - intros g gr c i F Hc Hi. cbv zeta. destruct (ro_cells_in _ _ _ _ _ _ RO g gr c i F Hc Hi) as [In1 In2].
    split; [intros K'; rewrite Hhi; exact (In1 K')| intros K'; rewrite K in K'; discriminate K'].
  - intros o Ho _ Hunc. rewrite Hhi in Ho. specialize (Ho K). rewrite (Hbg o Ho), Hev.
    pose proof (ro_bg _ _ _ _ _ _ RO o (fun _ => Ho) (fun K' => ltac:(rewrite K in K'; discriminate K')) Hunc) as X.
    destruct (bg_byte segs E k r o) as [b|]; [|exact I]. rewrite <- X. apply (Hag (bv_unsigned (ev E k) + o)). lia.
Qed.

Fixpoint sv_okb (P : int -> bool) (v : sv) : bool :=
  match v with
  | VL _ => true
  | VP k _ => P k
  | VAlu _ a b | VAluw _ a b | VMd _ a b | VMdw _ a b | VIns _ _ a b => sv_okb P a && sv_okb P b
  | VExt _ _ _ a | VF1 _ a => sv_okb P a
  | VBlob _ _ off _ => sv_okb P off
  | VBg _ _ _ _ => false
  end.
Lemma den_agree : forall P E E', (forall k, P k = true -> ev E' k = ev E k) -> eb E' = eb E ->
  forall v, sv_okb P v = true -> den E' v = den E v.
Proof.
  intros P E E' Hev Heb. induction v; intros H; cbn [sv_okb] in H; cbn [den];
    repeat match goal with H : (_ && _) = true |- _ => apply andb_prop in H as [? ?] end;
    try discriminate; try reflexivity;
    repeat match goal with IH : _ = true -> den E' ?a = den E ?a |- _ => rewrite (IH ltac:(assumption)); clear IH end;
    try reflexivity.
  - rewrite (Hev k H). reflexivity.
  - rewrite Heb. reflexivity.
Qed.

Definition fact_okb (P : int -> bool) (f : fact) : bool :=
  match f with
  | FRange k _ _ | FAlign k _ => P k
  | FULt a b | FULe a b | FEq a b | FNe a b | FSLt a b | FSLe a b => sv_okb P a && sv_okb P b
  end.
Lemma fact_holds_agree : forall P E E', (forall k, P k = true -> ev E' k = ev E k) -> eb E' = eb E ->
  forall f, fact_okb P f = true -> fact_holds E f -> fact_holds E' f.
Proof.
  intros P E E' Hev Heb f H HF. destruct f; cbn [fact_okb] in H; cbn [fact_holds] in *;
    try (apply andb_prop in H as [H1 H2]; rewrite (den_agree P E E' Hev Heb _ H1), (den_agree P E E' Hev Heb _ H2); exact HF).
  - rewrite (Hev k H). exact HF.
  - rewrite (Hev k H). exact HF.
Qed.
Lemma facts_hold_agree : forall P E E', (forall k, P k = true -> ev E' k = ev E k) -> eb E' = eb E ->
  forall fs, forallb (fact_okb P) fs = true -> facts_hold E fs -> facts_hold E' fs.
Proof.
  intros P E E' Hev Heb fs H HF. unfold facts_hold in *. apply Forall_forall. intros f Hf.
  exact (fact_holds_agree P E E' Hev Heb f (proj1 (forallb_forall _ _) H f Hf) (proj1 (Forall_forall _ _) HF f Hf)).
Qed.

End WithSegs.
End InitAsanLib.
