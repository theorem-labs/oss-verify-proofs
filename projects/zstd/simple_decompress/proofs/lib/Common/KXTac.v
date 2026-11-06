(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge.
Import ListNotations.
Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zsa (e : zexp) : saddr := to_saddr (zx e) 0.
Definition zoff (e : zexp) : Z := a_off (zsa e).

Lemma adenot_estart : forall E a, adenot E a = Z_to_bv 64 (estart E a).
Proof. reflexivity. Qed.

Lemma estart_zx : forall zs E e, atoms_ok zs E -> zwf (length zs) e = true ->
  0 <= zden zs e - zoff e < 2^64 -> estart E (zsa e) = zden zs e.
Proof.
  intros zs E e HA HW Hr.
  pose proof (to_saddr_denot E (zx e) 0) as H. fold (zsa e) in H. rewrite adenot_estart, (zx_sound zs E e HA HW) in H.
  unfold AS.PropExec.v_addi in H. rewrite Z.add_0_r in H.
  apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H.
  rewrite !AS.PropExec.bv_wrap64_mod in H. rewrite Zmod_mod in H.
  unfold estart in *. fold (zoff e) in *.
  pose proof (bv_unsigned_in_range 64 (edenot E (a_base (zsa e)))) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 64) with (2^64) in Hb.
  set (u := bv_unsigned (edenot E (a_base (zsa e)))) in *. set (k := zoff e) in *. set (z := zden zs e) in *.
  assert (Hu : u = z - k).
  { assert (Hm : u mod 2^64 = (z - k) mod 2^64).
    { replace u with ((u + k) - k) by lia. rewrite Zminus_mod, H, <- Zminus_mod. reflexivity. }
    rewrite !Z.mod_small in Hm by lia. exact Hm. }
  lia.
Qed.

Lemma elen_zx : forall zs E e, atoms_ok zs E -> zwf (length zs) e = true ->
  0 <= zden zs e < 2^64 -> elenZ E (zx e) = zden zs e.
Proof.
  intros zs E e HA HW Hr. unfold elenZ. rewrite (zx_sound zs E e HA HW), Z_to_bv_unsigned.
  apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). exact Hr.
Qed.

(* [comment removed for export] *)
Definition zspan_ok (zs : list Z) (a n : zexp) : Prop :=
  0 <= zden zs a - zoff a < 2^64 /\ 0 <= zden zs n < 2^64 /\ 0 <= zden zs a < 2^64.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Rd.
Variable segs : list Segment.

Definition rd_at (m : word -> option byte) (A N : Z) : Prop :=
  0 <= A /\ A + N <= 2^64 /\ forall i, 0 <= i < N -> mrd segs m (wa (A + i)) <> None.

Lemma rd_at_sub : forall m A N a n, rd_at m A N -> A <= a -> a + n <= A + N -> rd_at m a n.
Proof.
  intros m A N a n (H0 & H1 & H) Ha Hn. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + i) with (A + (a - A + i)) by lia. apply H. lia.
Qed.

Lemma rd_at_bytes_at : forall m A bs, bytes_at segs m A bs -> rd_at m A (Z.of_nat (length bs)).
Proof.
  intros m A bs (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite H by lia.
  intro Hc. apply nth_error_None in Hc. lia.
Qed.

Lemma rd_at_u8arr : forall m A bs, u8arr segs m A bs -> rd_at m A (Z.of_nat (length bs)).
Proof. intros m A bs [H _]. apply rd_at_bytes_at. exact H. Qed.

Lemma rd_at_cells : forall m A cs, cells_at segs m A cs -> rd_at m A (Z.of_nat (cells_size cs)).
Proof.
  intros m A cs [Hwf Hb]. rewrite <- (cells_bytes_length cs Hwf). apply rd_at_bytes_at. exact Hb.
Qed.

Lemma rd_at_rw_cells : forall m A cs, rw_cells segs m A cs -> rd_at m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs [H _]. apply rd_at_cells. exact H. Qed.

Lemma rd_at_ro_cells : forall m A cs, ro_cells segs m A cs -> rd_at m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs H. apply rd_at_cells. exact H. Qed.

Lemma rd_at_stk : forall m lo hi, stk segs m lo hi -> lo <= hi -> rd_at m lo (hi - lo).
Proof.
  intros m lo hi (H0 & H1 & H) Hle. split; [exact H0|]. split; [lia|].
  intros i Hi. destruct (H (lo + i) ltac:(lia)) as [_ [b Hb]]. rewrite Hb. discriminate.
Qed.

Lemma wr_at_sub : forall m A N a n, wr_at segs m A N -> A <= a -> a + n <= A + N -> wr_at segs m a n.
Proof.
  intros m A N a n (H0 & H1 & H) Ha Hn. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + i) with (A + (a - A + i)) by lia. apply H. lia.
Qed.

Lemma wr_at_stk : forall m lo hi, stk segs m lo hi -> lo <= hi -> wr_at segs m lo (hi - lo).
Proof.
  intros m lo hi (H0 & H1 & H) Hle. split; [exact H0|]. split; [lia|].
  intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))).
Qed.

(* [comment removed for export] *)
Lemma kx_word_of_cells : forall m A cs (k : Z) c (w : nat) (V : word),
  cells_at segs m A cs -> 0 <= k -> cell_at cs (Z.to_nat k) = Some c -> csize c = w -> cbytes c = word_to_le_bytes w V ->
  rdn segs m (wa (A + k)) w = Some (word_to_le_bytes w V).
Proof.
  intros m A cs k c w V Hc Hk Hat Hsz Hb. pose proof (cells_at_read segs m A cs (Z.to_nat k) c Hc Hat) as H.
  rewrite Z2Nat.id in H by exact Hk. rewrite ov_rdn, Hsz, Hb in H. exact H.
Qed.

Lemma kx_u64_range : forall w : word, 0 <= bv_unsigned w < 18446744073709551616.
Proof. intro w. exact (bv_unsigned_in_range 64 w). Qed.

(* [comment removed for export] *)
Fixpoint rom_range_b (A : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match seg_rom segs (wa A) with Some _ => rom_range_b (A + 1) n' | None => false end
  end.

Lemma rom_range_b_sound : forall n A, rom_range_b A n = true -> forall i, 0 <= i < Z.of_nat n -> seg_rom segs (wa (A + i)) <> None.
Proof.
  induction n as [|n IH]; intros A H i Hi; [lia|]. cbn [rom_range_b] in H.
  destruct (seg_rom segs (wa A)) eqn:E; [|discriminate H].
  destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite Z.add_0_r, E; discriminate|].
  replace (A + i) with (A + 1 + (i - 1)) by lia. apply IH; [exact H|lia].
Qed.

Lemma rd_at_img : forall m A n, 0 <= A -> A + Z.of_nat n <= 2^64 -> rom_range_b A n = true -> rd_at m A (Z.of_nat n).
Proof.
  intros m A n H0 H1 Hb. split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold mrd. destruct (m (wa (A + i))); [discriminate|]. exact (rom_range_b_sound n A Hb i Hi).
Qed.

Lemma rd_at_imgZ : forall m A N, 0 <= A -> 0 <= N -> A + N <= 2^64 -> rom_range_b A (Z.to_nat N) = true -> rd_at m A N.
Proof. intros m A N H0 HN H1 Hb. rewrite <- (Z2Nat.id N HN). apply rd_at_img; [exact H0 | rewrite Z2Nat.id by exact HN; exact H1 | exact Hb]. Qed.

Lemma rdn_rd_at : forall m (n : nat) s, (forall i, 0 <= i < Z.of_nat n -> mrd segs m (wa (s + i)) <> None) ->
  rdn segs m (wa s) n <> None.
Proof.
  intros m n. induction n as [|n IH]; intros s H; [discriminate|].
  cbn [rdn]. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold mrd in H0.
  destruct (match m (wa s) with Some b => Some b | None => seg_rom segs (wa s) end) as [b|]; [|congruence].
  rewrite wa_succ. specialize (IH (s + 1)).
  destruct (rdn segs m (wa (s + 1)) n); [discriminate|].
  exfalso. apply IH; [|reflexivity]. intros i Hi. replace (s + 1 + i) with (s + (1 + i)) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Fixpoint ro_range_b (A : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => ro_addr segs (wa A) && ro_range_b (A + 1) n'
  end.

Lemma ro_range_b_sound : forall n A, ro_range_b A n = true -> forall i, 0 <= i < Z.of_nat n -> ro_addr segs (wa (A + i)) = true.
Proof.
  induction n as [|n IH]; intros A H i Hi; [lia|]. cbn [ro_range_b] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite Z.add_0_r; exact H1|].
  replace (A + i) with (A + 1 + (i - 1)) by lia. apply IH; [exact H2|lia].
Qed.

Lemma kx_img_none : forall m lo (n : nat) hi, mem_inv segs m -> ro_range_b lo n = true -> hi = lo + Z.of_nat n ->
  forall i, lo <= i < hi -> m (wa i) = None.
Proof.
  intros m lo n hi MI Hb -> i Hi. destruct (m (wa i)) as [b|] eqn:E; [|reflexivity].
  pose proof (MI _ _ E) as Hro. replace i with (lo + (i - lo)) in Hro by lia.
  rewrite (ro_range_b_sound n lo Hb (i - lo)) in Hro by lia. discriminate Hro.
Qed.

End Rd.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive zk : Type :=
| ZKRange (e : zexp) (lo hi : Z)
| ZKDisj (a1 n1 a2 n2 : zexp)
| ZKWr (a n : zexp)
| ZKImg (lo hi : Z)
| ZKAlign (e : zexp) (m : Z)
| ZKWord (a : zexp) (w : nat) (v : zexp)
| ZKZero (a n : zexp)
| ZKWrImg (a n : zexp) (lo hi : Z)   (* [comment removed for export] *)
| ZKTbl (a : zexp) (size stride off lo hi : Z)   (* [comment removed for export] *)
| ZKTblLog (a sh : zexp) (stride off lo hi : Z). (* [comment removed for export] *)

Definition zk_kentry (k : zk) : kentry :=
  match k with
  | ZKRange e lo hi => KRange (zx e) lo hi
  | ZKDisj a1 n1 a2 n2 => KDisj (zsa a1) (zx n1) (zsa a2) (zx n2)
  | ZKWr a n => KWr (zsa a) (zx n)
  | ZKImg lo hi => KImg lo hi
  | ZKAlign e m => KAlign (zx e) m
  | ZKWord a w v => KWord (zsa a) w (zx v)
  | ZKZero a n => KZero (zsa a) (zx n)
  | ZKWrImg a n lo hi => KDisj (zsa a) (zx n) (SA (ELit 0) lo) (ELit (hi - lo))
  | ZKTbl _ _ _ _ _ _ => KRange (ELit 0) 0 0   (* [comment removed for export] *)
  | ZKTblLog _ _ _ _ _ _ => KRange (ELit 0) 0 0
  end.

Definition zk_wf (nz : nat) (k : zk) : bool :=
  match k with
  | ZKRange e lo hi => zwf nz e && Z.leb 0 lo && Z.ltb hi (2^64)
  | ZKDisj a1 n1 a2 n2 => zwf nz a1 && zwf nz n1 && zwf nz a2 && zwf nz n2
  | ZKWr a n | ZKZero a n => zwf nz a && zwf nz n
  | ZKImg lo hi => Z.leb 0 lo && Z.leb hi (2^64)
  | ZKAlign e m => zwf nz e && Z.ltb 0 m
  | ZKWord a w v => zwf nz a && zwf nz v && Nat.leb 1 w && Nat.leb w 8
  | ZKWrImg a n lo hi => zwf nz a && zwf nz n && Z.leb 0 lo && Z.ltb lo hi && Z.ltb hi (2^64)
  | ZKTbl a size stride off lo hi => zwf nz a
  | ZKTblLog a sh stride off lo hi => zwf nz a && zwf nz sh
  end.

Section ZK.
Variable segs : list Segment.
Variable m : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tbl_in (A size stride off lo hi : Z) : Prop :=
  forall i, 0 <= i -> stride * i + off < size ->
    lo <= bv_unsigned (rdval segs m (wa (A + stride * i + off)) 1 false) <= hi.

Definition tbl_in_log (A sh stride off lo hi : Z) : Prop :=
  forall i, 0 <= i < 2 ^ (64 - sh) ->
    lo <= bv_unsigned (rdval segs m (wa (A + stride * i + off)) 1 false) <= hi.

Definition zk_prop (zs : list Z) (k : zk) : Prop :=
  match k with
  | ZKRange e lo hi => lo <= zden zs e <= hi
  | ZKDisj a1 n1 a2 n2 =>
      zspan_ok zs a1 n1 /\ zspan_ok zs a2 n2 /\
      (zden zs a1 + zden zs n1 <= zden zs a2 \/ zden zs a2 + zden zs n2 <= zden zs a1)
  | ZKWr a n => zspan_ok zs a n /\ wr_at segs m (zden zs a) (zden zs n)
  | ZKImg lo hi => forall i, lo <= i < hi -> m (wa i) = None
  | ZKAlign e mm => 0 <= zden zs e < 2^64 /\ zden zs e mod mm = 0
  | ZKWord a w v =>
      0 <= zden zs a - zoff a < 2^64 /\ 0 <= zden zs a /\ zden zs a + Z.of_nat w <= 2^64 /\
      rdn segs m (wa (zden zs a)) w = Some (word_to_le_bytes w (Z_to_bv 64 (zden zs v)))
  | ZKZero a n => zspan_ok zs a n /\ zden zs a + zden zs n <= 2^64 /\
      forall i, 0 <= i < zden zs n -> m (wa (zden zs a + i)) = Some (Z_to_bv 8 0)
  | ZKWrImg a n lo hi =>
      zspan_ok zs a n /\ 0 < zden zs n /\ wr_at segs m (zden zs a) (zden zs n) /\ mem_inv segs m /\
      ro_range_b segs lo (Z.to_nat (hi - lo)) = true
  | ZKTbl a size stride off lo hi => 0 <= zden zs a - zoff a < 2^64 /\ tbl_in (zden zs a) size stride off lo hi
  | ZKTblLog a sh stride off lo hi =>
      0 <= zden zs a - zoff a < 2^64 /\ 0 <= zden zs sh < 64 /\ tbl_in_log (zden zs a) (zden zs sh) stride off lo hi
  end.

Lemma zk_ent : forall zs E k, atoms_ok zs E -> zk_wf (length zs) k = true -> zk_prop zs k -> kentry_ok segs E m (zk_kentry k).
Proof.
  intros zs E k HA HW HP. destruct k as [e lo hi|a1 n1 a2 n2|a n|lo hi|e mm|a w v|a n|a n lo hi|a size stride off lo hi|a sh stride off lo hi]; cbn [zk_wf zk_prop zk_kentry kentry_ok] in *;
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
  - (* [comment removed for export] *)
    match goal with H : Z.leb 0 lo = true |- _ => apply Z.leb_le in H end.
    match goal with H : Z.ltb hi _ = true |- _ => apply Z.ltb_lt in H end.
    rewrite (zx_sound zs E e HA) by assumption. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia). lia.
  - (* [comment removed for export] *)
    destruct HP as ((S1 & L1 & B1) & (S2 & L2 & B2) & HD).
    rewrite !(estart_zx zs E) by assumption. rewrite !(elen_zx zs E) by assumption. exact HD.
  - (* [comment removed for export] *)
    destruct HP as ((S1 & L1 & B1) & (W0 & W1 & WW)).
    unfold flat. rewrite !(estart_zx zs E) by assumption. rewrite !(elen_zx zs E) by assumption.
    split; [lia|]. intros d mm Hd Hm.
    apply (wr_at_store_ok segs m (zden zs a) (zden zs n)); [split; [exact W0|split; [exact W1|exact WW]] | exact Hd | exact Hm].
  - (* [comment removed for export] *)
    match goal with H : Z.leb 0 lo = true |- _ => apply Z.leb_le in H end.
    match goal with H : Z.leb hi _ = true |- _ => apply Z.leb_le in H end.
    split; [assumption|]. split; [assumption|]. exact HP.
  - (* [comment removed for export] *)
    match goal with H : Z.ltb 0 mm = true |- _ => apply Z.ltb_lt in H end.
    destruct HP as [R M]. split; [assumption|].
    rewrite (zx_sound zs E e HA) by assumption. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia). exact M.
  - (* [comment removed for export] *)
    destruct HP as (S1 & S0 & S2 & HR).
    match goal with H : Nat.leb 1 w = true |- _ => apply Nat.leb_le in H end.
    match goal with H : Nat.leb w 8 = true |- _ => apply Nat.leb_le in H end.
    split; [assumption|]. unfold flat. rewrite adenot_estart, !(estart_zx zs E), (zx_sound zs E v) by assumption.
    split; [lia|]. exact HR.
  - (* [comment removed for export] *)
    destruct HP as ((S1 & L1 & B1) & S2 & HZ).
    unfold flat. rewrite !(estart_zx zs E) by assumption. rewrite !(elen_zx zs E) by assumption.
    split; [lia|]. exact HZ.
  - (* [comment removed for export] *)
    destruct HP as ((S1 & L1 & B1) & NP & (W0 & W1 & WW) & MI & RO).
    repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H end.
    rewrite (estart_zx zs E a) by assumption. rewrite (elen_zx zs E n) by assumption.
    unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite !Z_to_bv_unsigned.
    rewrite (bv_wrap_small 64 0) by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
    rewrite (bv_wrap_small 64 (hi - lo)) by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
    destruct (Z_le_gt_dec (zden zs a + zden zs n) lo) as [L|G]; [left; lia|].
    destruct (Z_le_gt_dec hi (zden zs a)) as [L2|G2]; [right; lia|]. exfalso.
    set (x := Z.max (zden zs a) lo).
    assert (X1 : zden zs a <= x < zden zs a + zden zs n) by (unfold x; lia).
    assert (X2 : lo <= x < hi) by (unfold x; lia).
    pose proof (WW (x - zden zs a) ltac:(lia)) as Hw. replace (zden zs a + (x - zden zs a)) with x in Hw by lia.
    pose proof (ro_range_b_sound segs (Z.to_nat (hi - lo)) lo RO (x - lo) ltac:(lia)) as Hro.
    replace (lo + (x - lo)) with x in Hro by lia.
    destruct (m (wa x)) as [b|] eqn:Em.
    + pose proof (MI _ _ Em) as Hc. rewrite Hro in Hc. discriminate Hc.
    + pose proof (wview_not_ro segs m (wa x) Hw Em) as Hc. rewrite Hro in Hc. discriminate Hc.
  - (* [comment removed for export] *)
    cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia). lia.
  - cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia). lia.
Qed.

Lemma zks_ent : forall zs E ks, atoms_ok zs E -> forallb (zk_wf (length zs)) ks = true -> Forall (zk_prop zs) ks ->
  know_ok segs E m (map zk_kentry ks).
Proof.
  intros zs E ks HA HW HP. unfold know_ok. induction HP as [|k ks Hk _ IH]; cbn [map]; [constructor|].
  cbn [forallb] in HW. apply andb_prop in HW as [W1 W2]. constructor; [exact (zk_ent zs E k HA W1 Hk) | exact (IH W2)].
Qed.

(* [comment removed for export] *)
Definition zk_tfs (ks : list zk) : list tblfact :=
  flat_map (fun k => match k with
                     | ZKTbl a size stride off lo hi => [(zsa a, size, stride, off, lo, hi, None)]
                     | ZKTblLog a sh stride off lo hi => [(zsa a, 0, stride, off, lo, hi, Some (zx sh))]
                     | _ => []
                     end) ks.

Lemma zk_tfs_ok : forall zs E ks, atoms_ok zs E -> forallb (zk_wf (length zs)) ks = true -> Forall (zk_prop zs) ks ->
  Forall (tf_ok segs m E) (zk_tfs ks).
Proof.
  intros zs E ks HA HW HP. induction HP as [|k ks Hk _ IH]; cbn [zk_tfs flat_map]; [constructor|].
  cbn [forallb] in HW. apply andb_prop in HW as [W1 W2]. specialize (IH W2). fold (zk_tfs ks).
  destruct k; try exact IH; cbn [app]; (constructor; [|exact IH]); cbn [zk_wf zk_prop] in W1, Hk.
  - destruct Hk as [R T]. cbn [tf_ok]. intros i I0 I1.
    rewrite (estart_zx zs E a HA W1 R). exact (T i I0 I1).
  - apply andb_prop in W1 as [Wa Ws]. destruct Hk as (R & RS & T). cbn [tf_ok]. intros i I0.
    rewrite (estart_zx zs E a HA Wa R).
    rewrite (zx_sound zs E sh HA Ws), Z_to_bv_unsigned, bv_wrap_small, (Z.mod_small (zden zs sh) 64) in I0
      by (try (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64)); lia).
    exact (T i I0).
Qed.

Lemma firstn1_skipn : forall (k : nat) (bs : list byte) b, nth_error bs k = Some b -> firstn 1 (skipn k bs) = [b].
Proof.
  induction k as [|k IH]; intros [|x bs] b H; cbn in H; try discriminate H.
  - injection H as ->. reflexivity.
  - cbn [skipn]. exact (IH bs b H).
Qed.

Lemma rdval_bytes_at_1 : forall A bs k b, bytes_at segs m A bs -> 0 <= k -> nth_error bs (Z.to_nat k) = Some b ->
  bv_unsigned (rdval segs m (wa (A + k)) 1 false) = bv_unsigned b.
Proof.
  intros A bs k b HB Hk Hn. unfold rdval.
  assert (L : (Z.to_nat k + 1 <= length bs)%nat).
  { assert (Z.to_nat k < length bs)%nat by (apply nth_error_Some; rewrite Hn; discriminate). lia. }
  pose proof (bytes_at_rdn segs m A bs (Z.to_nat k) 1 HB L) as H. rewrite Z2Nat.id in H by lia. rewrite H.
  rewrite (firstn1_skipn _ _ _ Hn). unfold extz. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in R.
  change (2 ^ Z.of_N 64) with (2^64). lia.
Qed.

(* [comment removed for export] *)
Lemma tbl_in_bytes_at : forall A bs stride off lo hi, bytes_at segs m A bs -> 0 <= stride -> 0 <= off ->
  (forall i, 0 <= i -> stride * i + off < Z.of_nat (length bs) ->
     exists b, nth_error bs (Z.to_nat (stride * i + off)) = Some b /\ lo <= bv_unsigned b <= hi) ->
  tbl_in A (Z.of_nat (length bs)) stride off lo hi.
Proof.
  intros A bs stride off lo hi HB Hs Ho HP i I0 I1. destruct (HP i I0 I1) as (b & Hn & Hr).
  assert (K0 : 0 <= stride * i + off) by nia.
  replace (A + stride * i + off) with (A + (stride * i + off)) by lia.
  rewrite (rdval_bytes_at_1 A bs (stride * i + off) b HB K0 Hn). exact Hr.
Qed.

Lemma tbl_in_log_bytes_at : forall A bs sh stride off lo hi, bytes_at segs m A bs -> 0 <= stride -> 0 <= off ->
  (forall i, 0 <= i < 2 ^ (64 - sh) ->
     exists b, nth_error bs (Z.to_nat (stride * i + off)) = Some b /\ lo <= bv_unsigned b <= hi) ->
  tbl_in_log A sh stride off lo hi.
Proof.
  intros A bs sh stride off lo hi HB Hs Ho HP i I0. destruct (HP i I0) as (b & Hn & Hr).
  assert (K0 : 0 <= stride * i + off) by nia.
  replace (A + stride * i + off) with (A + (stride * i + off)) by lia.
  rewrite (rdval_bytes_at_1 A bs (stride * i + off) b HB K0 Hn). exact Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zreg : Type := (zexp * zexp)%type.
Definition zreg_wf (nz : nat) (r : zreg) : bool := zwf nz (fst r) && zwf nz (snd r).
Definition zreg_prop (zs : list Z) (r : zreg) : Prop :=
  let '(a, n) := r in zspan_ok zs a n /\ rd_at segs m (zden zs a) (zden zs n).
Definition zwin_prop (RNG : footprint) (zs : list Z) (r : zreg) : Prop :=
  let '(a, n) := r in zspan_ok zs a n /\ rng RNG (zden zs a) (zden zs n).

(* [comment removed for export] *)
Definition kx_cov (kn : list kentry) (rs : list zreg) (a : saddr) (n : nat) : bool :=
  existsb (fun r : zreg => xinside kn (a_base a) (a_off a) (ELit (Z.of_nat n)) (a_base (zsa (fst r))) (zoff (fst r)) (zx (snd r))) rs.

Lemma sa_eta : forall a : saddr, SA (a_base a) (a_off a) = a.
Proof. intros [b k]. reflexivity. Qed.

Lemma kx_cov_sound : forall zs E kn rs a n, atoms_ok zs E -> know_ok segs E m kn ->
  forallb (zreg_wf (length zs)) rs = true -> Forall (fun r : zreg => zspan_ok zs (fst r) (snd r)) rs ->
  (n <= 8)%nat -> kx_cov kn rs a n = true ->
  exists r, In r rs /\ zden zs (fst r) <= estart E a /\ estart E a + Z.of_nat n <= zden zs (fst r) + zden zs (snd r).
Proof.
  intros zs E kn rs a n HA HK HW HS Hn Hc. unfold kx_cov in Hc. apply existsb_exists in Hc as (r & Hin & Hx).
  exists r. split; [exact Hin|].
  rewrite forallb_forall in HW. specialize (HW r Hin). unfold zreg_wf in HW. apply andb_prop in HW as [W1 W2].
  rewrite Forall_forall in HS. destruct (HS r Hin) as (S1 & S2 & S3).
  pose proof (xinside_sound segs E m kn _ _ _ _ _ _ HK Hx) as [A B].
  unfold zoff in A, B. rewrite !sa_eta in A, B.
  rewrite (estart_zx zs E (fst r) HA W1 S1) in A, B. rewrite (elen_zx zs E (snd r) HA W2 S2) in B.
  unfold elenZ in B. cbn [edenot] in B. rewrite Z_to_bv_unsigned, bv_wrap_small in B by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  split; [exact A | exact B].
Qed.

Definition sc_auto (kn : list kentry) (rs : list zreg) (sc : sidecond) : bool :=
  match sc with
  | SCReadBase a n _ _ => Nat.leb n 8 && kx_cov kn rs a n
  | SCFlat a (ELit z) => Z.leb 1 z && Z.leb z 8 && kx_cov kn rs a (Z.to_nat z)
  | _ => false
  end.

Lemma sc_auto_sound : forall zs E kn rs sc, atoms_ok zs E -> know_ok segs E m kn ->
  forallb (zreg_wf (length zs)) rs = true -> Forall (zreg_prop zs) rs ->
  sc_auto kn rs sc = true -> sc_resid segs m E sc.
Proof.
  intros zs E kn rs sc HA HK HW HR Hc.
  assert (HS : Forall (fun r : zreg => zspan_ok zs (fst r) (snd r)) rs) by (eapply Forall_impl; [|exact HR]; intros [ra rn] [H _]; exact H).
  destruct sc as [| a n | | | | a n sx e |]; try discriminate Hc; cbn [sc_auto] in Hc.
  - (* [comment removed for export] *)
    destruct n as [z| | | | | | |]; try discriminate Hc.
    apply andb_prop in Hc as [Hc Hcov]. apply andb_prop in Hc as [Z1 Z8]. apply Z.leb_le in Z1, Z8.
    destruct (kx_cov_sound zs E kn rs a (Z.to_nat z) HA HK HW HS ltac:(lia) Hcov) as (r & Hin & A & B).
    rewrite Forall_forall in HR. pose proof (HR r Hin) as HRr. destruct r as [ra rn]. destruct HRr as (_ & R0 & R1 & _). cbn [fst snd] in *.
    cbn [sc_resid sc_denot]. unfold flat, elenZ. cbn [edenot].
    rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia). lia.
  - (* [comment removed for export] *)
    apply andb_prop in Hc as [N8 Hcov]. apply Nat.leb_le in N8.
    destruct (kx_cov_sound zs E kn rs a n HA HK HW HS N8 Hcov) as (r & Hin & A & B).
    rewrite Forall_forall in HR. pose proof (HR r Hin) as HRr. destruct r as [ra rn]. destruct HRr as (_ & R0 & R1 & RR). cbn [fst snd] in *.
    cbn [sc_resid]. unfold rd_ok. rewrite adenot_estart. apply rdn_rd_at.
    intros i Hi. replace (estart E a + i) with (zden zs ra + (estart E a - zden zs ra + i)) by lia. apply RR. lia.
Qed.

Definition acc_auto (kn : list kentry) (ws : list zreg) (an : saddr * nat) : bool :=
  Nat.leb 1 (snd an) && Nat.leb (snd an) 8 && kx_cov kn ws (fst an) (snd an).

Lemma acc_auto_sound : forall RNG zs E kn ws an, atoms_ok zs E -> know_ok segs E m kn ->
  forallb (zreg_wf (length zs)) ws = true -> Forall (zwin_prop RNG zs) ws ->
  acc_auto kn ws an = true -> accP E RNG an.
Proof.
  intros RNG zs E kn ws [a n] HA HK HW HR Hc.
  assert (HS : Forall (fun r : zreg => zspan_ok zs (fst r) (snd r)) ws) by (eapply Forall_impl; [|exact HR]; intros [ra rn] [H _]; exact H).
  unfold acc_auto in Hc. cbn [fst snd] in Hc. apply andb_prop in Hc as [Hc Hcov]. apply andb_prop in Hc as [N1 N8].
  apply Nat.leb_le in N1, N8.
  destruct (kx_cov_sound zs E kn ws a n HA HK HW HS N8 Hcov) as (r & Hin & A & B).
  rewrite Forall_forall in HR. pose proof (HR r Hin) as HRr. destruct r as [ra rn]. destruct HRr as (_ & R0 & R1 & RR). cbn [fst snd] in *.
  unfold accP. cbn [fst snd]. rewrite adenot_estart, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  apply RR; lia.
Qed.

End ZK.

(* [comment removed for export] *)
Definition acc_eqb (x y : saddr * nat) : bool := saddr_eqb (fst x) (fst y) && Nat.eqb (snd x) (snd y).
Definition acc_mem (x : saddr * nat) (l : list (saddr * nat)) : bool := existsb (acc_eqb x) l.
Lemma acc_mem_In : forall x l, acc_mem x l = true -> In x l.
Proof.
  intros [a n] l H. apply existsb_exists in H as ([a' n'] & Hin & He). unfold acc_eqb in He. cbn [fst snd] in He.
  apply andb_prop in He as [H1 H2]. apply saddr_eqb_eq in H1. apply Nat.eqb_eq in H2. subst. exact Hin.
Qed.

(* [comment removed for export] *)
Definition kx_bc_eqb (x y : branch_cond) : bool :=
  match x, y with
  | BC_EQ, BC_EQ | BC_NE, BC_NE | BC_LT, BC_LT | BC_GE, BC_GE | BC_LTU, BC_LTU | BC_GEU, BC_GEU => true
  | _, _ => false
  end.
Definition sc_eqbx (x y : sidecond) : bool :=
  match x, y with
  | SCReadBase a n sx e, SCReadBase a' n' sx' e' => saddr_eqb a a' && Nat.eqb n n' && Bool.eqb sx sx' && expr_eqb e e'
  | SCEq a b, SCEq a' b' => expr_eqb a a' && expr_eqb b b'
  | SCBr t c a b, SCBr t' c' a' b' => Bool.eqb t t' && kx_bc_eqb c c' && expr_eqb a a' && expr_eqb b b'
  | _, _ => sidecond_eqb x y
  end.
Lemma sc_eqbx_eq : forall x y, sc_eqbx x y = true -> x = y.
Proof.
  intros x y H.
  destruct x, y; cbn [sc_eqbx] in H; try (apply sidecond_eqb_eq; exact H);
    repeat match goal with X : (_ && _)%bool = true |- _ => apply andb_prop in X; destruct X end;
    repeat match goal with
      | X : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in X
      | X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X
      | X : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in X
      | X : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in X
      end; subst; try reflexivity.
  match goal with X : kx_bc_eqb ?c ?c' = true |- _ => destruct c, c'; try discriminate X end; reflexivity.
Qed.
Fixpoint sc_memx (x : sidecond) (l : list sidecond) : bool :=
  match l with [] => false | y :: t => if sc_eqbx x y then true else sc_memx x t end.
Lemma sc_memx_In : forall x l, sc_memx x l = true -> In x l.
Proof.
  induction l as [|y t IH]; cbn [sc_memx]; intros H; [discriminate|].
  destruct (sc_eqbx x y) eqn:Ex; [left; symmetry; apply sc_eqbx_eq; exact Ex | right; exact (IH H)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Go.
Variable segs : list Segment.
Variables (F : bvmap 5 word) (fc : bv 32).

(* [comment removed for export] *)
Definition kx_chk (zs : list Z) (rz : list zexp) (zks : list zk) (rk : list kentry) (rs : list zreg)
                  (reads : list rdspec) (scs rest : list sidecond) : bool :=
  let nz := length zs in
  let kn := map zk_kentry zks ++ rk in
  forallb (zwf nz) rz && rds_chk nz 0 reads && forallb (sc_rd_chk nz reads) scs && forallb (rk_chk (map zk_kentry zks) (zk_tfs zks) nz reads) rk
  && forallb (zk_wf nz) zks && forallb (zreg_wf nz) rs
  && forallb (fun sc => sc_auto kn rs sc || sc_memx sc rest) scs.

Definition kx_chkF (zs : list Z) (rk : list kentry) (zks : list zk) (ws : list zreg) (accs arest : list (saddr * nat)) : bool :=
  let kn := map zk_kentry zks ++ rk in
  forallb (zreg_wf (length zs)) ws && forallb (fun an => acc_auto kn ws an || acc_mem an arest) accs.

Lemma kx_scs_bulk : forall m zs E kn rs scs rest, atoms_ok zs E -> know_ok segs E m kn ->
  forallb (zreg_wf (length zs)) rs = true -> Forall (zreg_prop segs m zs) rs ->
  forallb (fun sc => sc_auto kn rs sc || sc_memx sc rest) scs = true ->
  Forall (sc_resid segs m E) rest -> Forall (sc_resid segs m E) scs.
Proof.
  intros m zs E kn rs scs rest HA HK HW HR Hc Hrest. rewrite forallb_forall in Hc. apply Forall_forall. intros sc Hin.
  specialize (Hc sc Hin). apply orb_prop in Hc as [Hc|Hc].
  - exact (sc_auto_sound segs m zs E kn rs sc HA HK HW HR Hc).
  - apply sc_memx_In in Hc. rewrite Forall_forall in Hrest. exact (Hrest sc Hc).
Qed.

Lemma kx_accs_bulk : forall m RNG zs E kn ws accs arest, atoms_ok zs E -> know_ok segs E m kn ->
  forallb (zreg_wf (length zs)) ws = true -> Forall (zwin_prop RNG zs) ws ->
  forallb (fun an => acc_auto kn ws an || acc_mem an arest) accs = true ->
  Forall (accP E RNG) arest -> Forall (accP E RNG) accs.
Proof.
  intros m RNG zs E kn ws accs arest HA HK HW HR Hc Hrest. rewrite forallb_forall in Hc. apply Forall_forall. intros an Hin.
  specialize (Hc an Hin). apply orb_prop in Hc as [Hc|Hc].
  - exact (acc_auto_sound segs m RNG zs E kn ws an HA HK HW HR Hc).
  - apply acc_mem_In in Hc. rewrite Forall_forall in Hrest. exact (Hrest an Hc).
Qed.

Theorem kx_go_evt : forall (Q : machine_state -> Prop) fuel stops dirs zs rz xs zks rk pc m rom ss' scs scr' accs reads rs rest,
  kx_exec segs fuel true stops (SCR dirs [] []) (SS pc (ELit 0 :: map zx rz) [] (map zk_kentry zks ++ rk) (length zs)) [] []
    = (ss', scs, scr', accs) ->
  kx_chk zs rz zks rk rs reads scs rest = true ->
  Forall2 (fun e x => x = Z_to_bv 64 (zden zs e)) rz xs ->
  Forall (zk_prop segs m zs) zks ->
  Forall (zreg_prop segs m zs) rs ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (map zk_kentry zks ++ rk) -> Forall (sc_resid segs m E) rest) ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (map zk_kentry zks ++ rk) -> log_flat E (s_log ss') ->
     (mem_inv segs m -> mem_inv segs (mem_denot E m (s_log ss'))) ->
     evt segs Q (MS (kx_regs E (s_regs ss')) F (Z_to_bv 64 (s_pc ss')) fc None (mem_denot E m (s_log ss')) rom)) ->
  evt segs Q (MS (mkRl xs) F (Z_to_bv 64 pc) fc None m rom).
Proof.
  intros Q fuel stops dirs zs rz xs zks rk pc m rom ss' scs scr' accs reads rs rest Hex Hchk Hregs Hzk Hrs Hrest K.
  unfold kx_chk in Hchk. repeat (apply andb_prop in Hchk as [Hchk ?]).
  eapply (kx_run_evt segs F fc Q fuel stops dirs zs rz xs (map zk_kentry zks) (zk_tfs zks) rk pc m rom ss' scs scr' accs reads); try eassumption.
  - intros E HE. apply (zks_ent segs m zs E zks (proj1 HE)); assumption.
  - intros E HE. apply (zk_tfs_ok segs m zs E zks (proj1 HE)); assumption.
  - intros E HE HK. eapply (kx_scs_bulk m zs E _ rs scs rest (proj1 HE) HK); try eassumption. exact (Hrest E HE HK).
Qed.

Theorem kx_go_evtF : forall RNG (Q : machine_state -> Prop) fuel stops dirs zs rz xs zks rk pc m rom ss' scs scr' accs reads rs rest ws arest,
  kx_exec segs fuel true stops (SCR dirs [] []) (SS pc (ELit 0 :: map zx rz) [] (map zk_kentry zks ++ rk) (length zs)) [] []
    = (ss', scs, scr', accs) ->
  kx_chk zs rz zks rk rs reads scs rest = true ->
  kx_chkF zs rk zks ws accs arest = true ->
  Forall2 (fun e x => x = Z_to_bv 64 (zden zs e)) rz xs ->
  Forall (zk_prop segs m zs) zks ->
  Forall (zreg_prop segs m zs) rs ->
  Forall (zwin_prop RNG zs) ws ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (map zk_kentry zks ++ rk) -> Forall (sc_resid segs m E) rest) ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (map zk_kentry zks ++ rk) -> Forall (accP E RNG) arest) ->
  (forall E, kx_env_ok segs m zs reads E -> know_ok segs E m (map zk_kentry zks ++ rk) -> log_flat E (s_log ss') ->
     (mem_inv segs m -> mem_inv segs (mem_denot E m (s_log ss'))) ->
     evtF segs RNG Q (MS (kx_regs E (s_regs ss')) F (Z_to_bv 64 (s_pc ss')) fc None (mem_denot E m (s_log ss')) rom)) ->
  evtF segs RNG Q (MS (mkRl xs) F (Z_to_bv 64 pc) fc None m rom).
Proof.
  intros RNG Q fuel stops dirs zs rz xs zks rk pc m rom ss' scs scr' accs reads rs rest ws arest Hex Hchk HchkF Hregs Hzk Hrs Hws Hrest Harest K.
  unfold kx_chk in Hchk. repeat (apply andb_prop in Hchk as [Hchk ?]).
  unfold kx_chkF in HchkF. apply andb_prop in HchkF as [HF1 HF2].
  eapply (kx_run_evtF segs F fc RNG Q fuel stops dirs zs rz xs (map zk_kentry zks) (zk_tfs zks) rk pc m rom ss' scs scr' accs reads); try eassumption.
  - intros E HE. apply (zks_ent segs m zs E zks (proj1 HE)); assumption.
  - intros E HE. apply (zk_tfs_ok segs m zs E zks (proj1 HE)); assumption.
  - intros E HE HK. eapply (kx_scs_bulk m zs E _ rs scs rest (proj1 HE) HK); try eassumption. exact (Hrest E HE HK).
  - intros E HE HK. eapply (kx_accs_bulk m RNG zs E _ ws accs arest (proj1 HE) HK); try eassumption. exact (Harest E HE HK).
Qed.

End Go.
