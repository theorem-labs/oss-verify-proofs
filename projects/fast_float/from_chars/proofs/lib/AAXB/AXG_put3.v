(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import RefMemcpyLib SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AxAsan AXG_put AXG_put2.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Lemma wview_frame : forall m m' x, m' (wa x) = m (wa x) -> wview SEGS m' (wa x) = wview SEGS m (wa x).
Proof. intros m m' x H. unfold wview. rewrite H. reflexivity. Qed.

Lemma wview_grows : forall m m' x, mem_grows m m' -> wview SEGS m (wa x) <> None -> wview SEGS m' (wa x) <> None.
Proof.
  intros m m' x G H. unfold wview in *. destruct (m (wa x)) as [b|] eqn:E.
  - assert (Hn : m (wa x) <> None) by (rewrite E; discriminate). pose proof (G _ Hn) as Hn'.
    destruct (m' (wa x)); [discriminate | exfalso; exact (Hn' eq_refl)].
  - destruct (m' (wa x)); [discriminate | exact H].
Qed.

(* [comment removed for export] *)
Lemma INV_D_frame : forall m m' D1 B1 n F st, INV_D m D1 B1 n F st ->
  (forall x, 0 <= x < 2^64 -> downed D1 B1 x -> m' (wa x) = m (wa x)) -> INV_D m' D1 B1 n F st.
Proof.
  intros m m' D1 B1 n F st I HF. destruct I as [In Inr Imap ID1 Itab IF Ist IFr IB1 IB1r Iwr Isep In0].
  assert (HD : forall a w, downed D1 B1 a -> downed D1 B1 (a + Z.of_nat w - 1) -> 0 <= a -> a + Z.of_nat w <= 2^64 ->
                 (forall x, a <= x < a + Z.of_nat w -> downed D1 B1 x) -> forall x, a <= x < a + Z.of_nat w -> m' (wa x) = m (wa x)).
  { intros a w _ _ Ha Hw Hall x Hx. apply HF; [lia | exact (Hall x Hx)]. }
  constructor; try assumption.
  - apply (rd_frame m m'); [lia | cbn; lia | | exact In]. intros x Hx. apply HF; [zn; lia|]. unfold downed in *. zn. lia.
  - apply (rd_frame m m'); [lia | cbn; lia | | exact Imap]. intros x Hx. apply HF; [zn; lia|]. unfold downed in *. zn. lia.
  - intros b Hb. destruct (Itab b Hb) as (hd & Hhd & Rhd & k & Hc). exists hd. split; [exact Hhd|]. split.
    + apply (rd_frame m m'); [lia | cbn; lia | | exact Rhd]. intros x Hx. apply HF; [zn; lia|]. unfold downed in *. zn. lia.
    + exists k. apply (chainz_frame m m' D1 n k hd); [lia | lia | lia | | exact Hc]. intros x Hx. apply HF; [lia|]. unfold downed. lia.
  - apply (rd_frame m m'); [lia | cbn; lia | | exact IF]. intros x Hx. apply HF; [zn; lia|]. unfold downed in *. zn. lia.
  - apply (rd_frame m m'); [lia | cbn; lia | | exact Ist]. intros x Hx. apply HF; [zn; lia|]. unfold downed in *. zn. lia.
  - apply (rd_frame m m'); [lia | cbn; lia | | exact IB1]. intros x Hx. apply HF; [zn; lia|]. unfold downed in *. zn. lia.
  - intros x Hx. assert (Hr : 0 <= x < 2^64) by (unfold downed in Hx; lia).
    rewrite (wview_frame m m' x (HF x Hr Hx)). exact (Iwr x Hx).
  - destruct In0 as (hv & lk & H1 & H2 & R1 & R2). destruct ID1 as (D1a & D1b & D1c). exists hv, lk. split; [exact H1|]. split; [exact H2|].
    split; [apply (rd_frame m m'); [lia | zn; lia | | exact R1] | apply (rd_frame m m'); [lia | zn; lia | | exact R2]].
    all: intros x Hx; apply HF; [zn; lia | unfold downed; zn; lia].
Qed.

Lemma chainz_range : forall m D1 n k id, chainz m D1 n k id -> id = 0 \/ 1 <= id <= n.
Proof. intros m D1 n [|k] id H; cbn [chainz] in H; [left; exact H|]. destruct H as [H|(H & _)]; [left; exact H | right; exact H]. Qed.

(* [comment removed for export] *)
Lemma rd_inj : forall m a w v1 v2, (w <= 8)%nat -> 0 <= v1 < 2^(8 * Z.of_nat w) -> 0 <= v2 < 2^(8 * Z.of_nat w) ->
  rd m a w v1 -> rd m a w v2 -> v1 = v2.
Proof.
  intros m a w v1 v2 Hw H1 H2 R1 R2. unfold rd in *. rewrite R1 in R2. injection R2 as E.
  apply (f_equal bytes_le_to_Z) in E. unfold word_to_le_bytes in E. rewrite !bytes_le_Z_to_le in E by (apply bv_unsigned_in_range).
  assert (P : 2^(8 * Z.of_nat w) <= 2^64) by (apply Z.pow_le_mono_r; lia).
  rewrite !u_wa_small in E by lia. rewrite !Z.mod_small in E by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma INV_D_insert : forall m m' D1 B1 n F st b hd h SZ, INV_D m D1 B1 n F st ->
  n <= 65532 -> 1 <= SZ <= 255 -> F + SZ + 1 <= 1048000 -> 0 <= b < 1048576 -> 0 <= h < 2^64 ->
  rd m (TAB + 4 * b) 4 hd -> 0 <= hd < 2^31 ->
  rd m' NUNIQ 4 (n + 1) -> rd m' (TAB + 4 * b) 4 (n + 1) -> rd m' (D1 + 16 * (n + 1)) 8 h -> rd m' (D1 + 16 * (n + 1) + 8) 4 hd ->
  rd m' SSF 8 (F + SZ + 1) -> rd m' SSS 4 (st + SZ + 1) ->
  (forall x, 0 <= x < 2^64 -> downed D1 B1 x -> ~ (NUNIQ <= x < NUNIQ + 4) -> ~ (TAB + 4 * b <= x < TAB + 4 * b + 4) ->
     ~ (D1 + 16 * (n + 1) <= x < D1 + 16 * (n + 1) + 16) -> ~ (SSF <= x < SSF + 8) -> ~ (SSS <= x < SSS + 4) ->
     ~ (B1 + 8 * F <= x < B1 + 8 * F + 8 * (SZ + 1)) -> m' (wa x) = m (wa x)) ->
  mem_grows m m' -> INV_D m' D1 B1 (n + 1) (F + SZ + 1) (st + SZ + 1).
Proof.
  intros m m' D1 B1 n F st b hd h SZ I Hn HSZ HF Hb Hh Rhd Hhd N1 T1 ND1 ND2 SF1 SS1 HFR G.
  destruct I as [In Inr Imap ID1 Itab IF Ist IFr IB1 IB1r Iwr Isep In0].
  destruct ID1 as (D1a & D1b & D1c). destruct IB1r as (B1a & B1b & B1c). destruct Isep as (S1 & S2 & S3).
  (* [comment removed for export] *)
  assert (FN : forall x, D1 + 16 <= x < D1 + 16 * (n + 1) -> m' (wa x) = m (wa x)).
  { intros x Hx. apply HFR; unfold downed in *; lia. }
  constructor.
  - exact N1.
  - lia.
  - apply (rd_frame m m'); [lia | zn; lia | | exact Imap].
    intros x Hx. zn. apply HFR; unfold downed in *; lia.
  - split; [lia|]. split; [lia | exact D1c].
  - intros b' Hb'. destruct (Z.eq_dec b' b) as [->|Hne].
    + exists (n + 1). split; [lia|]. split; [exact T1|]. destruct (Itab b Hb) as (hd0 & Hhd0 & Rhd0 & k0 & Hc0).
      assert (Ehd : hd0 = hd) by (apply (rd_inj m (TAB + 4 * b) 4 hd0 hd); [lia | zn; lia | zn; lia | exact Rhd0 | exact Rhd]). subst hd0.
      exists (S k0). cbn [chainz]. right. split; [lia|]. exists h, hd. split; [exact Hh|].
      split; [destruct (chainz_range _ _ _ _ _ Hc0); lia|]. split; [exact ND1|]. split; [exact ND2|].
      apply (chainz_mono_n m' D1 n (n + 1)); [lia|]. apply (chainz_frame m m' D1 n k0 hd); [lia | lia | lia | exact FN | exact Hc0].
    + destruct (Itab b' Hb') as (hd0 & Hhd0 & Rhd0 & k0 & Hc0). exists hd0. split; [exact Hhd0|]. split.
      * apply (rd_frame m m'); [lia | zn; lia | | exact Rhd0].
        intros x Hx. zn. apply HFR; unfold downed in *; lia.
      * exists k0. apply (chainz_mono_n m' D1 n (n + 1)); [lia|]. apply (chainz_frame m m' D1 n k0 hd0); [lia | lia | lia | exact FN | exact Hc0].
  - exact SF1.
  - exact SS1.
  - lia.
  - apply (rd_frame m m'); [lia | zn; lia | | exact IB1].
    intros x Hx. zn. apply HFR; unfold downed in *; lia.
  - split; [lia|]. split; [lia | exact B1c].
  - intros x Hx. apply (wview_grows m m' x G). exact (Iwr x Hx).
  - split; [lia|]. split; lia.
  - destruct In0 as (hv & lk & H1 & H2 & R1 & R2). exists hv, lk. split; [exact H1|]. split; [exact H2|].
    split; [apply (rd_frame m m'); [lia | zn; lia | | exact R1] | apply (rd_frame m m'); [lia | zn; lia | | exact R2]].
    all: intros x Hx; zn; apply HFR; unfold downed in *; lia.
Qed.
(* [comment removed for export] *)
