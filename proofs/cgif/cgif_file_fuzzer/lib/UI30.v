(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP09 YI06 UI5b YI09 YI0t YI0r UH00 UI3n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition vtabs_at (mem : word -> option byte) (cx : lzw_tcx) (PIX : list Z) (V : lzw_v) : Prop :=
garr8 ubs0segs mem (y_lc cx) (v_LC V) /\ garr8 ubs0segs mem (y_img cx) PIX /\ arr16 ubs0segs mem (y_ld cx) (v_LD V).
Definition vinv (cx : lzw_tcx) (PIX : list Z) (X : lzw_abs) (V : lzw_v) : Prop :=
length (v_LC V) = 4096%nat /\ length PIX = Z.to_nat (y_nP cx) /\ Z.of_nat (length (v_LD V)) = la_lp X.
Definition vframe (mem mem' : word -> option byte) (W : Z -> Prop) : Prop := forall a, 0 <= a < 2 ^ 64 -> ~ W a -> mbyte ubs0segs mem' a = mbyte ubs0segs mem a.
Definition voff (cx : lzw_tcx) (lp : Z) (W : Z -> Prop) : Prop :=
(forall a, y_lc cx <= a < y_lc cx + 4096 -> 0 <= a < 2 ^ 64 /\ ~ W a) /\
(forall a, y_img cx <= a < y_img cx + y_nP cx -> 0 <= a < 2 ^ 64 /\ ~ W a) /\
(forall a, y_ld cx <= a < y_ld cx + 2 * lp -> 0 <= a < 2 ^ 64 /\ ~ W a).
Lemma vtabs_keep : forall mem mem' cx PIX V X W,
vtabs_at mem cx PIX V -> vinv cx PIX X V -> 0 <= y_nP cx -> vframe mem mem' W -> voff cx (la_lp X) W -> vtabs_at mem' cx PIX V.
Proof using.
intros mem mem' cx PIX V X W (GLC & GPIX & ALD) (LenLC & LenPIX & LenLD) HnP HFR (OLC & OPIX & OLD). split; [|split].
- eapply garr8_frame; [exact GLC|]. intros a Ha. rewrite LenLC in Ha. destruct (OLC a ltac:(lia)) as [R1 R2]. exact (HFR a R1 R2).
- eapply garr8_frame; [exact GPIX|]. intros a Ha. rewrite LenPIX, Z2Nat.id in Ha by lia. destruct (OPIX a ltac:(lia)) as [R1 R2]. exact (HFR a R1 R2).
- eapply arr16_frame; [exact ALD|]. intros a Ha. rewrite LenLD in Ha. destruct (OLD a ltac:(lia)) as [R1 R2]. exact (HFR a R1 R2).
Qed.
Lemma vtabs_keep_len : forall mem mem' cx PIX V W,
vtabs_at mem cx PIX V -> length (v_LC V) = 4096%nat -> length PIX = Z.to_nat (y_nP cx) -> 0 <= y_nP cx ->
vframe mem mem' W -> voff cx (Z.of_nat (length (v_LD V))) W -> vtabs_at mem' cx PIX V.
Proof using.
intros mem mem' cx PIX V W (GLC & GPIX & ALD) LenLC LenPIX HnP HFR (OLC & OPIX & OLD). split; [|split].
- eapply garr8_frame; [exact GLC|]. intros a Ha. rewrite LenLC in Ha. destruct (OLC a ltac:(lia)) as [R1 R2]. exact (HFR a R1 R2).
- eapply garr8_frame; [exact GPIX|]. intros a Ha. rewrite LenPIX, Z2Nat.id in Ha by lia. destruct (OPIX a ltac:(lia)) as [R1 R2]. exact (HFR a R1 R2).
- eapply arr16_frame; [exact ALD|]. intros a Ha. destruct (OLD a ltac:(lia)) as [R1 R2]. exact (HFR a R1 R2).
Qed.
Lemma vtabs_emit : forall mem mem' cx PIX V X W q,
vtabs_at mem cx PIX V -> vinv cx PIX X V -> 0 <= y_nP cx -> vframe mem mem' W -> voff cx (la_lp X) W ->
val_mem ubs0segs mem' (y_ld cx + 2 * la_lp X) 2 q -> 0 <= q < 65536 ->
vtabs_at mem' cx PIX (mkLV (v_LC V) (v_LD V ++ [q])).
Proof using.
intros mem mem' cx PIX V X W q HVT HVI HnP HFR HOFF Vq Hq.
destruct (vtabs_keep mem mem' cx PIX V X W HVT HVI HnP HFR HOFF) as (GLC & GPIX & _).
destruct HVT as (_ & _ & ALD). destruct HVI as (_ & _ & LenLD). destruct HOFF as (_ & _ & OLD).
split; [exact GLC|]. split; [exact GPIX|]. cbn [v_LD].
eapply arr16_app1; [exact ALD | rewrite LenLD; exact Vq | exact Hq |].
intros a Ha. rewrite LenLD in Ha. destruct (OLD a Ha) as [R1 R2]. exact (HFR a R1 R2).
Qed.
Lemma vtabs_emit_lc : forall mem mem' cx PIX V X W q c,
vtabs_at mem cx PIX V -> vinv cx PIX X V -> 0 <= y_nP cx -> 0 <= q < 4096 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ W a -> a <> y_lc cx + q -> mbyte ubs0segs mem' a = mbyte ubs0segs mem a) ->
voff cx (la_lp X) W ->
val_mem ubs0segs mem' (y_ld cx + 2 * la_lp X) 2 q -> val_mem ubs0segs mem' (y_lc cx + q) 1 c -> 0 <= c < 256 ->
(forall a, y_img cx <= a < y_img cx + y_nP cx -> a <> y_lc cx + q) -> (forall a, y_ld cx <= a < y_ld cx + 2 * la_lp X -> a <> y_lc cx + q) ->
vtabs_at mem' cx PIX (mkLV (updn (v_LC V) (Z.to_nat q) c) (v_LD V ++ [q])).
Proof using.
intros mem mem' cx PIX V X W q c (GLC & GPIX & ALD) (LenLC & LenPIX & LenLD) HnP Hq HFR (OLC & OPIX & OLD) Vq Vc Hc NPIX NLD.
split; [|split]; cbn [v_LC v_LD].
- eapply garr8_upd; [exact GLC | rewrite LenLC; lia | rewrite Z2Nat.id by lia; exact Vc | exact Hc |].
intros a Ha Hne. rewrite LenLC in Ha. rewrite Z2Nat.id in Hne by lia. destruct (OLC a ltac:(lia)) as [R1 R2]. exact (HFR a R1 R2 Hne).
- eapply garr8_frame; [exact GPIX|]. intros a Ha. rewrite LenPIX, Z2Nat.id in Ha by lia. destruct (OPIX a ltac:(lia)) as [R1 R2]. exact (HFR a R1 R2 (NPIX a ltac:(lia))).
- eapply arr16_app1; [exact ALD | rewrite LenLD; exact Vq | lia |].
intros a Ha. rewrite LenLD in Ha. destruct (OLD a Ha) as [R1 R2]. exact (HFR a R1 R2 (NLD a Ha)).
Qed.
Lemma vtabs_reset : forall mem mem' cx PIX V W v,
vtabs_at mem cx PIX V -> length PIX = Z.to_nat (y_nP cx) -> 0 <= y_nP cx -> vframe mem mem' W ->
(forall a, y_img cx <= a < y_img cx + y_nP cx -> 0 <= a < 2 ^ 64 /\ ~ W a) ->
(forall a, y_ld cx <= a < y_ld cx + 2 * Z.of_nat (length (v_LD V)) -> 0 <= a < 2 ^ 64 /\ ~ W a) ->
(forall a, y_lc cx <= a < y_lc cx + 4096 -> mbyte ubs0segs mem' a = Some (Z_to_bv 8 0)) ->
val_mem ubs0segs mem' (y_ld cx + 2 * Z.of_nat (length (v_LD V))) 2 v -> 0 <= v < 65536 ->
vtabs_at mem' cx PIX (mkLV (repeat 0 4096) (v_LD V ++ [v])).
Proof using.
intros mem mem' cx PIX V W v (GLC & GPIX & ALD) LenPIX HnP HFR OPIX OLD ZLC Vv Hv. split; [|split]; cbn [v_LC v_LD].
- apply garr8_zeros. intros a Ha. apply ZLC. change (Z.of_nat 4096) with 4096 in Ha. exact Ha.
- eapply garr8_frame; [exact GPIX|]. intros a Ha. rewrite LenPIX, Z2Nat.id in Ha by lia. destruct (OPIX a ltac:(lia)) as [R1 R2]. exact (HFR a R1 R2).
- eapply arr16_app1; [exact ALD | exact Vv | exact Hv |]. intros a Ha. destruct (OLD a Ha) as [R1 R2]. exact (HFR a R1 R2).
Qed.
Lemma vtabs_init : forall mem mem' cx PIX W v,
garr8 ubs0segs mem (y_img cx) PIX -> length PIX = Z.to_nat (y_nP cx) -> 0 <= y_nP cx -> vframe mem mem' W ->
(forall a, y_img cx <= a < y_img cx + y_nP cx -> 0 <= a < 2 ^ 64 /\ ~ W a) ->
(forall a, y_lc cx <= a < y_lc cx + 4096 -> mbyte ubs0segs mem' a = Some (Z_to_bv 8 0)) ->
val_mem ubs0segs mem' (y_ld cx) 2 v -> 0 <= v < 65536 ->
vtabs_at mem' cx PIX (mkLV (repeat 0 4096) [v]).
Proof using.
intros mem mem' cx PIX W v GPIX LenPIX HnP HFR OPIX ZLC Vv Hv. split; [|split]; cbn [v_LC v_LD].
- apply garr8_zeros. intros a Ha. apply ZLC. change (Z.of_nat 4096) with 4096 in Ha. exact Ha.
- eapply garr8_frame; [exact GPIX|]. intros a Ha. rewrite LenPIX, Z2Nat.id in Ha by lia. destruct (OPIX a ltac:(lia)) as [R1 R2]. exact (HFR a R1 R2).
- intros [|j] Hj; cbn in Hj; [|lia]. cbn [nth Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. split; [exact Vv | exact Hv].
Qed.
Lemma vtabs_at_eq : forall mem mem' cx PIX V, vtabs_at mem cx PIX V -> (forall x, mem' x = mem x) -> vtabs_at mem' cx PIX V.
Proof using.
intros mem mem' cx PIX V (GLC & GPIX & ALD) Hm.
assert (Hb : forall a, mbyte ubs0segs mem' a = mbyte ubs0segs mem a) by (intros a; unfold mbyte; rewrite Hm; reflexivity).
split; [|split]; [eapply garr8_frame | eapply garr8_frame | eapply arr16_frame]; try eassumption; intros; apply Hb.
Qed.
Lemma vtabs_px : forall mem cx PIX V, vtabs_at mem cx PIX V -> forall i, 0 <= px PIX i < 256.
Proof using.
intros mem cx PIX V (_ & GPIX & _) i. unfold px. destruct (Nat.lt_ge_cases (Z.to_nat i) (length PIX)) as [Hlt | Hge].
- exact (proj2 (GPIX _ Hlt)).
- rewrite nth_overflow by exact Hge. lia.
Qed.
End b.
