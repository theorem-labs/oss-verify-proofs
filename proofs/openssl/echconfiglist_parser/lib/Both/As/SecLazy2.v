(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_LargeAlloc1 AW_PoisonRemap1 SecLazy.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition wmono_out (X : list ivl) (m m' : mem) : Prop :=
  forall x : word, outside X (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None.

Lemma wmono_out_of_wmono : forall X m m', wmono asegs m m' -> wmono_out X m m'.
Proof. intros X m m' WM x _ Hx. exact (WM x Hx). Qed.

Lemma wmono_out_refl : forall X m, wmono_out X m m.
Proof. intros X m x _ Hx. exact Hx. Qed.

Lemma wmono_out_trans : forall X m1 m2 m3, wmono_out X m1 m2 -> wmono_out X m2 m3 -> wmono_out X m1 m3.
Proof. intros X m1 m2 m3 A B x Ho Hx. exact (B x Ho (A x Ho Hx)). Qed.

Lemma wmono_out_wmono_l : forall X m1 m2 m3, wmono asegs m1 m2 -> wmono_out X m2 m3 -> wmono_out X m1 m3.
Proof. intros X m1 m2 m3 A B. eapply wmono_out_trans; [apply wmono_out_of_wmono; exact A| exact B]. Qed.

Lemma wmono_out_wmono_r : forall X m1 m2 m3, wmono_out X m1 m2 -> wmono asegs m2 m3 -> wmono_out X m1 m3.
Proof. intros X m1 m2 m3 A B. eapply wmono_out_trans; [exact A| apply wmono_out_of_wmono; exact B]. Qed.

(* [comment removed for export] *)
Lemma wmono_out_weaken : forall X X' m m', sub_fp X X' -> wmono_out X m m' -> wmono_out X' m m'.
Proof. intros X X' m m' SUB A x Ho Hx. exact (A x (SUB _ Ho) Hx). Qed.

(* [comment removed for export] *)
Lemma wview_pointwise : forall (m m' : mem) (x : word), m' x = m x -> wview asegs m' x = wview asegs m x.
Proof. intros m m' x E. unfold wview. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma munch_wmono_out : forall W m m', munch W m m' -> wmono_out W m m'.
Proof. intros W m m' MU x Ho Hx. rewrite (wview_pointwise m m' x (MU x Ho)). exact Hx. Qed.

Lemma unfill_wmono_out : forall (a n : word) (m : mem),
  wmono_out [(bv_unsigned a, bv_unsigned a + bv_unsigned n)] m (unfill a n m).
Proof. intros a n m. apply munch_wmono_out. apply unfill_munch. Qed.

(* [comment removed for export] *)
Lemma unfill_none : forall (a n : word) (m : mem) (x : word),
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> unfill a n m x = None.
Proof.
  intros a n m x Hx. unfold unfill.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)); cbn [andb];
    try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma none_range_munch : forall W (m m' : mem) (lo hi : Z),
  (forall x : word, lo <= bv_unsigned x < hi -> m x = None) -> munch W m m' -> disjoint_from W lo (hi - lo) ->
  forall x : word, lo <= bv_unsigned x < hi -> m' x = None.
Proof.
  intros W m m' lo hi N MU D x Hx. rewrite (MU x); [exact (N x Hx)|].
  eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MuTransport.
  Variables (W : list ivl) (m m' : mem).
  Hypothesis MU : munch W m m'.

  Lemma wr_at_transport_mu : forall A n, wr_at asegs m A n -> disjoint_from W A n -> wr_at asegs m' A n.
  Proof.
    intros A n (Ha & Hn & H) D. split; [exact Ha|]. split; [exact Hn|]. intros i Hi.
    rewrite (wview_pointwise m m'); [exact (H i Hi)|]. apply MU. eapply disjoint_outside; [exact D|]. rewrite wa_unsigned by lia. lia.
  Qed.

  Lemma rw_cells_transport_mu : forall A cs,
    rw_cells asegs m A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
  Proof.
    intros A cs [[Hwf Hb] Hw] D. split; [split; [exact Hwf|]|].
    - eapply bytes_at_transport; [exact Hb| exact MU|]. rewrite cells_bytes_length by assumption. exact D.
    - eapply wr_at_transport_mu; [exact Hw| exact D].
  Qed.

  Lemma stk_transport_mu : forall lo hi, stk asegs m lo hi -> disjoint_from W lo (hi - lo) -> stk asegs m' lo hi.
  Proof.
    intros lo hi (H1 & H2 & H) D. split; [exact H1|]. split; [exact H2|]. intros a Ha.
    assert (E : m' (wa a) = m (wa a)) by (apply MU; eapply disjoint_outside; [exact D|]; rewrite wa_unsigned by lia; lia).
    destruct (H a Ha) as [Hw (b & Hb)]. split.
    - rewrite (wview_pointwise m m' (wa a) E). exact Hw.
    - exists b. unfold mrd in *. rewrite E. exact Hb.
  Qed.

  Lemma u8arr_transport_mu : forall A bs, u8arr asegs m A bs -> disjoint_from W A (Z.of_nat (length bs)) -> u8arr asegs m' A bs.
  Proof.
    intros A bs [Hb Hw] D. split; [eapply bytes_at_transport; [exact Hb| exact MU| exact D]| eapply wr_at_transport_mu; [exact Hw| exact D]].
  Qed.

  Lemma u64arr_transport_mu : forall A ws, u64arr asegs m A ws -> disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
  Proof.
    intros A ws [Hb Hw] D. split.
    - eapply bytes_at_transport; [exact Hb| exact MU|]. rewrite u64s_length, Nat2Z.inj_mul. exact D.
    - eapply wr_at_transport_mu; [exact Hw| exact D].
  Qed.

  Lemma senv_transport_mu : forall tp TSD CTX TH,
    SENV tp TSD CTX TH m ->
    disjoint_from W 6988128 8 -> disjoint_from W (bv_unsigned tp + -88) 8 -> disjoint_from W TSD 8 -> disjoint_from W (CTX + 152) 8 ->
    disjoint_from W 6988124 1 -> disjoint_from W 6191096 120 -> disjoint_from W 6990072 8 -> disjoint_from W 6993376 24 ->
    disjoint_from W 7586976 8 -> disjoint_from W 7587000 8 -> disjoint_from W 7587116 1 -> disjoint_from W 6204016 8 ->
    disjoint_from W 7578528 8 -> disjoint_from W 6204072 8 ->
    SENV tp TSD CTX TH m'.
  Proof.
    intros tp TSD CTX TH E; intros; destruct E; constructor;
      (eapply rw_cells_transport_mu; [eassumption | ]);
      unfold AGOT_VALS; cbn [cells_size csize length map Nat.add Nat.mul]; assumption.
  Qed.

  Lemma renv_transport_mu : forall g b,
    RENV g b m ->
    disjoint_from W 6191096 120 -> disjoint_from W 6990072 8 -> disjoint_from W 6993376 24 -> disjoint_from W 7586976 8 ->
    disjoint_from W 7587000 8 -> disjoint_from W 7587075 1 -> disjoint_from W 7587100 1 -> disjoint_from W 6204016 8 ->
    disjoint_from W 7578528 8 -> disjoint_from W 12590928 8 -> disjoint_from W 6199192 8 -> disjoint_from W 12590288 8 ->
    RENV g b m'.
  Proof.
    intros g b E; intros; destruct E; constructor;
      (eapply rw_cells_transport_mu; [eassumption | ]);
      unfold AGOT_VALS; cbn [cells_size csize length map Nat.add Nat.mul]; assumption.
  Qed.
End MuTransport.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rem_uncovered : forall (e : word * word) (C : list (word * word)),
  (forall x, lo e <= x < hi e -> zcovb C x = false) -> rem e C = bv_unsigned (snd e).
Proof.
  intros e C H. unfold rem. rewrite <- hi_minus_lo. apply zmeasure_all; [apply lo_hi|].
  intros x Hx. rewrite (H x Hx). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zcovb_maps_subtract_false : forall C l h x,
  entries_nowrap C -> 0 <= l -> l <= h -> zcovb C x = false -> zcovb (maps_subtract C l h) x = false.
Proof. intros C l h x NW Hl Hlh H. rewrite (zcovb_maps_subtract C l h x NW Hl Hlh), H. reflexivity. Qed.

Lemma zcovb_app_false : forall C1 C2 x, zcovb C1 x = false -> zcovb C2 x = false -> zcovb (C1 ++ C2) x = false.
Proof. intros C1 C2 x H1 H2. rewrite zcovb_app, H1, H2. reflexivity. Qed.

Lemma zcovb_cons_false : forall c C x, zin_rangeb x c = false -> zcovb C x = false -> zcovb (c :: C) x = false.
Proof. intros c C x H1 H2. rewrite zcovb_cons, H1, H2. reflexivity. Qed.

(* [comment removed for export] *)
Lemma in_rangesb_false_zcovb : forall (C : list (word * word)) (x : Z),
  0 <= x < 2^64 -> in_rangesb (wz x) C = false -> zcovb C x = false.
Proof. intros C x Hx H. rewrite in_rangesb_zcovb in H. unfold wz in H. rewrite unsigned_lit in H by lia. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ecall_1d6988 : fetch_word asegs (Z_to_bv 64 0x1d1910) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

End HCW.

