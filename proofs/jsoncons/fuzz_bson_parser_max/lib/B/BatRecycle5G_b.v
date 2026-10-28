(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatSecAllocPost_b
     BatRecycle2C_b BatRecycle3L_b BatRecycle4P_b BatRecycle4S_b BatRecycle5A_b BatRecycle5I_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Gap.
Variables (HI t ctx tp key tsd spb ris qs parr : Z).
Hypothesis GEO : art_geo HI t ctx tp tsd spb ris qs.

(* [comment removed for export] *)
Definition art_rel_geo (G : art_rg) (e : art_rel) : Prop :=
  match e with
  | REP c w d b1 n =>
      1 <= c <= 30 /\ 0 <= w /\ 16 * w + AsanTab.class_size c <= 3758096384 /\ 0 <= d /\ d mod 16 = 0 /\ d + 16 + (n + 7) / 8 * 8 <= AsanTab.class_size c /\ 0 <= n
      /\ 4 * Z.of_nat (length (cl_free (rg_cls G c))) + 32 <= 2 ^ 29
  | RES mb ms m b1 n =>
      In (mb, ms) (rg_bl G)
  | REB wb => 0 <= wb /\ 16 * wb + 8192 <= 3758096384 /\ 4 * Z.of_nat (length (cl_free (rg_cls G 24))) + 32 <= 2 ^ 29
  end.
Definition art_bl_geo (G : art_rg) : Prop :=
  art_sec_geo HI t ctx parr (rg_bl G) /\ (forall b, In b (rg_bl G) -> apart (fst b) (snd b) spb (2 ^ 37 + 4096)) /\ apart parr (8 * Z.of_nat (length (rg_bl G))) spb (2 ^ 37 + 4096).

#[using="Type"] Lemma art_rel_geo_of_inv : forall nt G (M : word -> option byte) e, 0 <= nt -> art_rcy_inv HI t ctx tp key tsd spb ris qs parr nt G M -> art_rel_pre G e -> art_rel_geo G e /\ art_bl_geo G.
Proof.
  intros nt G M e Hnt (ICLS & _ & _ & _ & _ & _ & _ & _ & _ & _ & ISG & IBK & IPK) PRE. split; [|split; [exact ISG|split; [exact IBK|exact IPK]]].
  destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_geo art_rel_pre] in *.
  - destruct PRE as (Hc & (Hw0 & Hwsz & _) & _ & Hd & Hd16 & Hdsz & _ & Hn). destruct (ICLS c Hc) as (_ & OK & _ & Rm).
    destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _ & (_ & Hmfa1) & Hnf4 & _ & _). pose proof (art_class_size_facts c Hc) as (Hsz & _).
    specialize (Rm ltac:(lia)). repeat split; try assumption; lia.
  - destruct PRE as (Hin & _). exact Hin.
  - destruct PRE as ((Hw0 & Hwsz & _) & _). destruct (ICLS 24 ltac:(lia)) as (_ & OK & _ & Rm).
    destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _ & (_ & Hmfa1) & Hnf4 & _ & _).
    specialize (Rm ltac:(lia)). repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
#[using="tp tsd qs GEO"] Lemma art_rel_fp_above : forall sp1 G e a n, art_rel_geo G e -> art_bl_geo G -> HI <= sp1 - 320 -> sp1 < 2 ^ 47 -> sp1 <= a -> 0 <= n ->
  art_gap (art_rel_fp t spb ris parr sp1 G e) a n.
Proof.
  intros sp1 G e a n RG BG HHI Hsp' Ha Hn0.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & _ & _ & _ & _ & G13 & G14 & _ & _ & _ & _ & G19 & G20 & G21 & G22).
  destruct BG as (ISG & IBK & IPK). pose proof ISG as (Gp1 & Gp2 & Gp3 & Gp4 & Apt & Apc & GB & GD).
  destruct e as [c w d b1 n'|mb ms m b1 n'|wb]; cbn [art_rel_geo art_rel_fp] in *.
  - destruct RG as (Hc & Hw0 & Hwsz & Hd & Hd16 & Hdsz & Hn' & Hnf).
    pose proof (art_class_size_facts c Hc) as (Hsz & _).
    set (rs := (n' + 7) / 8 * 8) in *. set (m := spb + c * 2 ^ 32 + 16 * w + d) in *.
    assert (Hrs : 0 <= rs /\ rs mod 8 = 0).
    { unfold rs. pose proof (Z.div_mod (n' + 7) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (n' + 7) 8 ltac:(lia)) as B. split; [lia|apply Z_mod_mult]. }
    destruct Hrs as (Hrs0 & Hrs8).
    pose proof (Z.div_mod (m + 16) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (m + 16) 8 ltac:(lia)) as Bq.
    pose proof (Z.div_mod rs 8 ltac:(lia)) as Dr. rewrite Hrs8 in Dr.
    assert (Em : m = spb + c * 2 ^ 32 + 16 * w + d) by reflexivity.
    unfold art_cbr_prim_fp, art_lcd_fp. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hn0 Hc Hw0 Hwsz Hd Hdsz Hsz Hrs0 Dq Bq Dr Em Hnf; unfold apart in *; cbn in *; lia)].
  - pose proof RG as Hin. destruct (GB _ Hin) as (Hmb4k & Hms4k & Hmb0 & Hmb1 & Hmb2 & _). cbn [fst snd] in *.
    assert (Hidx : (art_bl_idx mb (rg_bl G) < length (rg_bl G))%nat).
    { apply nth_error_Some. rewrite (art_bl_idx_nth (rg_bl G) mb ms Hin (art_sec_geo_inj HI t ctx parr (rg_bl G) ISG)). discriminate. }
    pose proof (proj1 (Nat2Z.inj_lt _ _) Hidx) as Hidx'.
    assert (Hlastin : In (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0)) (rg_bl G)) by (apply nth_In; lia).
    destruct (GB _ Hlastin) as (_ & _ & Hl0 & Hl1 & Hl2 & _).
    pose proof (Z.div_mod mb 8 ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound mb 8 ltac:(lia)) as Bm.
    pose proof (Z.div_mod ms 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound ms 8 ltac:(lia)) as Bs.
    unfold art_cbr_sec_fp, art_secd_fp. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hn0 Hmb0 Hmb1 Hmb2 Hidx' Hl0 Hl1 Hl2 Gp1 Gp2 Dm Bm Ds Bs; unfold apart in *; cbn in *; lia)].
  - destruct RG as (Hw0 & Hwsz & Hnf).
    unfold art_lcd_fp. cbn [art_gap app fst snd]. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hn0 Hw0 Hwsz Hnf; unfold apart in *; cbn in *; lia)].
Qed.

(* [comment removed for export] *)
#[using="tp tsd qs GEO"] Lemma art_rel_fp_prot : forall sp1 G e zlo zlen a n, art_rel_geo G e -> art_bl_geo G -> HI <= sp1 - 320 -> sp1 < 2 ^ 47 ->
  0 < zlen -> art_rcy_prot spb G zlo zlen -> apart (fst (art_rel_zone spb e)) (snd (art_rel_zone spb e)) zlo zlen -> zlo <= a -> a + n <= zlo + zlen -> 0 <= n ->
  art_gap (art_rel_fp t spb ris parr sp1 G e) a n.
Proof.
  intros sp1 G e zlo zlen a n RG BG HHI Hsp' Hz PROT AP Ha Hk Hn0.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & _ & Gts & Atk & _ & G13 & G14 & _ & _ & _ & _ & G19 & G20 & G21 & G22).
  destruct BG as (ISG & IBK & IPK). pose proof ISG as (Gp1 & Gp2 & Gp3 & Gp4 & Apt & Apc & GB & GD).
  destruct e as [c w d b1 n'|mb ms m b1 n'|wb]; cbn [art_rel_geo art_rel_fp art_rel_zone fst snd] in *.
  - (* [comment removed for export] *)
    destruct RG as (Hc & Hw0 & Hwsz & Hd & Hd16 & Hdsz & Hn' & Hnf).
    pose proof (art_class_size_facts c Hc) as (Hsz & _).
    set (rs := (n' + 7) / 8 * 8) in *. set (m := spb + c * 2 ^ 32 + 16 * w + d) in *.
    assert (Hrs : 0 <= rs /\ rs mod 8 = 0).
    { unfold rs. pose proof (Z.div_mod (n' + 7) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (n' + 7) 8 ltac:(lia)) as B. split; [lia|apply Z_mod_mult]. }
    destruct Hrs as (Hrs0 & Hrs8).
    pose proof (Z.div_mod (m + 16) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (m + 16) 8 ltac:(lia)) as Bq.
    pose proof (Z.div_mod rs 8 ltac:(lia)) as Dr. rewrite Hrs8 in Dr.
    assert (Em : m = spb + c * 2 ^ 32 + 16 * w + d) by reflexivity.
    unfold art_cbr_prim_fp, art_lcd_fp. cbn [art_gap app fst snd]. unfold SB.
    destruct PROT as [(c' & Hc' & Z1 & Z2)|(b & Hb & Z1 & Z2)].
    + repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hc Hw0 Hwsz Hd Hdsz Hsz Em; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 AP Hc Hw0 Hwsz Hd Hdsz Hsz Hrs0 Em; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hc Hw0 Hwsz Hd Hdsz Hsz Hrs0 Dq Bq Dr Em; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hc Atk; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hc Hnf; unfold apart in *; cbn in *; lia)].
    + destruct (GB _ Hb) as (_ & _ & Hs & Hb0 & Hb1' & Hbapp & _ & Hbt & _). pose proof (IBK _ Hb) as Hbk. unfold appmem, SB, kHighMemBeg in Hbapp.
      repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbk Hc Hw0 Hwsz Hd Hdsz Hsz Hrs0 Em Hnf; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbapp Hc Hw0 Hwsz Hd Hdsz Hsz Hrs0 Dq Bq Dr Em; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbt Hc; unfold apart in *; cbn in *; lia)].
  - (* [comment removed for export] *)
    pose proof RG as Hin. destruct (GB _ Hin) as (Hmb4k & Hms4k & Hmb0 & Hmb1 & Hmb2 & Hmbapp & Abp & Abt & Abc). cbn [fst snd] in *.
    pose proof (IBK _ Hin) as Abk. cbn [fst snd] in Abk. unfold appmem, SB, kHighMemBeg in Hmbapp.
    pose proof (art_bl_idx_nth (rg_bl G) mb ms Hin (art_sec_geo_inj HI t ctx parr (rg_bl G) ISG)) as Hnth.
    assert (Hidx : (art_bl_idx mb (rg_bl G) < length (rg_bl G))%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
    pose proof (proj1 (Nat2Z.inj_lt _ _) Hidx) as Hidx'.
    assert (Hlastin : In (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0)) (rg_bl G)) by (apply nth_In; lia).
    destruct (GB _ Hlastin) as (_ & _ & Hl0 & Hl1 & Hl2 & Hlapp & _ & Hlt & Hlc). pose proof (IBK _ Hlastin) as Hlk.
    pose proof (Z.div_mod mb 8 ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound mb 8 ltac:(lia)) as Bm.
    pose proof (Z.div_mod ms 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound ms 8 ltac:(lia)) as Bs.
    unfold art_cbr_sec_fp, art_secd_fp. cbn [art_gap app fst snd]. unfold SB.
    destruct PROT as [(c' & Hc' & Z1 & Z2)|(b & Hb & Z1 & Z2)].
    + repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Atk; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 IPK Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hlk Hl0; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hmb0 Hmb1 Hmb2 Dm Bm Ds Bs; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Abk; unfold apart in *; cbn in *; lia)].
    + destruct (GB _ Hb) as (_ & _ & Hs & Hb0 & Hb1' & Hbapp & Hbp & Hbt & _). unfold appmem, SB, kHighMemBeg in Hbapp.
      (* [comment removed for export] *)
      assert (Hlast : fst (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0)) + 32 <= zlo \/ zlo + zlen <= fst (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0))).
      { destruct (In_nth_error _ _ Hb) as (j & Hj).
        assert (Hjl : (j < length (rg_bl G))%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
        destruct (Nat.eq_dec j (length (rg_bl G) - 1)) as [->|NE].
        - rewrite (nth_error_nth _ _ (0, 0) Hj). left. clear - Z1. lia.
        - assert (Hll : (length (rg_bl G) - 1 < length (rg_bl G))%nat) by lia.
          pose proof (GD j (length (rg_bl G) - 1)%nat b _ Hj (nth_error_nth' (rg_bl G) (0, 0) Hll) NE) as Ap. unfold apart in Ap. clear - Ap Z1 Z2 Hl0 Hs. lia. }
      repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbt; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbp Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hlast; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbapp Hmb0 Hmb1 Hmb2 Dm Bm Ds Bs; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 AP; unfold apart in *; cbn in *; lia)].
  - (* [comment removed for export] *)
    destruct RG as (Hw0 & Hwsz & Hnf).
    unfold art_lcd_fp. cbn [art_gap app fst snd].
    destruct PROT as [(c' & Hc' & Z1 & Z2)|(b & Hb & Z1 & Z2)].
    + repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Atk; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hnf; unfold apart in *; cbn in *; lia)].
    + destruct (GB _ Hb) as (_ & _ & Hs & Hb0 & Hb1' & Hbapp & _ & Hbt & _). pose proof (IBK _ Hb) as Hbk.
      repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbk Hnf; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbt; unfold apart in *; cbn in *; lia)].
Qed.
End Gap.
