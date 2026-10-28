(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_auxv D_libiface D_clx FX_Exit I_iodefs X_aexdefs D_aex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record gdesc := mkGD { gd_beg : Z; gd_size : Z; gd_srz : Z; gd_name : Z; gd_mod : Z; gd_dyn : Z; gd_loc : Z; gd_odr : Z }.

Definition gd_cells (g : gdesc) : list cell :=
  [C8 (Z_to_bv 64 (gd_beg g)); C8 (Z_to_bv 64 (gd_size g)); C8 (Z_to_bv 64 (gd_srz g)); C8 (Z_to_bv 64 (gd_name g));
   C8 (Z_to_bv 64 (gd_mod g)); C8 (Z_to_bv 64 (gd_dyn g)); C8 (Z_to_bv 64 (gd_loc g)); C8 (Z_to_bv 64 (gd_odr g))].

Fixpoint gds_at (m : mem) (a : Z) (gs : list gdesc) : Prop :=
  match gs with
  | [] => True
  | g :: gs' => ro_cells bsegs m a (gd_cells g) /\ gds_at m (a + 64) gs'
  end.

Definition ODR_NONE : Z := 0xffffffffffffffff.

Definition asan_gds : list gdesc := [
  mkGD 0x23580 0xd 0x20 0x1d28e 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235a0 0x3 0x20 0x172d9 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235c0 0x3 0x20 0x1a1d3 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235e0 0x4 0x20 0x16a86 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23620 0x4 0x20 0x10b98 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23640 0x11 0x40 0x1f4b4 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23680 0x1a 0x40 0x1ad69 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x236c0 0x9 0x20 0x1b5a0 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x236e0 0x9 0x20 0x2088a 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23700 0x2 0x20 0x172e1 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23720 0x12 0x40 0x126e8 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23760 0x7 0x20 0x1fc8d 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23780 0x6 0x20 0x1dbc2 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237a0 0x6 0x20 0x172e9 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237c0 0x7 0x20 0x1a1db 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237e0 0x25 0x60 0x1d296 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23840 0x20 0x40 0x19a87 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23880 0x12 0x40 0x1e5fe 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238c0 0x29 0x60 0x1f4bc 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23920 0x17 0x40 0x126f0 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23960 0x25 0x60 0x172f1 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239c0 0x29 0x60 0x1dbca 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a20 0x8 0x20 0x1d29e 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a40 0xf 0x20 0x15865 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a60 0x3 0x20 0x10ba0 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a80 0x3 0x20 0x1ecd6 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23aa0 0x3 0x20 0x132c2 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ac0 0x3 0x20 0x1586d 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ae0 0x3 0x20 0x212b3 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b00 0x3 0x20 0x1632b 0x23b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24120 0x100 0x140 0x22bc2 0x2b860 0x0 0x0 0x6aa3e0;
  mkGD 0x24260 0xdd8 0x1140 0x1b5a8 0x2b860 0x0 0x0 0x6aa3e1;
  mkGD 0x253a0 0xb8 0xe0 0x21c76 0x2b860 0x0 0x0 0x6aa3e2;
  mkGD 0x25480 0x28b0 0x32e0 0x17ce0 0x2b860 0x0 0x0 0x6aa3e3;
  mkGD 0x28760 0x9 0x20 0x18f6d 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28780 0x25 0x60 0x11e66 0x2b860 0x0 0x0 0x6aa3e6;
  mkGD 0x28800 0x30 0x60 0x172f9 0x2b860 0x0 0x0 0x6aa3e9;
  mkGD 0x288a0 0xc 0x20 0x18f75 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x288c0 0x30 0x60 0x1162d 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28960 0x20 0x40 0x22c16 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x289a0 0x100 0x140 0x20892 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28ae0 0x100 0x140 0x17398 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2b4e0 0xa0 0xc0 0x1fd0f 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2b820 0x1 0x20 0x1fd39 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2b840 0x1 0x20 0x1f4c4 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x168f40 0x40 0x60 0x1b5cb 0x2b860 0x0 0x0 0x6aa3e4;
  mkGD 0x168fa0 0x18 0x40 0x126f8 0x2b860 0x0 0x0 0x6aa3e5;
  mkGD 0x169000 0x60 0x80 0x1fc95 0x2b860 0x0 0x0 0x6aa3e7;
  mkGD 0x169080 0x18 0x40 0x143f0 0x2b860 0x0 0x0 0x6aa3e8;
  mkGD 0x172ec0 0x300 0x3c0 0x22bf7 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6aa240 0x30 0x60 0x15876 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6aa2a0 0x8 0x20 0x14f6a 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6aa2c0 0x8 0x20 0x1c765 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6aa2e0 0x8 0x20 0x22596 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6aa300 0x10 0x20 0x17339 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6aa320 0x8 0x20 0x13ce9 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6aa340 0x8 0x20 0x12728 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6aa360 0x30 0x60 0x1fcce 0x2b860 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6aa3c0 0x8 0x20 0x1d2a6 0x2b860 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 59%nat.
Proof. reflexivity. Qed.

Notation XS1_LO := 0x7fffc6b0%Z (only parsing).  Notation XS1_HI := 0x7fffd70c%Z (only parsing).
Notation XS2_LO := 0x800251e8%Z (only parsing).  Notation XS2_HI := 0x8002689e%Z (only parsing).
Notation XS3_LO := 0x800cd448%Z (only parsing).  Notation XS3_HI := 0x800cd47c%Z (only parsing).

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || ((0x6aa3e0 <=? o) && (o <? 0x6aa3eb)).

Definition gd_okb (g : gdesc) : bool :=
  (0 <=? gd_beg g) && (gd_beg g mod 8 =? 0) && (8 <=? gd_srz g) && (gd_srz g mod 8 =? 0)
  && (gd_beg g + gd_srz g <=? SEGTOP_A) && (gd_srz g / 8 <? 0x10000)
  && in_scratchb (SHB + gd_beg g / 8) (gd_srz g / 8) && odr_okb (gd_odr g)
  && (0 <=? gd_size g) && (gd_size g <? 2^64) && (0 <=? gd_name g) && (gd_name g <? 2^64) && (0 <=? gd_mod g) && (gd_mod g <? 2^64)
  && (0 <=? gd_dyn g) && (gd_dyn g <? 2^64) && (0 <=? gd_loc g) && (gd_loc g <? 2^64).

Lemma asan_gds_ok : Forall (fun g => gd_okb g = true) asan_gds.
Proof.
  assert (H : forallb gd_okb asan_gds = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Forall_forall. exact H.
Qed.

Lemma gd_okb_spec : forall g, gd_okb g = true ->
  0 <= gd_beg g /\ gd_beg g mod 8 = 0 /\ 8 <= gd_srz g /\ gd_srz g mod 8 = 0 /\ gd_beg g + gd_srz g <= SEGTOP_A
  /\ gd_srz g / 8 < 0x10000
  /\ ((XS1_LO <= SHB + gd_beg g / 8 /\ SHB + gd_beg g / 8 + gd_srz g / 8 <= XS1_HI)
      \/ (XS2_LO <= SHB + gd_beg g / 8 /\ SHB + gd_beg g / 8 + gd_srz g / 8 <= XS2_HI)
      \/ (XS3_LO <= SHB + gd_beg g / 8 /\ SHB + gd_beg g / 8 + gd_srz g / 8 <= XS3_HI))
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x6aa3e0 \/ gd_odr g = 0x6aa3e1 \/ gd_odr g = 0x6aa3e2 \/ gd_odr g = 0x6aa3e3 \/ gd_odr g = 0x6aa3e4 \/ gd_odr g = 0x6aa3e5 \/ gd_odr g = 0x6aa3e6 \/ gd_odr g = 0x6aa3e7 \/ gd_odr g = 0x6aa3e8 \/ gd_odr g = 0x6aa3e9 \/ gd_odr g = 0x6aa3ea)
  /\ 0 <= gd_size g < 2^64 /\ 0 <= gd_name g < 2^64 /\ 0 <= gd_mod g < 2^64 /\ 0 <= gd_dyn g < 2^64 /\ 0 <= gd_loc g < 2^64.
Proof.
  intros g H. unfold gd_okb, in_scratchb, odr_okb in H.
  repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H
                       | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
                       | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end.
  repeat split; try assumption; lia.
Qed.

Definition XENV_CORE_FPA : list (Z * Z) :=
  [(0x6abd40, 0x6abd44); (0x6cc058, 0x6cc05c); (0x6cc078, 0x6cc080);
   (0x6cc5f0, 0x6cc5f8); (0x173418, 0x173420); (0x173508, 0x173510); (0x173510, 0x174508); (0x174550, 0x174551);
   (0x6aa3e0, 0x6aa3e1); (0x6aa3e1, 0x6aa3eb);
   (0x172ea8, 0x172eb0); (0x173288, 0x173298)].
Definition XENV_FPA : list (Z * Z) := XENV_CORE_FPA ++ AEX_FPA.

Definition XENV_coreA (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells bsegs m 0x6abd40 [C4 (Z_to_bv 64 tid)])
  /\ rw_cells bsegs m 0x6cc058 [C4 (Z_to_bv 64 0)]
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells bsegs m 0x6cc078 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
  /\ rw_cells bsegs m 0x6cc5f0 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x173418 [C8 (Z_to_bv 64 0x173330)]
  /\ rw_cells bsegs m 0x173508 [C8 (Z_to_bv 64 0x173420)]
  /\ stdin_file m /\ rw_cells bsegs m 0x1735f8 [C8 (Z_to_bv 64 0x173510)]
  /\ gds_at m 0x173630 asan_gds
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells bsegs m 0x174500 [C8 v])
  /\ rw_cells bsegs m 0x174550 [C1 (Z_to_bv 8 0)]
  /\ (exists o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte, rw_cells bsegs m 0x6aa3e0 [C1 o1] /\ rw_cells bsegs m 0x6aa3e1 [C1 o2] /\ rw_cells bsegs m 0x6aa3e2 [C1 o3] /\ rw_cells bsegs m 0x6aa3e3 [C1 o4] /\ rw_cells bsegs m 0x6aa3e4 [C1 o5] /\ rw_cells bsegs m 0x6aa3e5 [C1 o6] /\ rw_cells bsegs m 0x6aa3e6 [C1 o7] /\ rw_cells bsegs m 0x6aa3e7 [C1 o8] /\ rw_cells bsegs m 0x6aa3e8 [C1 o9] /\ rw_cells bsegs m 0x6aa3e9 [C1 o10] /\ rw_cells bsegs m 0x6aa3ea [C1 o11])
  /\ el_xdataA m.

Definition XENVA (m : mem) : Prop := XENV_coreA m /\ aexA m.

Lemma in_XENV_CORE_FPA : forall lo hi x, In (lo, hi) XENV_CORE_FPA -> lo <= x < hi -> in_ranges XENV_CORE_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.
Lemma in_XENV_FPA : forall lo hi x, In (lo, hi) XENV_FPA -> lo <= x < hi -> in_ranges XENV_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.
Lemma in_ranges_app_l : forall l1 l2 x, in_ranges l1 x -> in_ranges (l1 ++ l2) x.
Proof. intros l1 l2 x (lo & hi & H1 & H2). exists lo, hi. split; [apply in_app_iff; left; exact H1| exact H2]. Qed.
Lemma in_ranges_app_r : forall l1 l2 x, in_ranges l2 x -> in_ranges (l1 ++ l2) x.
Proof. intros l1 l2 x (lo & hi & H1 & H2). exists lo, hi. split; [apply in_app_iff; right; exact H1| exact H2]. Qed.
Lemma in_ranges_app_inv : forall l1 l2 x, in_ranges (l1 ++ l2) x -> in_ranges l1 x \/ in_ranges l2 x.
Proof.
  intros l1 l2 x (lo & hi & H1 & H2). apply in_app_iff in H1. destruct H1 as [H1|H1]; [left| right]; exists lo, hi; (split; [exact H1| exact H2]).
Qed.

Lemma gds_at_agree : forall gs m m' a, gds_at m a gs ->
  agree_on (fun x => a <= x < a + 64 * Z.of_nat (length gs)) m m' -> gds_at m' a gs.
Proof.
  induction gs as [|g gs IH]; intros m m' a H AG; [exact I|]. destruct H as [H1 H2]. split.
  - apply (ro_cells_agree bsegs m m' _ _ H1). apply (agree_sub _ _ _ _ AG). intros x Hx. unfold gd_cells in Hx.
    cbn [cells_size csize Nat.add] in Hx. cbn [length]. lia.
  - apply (IH m m' (a + 64) H2). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [length]. lia.
Qed.

Lemma XENV_coreA_loc : fp_local XENV_CORE_FPA XENV_coreA.
Proof.
  intros m m' (TID & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR & XD) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_CORE_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw bsegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_CORE_FPA lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x6abd40 0x6abd44); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x6cc058 0x6cc05c); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x6cc078 0x6cc080); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0x6cc5f0 0x6cc5f8); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x173418 0x173420); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x173508 0x173510); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x173510 0x174508); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x173510 0x174508); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; apply AG; apply (in_XENV_CORE_FPA 0x173510 0x174508); [cbn; tauto|];
          rewrite asan_gds_length in Ha; cbn in Ha; lia|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x173510 0x174508); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x174550 0x174551); [cbn; tauto| lia| cbn; lia| exact CPL]|].
  split; cycle 1.
  { destruct XD as [X1 X2]. split; [apply (R 0x172ea8 (0x172ea8 + 8)); [cbn; tauto| lia| cbn; lia| exact X1]
                                  | apply (R 0x173288 (0x173288 + 16)); [cbn; tauto| lia| cbn; lia| exact X2]]. }
  destruct ODR as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & OC1 & OC2 & OC3 & OC4 & OC5 & OC6 & OC7 & OC8 & OC9 & OC10 & OC11).
  exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11.
  split; [apply (R 0x6aa3e0 0x6aa3e1); [cbn; tauto| lia| cbn; lia| exact OC1]|].
  split; [apply (R 0x6aa3e1 0x6aa3eb); [cbn; tauto| lia| cbn; lia| exact OC2]|].
  split; [apply (R 0x6aa3e1 0x6aa3eb); [cbn; tauto| lia| cbn; lia| exact OC3]|].
  split; [apply (R 0x6aa3e1 0x6aa3eb); [cbn; tauto| lia| cbn; lia| exact OC4]|].
  split; [apply (R 0x6aa3e1 0x6aa3eb); [cbn; tauto| lia| cbn; lia| exact OC5]|].
  split; [apply (R 0x6aa3e1 0x6aa3eb); [cbn; tauto| lia| cbn; lia| exact OC6]|].
  split; [apply (R 0x6aa3e1 0x6aa3eb); [cbn; tauto| lia| cbn; lia| exact OC7]|].
  split; [apply (R 0x6aa3e1 0x6aa3eb); [cbn; tauto| lia| cbn; lia| exact OC8]|].
  split; [apply (R 0x6aa3e1 0x6aa3eb); [cbn; tauto| lia| cbn; lia| exact OC9]|].
  split; [apply (R 0x6aa3e1 0x6aa3eb); [cbn; tauto| lia| cbn; lia| exact OC10]|].
  apply (R 0x6aa3e1 0x6aa3eb); [cbn; tauto| lia| cbn; lia| exact OC11].
Qed.

Lemma XENV_locA : fp_local XENV_FPA XENVA.
Proof.
  intros m m' [CORE AEXP] AG. split.
  - apply (XENV_coreA_loc m m' CORE). intros a Ha. apply AG. apply in_ranges_app_l. exact Ha.
  - apply (aexA_agree m m'); [| exact AEXP]. intros a Ha. apply AG. apply in_ranges_app_r. exact Ha.
Qed.

Lemma aex_core_sep : forall x, in_ranges AEX_FPA x -> ~ in_ranges XENV_CORE_FPA x.
Proof.
  intros x Hx (lo & hi & Hin & Hlh). apply in_AEX_FPA_iff in Hx. unfold AEX, AEX_A0, TR_LATCH, AEF_INCB in Hx. cbn in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Definition XENV_lawsA : xenv_laws XENVA XENV_FPA.
Proof.
  refine {| xl_loc := XENV_locA; xl_core := XENV_coreA; xl_core_fp := XENV_CORE_FPA; xl_split := _;
            xl_core_loc := XENV_coreA_loc; xl_core_sep := aex_core_sep; xl_aex_in := _; xl_core_in := _; xl_libc := _; xl_xdata := _ |}.
  - intros m. unfold XENVA. tauto.
  - intros x Hx. apply in_ranges_app_r. exact Hx.
  - intros x Hx. apply in_ranges_app_l. exact Hx.
  - intros m (TID & EXL & LIBC & _). exact LIBC.
  - intros m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XD). exact XD.
Defined.

Lemma XENV_imgA : forall x, in_ranges XENV_FPA x -> client_static x /\ ~ drv_cell x /\ outside IO_FPA x /\ outside LIB_FP x.
Proof.
  intros x (lo & hi & Hin & Hx). unfold XENV_FPA, XENV_CORE_FPA, AEX_FPA, AEX, AEX_A0, TR_LATCH, AEF_INCB in Hin. cbn in Hin.
  split; [| split; [| split]].
  - apply client_static_intro.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, TR_INIT, g_read_stage.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold IO_FPA. cbn.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (split; [lia| split; [lia| split; [lia| exact I]]])|]). destruct Hin.
  - unfold LIB_FP. cbn.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (repeat (split; [lia|])); try exact I|]). destruct Hin.
Qed.

Definition xit_rt (m : mem) : Prop :=
  ro_cells bsegs m 0x168998 [C8 (Z_to_bv 64 0xb2520); C8 (Z_to_bv 64 0x58498)]
  /\ ro_cells bsegs m 0x16f538 [C8 (Z_to_bv 64 0x1689a8); C8 (Z_to_bv 64 0x168998)]
  /\ ro_cells bsegs m 0x16e740 [C8 (Z_to_bv 64 0x14fba4); C8 (Z_to_bv 64 0)]
  /\ (exists d : word, ro_cells bsegs m 0x170580 [C8 d])
  /\ ro_cells bsegs m 0x16f438 [C8 (Z_to_bv 64 0x173630); C8 (Z_to_bv 64 0x1744f0)]
  /\ ro_cells bsegs m 0x16e750 [C8 (Z_to_bv 64 0x207660)]
  /\ ro_cells bsegs m 0x16e760 [C8 (Z_to_bv 64 0x2096e8); C8 (Z_to_bv 64 0x1753b8); C8 (Z_to_bv 64 0x177bb8);
                               C8 (Z_to_bv 64 0x1788a8); C8 (Z_to_bv 64 0x1788b0); C8 (Z_to_bv 64 0x1788a0);
                               C8 (Z_to_bv 64 0x170780)]
  /\ ro_cells bsegs m 0x1753d0 [C4 (Z_to_bv 64 1)]
  /\ rw_cells bsegs m 0x175470 [C8 (Z_to_bv 64 0)]
  /\ ro_cells bsegs m 0x177bb8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells bsegs m 0x178898 [C1 (Z_to_bv 8 1)]
  /\ ro_cells bsegs m 0x17741c [C1 (Z_to_bv 8 1)]
  /\ ro_cells bsegs m 0x209760 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ ro_cells bsegs m 0x170780 [C8 (Z_to_bv 64 0x161214)]
  /\ ro_cells bsegs m 0x209a60 [C1 (Z_to_bv 8 0)]
  /\ stk bsegs m XS1_LO XS1_HI /\ stk bsegs m XS2_LO XS2_HI /\ stk bsegs m XS3_LO XS3_HI.
