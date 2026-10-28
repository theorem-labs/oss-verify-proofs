From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_x2t_hdefs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma x2hb_r1_nth : forall ws A bs a i, (i < length bs)%nat ->
  nth_error (replay1 A bs a ws) i =
    if (Z.leb a (A + Z.of_nat i) && Z.ltb (A + Z.of_nat i) (a + Z.of_nat (length ws)))%bool
    then nth_error ws (Z.to_nat (A + Z.of_nat i - a)) else nth_error bs i.
Proof.
  induction ws as [|b ws IH]; intros A bs a i Hi.
  - cbn [replay1 length]. destruct (Z.leb_spec a (A + Z.of_nat i)); destruct (Z.ltb_spec (A + Z.of_nat i) (a + Z.of_nat 0));
      cbn [andb]; first [reflexivity | lia].
  - cbn [replay1 length].
    assert (LB : Nat.lt i (length (if (Z.leb A a && Z.ltb a (A + Z.of_nat (length bs)))%bool
                              then upd_bytes bs (Z.to_nat (a - A)) [b] else bs))).
    { destruct (Z.leb_spec A a); destruct (Z.ltb_spec a (A + Z.of_nat (length bs))); cbn [andb]; try exact Hi.
      rewrite upd_bytes_length; cbn [length]; lia. }
    rewrite (IH A _ (a + 1) i LB). clear LB IH.
    destruct (Z.leb_spec A a); destruct (Z.ltb_spec a (A + Z.of_nat (length bs)));
    destruct (Z.leb_spec (a + 1) (A + Z.of_nat i)); destruct (Z.ltb_spec (A + Z.of_nat i) (a + 1 + Z.of_nat (length ws)));
    destruct (Z.leb_spec a (A + Z.of_nat i)); destruct (Z.ltb_spec (A + Z.of_nat i) (a + Z.of_nat (S (length ws))));
    cbn [andb]; try lia;
    try (rewrite upd_bytes_nth by (cbn [length]; lia);
         destruct (Nat.leb_spec (Z.to_nat (a - A)) i); destruct (Nat.ltb_spec i (Z.to_nat (a - A) + length [b]));
         cbn [andb length] in *; try lia);
    first [ reflexivity
          | replace (Z.to_nat (A + Z.of_nat i - a)) with (S (Z.to_nat (A + Z.of_nat i - (a + 1)))) by lia; reflexivity
          | replace (Z.to_nat (A + Z.of_nat i - a)) with O by lia; replace (i - Z.to_nat (a - A))%nat with O by lia; reflexivity ].
Qed.

Lemma x2hb_r1_in : forall ws A bs a j, 0 <= j -> A <= a -> a + Z.of_nat (length ws) <= A + Z.of_nat (length bs) ->
  a <= A + j < a + Z.of_nat (length ws) ->
  nth_error (replay1 A bs a ws) (Z.to_nat j) = nth_error ws (Z.to_nat (A + j - a)).
Proof.
  intros ws A bs a j H0 H1 H2 H3. rewrite x2hb_r1_nth by lia. rewrite Z2Nat.id by lia.
  destruct (Z.leb_spec a (A + j)); destruct (Z.ltb_spec (A + j) (a + Z.of_nat (length ws))); cbn [andb]; first [reflexivity | lia].
Qed.

Lemma x2hb_r1_out : forall ws A bs a j, 0 <= j < Z.of_nat (length bs) -> (A + j < a \/ a + Z.of_nat (length ws) <= A + j) ->
  nth_error (replay1 A bs a ws) (Z.to_nat j) = nth_error bs (Z.to_nat j).
Proof.
  intros ws A bs a j H0 H1. rewrite x2hb_r1_nth by lia. rewrite Z2Nat.id by lia.
  destruct (Z.leb_spec a (A + j)); destruct (Z.ltb_spec (A + j) (a + Z.of_nat (length ws))); cbn [andb]; first [reflexivity | lia].
Qed.

Lemma x2hb_znth_map : forall (bs : list byte) i b, nth_error bs (Z.to_nat i) = Some b ->
  Znth i (map bv_unsigned bs) = bv_unsigned b.
Proof.
  intros bs i b H. unfold Znth. apply nth_error_nth. rewrite nth_error_map, H. reflexivity.
Qed.

Lemma x2hb_znth_old : forall (dt : list Z) i, 0 <= i < zlen dt -> Forall isbyte dt ->
  nth_error (map (Z_to_bv 8) dt) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i dt)) /\ 0 <= Znth i dt < 256.
Proof.
  intros dt i Hi HB. unfold Znth. rewrite nth_error_map.
  rewrite (nth_error_nth' dt 0) by lia. split; [reflexivity|].
  apply (proj1 (Forall_forall _ dt) HB). apply nth_In. lia.
Qed.

Lemma x2hb_bv8 : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma x2hb_dt_of : forall (bs : list byte), map (Z_to_bv 8) (map bv_unsigned bs) = bs /\ Forall isbyte (map bv_unsigned bs).
Proof.
  intros bs. split.
  - rewrite map_map. rewrite (map_ext _ (fun b => b)); [apply map_id|].
    intros b. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. apply bv_unsigned_in_range.
  - apply Forall_map, Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Lemma x2hb_pro : forall (RNG : footprint) (x1 gp tp x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPF DT SYM pos cnt bg nb T bs lvl mtl : Z) (Q : machine_state -> Prop),
  x2hb_hyps RNG SPF DT SYM mtl -> mem_inv bsegs m -> stk bsegs m (SPF - 112) SPF -> x2hb_art m -> tp = Z_to_bv 64 ATP ->
  (forall m1 (j0 : list byte), rw_cells bsegs m1 (SPF + -112) (X2HBFR x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 j0) ->
     mem_inv bsegs m1 -> munch [(SPF - 112, SPF)] m m1 -> wmono bsegs m m1 ->
     evtF bsegs RNG Q
       (MS (mkR x1 (Z_to_bv 64 (SPF + -112)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4 + 4 * pos)) (Z_to_bv 64 (SYM + bg))
                (Z_to_bv 64 (SYM + bg + cnt)) (Z_to_bv 64 nb) (Z_to_bv 64 T) (Z_to_bv 64 bs) (Z_to_bv 64 lvl) (Z_to_bv 64 ASHBASE)
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x8d29c) fc None m1 (seg_rom bsegs))) ->
  evtF bsegs RNG Q
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4 + 4 * pos)) (Z_to_bv 64 (SYM + bg)) (Z_to_bv 64 (SYM + bg + cnt))
              (Z_to_bv 64 nb) (Z_to_bv 64 T) (Z_to_bv 64 bs) (Z_to_bv 64 lvl) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8d25c) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros HY MI STK0 ART TP K. open_hyhb HY. destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  unfold KHIGH in KLO.
  pose proof (munch_refl [(SPF - 112, SPF)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep.
  carve_frame 112%nat STK0.
  do 15 zstep.
  try kx_mkR_foldF.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?v _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    replace v with (Z_to_bv 64 ASHBASE) by (unfold ASHBASE; reflexivity) end.
  eapply K; [eassumption| eassumption| eassumption| eassumption].
Qed.

Definition x2hb_hs (x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : amem) (SPF DT SYM pos bg cnt nb bs lvl L a7 pc : Z) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (SPF + -112)) gp tp (Z_to_bv 64 ASHOFF) (Z_to_bv 64 3) x7 x8 x9 (Z_to_bv 64 (DT + 4 * pos + 4))
          (Z_to_bv 64 (SYM + bg)) (Z_to_bv 64 (SYM + (bg + cnt))) (Z_to_bv 64 nb) (Z_to_bv 64 L) (Z_to_bv 64 bs)
          (Z_to_bv 64 lvl) (Z_to_bv 64 a7) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma x2hb_disp : forall (RNG : footprint) (x1 gp tp x5 x6 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPF DT SYM pos cnt bg nb T bs lvl : Z) (Q : machine_state -> Prop),
  0 <= nb <= T -> 1 <= T <= 12 -> rng_aimg RNG -> mem_inv bsegs m -> x2hb_art m ->
  (T - nb = 0 -> evtF bsegs RNG Q (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                                     SPF DT SYM pos bg cnt nb bs lvl 1 1 0x8d7f8)) ->
  (T - nb = 1 -> evtF bsegs RNG Q (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                                     SPF DT SYM pos bg cnt nb bs lvl 2 2 0x8d2c0)) ->
  (T - nb = 2 -> evtF bsegs RNG Q (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                                     SPF DT SYM pos bg cnt nb bs lvl 4 4 0x8d8b8)) ->
  (T - nb = 3 -> evtF bsegs RNG Q (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                                     SPF DT SYM pos bg cnt nb bs lvl 8 8 0x8d3e8)) ->
  (4 <= T - nb -> evtF bsegs RNG Q (x2hb_hs x1 gp tp x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                                     SPF DT SYM pos bg cnt nb bs lvl (2 ^ (T - nb)) 8 0x8d5dc)) ->
  evtF bsegs RNG Q
    (MS (mkR x1 (Z_to_bv 64 (SPF + -112)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4 + 4 * pos)) (Z_to_bv 64 (SYM + bg))
             (Z_to_bv 64 (SYM + bg + cnt)) (Z_to_bv 64 nb) (Z_to_bv 64 T) (Z_to_bv 64 bs) (Z_to_bv 64 lvl) (Z_to_bv 64 ASHBASE)
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x8d29c) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros HNB HT RI MI ART K0 K1 K2 K3 K4.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL). unfold x2hb_hs in K0, K1, K2, K3, K4.
  unfold ASHBASE. do 5 zstep. try kx_mkR_foldF.
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ ?v5 _ _ _ _ _ _ _ _ ?v14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    replace v14 with (Z_to_bv 64 (2 ^ (T - nb)));
    [| f_equal; rewrite (KXS.swrap32_small (T - nb)) by lia; rewrite !(Z.mod_small (T - nb)) by lia;
       rewrite Z.shiftl_1_l; symmetry; apply KXS.swrap32_small; split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]];
    replace v5 with (Z_to_bv 64 ASHOFF) by (unfold ASHOFF; reflexivity)
  end.
  assert (C : T - nb = 0 \/ T - nb = 1 \/ T - nb = 2 \/ T - nb = 3 \/ 4 <= T - nb) by lia.
  destruct C as [C|[C|[C|[C|C]]]].
  1: replace (2 ^ (T - nb)) with 1 by (rewrite C; reflexivity).
  2: replace (2 ^ (T - nb)) with 2 by (rewrite C; reflexivity).
  3: replace (2 ^ (T - nb)) with 4 by (rewrite C; reflexivity).
  4: replace (2 ^ (T - nb)) with 8 by (rewrite C; reflexivity).
  1-4: kx_runFm [0x8d2c0; 0x8d3e8; 0x8d5dc; 0x8d7f8; 0x8d8b8] 30%nat (@nil kz) (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  5: assert (LB : 16 <= 2 ^ (T - nb) <= 4096) by (split; [change 16 with (2^4) | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
  5: kx_runFm [0x8d2c0; 0x8d3e8; 0x8d5dc; 0x8d7f8; 0x8d8b8] 30%nat [KZRange (2 ^ (T - nb)) 16 4096]
       (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
  all: kx_post_regs; cbn [mem_denot].
  - exact (K0 C).
  - exact (K1 C).
  - exact (K2 C).
  - exact (K3 C).
  - exact (K4 C).
Qed.

Lemma x2hb_ret : forall (RNG : footprint) (x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
    (m m1 : amem) (SPF DT T mtl cur : Z) (j0 : list byte) (dt : list Z)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
  rng RNG (SPF - 112) 112 -> KHIGH <= SPF - 112 -> SPF + 16 <= 2^47 ->
  rw_cells bsegs m1 (SPF + -112) (X2HBFR x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 j0) -> mem_inv bsegs m1 ->
  munch [(DT + 4, DT + (4 * (1 + 2 ^ mtl))); (SPF - 112, SPF)] m m1 -> wmono bsegs m m1 ->
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt) -> zlen dt = (4 * (1 + 2 ^ mtl)) -> Forall isbyte dt -> x2pref T cur dt ->
  evtF bsegs RNG (x2hb_post x1 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc SPF DT T mtl m cur)
    (MS (mkR y1 (Z_to_bv 64 (SPF + -112)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24
             y25 y26 y27 y28 y29 y30 y31) F (Z_to_bv 64 0x8dbd8) fc None m1 (seg_rom bsegs)).
Proof.
  intros until y31. intros RSTF KLO SPT FR MI MU WM DTC DTLEN DTBY PRE. unfold KHIGH in KLO.
  unfold X2HBFR in FR.
  do 15 zstep.
  apply evtF_done.
  pose proof (stk_of_rw_cells bsegs _ _ _ FR) as STK. cbn [cells_size csize Nat.add length] in STK.
  unfold x2hb_post. do 17 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]).
  replace (SPF - 112) with (SPF + -112) by lia. replace SPF with (SPF + -112 + Z.of_nat 112) at 2 by lia. exact STK.
Qed.
End CANSEC1.
