(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 279 of its 294 lines of code are new or changed and 45 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img owed_seg7_c.
Import ListNotations.
Open Scope Z_scope.

(** owed_seg7 of the plain image (0x150d0, 37 instructions, leaf). The loop at 0x150e4 visits GLYPH's 29
    entries with a1 = 29 - i and a2 = &GLYPH[i].segs; the entry's character g is tested against c by
    [glyph_test] (the machine's three branches), which equals [glyph_match] on every entry and every c < 256.
    On a match the segment string (in .rodata) is folded by the loop at 0x15140; after the last entry a0 = -1. *)

Module OwedSeg7W.

(** ---- the model side ---- *)

(** The machine's test of entry character g against c (0x150e8-0x1510c). *)
Definition glyph_test (g c : Z) : bool :=
  if Z.land g 223 =? 72 then c =? g
  else (c =? g) || (((Z.land g 223 + -65) mod 18446744073709551616 <=? 25) && (Z.land (Z.lxor c g) 223 =? 0)).

Lemma glyph_test_check :
  zall (fun i => zall (fun c => Bool.eqb (glyph_test (nth (Z.to_nat i) codec_glyph_chr 0) c)
                                         (glyph_match (nth (Z.to_nat i) codec_glyph_chr 0) c)) 0 256) 0 29 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma glyph_test_ok : forall i c, 0 <= i < 29 -> 0 <= c < 256 ->
  glyph_test (nth (Z.to_nat i) codec_glyph_chr 0) c = glyph_match (nth (Z.to_nat i) codec_glyph_chr 0) c.
Proof.
  intros i c Hi Hc.
  pose proof (zall_range _ 0 29 glyph_test_check i Hi) as H. cbv beta in H.
  pose proof (zall_range _ 0 256 H c Hc) as H'. cbv beta in H'.
  apply Bool.eqb_prop in H'. exact H'.
Qed.

Lemma glyph_chr_eq : map fst glyph = codec_glyph_chr.
Proof. vm_compute. reflexivity. Qed.
Lemma glyph_str_eq : map snd glyph = codec_glyph_str.
Proof. vm_compute. reflexivity. Qed.
Lemma glyph_len : length glyph = 29%nat.
Proof. reflexivity. Qed.

Lemma skipn_cons_nth : forall {A} (l : list A) (d : A) (k : nat), (k < length l)%nat ->
  skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l d. induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma go_step : forall i c, 0 <= i < 29 ->
  owed_seg7_go (skipn (Z.to_nat i) glyph) c =
  if glyph_match (nth (Z.to_nat i) codec_glyph_chr 0) c
  then segs_val (nth (Z.to_nat i) codec_glyph_str [])
  else owed_seg7_go (skipn (Z.to_nat (i + 1)) glyph) c.
Proof.
  intros i c Hi.
  rewrite (skipn_cons_nth glyph (0, []) (Z.to_nat i)) by (rewrite glyph_len; lia).
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite <- glyph_chr_eq, <- glyph_str_eq.
  assert (E1 : nth (Z.to_nat i) (map fst glyph) 0 = fst (nth (Z.to_nat i) glyph (0, [])))
    by (apply (map_nth fst glyph (0, []))).
  assert (E2 : nth (Z.to_nat i) (map snd glyph) [] = snd (nth (Z.to_nat i) glyph (0, [])))
    by (apply (map_nth snd glyph (0, []))).
  rewrite E1, E2.
  destruct (nth (Z.to_nat i) glyph (0, [])) as [g s]. reflexivity.
Qed.

Lemma go_end : forall c, owed_seg7_go (skipn (Z.to_nat 29) glyph) c = -1.
Proof. reflexivity. Qed.

Lemma glyph_chr_range : forall i, 0 <= i < 29 -> 0 <= nth (Z.to_nat i) codec_glyph_chr 0 < 256.
Proof.
  intros i Hi.
  pose proof (zall_range (fun i => (0 <=? nth (Z.to_nat i) codec_glyph_chr 0) && (nth (Z.to_nat i) codec_glyph_chr 0 <? 256))
                0 29 ltac:(vm_compute; reflexivity) i Hi) as H.
  cbv beta in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma glyph_str_chars : forall i, 0 <= i < 29 ->
  Forall (fun ch => 0x61 <= ch <= 0x67) (nth (Z.to_nat i) codec_glyph_str []).
Proof.
  intros i Hi.
  pose proof (zall_range (fun i => forallb (fun ch => (0x61 <=? ch) && (ch <=? 0x67)) (nth (Z.to_nat i) codec_glyph_str []))
                0 29 ltac:(vm_compute; reflexivity) i Hi) as H.
  cbv beta in H. apply Forall_forall. intros ch Hin. rewrite forallb_forall in H. specialize (H ch Hin).
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma segs_fold_step : forall s acc ch,
  fold_left (fun v ch => Z.lor v (2 ^ (6 - (ch - 0x61)))) (ch :: s) acc =
  fold_left (fun v ch => Z.lor v (2 ^ (6 - (ch - 0x61)))) s (Z.lor acc (2 ^ (6 - (ch - 0x61)))).
Proof. reflexivity. Qed.

(* The read of byte k of a byte list in memory. *)
Lemma byte_read : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma u8_small : forall g, 0 <= g < 256 -> bv_unsigned (Z_to_bv 8 g) = g.
Proof. intros g Hg. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia. Qed.

(* The segment bit of 0x15140-0x15148 (subw, sllw) for a segment letter 'a'..'g'. *)
Lemma bit_val : forall ch, 97 <= ch <= 103 ->
  bv_swrap 32 (Z.shiftl 1 ((bv_swrap 32 (103 - ch) mod 18446744073709551616) mod 32)) mod 18446744073709551616 =
  2 ^ (6 - (ch - 97)).
Proof.
  intros ch Hch.
  assert (E : ch = 97 \/ ch = 98 \/ ch = 99 \/ ch = 100 \/ ch = 101 \/ ch = 102 \/ ch = 103) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; vm_compute; reflexivity.
Qed.

(** ---- the walk ---- *)

Section W.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z).
Hypothesis HC : 0 <= c < 256.
Hypothesis HRL : relro_img m.
Hypothesis HMI : mem_inv rsegs m.

Definition Qs (ms' : machine_state) : Prop :=
  exists (a1' a2' a3' a4' a5' a6' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (owed_seg7_spec c)) a1' a2' a3' a4' a5' a6' a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs).

(* The segment loop at 0x15140: a1 = the current character ch, a2 = the address p of the rest. *)
Lemma seg_loop : forall (rest : list Z) (ch acc p : Z) (a5 a6 : word),
  0x61 <= ch <= 0x67 -> Forall (fun ch => 0x61 <= ch <= 0x67) rest -> 0 <= acc < 128 ->
  bytes_at rsegs m p (map (Z_to_bv 8) (rest ++ [0])) ->
  owed_seg7_spec c = fold_left (fun v ch => Z.lor v (2 ^ (6 - (ch - 0x61)))) (ch :: rest) acc ->
  evt rsegs Qs
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 acc) (Z_to_bv 64 ch) (Z_to_bv 64 p) (Z_to_bv 64 0x67) (Z_to_bv 64 1) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15140) fc None m (seg_rom rsegs)).
Proof.
  induction rest as [|ch' rest IH]; intros ch acc p a5 a6 Hch Hrest Hacc HB HS.
  - pose proof (byte_read m p _ 0 HB ltac:(cbn; lia)) as HR0.
    rewrite Z.add_0_r in HR0. change (Z.to_nat 0) with 0%nat in HR0. cbn [app map nth] in HR0.
    do 5 zstep.
    rewrite (bit_val ch Hch).
    replace (Z.lor (2 ^ (6 - (ch - 97))) acc) with (owed_seg7_spec c)
      by (rewrite HS; cbn [fold_left]; apply Z.lor_comm).
    cbv beta. try (rewrite u8_small by lia).
    zstep.
    if_cases K.
    + exfalso. zify_cond K. lia.
    + zstep. finish.
  - pose proof (byte_read m p _ 0 HB ltac:(cbn; lia)) as HR0.
    rewrite Z.add_0_r in HR0. change (Z.to_nat 0) with 0%nat in HR0. cbn [app map nth] in HR0.
    inversion Hrest as [|x l Hch' Hrest']; subst x l.
    assert (HB' : bytes_at rsegs m (p + 1) (map (Z_to_bv 8) (rest ++ [0]))).
    { change (map (Z_to_bv 8) ((ch' :: rest) ++ [0])) with ([Z_to_bv 8 ch'] ++ map (Z_to_bv 8) (rest ++ [0])) in HB.
      apply bytes_at_app in HB. destruct HB as [_ HB]. exact HB. }
    do 5 zstep.
    rewrite (bit_val ch Hch), Z.lor_comm.
    cbv beta. try (rewrite u8_small by lia).
    zstep.
    if_cases K.
    + eapply IH; try eassumption.
      pose proof (lor_lt_pow2 acc (2 ^ (6 - (ch - 97))) 7 ltac:(lia)) as L.
      assert (0 <= 2 ^ (6 - (ch - 97)) < 2 ^ 7) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
      specialize (L H). change (2 ^ 7) with 128 in L. exact L.
    + exfalso. zify_cond K. lia.
Qed.

(* The matched entry i (0x15124): load its segment string and fold it. *)
Lemma found_ok : forall (i : Z) (a1 a2 a3 a4 a5 a6 : word),
  0 <= i < 29 -> bv_unsigned a2 = 0x1f230 + 16 * i ->
  owed_seg7_spec c = segs_val (nth (Z.to_nat i) codec_glyph_str []) ->
  evt rsegs Qs
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15124) fc None m (seg_rom rsegs)).
Proof.
  intros i a1 a2 a3 a4 a5 a6 Hi H2 HS.
  pose proof (codec_GLYPH_ptr_read m i HRL Hi) as HP. unfold CODEC_GLYPH in HP.
  pose proof (codec_glyph_str_at m i HMI Hi) as HB.
  pose proof (glyph_str_chars i Hi) as HF.
  set (p := nth (Z.to_nat i) codec_glyph_ptr 0) in *.
  assert (E2 : a2 = Z_to_bv 64 (127528 + 16 * i + 8)) by (rewrite <- (Z_to_bv_bv_unsigned a2), H2; f_equal; lia).
  subst a2. cbv delta [wa] in HP.
  zstep.
  destruct (nth (Z.to_nat i) codec_glyph_str []) as [|ch rest] eqn:ES.
  - pose proof (byte_read m p _ 0 HB ltac:(cbn; lia)) as HR0.
    rewrite Z.add_0_r in HR0. change (Z.to_nat 0) with 0%nat in HR0. cbn [app map nth] in HR0.
    zstep. cbv beta. try (rewrite u8_small by lia).
    zstep.
    if_cases K.
    + zstep. zstep.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (owed_seg7_spec c)) by (rewrite HS; reflexivity).
      finish.
    + exfalso. zify_cond K. lia.
  - inversion HF as [|x l Hch Hrest]; subst x l.
    pose proof (byte_read m p _ 0 HB ltac:(cbn; lia)) as HR0.
    rewrite Z.add_0_r in HR0. change (Z.to_nat 0) with 0%nat in HR0. cbn [app map nth] in HR0.
    assert (HB' : bytes_at rsegs m (p + 1) (map (Z_to_bv 8) (rest ++ [0]))).
    { change (map (Z_to_bv 8) ((ch :: rest) ++ [0])) with ([Z_to_bv 8 ch] ++ map (Z_to_bv 8) (rest ++ [0])) in HB.
      apply bytes_at_app in HB. destruct HB as [_ HB]. exact HB. }
    zstep. cbv beta. try (rewrite u8_small by lia).
    zstep.
    if_cases K.
    + exfalso. zify_cond K. lia.
    + do 4 zstep.
      eapply seg_loop; try eassumption; lia.
Qed.

Definition loop_ok (k : nat) : Prop :=
  forall (i : Z) (a1 a2 a5 a6 : word),
  Z.of_nat k = 29 - i -> 0 <= i < 29 ->
  bv_unsigned a1 = 29 - i -> bv_unsigned a2 = 0x1f230 + 16 * i ->
  owed_seg7_spec c = owed_seg7_go (skipn (Z.to_nat i) glyph) c ->
  evt rsegs Qs
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) a1 a2 (Z_to_bv 64 72) (Z_to_bv 64 25) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x150e4) fc None m (seg_rom rsegs)).

(* No match at entry i (0x15110): the next entry, or a0 = -1 after the last. *)
Lemma next_ok : forall k, loop_ok k ->
  forall (i : Z) (a1 a2 a5 a6 : word),
  Z.of_nat (S k) = 29 - i -> 0 <= i < 29 ->
  bv_unsigned a1 = 29 - i -> bv_unsigned a2 = 0x1f230 + 16 * i ->
  owed_seg7_spec c = owed_seg7_go (skipn (Z.to_nat (i + 1)) glyph) c ->
  evt rsegs Qs
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) a1 a2 (Z_to_bv 64 72) (Z_to_bv 64 25) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15110) fc None m (seg_rom rsegs)).
Proof.
  intros k LOOP i a1 a2 a5 a6 Hk Hi H1 H2 HS.
  do 3 zstep. rewrite ?H1, ?H2.
  if_cases K.
  - zify_cond K.
    eapply LOOP with (i := i + 1); try (rewrite unsigned_lit by lia); try lia.
  - zify_cond K.
    assert (i = 28) by lia. subst i.
    zstep. zstep.
    replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (owed_seg7_spec c)) by (rewrite HS; reflexivity).
    finish.
Qed.

Lemma iter_ok : forall k, loop_ok k -> loop_ok (S k).
Proof.
  intros k LOOP i a1 a2 a5 a6 Hk Hi H1 H2 HS.
  pose proof (codec_GLYPH_chr_read m i HRL Hi) as HG. unfold CODEC_GLYPH in HG.
  pose proof (glyph_chr_range i Hi) as Hg.
  pose proof (glyph_test_ok i c Hi HC) as HT.
  pose proof (go_step i c Hi) as HGo.
  set (g := nth (Z.to_nat i) codec_glyph_chr 0) in *.
  set (s := nth (Z.to_nat i) codec_glyph_str []) in *.
  do 3 zstep. rewrite u8_small by lia.
  if_cases K1.
  - (* (g & 0xdf) == 'H': match iff c == g *)
    zify_cond K1. zstep.
    if_cases K2.
    + zify_cond K2.
      assert (E : glyph_test g c = true) by (unfold glyph_test; rewrite K1, Z.eqb_refl; apply Z.eqb_eq; lia).
      eapply found_ok; try eassumption. rewrite HS, HGo, <- HT, E. reflexivity.
    + zify_cond K2.
      assert (E : glyph_test g c = false) by (unfold glyph_test; rewrite K1, Z.eqb_refl; apply Z.eqb_neq; lia).
      eapply next_ok; try eassumption. rewrite HS, HGo, <- HT, E. reflexivity.
  - zify_cond K1. zstep.
    if_cases K2.
    + (* c == g: the test at 0x1510c is taken *)
      zify_cond K2. zstep.
      if_cases K3.
      * assert (E : glyph_test g c = true)
          by (unfold glyph_test; rewrite (proj2 (Z.eqb_neq _ _) K1); replace (c =? g) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
        eapply found_ok; try eassumption. rewrite HS, HGo, <- HT, E. reflexivity.
      * exfalso. zify_cond K3. lia.
    + zify_cond K2. do 2 zstep.
      if_cases K3.
      * (* not a letter *)
        zify_cond K3.
        assert (E : glyph_test g c = false)
          by (unfold glyph_test; rewrite (proj2 (Z.eqb_neq _ _) K1); replace (c =? g) with false by (symmetry; apply Z.eqb_neq; lia);
              replace ((Z.land g 223 + -65) mod 18446744073709551616 <=? 25) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
        eapply next_ok; try eassumption. rewrite HS, HGo, <- HT, E. reflexivity.
      * zify_cond K3. do 3 zstep.
        if_cases K4.
        -- zify_cond K4.
           assert (E : glyph_test g c = true)
             by (unfold glyph_test; rewrite (proj2 (Z.eqb_neq _ _) K1); replace (c =? g) with false by (symmetry; apply Z.eqb_neq; lia);
                 replace ((Z.land g 223 + -65) mod 18446744073709551616 <=? 25) with true by (symmetry; apply Z.leb_le; lia);
                 cbn [orb andb]; apply Z.eqb_eq; lia).
           eapply found_ok; try eassumption. rewrite HS, HGo, <- HT, E. reflexivity.
        -- zify_cond K4.
           assert (E : glyph_test g c = false)
             by (unfold glyph_test; rewrite (proj2 (Z.eqb_neq _ _) K1); replace (c =? g) with false by (symmetry; apply Z.eqb_neq; lia);
                 replace ((Z.land g 223 + -65) mod 18446744073709551616 <=? 25) with true by (symmetry; apply Z.leb_le; lia);
                 cbn [orb andb]; apply Z.eqb_neq; lia).
           zstep.
           eapply next_ok; try eassumption. rewrite HS, HGo, <- HT, E. reflexivity.
Qed.

Lemma loop_all : forall k, loop_ok k.
Proof.
  induction k as [|k IH].
  - intros i a1 a2 a5 a6 Hk Hi. exfalso. cbn in Hk. lia.
  - apply iter_ok. exact IH.
Qed.

Lemma entry_ok : forall (a0 a1 a2 a3 a4 a5 a6 : word), a0 = Z_to_bv 64 c ->
  evt rsegs Qs
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OWED_SEG7) fc None m (seg_rom rsegs)).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 ->. unfold OWED_SEG7.
  do 5 zstep.
  eapply (loop_all 29) with (i := 0); try (rewrite unsigned_lit by lia); try lia. reflexivity.
Qed.

End W.
End OwedSeg7W.

Theorem owed_seg7_holds : owed_seg7_contract.
Proof.
  unfold owed_seg7_contract, owed_seg7_pre.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m c [HC [HA [HRL HMI]]].
  change (evt rsegs (OwedSeg7W.Qs ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OWED_SEG7) fc None m (seg_rom rsegs))).
  eapply OwedSeg7W.entry_ok; eassumption.
Qed.
