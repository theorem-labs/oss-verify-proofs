(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 4602 of its 4661 lines of code are new or changed and 310 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntStep.v, with its module paths, module names and numbers changed; 3340 of its 3586 lines of code are new or changed and 4415 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableAge ReacArbitrate ReacSenderKind.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c hunt_c reac_rate_snap_c reac_master_only_cadence_ns_c reac_hunt_step_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP0l YP06 YP0e YP03 YCbn YC1h YC1g YA0q YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0o.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_hunt_step disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Bytes PropExec Mem.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma hs_ble_cons : forall (b : byte) (bs : list byte), bytes_le_to_Z (b :: bs) = bv_unsigned b + 256 * bytes_le_to_Z bs.
Proof.
intros b bs. cbn [bytes_le_to_Z]. apply Bytes.lor_shiftl8_add.
- pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia.
- apply PropExec.bytes_le_to_Z_nonneg.
Qed.
Lemma hs_ble_nth : forall (bs : list byte) j, (j < length bs)%nat ->
Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat j) mod 256 = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b bs IH]; intros j Hj; cbn [length] in Hj; [lia|].
rewrite hs_ble_cons. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg bs) as Hr.
destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
- cbn [nth]. replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia.
rewrite <- Z.shiftr_shiftr by lia. rewrite (Z.shiftr_div_pow2 _ 8) by lia. change (2 ^ 8) with 256.
replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs) by (symmetry; Z.div_mod_to_equations; lia).
apply IH. lia.
Qed.
Lemma hs_nth_le : forall n z j, (j < n)%nat ->
nth j (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat j)).
Proof.
induction n as [|n IH]; intros z j Hj; [lia|].
destruct j as [|j]; cbn [Z_to_le_bytes nth].
- rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
- rewrite (IH (Z.shiftr z 8) j ltac:(lia)). rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma hs_nth_sub : forall (L : list byte) k n j, 0 <= k -> (j < n)%nat ->
nth j (sub L k n) (Z_to_bv 8 0) = nth (Z.to_nat k + j) L (Z_to_bv 8 0).
Proof.
intros L k n j Hk Hj. unfold sub.
assert (E1 : nth j (firstn n (skipn (Z.to_nat k) L)) (Z_to_bv 8 0) = nth j (skipn (Z.to_nat k) L) (Z_to_bv 8 0)).
{ destruct (Nat.lt_ge_cases j (length (skipn (Z.to_nat k) L))) as [Hl|Hl].
  - rewrite <- (firstn_skipn n (skipn (Z.to_nat k) L)) at 2. rewrite app_nth1; [reflexivity|]. rewrite length_firstn. lia.
  - rewrite !nth_overflow; [reflexivity | exact Hl | rewrite length_firstn; lia]. }
rewrite E1.
destruct (Nat.lt_ge_cases (Z.to_nat k) (length L)) as [Hl|Hl].
- rewrite <- (firstn_skipn (Z.to_nat k) L) at 2. rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn. f_equal. lia.
- rewrite skipn_all2 by exact Hl. transitivity (Z_to_bv 8 0 : byte); [destruct j; reflexivity | symmetry; apply nth_overflow; lia].
Qed.
Lemma hs_vm : forall segs (m : word -> option byte) a (L : list byte) k n,
garr8 segs m a (map (fun b : byte => bv_unsigned b) L) -> 0 <= k -> (Z.to_nat k + n <= length L)%nat ->
val_mem segs m (a + k) n (u_at L k n).
Proof.
intros segs m a L k n HG Hk Hn j Hj.
assert (LS : length (sub L k n) = n) by (unfold sub; rewrite length_firstn, length_skipn; lia).
pose proof (disco_table.ble_range (sub L k n)) as Hr. rewrite LS in Hr.
unfold u_at. rewrite le_byte_small by lia.
pose proof (garr8_mbyte segs m a _ (Z.to_nat k + j) HG ltac:(rewrite length_map; lia)) as Hm.
replace (a + k + Z.of_nat j) with (a + Z.of_nat (Z.to_nat k + j)) by lia. rewrite Hm. f_equal.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia). rewrite map_nth.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite (hs_ble_nth (sub L k n) j) by lia. rewrite hs_nth_sub by lia.
pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k + j) L (Z_to_bv 8 0))) as Hb. change (bv_modulus 8) with 256 in Hb.
apply Z.mod_small. lia.
Qed.
Lemma hs_garr8_le : forall segs (m : word -> option byte) a n v, val_mem segs m a n v -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 segs m a (map (fun b : byte => bv_unsigned b) (Z_to_le_bytes n v)).
Proof.
intros segs m a n v Hv Hr j Hj. rewrite length_map, length_Z_to_le_bytes in Hj.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; lia).
rewrite map_nth, hs_nth_le by lia.
pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat j)))) as Hb. change (bv_modulus 8) with 256 in Hb.
split; [|lia].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (Hv j Hj). f_equal. rewrite le_byte_small by lia. rewrite le_byte_small by (change (8 * Z.of_nat 1) with 8; lia).
rewrite Z.shiftr_0_r. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma hs_sub_r : forall (L1 L2 : list byte) k n, 0 <= k -> (length L1 <= Z.to_nat k)%nat ->
sub (L1 ++ L2) k n = sub L2 (k - Z.of_nat (length L1)) n.
Proof.
intros L1 L2 k n Hk Hl. unfold sub. rewrite skipn_app. rewrite (skipn_all2 L1) by lia. cbn [app].
f_equal. f_equal. lia.
Qed.
Lemma hs_sub_l : forall (L1 L2 : list byte) k n, 0 <= k -> (Z.to_nat k + n <= length L1)%nat ->
sub (L1 ++ L2) k n = sub L1 k n.
Proof.
intros L1 L2 k n Hk Hl. unfold sub. rewrite skipn_app, firstn_app, length_skipn.
replace (n - (length L1 - Z.to_nat k))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.
Lemma hs_fr_mbyte : forall segs E rs (m m' : word -> option byte) a, frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
~ in_wrange E rs a -> mbyte segs m' a = mbyte segs m a.
Proof.
intros segs E rs m m' a HF Ha Hn. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma hs_aregs : forall (regs0 regs' : bvmap 5 word),
getr regs' 2 = getr regs0 2 -> getr regs' 3 = getr regs0 3 -> getr regs' 4 = getr regs0 4 ->
getr regs' 8 = getr regs0 8 -> getr regs' 9 = getr regs0 9 -> getr regs' 18 = getr regs0 18 ->
getr regs' 19 = getr regs0 19 -> getr regs' 20 = getr regs0 20 -> getr regs' 21 = getr regs0 21 ->
getr regs' 22 = getr regs0 22 -> getr regs' 23 = getr regs0 23 -> getr regs' 24 = getr regs0 24 ->
getr regs' 25 = getr regs0 25 -> getr regs' 26 = getr regs0 26 -> getr regs' 27 = getr regs0 27 ->
aregs_preserved regs0 regs'.
Proof.
intros regs0 regs' H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr. unfold acallee_saved in Hr.
destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [assumption..|].
assert (E : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; assumption.
Qed.
Ltac hs_ck_sv Hs :=
  lazymatch goal with
  | |- YP09.chunk_ok _ ?E _ _ (YP09.mkChunk ?o (CVal _ (SOff ?k 0))) =>
    lazymatch goal with
    | Hk : ew E k = getr ?rg ?r |- _ =>
      apply (chunk_ok_val _ E _ _ o 8 (SOff k 0) (bv_unsigned (getr rg r)));
      [ cbn [sv_denot]; rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr rg r)) as Hbr; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hbr; exact Hbr
      | lia
      | exact (Hs (o, r) ltac:(repeat (first [left; reflexivity | right]))) ]
    end
  end.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing} {PO : PAObjImg lib_both3_0_listing} {PH : PAHiImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis TAGE : treac_disco_table_age_spec B.
Hypothesis TARB : treac_arbitrate_spec B.
Hypothesis TSENDER : treac_sender_kind_spec B.
Definition REAC_HUNT_STEP_STK : Z := 128 + REAC_ARBITRATE_STK.
Definition treac_hunt_step_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (h now : Z) (H : list byte) : world SEGS -> config -> Prop :=
  fun W' c' => exists fq' : YK11.FPState,
    freg_kept (@YK11.fp_regs fq) (@YK11.fp_regs fq') /\ @YK11.fp_csr fq' = @YK11.fp_csr fq /\
    apost_base (fx := fq') SEGS B REAC_HUNT_STEP_STK [(h, h + 400); (h + 440, h + 476)] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (if hs_verdict h H now =? s32_at H 440 then 0 else 1) /\
         garr8 SEGS (mrestrict (w_H W') mem') h (map (fun b : byte => bv_unsigned b) (hs_hunt h H now)) /\
         hunt_ok (hs_hunt h H now) /\
         Permutation (ablocks B ly' S') (ablocks B ly S)) W' c'.
Definition treac_hunt_step_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (h now hb hn : Z) (H : list byte),
  afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 h -> getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
  0 < h -> h mod 8 = 0 ->
  In (hb, hn) (ablocks B ly S) -> hb <= h -> h + 480 <= hb + req_size hn ->
  hunt_ok H ->
  garr8 SEGS (mrestrict (w_H W) mem) h (map (fun b : byte => bv_unsigned b) H) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 99) + 1608) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 98) + 1812) 8 D3837 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_hunt_step) regs mem md)
    (treac_hunt_step_post fq regs ly S W mem md h now H).
Definition SB_HS : Z := 0x7fff8000.
Definition Bspan_HS : Z * Z := (SB_HS, SB_HS + 2 ^ 44 - 1).
Definition HS_CEIL : Z := 140737479966720.
Definition HS_FP (h : Z) : list (Z * Z) := [(h, h + 400); (h + 440, h + 476)].
Definition hs_blk (h : Z) (H : list byte) (now : Z) : list byte :=
  hs_table H now ++ sub H 400 40 ++ sub H 440 4 ++ hs_arb h H now ++ skipn 476 H.
Definition HS_SLOTS : list (Z * bv 5) := [(120, 1%bv); (112, 8%bv); (104, 9%bv); (96, 18%bv); (88, 19%bv);
  (80, 20%bv); (72, 21%bv); (64, 22%bv); (56, 23%bv); (48, 24%bv); (40, 25%bv); (32, 26%bv); (24, 27%bv)].
Definition hs_saved (regs0 : bvmap 5 word) (W : world SEGS) (mem : word -> option byte) : Prop :=
  Forall (fun p : Z * bv 5 => val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 128 + fst p) 8
    (bv_unsigned (getr regs0 (snd p)))) HS_SLOTS.
Definition hs_rates_img : Prop :=
  (forall j, 0 <= j < 12 -> in_img SEGS (VAL (A_OBJ 65) + j)) /\
  (forall k, 0 <= k < 8 -> in_img SEGS (VAL (A_HI 99) + 1608 + k) /\ in_img SEGS (VAL (A_HI 98) + 1812 + k)).
Lemma hs_rates_img_ok : hs_rates_img.
Proof.
split.
- intros j Hj. replace (VAL (A_OBJ 65) + j) with (VAL (A_OBJ 65) + 0 + j) by lia.
  apply (pa_obj_win 65 0 j); [vm_compute; lia|].
  split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 Hj)|]. vm_compute. discriminate.
- intros k Hk. split.
  + apply (pa_hi_win 99 1608 k); [vm_compute; lia|].
    split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 Hk)|]. vm_compute. discriminate.
  + apply (pa_hi_win 98 1812 k); [vm_compute; lia|].
    split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 Hk)|]. vm_compute. discriminate.
Qed.
Definition hs_rates (W : world SEGS) (mem : word -> option byte) : Prop :=
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 /\
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 99) + 1608) 8 D6000 /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 98) + 1812) 8 D3837.
Definition hs_pre (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (ch : list (Z * Z * Z)) (h now hb hn : Z) (H : list byte) : Prop :=
  afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
  0 <= now < 2 ^ 64 /\ 0 < h /\ h mod 8 = 0 /\
  In (hb, hn) (ablocks B ly S) /\ hb <= h /\ h + 480 <= hb + req_size hn /\ hunt_ok H.
Definition hs_mod (h now : Z) (H : list byte) : Prop :=
  length (hs_table H now) = 400%nat /\ table_ok (hs_table H now) /\ length (hs_arb h H now) = 32%nat.
Definition hs_post (F0 : bvmap 5 word) (C0 : bv 32) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (h now : Z) (H : list byte) : world SEGS -> config -> Prop :=
  fun W' c' => exists fq' : YK11.FPState,
    freg_kept F0 (@YK11.fp_regs fq') /\ @YK11.fp_csr fq' = C0 /\
    apost_base (fx := fq') SEGS B REAC_HUNT_STEP_STK [(h, h + 400); (h + 440, h + 476)] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (if hs_verdict h H now =? s32_at H 440 then 0 else 1) /\
         garr8 SEGS (mrestrict (w_H W') mem') h (map (fun b : byte => bv_unsigned b) (hs_hunt h H now)) /\
         hunt_ok (hs_hunt h H now) /\
         Permutation (ablocks B ly' S') (ablocks B ly S)) W' c'.
Definition hs_fc (C0 : bv 32) (fq : YK11.FPState) : Prop :=
  @YK11.fp_csr fq = C0 \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fq)) 5) 7 = 0.
Lemma hs_fc_apost : forall (C0 : bv 32) (fa fb : YK11.FPState), hs_fc C0 fa ->
  (@YK11.fp_csr fb = @YK11.fp_csr fa \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fb)) 5) 7 = 0) -> hs_fc C0 fb.
Proof. intros C0 fa fb HA [E|E]; unfold hs_fc; [rewrite E; exact HA | right; exact E]. Qed.
Lemma hs_fk_apost : forall (F0 : bvmap 5 word) (fa fb : YK11.FPState), freg_kept F0 (@YK11.fp_regs fa) ->
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fb) k = Sem.reg_get (@YK11.fp_regs fa) k) ->
  freg_kept F0 (@YK11.fp_regs fb).
Proof. intros F0 fa fb HA HB k H10 H14 H15. rewrite (HB k H10). exact (HA k H10 H14 H15). Qed.
Lemma hs_apost_fix : forall (C0 : bv 32) (fq : YK11.FPState) STK FP (regs : bvmap 5 word) ly S W mem md k Q W' c',
  hs_fc C0 fq ->
  apost_base (fx := fq) SEGS B STK FP regs ly S W mem md k Q W' c' ->
  apost_base (fx := YK11.mkFP (@YK11.fp_regs fq) C0) SEGS B STK FP regs ly S W mem md k Q W' c'.
Proof.
intros C0 fq STK FP regs ly S W mem md k Q W' c' HFC (fx' & ly' & S' & regs' & mem' & md' & Hc & Hfr & Hcs & HR).
exists fx', ly', S', regs', mem', md'. split; [exact Hc|]. split; [exact Hfr|].
split; [|exact HR]. cbn [YK11.fp_csr]. destruct Hcs as [E|E]; [rewrite E; exact HFC | right; exact E].
Qed.
Definition hs_inv (F0 : bvmap 5 word) (C0 : bv 32) (fq : YK11.FPState) (regs0 : bvmap 5 word) (ly : alayout) (S : astate)
  (W : world SEGS) (mem0 : word -> option byte) (md0 : Model) (h now : Z) (H : list byte)
  (mem : word -> option byte) (md : Model) : Prop :=
  (exists lyc Sc, ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc Sc W mem md 0 /\
     Permutation (ablocks B lyc Sc) (ablocks B ly S)) /\
  hs_mod h now H /\
  garr8 SEGS (mrestrict (w_H W) mem) h (map (fun b : byte => bv_unsigned b) (hs_blk h H now)) /\
  hs_saved regs0 W mem /\ hs_rates W mem /\
  freg_kept F0 (@YK11.fp_regs fq) /\ hs_fc C0 fq.
Definition hs_mid (F0 : bvmap 5 word) (C0 : bv 32) (fq : YK11.FPState) (regs0 : bvmap 5 word) (ly : alayout) (S : astate)
  (W : world SEGS) (mem0 : word -> option byte) (md0 : Model) (h now : Z) (H : list byte)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  hs_inv F0 C0 fq regs0 ly S W mem0 md0 h now H mem md /\
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112) 8 (h + 440) /\
  getr regs 2 = w64 (spZ regs0 - 128) /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
  getr regs 9 = w64 h /\ getr regs 18 = w64 now /\ getr regs 22 = w64 SB_HS.
Definition hs_epi_ex (regs0 : bvmap 5 word) (h u : Z) : list word :=
  w64 (h + 440) :: map (fun p : Z * bv 5 => getr regs0 (snd p)) HS_SLOTS ++ [w64 u].
Definition hs_epi_stack : YP09.region := YP09.mkRegion (Some 2%nat) 0 128 0 0
  [YP09.mkChunk 16 (CVal 8 (SOff 32 0)); YP09.mkChunk 120 (CVal 8 (SOff 33 0)); YP09.mkChunk 112 (CVal 8 (SOff 34 0));
   YP09.mkChunk 104 (CVal 8 (SOff 35 0)); YP09.mkChunk 96 (CVal 8 (SOff 36 0)); YP09.mkChunk 88 (CVal 8 (SOff 37 0));
   YP09.mkChunk 80 (CVal 8 (SOff 38 0)); YP09.mkChunk 72 (CVal 8 (SOff 39 0)); YP09.mkChunk 64 (CVal 8 (SOff 40 0));
   YP09.mkChunk 56 (CVal 8 (SOff 41 0)); YP09.mkChunk 48 (CVal 8 (SOff 42 0)); YP09.mkChunk 40 (CVal 8 (SOff 43 0));
   YP09.mkChunk 32 (CVal 8 (SOff 44 0)); YP09.mkChunk 24 (CVal 8 (SOff 45 0))].
Definition hs_epi_h : YP09.region := YP09.mkRegion (Some 32%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 46 0))].
Definition ss_epi : sstate := mkSS (AF_both3_reac_hunt_step + 268) sr_atoms [hs_epi_stack; hs_epi_h] None
  (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (22%nat, mkAF SB_HS SB_HS 0); (32%nat, mkAF 4096 HS_CEIL 3)] [] []).
Definition Bx_HS : sv := SOff 22 0.
Definition SH_EPI : list shent := [mkSHE 32 0 4].
Lemma hs_fr_aview : forall E rs (Hh : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict Hh m) (mrestrict Hh m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS Hh m' a = aview SEGS Hh m a.
Proof. intros E rs Hh m m' a HF Ha Hn. unfold aview. rewrite (hs_fr_mbyte SEGS E rs _ _ a HF Ha Hn). reflexivity. Qed.
Lemma hs_inv_kept : forall F0 C0 (fq : YK11.FPState) regs0 ly S W mem0 md0 ch h now hb hn H mem md mem' md',
  hs_pre ly S W regs0 mem0 md0 ch h now hb hn H ->
  hs_inv F0 C0 fq regs0 ly S W mem0 md0 h now H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ spZ regs0 - 104 <= a) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (exists lyc Sc, ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc Sc W mem' md' 0 /\
     Permutation (ablocks B lyc Sc) (ablocks B ly S)) ->
  hs_inv F0 C0 fq regs0 ly S W mem0 md0 h now H mem' md'.
Proof.
intros F0 C0 fq regs0 ly S W mem0 md0 ch h now hb hn H mem md mem' md' HPRE HINV HK HJ.
destruct HPRE as (HPRE & HROD & Hnow & Hh0 & Hh8 & Hin & Hhb & Hhe & HOK).
destruct HINV as (_ & HMOD & HBLK & HSAV & HRATES & HFK & HCSR).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem0 md0 hb hn HAR0 Hin) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & Hbpres & _).
pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as Rsp0. change (bv_modulus 64) with (2 ^ 64) in Rsp0. fold (spZ regs0) in Rsp0.
pose proof (pa_obj_img_all 65 ltac:(vm_compute; lia)) as O65. pose proof (pa_hi_img 99 ltac:(vm_compute; lia)) as H99.
pose proof (pa_hi_img 98 ltac:(vm_compute; lia)) as H98. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in O65, H99, H98.
split; [exact HJ|]. split; [exact HMOD|].
split.
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem' h _); [|exact HBLK].
  intros a Ha. rewrite length_map in Ha. assert (LB : (length (hs_blk h H now) <= 480)%nat).
  { destruct HMOD as (LT & _ & LA). destruct HOK as (LH & _).
    unfold hs_blk. rewrite !length_app, LT, LA, length_skipn, !disco_table.length_sub by (rewrite ?LH; lia). lia. }
  apply HK; lia. }
split.
{ unfold hs_saved in *. rewrite Forall_forall in HSAV |- *. intros p Hp.
  apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem'); [|exact (HSAV p Hp)].
  assert (Hp2 : 24 <= fst p <= 120) by (cbv [HS_SLOTS In] in Hp; repeat destruct Hp as [<-|Hp]; cbn [fst]; lia || destruct Hp).
  intros k Hk. apply HK; lia. }
split.
{ destruct HRATES as (R1 & R2 & R3 & R4). split; [|split; [|split]].
  - apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact R1].
    intros x Hx. unfold shadow_of_addr, SHADOW_OFF. apply HK; [|left]; Z.div_mod_to_equations; lia.
  - apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem' _ _); [|exact R2].
    intros a Ha. rewrite length_map in Ha. change (length RATES) with 12%nat in Ha. apply HK; lia.
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem'); [|exact R3]. intros k Hk. apply HK; lia.
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem'); [|exact R4]. intros k Hk. apply HK; lia. }
split; [exact HFK | exact HCSR].
Qed.
Lemma hs_blk_T : forall h H now k n, length (hs_table H now) = 400%nat -> 0 <= k -> (Z.to_nat k + n <= 400)%nat ->
  sub (hs_blk h H now) k n = sub (hs_table H now) k n.
Proof. intros h H now k n LT Hk Hn. unfold hs_blk. apply hs_sub_l; [exact Hk | rewrite LT; exact Hn]. Qed.
Lemma hs_blk_H : forall h H now k n, length (hs_table H now) = 400%nat -> length H = 480%nat ->
  400 <= k -> (Z.to_nat k + n <= 440)%nat -> sub (hs_blk h H now) k n = sub H k n.
Proof.
intros h H now k n LT LH Hk Hn. unfold hs_blk.
assert (L40 : length (sub H 400 40) = 40%nat) by (apply disco_table.length_sub; rewrite ?LH; lia).
rewrite hs_sub_r by (rewrite ?LT; lia). rewrite LT. rewrite hs_sub_l by (rewrite ?L40; lia).
rewrite reac_hunt_step.hs_sub_sub by lia. f_equal. lia.
Qed.
Lemma hs_blk_440 : forall h H now, length (hs_table H now) = 400%nat -> length H = 480%nat ->
  sub (hs_blk h H now) 440 4 = sub H 440 4.
Proof.
intros h H now LT LH. unfold hs_blk.
assert (L40 : length (sub H 400 40) = 40%nat) by (apply disco_table.length_sub; rewrite ?LH; lia).
assert (L4 : length (sub H 440 4) = 4%nat) by (apply disco_table.length_sub; rewrite ?LH; lia).
rewrite hs_sub_r by (rewrite ?LT; lia). rewrite LT. rewrite hs_sub_r by (rewrite ?L40; lia). rewrite L40.
rewrite hs_sub_l by (rewrite ?L4; lia). unfold sub at 1. cbn [Z.to_nat Pos.to_nat]. rewrite skipn_O.
apply firstn_all2. rewrite L4. lia.
Qed.
Lemma hs_blk_A : forall h H now k n, length (hs_table H now) = 400%nat -> length H = 480%nat -> length (hs_arb h H now) = 32%nat ->
  444 <= k -> (Z.to_nat k + n <= 476)%nat -> sub (hs_blk h H now) k n = sub (hs_arb h H now) (k - 444) n.
Proof.
intros h H now k n LT LH LA Hk Hn. unfold hs_blk.
assert (L40 : length (sub H 400 40) = 40%nat) by (apply disco_table.length_sub; rewrite ?LH; lia).
assert (L4 : length (sub H 440 4) = 4%nat) by (apply disco_table.length_sub; rewrite ?LH; lia).
rewrite hs_sub_r by (rewrite ?LT; lia). rewrite LT. rewrite hs_sub_r by (rewrite ?L40; lia). rewrite L40.
rewrite hs_sub_r by (rewrite ?L4; lia). rewrite L4. rewrite hs_sub_l by (rewrite ?LA; lia). f_equal. lia.
Qed.
Lemma hs_zc_eq : forall x c, -2 ^ 63 <= x < 2 ^ 63 -> 0 <= c < 2 ^ 63 -> (zcanon x =? c) = (x =? c).
Proof.
intros x c Hx Hc. unfold zcanon, M64.
destruct (Z_lt_le_dec x 0) as [Hn|Hp].
- rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
  destruct (Z.eqb_spec (x + 1 * 2 ^ 64) c), (Z.eqb_spec x c); try reflexivity; lia.
- rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma hs_sw32 : forall u, -2 ^ 31 <= bv_swrap 32 u < 2 ^ 31.
Proof.
intros u. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
Z.div_mod_to_equations. lia.
Qed.
Lemma hs_U32 : forall E k u, ew E k = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> U E (SExt true 32 (SOff k 0)) = zcanon (bv_swrap 32 u).
Proof.
intros E k u Hk Hu. rewrite U_SExt, (U_atom E k u Hk) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small u) by lia. reflexivity.
Qed.
Lemma hs_br32 : forall E k u c, ew E k = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> 0 <= c < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff k 0))) (sv_denot E (SLit c)) = (bv_swrap 32 u =? c) /\
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff k 0))) (sv_denot E (SLit c)) = negb (bv_swrap 32 u =? c).
Proof.
intros E k u c Hk Hu Hc. pose proof (hs_sw32 u) as Hs.
rewrite branch_eq_U, branch_ne_U, (hs_U32 E k u Hk Hu), U_lit by lia. rewrite hs_zc_eq by lia. split; reflexivity.
Qed.
Lemma hs_zc_sub : forall p c, -2 ^ 62 <= p < 2 ^ 62 -> 0 <= c < 2 ^ 62 ->
  (zcanon (zcanon p + zcanon (- c)) <? zcanon 1) = (p =? c).
Proof.
intros p c Hp Hc. change (zcanon 1) with 1.
assert (E1 : zcanon (zcanon p + zcanon (- c)) = zcanon (p - c)) by (unfold zcanon, M64; rewrite <- Zplus_mod; f_equal; lia).
rewrite E1. assert (R : 0 <= zcanon (p - c) < 2 ^ 64) by (unfold zcanon, M64; apply Z.mod_pos_bound; lia).
replace (zcanon (p - c) <? 1) with (zcanon (p - c) =? 0) by (destruct (Z.eqb_spec (zcanon (p - c)) 0), (Z.ltb_spec (zcanon (p - c)) 1); try reflexivity; lia).
rewrite hs_zc_eq by lia. destruct (Z.eqb_spec (p - c) 0), (Z.eqb_spec p c); try reflexivity; lia.
Qed.
Lemma hs_zc_m1 : forall p, -2 ^ 62 <= p < 2 ^ 62 -> (zcanon (zcanon p + zcanon (-1)) <? zcanon 1) = (p =? 1).
Proof. intros p Hp. exact (hs_zc_sub p 1 Hp ltac:(lia)). Qed.
Lemma hs_zc_m3 : forall p, -2 ^ 62 <= p < 2 ^ 62 -> (zcanon (zcanon p + zcanon (-3)) <? zcanon 1) = (p =? 3).
Proof. intros p Hp. exact (hs_zc_sub p 3 Hp ltac:(lia)). Qed.
Lemma hs_sw64_zc : forall x, -2 ^ 63 <= x < 2 ^ 63 -> bv_swrap 64 (zcanon x) = x.
Proof.
intros x Hx. unfold bv_swrap, bv_wrap, zcanon, M64. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. Z.div_mod_to_equations. lia.
Qed.
Lemma hs_brge0 : forall E k u, ew E k = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SExt true 32 (SOff k 0))) = (bv_swrap 32 u <=? 0).
Proof.
intros E k u Hk Hu. pose proof (hs_sw32 u) as Hs. cbn [branch_taken]. unfold bv_lts.
change (bv_signed (sv_denot E (SLit 0))) with (Sg E (SLit 0)). change (bv_signed (sv_denot E (SExt true 32 (SOff k 0)))) with (Sg E (SExt true 32 (SOff k 0))).
rewrite !S_of_U, U_SLit, (hs_U32 E k u Hk Hu). rewrite (hs_sw64_zc (bv_swrap 32 u)) by lia. change (bv_swrap 64 (zcanon 0)) with 0.
destruct (Z.ltb_spec 0 (bv_swrap 32 u)), (Z.leb_spec (bv_swrap 32 u) 0); first [reflexivity | exfalso; lia].
Qed.
Definition hs_s2_ex (h now : Z) (H : list byte) : list word :=
  map w64 [u_at H 432 4; u_at H 436 4; u_at H 440 4; u_at H 420 4; u_at H 424 8;
    u_at (hs_table H now) 384 4; u_at (hs_arb h H now) 0 4; u_at (hs_arb h H now) 24 4].
Definition hs_s2_h : YP09.region := YP09.mkRegion (Some 9%nat) 0 480 0 0
  [YP09.mkChunk 432 (CVal 4 (SOff 32 0)); YP09.mkChunk 436 (CVal 4 (SOff 33 0)); YP09.mkChunk 440 (CVal 4 (SOff 34 0));
   YP09.mkChunk 420 (CVal 4 (SOff 35 0)); YP09.mkChunk 424 (CVal 8 (SOff 36 0)); YP09.mkChunk 384 (CVal 4 (SOff 37 0));
   YP09.mkChunk 444 (CVal 4 (SOff 38 0)); YP09.mkChunk 468 (CVal 4 (SOff 39 0))].
Definition hs_s2_stack : YP09.region := YP09.mkRegion (Some 2%nat) 0 128 8 24 [].
Definition ss_s2 : sstate := mkSS (AF_both3_reac_hunt_step + 132) (sr_set (sr_set sr_atoms 19%bv (SOff 9 444)) 20%bv (SOff 9 412))
  [hs_s2_stack; hs_s2_h] None
  (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF 4096 HS_CEIL 3); (22%nat, mkAF SB_HS SB_HS 0)] [] []).
Definition SH_S2 : list shent := [mkSHE 9 0 480].
Definition hs_keep_p (W : world SEGS) (sp0 : Z) (mem m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ sp0 - 104 <= a) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a.
Lemma hs_keep_step : forall W sp0 (mem m0 m1 : word -> option byte) E0 rs,
  hs_keep_p W sp0 mem m0 -> frame_of E0 rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) ->
  (forall a, (a < alloc_ceiling \/ sp0 - 104 <= a) -> ~ in_wrange E0 rs a) -> hs_keep_p W sp0 mem m1.
Proof.
intros W sp0 mem m0 m1 E0 rs HK HF HN a Ha Hb. rewrite (hs_fr_aview E0 rs (w_H W) m0 m1 a HF Ha (HN a Hb)). exact (HK a Ha Hb).
Qed.
Ltac hs_nw Usp :=
  let a := fresh "a" in let Ha := fresh "Ha" in let r := fresh "r" in let Hr := fresh "Hr" in let Hra := fresh "Hra" in
  intros a Ha (r & Hr & Hra);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr; repeat destruct Hr as [<-|Hr]; try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra; try rewrite Usp in Hra; lia.
Ltac hs_awr Usp :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-128));
      [ reflexivity | cbn [ew ewset Nat.eqb extK]; rewrite Usp; lia
      | cbn [YP09.r_wlo YP09.r_whi]; unfold REAC_HUNT_STEP_STK, REAC_ARBITRATE_STK, ESTACK; lia
      | cbn [YP09.r_wlo YP09.r_whi]; lia | ] ].
Ltac hs_keep Usp :=
  lazymatch goal with KEEP : hs_keep_p _ _ _ ?m0, HFr : frame_of ?E0 ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let K := fresh "KEEP" in pose proof (hs_keep_step _ _ _ _ _ E0 rs KEEP HFr ltac:(hs_nw Usp)) as K;
    clear KEEP; rename K into KEEP end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Definition hs_kx (W : world SEGS) (sp0 h : Z) (mem m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> (sp0 <= a \/ a < alloc_ceiling) -> ~ (h <= a < h + 400) -> ~ (h + 444 <= a < h + 476) ->
    aview SEGS (w_H W) m a = aview SEGS (w_H W) mem a.
Lemma hs_kx_step : forall W sp0 h (mem m0 m1 : word -> option byte) E0 rs,
  hs_kx W sp0 h mem m0 -> frame_of E0 rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) ->
  (forall a, (sp0 <= a \/ a < alloc_ceiling) -> ~ in_wrange E0 rs a) -> hs_kx W sp0 h mem m1.
Proof.
intros W sp0 h mem m0 m1 E0 rs HK HF HN a Ha Hb H1 H2.
rewrite (hs_fr_aview E0 rs (w_H W) m0 m1 a HF Ha (HN a Hb)). exact (HK a Ha Hb H1 H2).
Qed.
Lemma hs_kx_call : forall W sp0 h (mem m0 m1 : word -> option byte) lo hi wlo whi,
  hs_kx W sp0 h mem m0 ->
  (forall a : word, ~ (lo <= bv_unsigned a < hi) -> ~ (wlo <= bv_unsigned a < whi) ->
     aview SEGS (w_H W) m1 (bv_unsigned a) = aview SEGS (w_H W) m0 (bv_unsigned a)) ->
  (forall a, (sp0 <= a \/ a < alloc_ceiling) -> ~ (h <= a < h + 400) -> ~ (h + 444 <= a < h + 476) ->
     ~ (lo <= a < hi) /\ ~ (wlo <= a < whi)) ->
  hs_kx W sp0 h mem m1.
Proof.
intros W sp0 h mem m0 m1 lo hi wlo whi HK HC HD a Ha Hb H1 H2.
destruct (HD a Hb H1 H2) as [D1 D2].
pose proof (HC (Z_to_bv 64 a)) as C. rewrite unsigned_lit_small in C by lia.
rewrite (C D1 D2). exact (HK a Ha Hb H1 H2).
Qed.
Lemma hs_mb_of_av : forall Hh (m m' : word -> option byte) a,
  aview SEGS Hh m' a = aview SEGS Hh m a -> mbyte SEGS (mrestrict Hh m') a = mbyte SEGS (mrestrict Hh m) a.
Proof.
intros Hh m m' a E. unfold aview in E.
destruct (mbyte SEGS (mrestrict Hh m') a) as [b'|], (mbyte SEGS (mrestrict Hh m) a) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma hs_g8_sub : forall segs m a (L : list byte) k n,
  garr8 segs m a (map (fun b : byte => bv_unsigned b) L) -> 0 <= k -> (Z.to_nat k + n <= length L)%nat ->
  garr8 segs m (a + k) (map (fun b : byte => bv_unsigned b) (sub L k n)).
Proof.
intros segs m a L k n HG Hk Hn. unfold sub.
rewrite <- (firstn_skipn (Z.to_nat k) L) in HG. rewrite map_app in HG. apply garr8_app in HG as [_ HG].
rewrite length_map, length_firstn in HG. replace (Nat.min (Z.to_nat k) (length L)) with (Z.to_nat k) in HG by lia.
rewrite Z2Nat.id in HG by lia.
rewrite <- (firstn_skipn n (skipn (Z.to_nat k) L)) in HG. rewrite map_app in HG. apply garr8_app in HG as [HG _]. exact HG.
Qed.
Ltac hs_nw1 Usp :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hra := fresh "Hra" in
  intros (r & Hr & Hra);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr; repeat destruct Hr as [<-|Hr]; try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra; try rewrite Usp in Hra; lia.
Ltac hs_kxs Usp :=
  lazymatch goal with KX : hs_kx _ _ _ _ ?m0, HFr : frame_of ?E0 ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let K := fresh "KX" in pose proof (hs_kx_step _ _ _ _ _ _ E0 rs KX HFr ltac:(hs_nw Usp)) as K;
    clear KX; rename K into KX end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Section w.
Context {fx : YK11.FPState}.
Let RUN := paj_run (PL := PL_both3_0) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (PL := PL_both3_0) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Lemma hs_epi : forall (F0 : bvmap 5 word) (C0 : bv 32) ly S W (regs0 : bvmap 5 word) mem0 md0 ch (h now hb hn : Z) (H : list byte)
  (regs : bvmap 5 word) mem md (v : Z),
  hs_pre ly S W regs0 mem0 md0 ch h now hb hn H ->
  hs_mid F0 C0 fx regs0 ly S W mem0 md0 h now H regs mem md ->
  getr regs 11 = w64 v -> v = hs_verdict h H now ->
  SRr SEGS W (mkCfg (mkst (fx := fx) regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 268))) mem (seg_rom SEGS)) md)
    (hs_post F0 C0 regs0 ly S W mem0 md0 h now H).
Proof.
intros F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H regs mem md v HPRE HMID H11 Hv.
destruct HPRE as (HPRE & HROD & Hnow & Hh0 & Hh8 & Hin & Hhb & Hhe & HOK).
destruct HMID as (((lyc & Sc & HJ & HPerm) & HMOD & HBLK & HSAV & HRATES & HFK & HCSR) & HSPILL & R2 & R3 & R4 & R9 & R18 & R22).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof HJ as (HAR & _).
assert (Hinc : In (hb, hn) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
destruct (al_blocks _ _ LAWS lyc Sc W mem md hb hn HAR Hinc) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & Hbpres & _).
destruct HMOD as (LT & TOK & LA).
destruct HOK as (LH & _ & LOK & V0R).
assert (WS : REAC_HUNT_STEP_STK = 8464) by reflexivity.
pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as Rsp0. change (bv_modulus 64) with (2 ^ 64) in Rsp0. fold (spZ regs0) in Rsp0.
assert (LB : length (hs_blk h H now) = 480%nat).
{ unfold hs_blk. rewrite !length_app, LT, LA, length_skipn. rewrite !disco_table.length_sub by (rewrite ?LH; lia). rewrite LH. reflexivity. }
assert (Hu : u_at (hs_blk h H now) 440 4 = u_at H 440 4).
{ unfold u_at. f_equal. unfold hs_blk.
  rewrite hs_sub_r by (rewrite ?LT; lia). rewrite LT. rewrite hs_sub_r by (rewrite ?disco_table.length_sub by (rewrite ?LH; lia); lia).
  rewrite disco_table.length_sub by (rewrite ?LH; lia). rewrite hs_sub_l by (rewrite ?disco_table.length_sub by (rewrite ?LH; lia); lia).
  unfold sub at 1. cbn [Z.to_nat Pos.to_nat]. rewrite skipn_O. apply firstn_all2. rewrite disco_table.length_sub by (rewrite ?LH; lia). lia. }
set (u := u_at (hs_blk h H now) 440 4).
assert (Ru : 0 <= u < 2 ^ 32).
{ unfold u, u_at. pose proof (disco_table.ble_range (sub (hs_blk h H now) 440 4)) as Rb.
  rewrite disco_table.length_sub in Rb by (rewrite ?LB; lia). exact Rb. }
remember (Eimg (Ereg regs (hs_epi_ex regs0 h u))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (hs_epi_ex regs0 h u)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E22 : ew E 22 = getr regs 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)).
assert (EX : forall j, (j < 15)%nat -> ew E (32 + j) = nth j (hs_epi_ex regs0 h u) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39. pose proof (EX 8%nat ltac:(lia)) as E40.
pose proof (EX 9%nat ltac:(lia)) as E41. pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44. pose proof (EX 13%nat ltac:(lia)) as E45. pose proof (EX 14%nat ltac:(lia)) as E46.
cbn [Nat.add nth hs_epi_ex HS_SLOTS map app snd] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46.
assert (HAE : env_agree 32 (Ereg regs (hs_epi_ex regs0 h u)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (HRO : regs_ok E sr_atoms regs) by (subst E; apply regs_ok_Eimg_Ereg).
clear HE EL EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 128) by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (Uh : bv_unsigned (ew E 32) = h + 440) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_epi (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 268))) mem (seg_rom SEGS)))).
{ rewrite YA0o.restrict_mkst_fx. unfold ss_epi. apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, hs_epi_stack. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold hs_saved in HSAV. rewrite Forall_forall in HSAV.
      rewrite Forall_forall. intros c Hc. cbn [In] in Hc.
      repeat destruct Hc as [<-|Hc];
      [ apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 32 0) (h + 440));
        [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia
        | replace (spZ regs0 - 128 + 16) with (spZ regs0 - 112) by lia; exact HSPILL ]
      | hs_ck_sv HSAV .. | destruct Hc ].
    + unfold region_ok, hs_epi_h. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uh.
      split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hbpres (h + 440 + o) ltac:(lia))).
      * constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 46 0) u); [cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 4) with 32; exact Ru | lia |].
        rewrite Z.add_0_r. exact (hs_vm SEGS _ h (hs_blk h H now) 440 4 HBLK ltac:(lia) ltac:(rewrite LB; lia)).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region, hs_epi_stack, hs_epi_h.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uh.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uh, E22, R22. unfold w64. rewrite unsigned_lit_small by (unfold SB_HS; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    unfold SB_HS, HS_CEIL. repeat split. all: try (exact I || lia). all: Z.div_mod_to_equations; lia. }
assert (SHOK : sh_ok SEGS Bx_HS SH_EPI E (mrestrict (w_H W) mem)).
{ unfold sh_ok, SH_EPI. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E Bx_HS 32 hb (req_size hn) (h + 440) 0 4).
  - exact (range_addressable_of_block SEGS B LAWS lyc Sc W mem md hb hn hb (req_size hn) HAR Hinc ltac:(lia) ltac:(lia)).
  - unfold Bx_HS. rewrite (U_atom E 22 SB_HS) by (first [rewrite E22, R22; reflexivity | unfold SB_HS; lia]). reflexivity.
  - rewrite (U_atom E 32 (h + 440)) by (first [rewrite E32; reflexivity | lia]). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
unfold cfg_at.
paj_run_tok RUN HS HJ SHOK Bspan_HS.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|].
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32 (h + 440)); [reflexivity | exact Uh | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. left. split.
  - exists (h + 440, h + 476). split; [unfold HS_FP; right; left; reflexivity | cbn [fst snd]; lia].
  - exists hb, hn. split; [exact Hinc | lia]. }
clear SHOK.
assert (F11 : ew (ewset (ewset E 512 w) 513 w0) 11 = Z_to_bv 64 v) by (cbn [ew ewset Nat.eqb]; rewrite E11, H11; reflexivity).
assert (F46 : ew (ewset (ewset E 512 w) 513 w0) 46 = Z_to_bv 64 u) by (cbn [ew ewset Nat.eqb]; rewrite E46; reflexivity).
assert (VR : 0 <= v <= 3) by (rewrite Hv; unfold hs_verdict; apply reac_hunt_step.hs_dec_range; exact V0R).
assert (NW : forall a, ~ (h + 440 <= a < h + 444) -> ~ in_wrange E (ss_mem ss_epi) a).
{ intros a Ha (r & Hr & Hra'). cbn [ss_mem ss_epi In] in Hr.
  destruct Hr as [<-|[<-|[]]]; cbn [hs_epi_stack hs_epi_h YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; [lia | rewrite Uh in Hra'; lia]. }
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG.
destruct RG as (_ & _ & _ & RC). cbn [YP09.r_chunks YP09.r_base base_val] in RC.
apply Forall_inv in RC. cbn [ms_mem restrict] in RC.
apply (val_of_chunk_ok SEGS _ _ _ 0 4 (SOff 11 0) v) in RC;
  [| cbn [sv_denot]; rewrite F11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 4) with 32; lia | lia].
change (bv_unsigned (ew (ewset (ewset E 512 w) 513 w0) 32)) with (bv_unsigned (ew E 32)) in RC. rewrite Uh, Z.add_0_r in RC.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HS) as Q10.
lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ =>
  let e := eval vm_compute in (sr_get (ss_regs ss1) 10%bv) in change (sr_get (ss_regs ss1) 10%bv) with e in Q10 end.
unfold hs_post. exists (YK11.mkFP (@YK11.fp_regs fx) C0). split; [exact HFK|]. split; [reflexivity|].
eapply (hs_apost_fix C0 fx); [exact HCSR|].
apply apost_base_same_fx. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split. { rewrite Q1, E33. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ. }
split.
{ apply hs_aregs.
  - rewrite Q2, Usp. replace (spZ regs0 - 128 + 128) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite Q3, E3. exact R3.
  - rewrite Q4, E4. exact R4.
  - rewrite Q8, E34. reflexivity.
  - rewrite Q9, E35. reflexivity.
  - rewrite Q18, E36. reflexivity.
  - rewrite Q19, E37. reflexivity.
  - rewrite Q20, E38. reflexivity.
  - rewrite Q21, E39. reflexivity.
  - rewrite Q22, E40. reflexivity.
  - rewrite Q23, E41. reflexivity.
  - rewrite Q24, E42. reflexivity.
  - rewrite Q25, E43. reflexivity.
  - rewrite Q26, E44. reflexivity.
  - rewrite Q27, E45. reflexivity. }
split.
{ rewrite Q10, denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SAlu. cbn [zalu_raw]. rewrite (U_atom _ 11 v F11) by lia.
  rewrite U_SExt. rewrite (U_atom _ 46 u F46) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small u) by lia.
  replace (bv_swrap 32 u) with (s32_at H 440) by (unfold s32_at, u; rewrite Hu; reflexivity).
  rewrite <- Hv. set (s := s32_at H 440) in *.
  assert (Ev : v = 0 \/ v = 1 \/ v = 2 \/ v = 3) by lia. assert (Es : s = 0 \/ s = 1 \/ s = 2 \/ s = 3) by lia.
  destruct Ev as [-> | [-> | [-> | ->]]]; destruct Es as [-> | [-> | [-> | ->]]]; reflexivity. }
split.
{ unfold hs_hunt. unfold hs_blk in HBLK. rewrite !map_app in HBLK |- *.
  apply garr8_app in HBLK as [B1 HBLK]. apply garr8_app in HBLK as [B2 HBLK].
  apply garr8_app in HBLK as [B3 HBLK]. apply garr8_app in HBLK as [B4 B5].
  assert (L40 : length (sub H 400 40) = 40%nat) by (apply disco_table.length_sub; rewrite ?LH; lia).
  assert (L4 : length (sub H 440 4) = 4%nat) by (apply disco_table.length_sub; rewrite ?LH; lia).
  rewrite !length_map in B2. rewrite !length_map in B3. rewrite !length_map in B4. rewrite !length_map in B5.
  rewrite LT in B2, B3, B4, B5. rewrite L40 in B3, B4, B5. rewrite L4 in B4, B5. rewrite LA in B5.
  assert (L476 : length (skipn 476 H) = 4%nat) by (rewrite length_skipn, LH; reflexivity).
  assert (FR : forall a l, garr8 SEGS (mrestrict (w_H W) mem) a l -> h <= a -> a + Z.of_nat (length l) <= h + 480 ->
    (a + Z.of_nat (length l) <= h + 440 \/ h + 444 <= a) -> garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) a l).
  { intros a l Hg Ha1 Ha2 Ha. apply (garr8_frame SEGS _ _ a l Hg). intros x Hx.
    apply (hs_fr_mbyte SEGS E (ss_mem ss_epi) _ _ x HFr); [lia | apply NW; lia]. }
  apply garr8_app. split; [apply FR; [exact B1 | lia | rewrite length_map, LT; lia | rewrite length_map, LT; lia]|]. rewrite length_map, LT.
  apply garr8_app. split; [apply FR; [exact B2 | lia | rewrite length_map, L40; lia | rewrite length_map, L40; lia]|]. rewrite length_map, L40.
  apply garr8_app. split.
  { unfold Mem.le4. rewrite <- Hv. rewrite unsigned_lit_small by lia.
    replace (h + Z.of_nat 400 + Z.of_nat 40) with (h + 440) by lia.
    apply hs_garr8_le; [exact RC | change (8 * Z.of_nat 4) with 32; lia]. }
  rewrite length_map, Mem.length_le4.
  apply garr8_app. split; [apply FR; [exact B4 | lia | rewrite length_map, LA; lia | rewrite length_map, LA; lia]|]. rewrite length_map, LA.
  apply FR; [exact B5 | lia | rewrite length_map, L476; lia | lia]. }
split.
{ unfold hs_hunt. rewrite <- Hv. exact (reac_hunt_step.hs_hunt_ok (hs_table H now) H v (hs_arb h H now) LT LH LA VR TOK LOK). }
exact HPerm.
Qed.
Lemma hs_spill_of : forall E ss (ms : machine_state) (W : world SEGS) r sp h,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) 0 = Some r ->
  YP09.r_base r = Some 2%nat -> In (YP09.mkChunk 16 (CVal 8 (SOff 9 440))) (YP09.r_chunks r) ->
  bv_unsigned (ew E 2) = sp -> ew E 9 = w64 h -> 0 <= h -> h + 440 < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (sp + 16) 8 (h + 440).
Proof.
intros E ss ms W r sp h HS Hn Hb Hc Hsp Hh Hr0 Hr.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS Hn) as (_ & _ & _ & RC).
rewrite Forall_forall in RC. specialize (RC _ Hc). cbn [ms_mem restrict] in RC. rewrite Hb in RC. cbn [base_val] in RC. rewrite Hsp in RC.
apply (val_of_chunk_ok SEGS E _ _ 16 8 (SOff 9 440) (h + 440)) in RC;
  [exact RC | cbn [sv_denot]; rewrite Hh; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia].
Qed.
End w.
Definition hs_postd_stmt : Prop :=
  forall (fq : YK11.FPState) (F0 : bvmap 5 word) (C0 : bv 32) ly S W (regs0 : bvmap 5 word) mem0 md0 ch (h now hb hn : Z)
    (H : list byte) (regs : bvmap 5 word) mem md,
  hs_pre ly S W regs0 mem0 md0 ch h now hb hn H ->
  hs_mid F0 C0 fq regs0 ly S W mem0 md0 h now H regs mem md ->
  getr regs 19 = w64 (h + 384) -> getr regs 23 = w64 (SB_HS + (h + 384) / 8) -> getr regs 24 = w64 (2 ^ 64 - 1 - h) ->
  s32_at H 432 = 0 -> s32_at (hs_arb h H now) 0 <> 2 ->
  desk_geometry_live h (hs_table H now) (sub H 412 6) now = false ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 736))) mem (seg_rom SEGS)) md)
    (hs_post F0 C0 regs0 ly S W mem0 md0 h now H).
Definition hs_loopd_stmt : Prop :=
  forall (k : nat) (i : Z) (fq : YK11.FPState) (F0 : bvmap 5 word) (C0 : bv 32) ly S W (regs0 : bvmap 5 word) mem0 md0 ch
    (h now hb hn : Z) (H : list byte) (regs : bvmap 5 word) mem md,
  Z.of_nat k = n_of (hs_table H now) - i -> 0 <= i < n_of (hs_table H now) ->
  (forall j, 0 <= j < i -> reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now j = false) ->
  hs_pre ly S W regs0 mem0 md0 ch h now hb hn H ->
  hs_mid F0 C0 fq regs0 ly S W mem0 md0 h now H regs mem md ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 120) 8 3 ->
  getr regs 8 = w64 5000000000 -> getr regs 19 = w64 (h + 384) -> getr regs 20 = w64 (h + 412) ->
  getr regs 23 = w64 (SB_HS + (h + 384) / 8) -> getr regs 24 = w64 (2 ^ 64 - 1 - h) ->
  getr regs 25 = w64 (48 * i) -> getr regs 26 = w64 i -> getr regs 27 = w64 432 ->
  s32_at H 432 = 0 -> s32_at (hs_arb h H now) 0 <> 2 ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 516))) mem (seg_rom SEGS)) md)
    (hs_post F0 C0 regs0 ly S W mem0 md0 h now H).
Definition hs_loopb_stmt : Prop :=
  forall (k : nat) (i : Z) (fq : YK11.FPState) (F0 : bvmap 5 word) (C0 : bv 32) ly S W (regs0 : bvmap 5 word) mem0 md0 ch
    (h now hb hn : Z) (H : list byte) (regs : bvmap 5 word) mem md,
  Z.of_nat k = n_of (hs_table H now) - i -> 0 <= i < n_of (hs_table H now) ->
  (forall j, 0 <= j < i -> reac_hunt_step.hs_fb h (hs_table H now) now j = false) ->
  hs_pre ly S W regs0 mem0 md0 ch h now hb hn H ->
  hs_mid F0 C0 fq regs0 ly S W mem0 md0 h now H regs mem md ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 120) 8 3 ->
  getr regs 8 = w64 (48 * i) -> getr regs 19 = w64 (h + 384) -> getr regs 20 = w64 i -> getr regs 21 = w64 432 ->
  getr regs 23 = w64 (SB_HS + (h + 384) / 8) -> getr regs 24 = w64 (2 ^ 64 - 1 - h) ->
  getr regs 25 = w64 2 -> getr regs 26 = w64 1 -> getr regs 27 = w64 5000000000 ->
  s32_at H 432 = 0 -> s32_at (hs_arb h H now) 0 <> 2 ->
  desk_geometry_live h (hs_table H now) (sub H 412 6) now = false ->
  s32_at H 420 = 0 -> ((now - u_at H 424 8) mod 2 ^ 64 <? REAC_HUNT_WINDOW_NS) = false ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 892))) mem (seg_rom SEGS)) md)
    (hs_post F0 C0 regs0 ly S W mem0 md0 h now H).
Section hs_ld.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition ld_ex (h now i : Z) (H : list byte) : list word :=
  map w64 [h + 48 * i; u_at (hs_table H now) (48 * i + 8) 4; u_at (hs_table H now) (48 * i + 20) 4;
    u_at (hs_table H now) (48 * i + 40) 8; u_at (hs_table H now) 384 4].
Definition ld_stack : YP09.region := YP09.mkRegion (Some 2%nat) 0 128 0 0
  [YP09.mkChunk 8 (CVal 8 (SLit 3)); YP09.mkChunk 16 (CVal 8 (SOff 9 440))].
Definition ld_ent : YP09.region := YP09.mkRegion (Some 32%nat) 0 48 0 0
  [YP09.mkChunk 8 (CVal 4 (SOff 33 0)); YP09.mkChunk 20 (CVal 4 (SOff 34 0)); YP09.mkChunk 40 (CVal 8 (SOff 35 0))].
Definition ld_nreg : YP09.region := YP09.mkRegion (Some 19%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 36 0))].
Definition ld_sr : list sv := sr_atoms.
Definition ld_facts : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 5000000000 5000000000 0); (9%nat, mkAF 4096 HS_CEIL 3);
   (19%nat, mkAF 4096 HS_CEIL 3); (22%nat, mkAF SB_HS SB_HS 0);
   (24%nat, mkAF 4096 (2 ^ 64 - 1) 0); (25%nat, mkAF 0 336 0); (26%nat, mkAF 0 7 0);
   (27%nat, mkAF 432 432 0); (32%nat, mkAF 4096 HS_CEIL 3)] []
  [(SAlu ALU_ADD (SOff 9 0) (SOff 25 0), SOff 32 0);
   (SOff 23 0, SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 22 0))].
Definition ld_ss (pc : Z) (sr : list sv) : sstate := mkSS pc sr [ld_stack; ld_ent; ld_nreg] None ld_facts.
Definition ss_ld : sstate := ld_ss (AF_both3_reac_hunt_step + 516) ld_sr.
Definition SH_LD : list shent := [mkSHE 32 0 48; mkSHE 19 0 8].
Definition ld_E (regs : bvmap 5 word) (h now i : Z) (H : list byte) : env := Eimg (Ereg regs (ld_ex h now i H)).
Lemma ld_aview_some : forall (HH : word -> bool) (m : word -> option byte) base (L : list byte) a,
  garr8 SEGS (mrestrict HH m) base (map (fun b : byte => bv_unsigned b) L) ->
  base <= a < base + Z.of_nat (length L) -> aview SEGS HH m a <> None.
Proof.
intros HH m base L a HG Ha.
assert (Hj : (Z.to_nat (a - base) < length L)%nat) by lia.
replace a with (base + Z.of_nat (Z.to_nat (a - base))) by lia. unfold aview.
rewrite (garr8_mbyte SEGS (mrestrict HH m) base _ (Z.to_nat (a - base)) HG ltac:(rewrite length_map; exact Hj)).
discriminate.
Qed.
Lemma ld_swrap_mod : forall u, bv_swrap 32 u mod 2 ^ 32 = u mod 2 ^ 32.
Proof.
intros u. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma ld_s32_vm : forall (m : word -> option byte) a u, val_mem SEGS m a 4 u -> val_mem SEGS m a 4 (bv_swrap 32 u).
Proof.
intros m a u HV k Hk. rewrite (HV k Hk). do 2 f_equal. unfold YO0f.le_byte.
change (8 * Z.of_nat 4) with 32. rewrite ld_swrap_mod. reflexivity.
Qed.
Lemma ld_bytes_eq : forall (HH : word -> bool) (m : word -> option byte) base (L : list byte) a b n,
  garr8 SEGS (mrestrict HH m) base (map (fun x : byte => bv_unsigned x) L) ->
  0 <= a -> 0 <= b -> (Z.to_nat a + n <= length L)%nat -> (Z.to_nat b + n <= length L)%nat ->
  ((forall j, 0 <= j < Z.of_nat n -> aview SEGS HH m (base + a + j) = aview SEGS HH m (base + b + j)) <->
   sub L a n = sub L b n).
Proof.
intros HH m base L a b n HG Ha Hb Hna Hnb.
assert (LA : length (sub L a n) = n) by (unfold sub; rewrite length_firstn, length_skipn; lia).
assert (LB : length (sub L b n) = n) by (unfold sub; rewrite length_firstn, length_skipn; lia).
assert (AV : forall k j, 0 <= k -> 0 <= j -> (Z.to_nat k + Z.to_nat j < length L)%nat ->
  aview SEGS HH m (base + k + j) = Some (bv_unsigned (nth (Z.to_nat k + Z.to_nat j) L (Z_to_bv 8 0)))).
{ intros k j Hk Hj Hkj. replace (base + k + j) with (base + Z.of_nat (Z.to_nat k + Z.to_nat j)) by lia.
  unfold aview. rewrite (garr8_mbyte SEGS (mrestrict HH m) base _ (Z.to_nat k + Z.to_nat j) HG
    ltac:(rewrite length_map; exact Hkj)). cbn [option_map]. f_equal.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia). rewrite map_nth.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
- intros HE. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [lia|].
  intros j Hj. rewrite LA in Hj. rewrite !hs_nth_sub by lia.
  pose proof (HE (Z.of_nat j) ltac:(lia)) as Hq. rewrite !AV in Hq by lia. rewrite !Nat2Z.id in Hq.
  injection Hq as Hq. apply bv_eq. exact Hq.
- intros HE j Hj. rewrite !AV by lia. do 2 f_equal.
  rewrite <- (hs_nth_sub L a n (Z.to_nat j) Ha ltac:(lia)), <- (hs_nth_sub L b n (Z.to_nat j) Hb ltac:(lia)).
  rewrite HE. reflexivity.
Qed.
Definition ld_keep_p (W : world SEGS) (sp0 : Z) (mem m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ sp0 - 128 <= a) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a.
Lemma ld_keep_hs : forall W sp0 mem m', ld_keep_p W sp0 mem m' -> hs_keep_p W sp0 mem m'.
Proof. intros W sp0 mem m' HK a Ha Hb. apply HK; [exact Ha | destruct Hb; [left | right]; lia]. Qed.
Lemma ld_keep_fr : forall W sp0 (mem m0 m1 : word -> option byte) E0 rs,
  ld_keep_p W sp0 mem m0 -> frame_of E0 rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) ->
  (forall a, (a < alloc_ceiling \/ sp0 - 128 <= a) -> ~ in_wrange E0 rs a) -> ld_keep_p W sp0 mem m1.
Proof.
intros W sp0 mem m0 m1 E0 rs HK HF HN a Ha Hb.
rewrite (hs_fr_aview E0 rs (w_H W) m0 m1 a HF Ha (HN a Hb)). exact (HK a Ha Hb).
Qed.
Lemma ld_keep_call : forall W sp0 (mem m0 m1 : word -> option byte) lo hi,
  ld_keep_p W sp0 mem m0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a) ->
  alloc_ceiling <= lo -> hi <= sp0 - 128 -> ld_keep_p W sp0 mem m1.
Proof.
intros W sp0 mem m0 m1 lo hi HK HC Hlo Hhi a Ha Hb.
rewrite (HC a Ha ltac:(destruct Hb; lia)). exact (HK a Ha Hb).
Qed.
Ltac ld_ewstrip := repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia].
Lemma ld_aview_of_kept : forall (HH : word -> bool) (m m' : word -> option byte) lo hi x,
  (forall y : word, ~ (lo <= bv_unsigned y < hi) -> m' y = m y) -> ~ (lo <= x mod 2 ^ 64 < hi) ->
  aview SEGS HH m' x = aview SEGS HH m x.
Proof.
intros HH m m' lo hi x K Hx. unfold aview, mbyte, mrestrict. rewrite (K (Z_to_bv 64 x)); [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact Hx.
Qed.
Ltac ld_keep Usp :=
  lazymatch goal with KEEP : ld_keep_p _ _ _ ?m0, HFr : frame_of ?E0 ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let K := fresh "KEEP" in pose proof (ld_keep_fr _ _ _ _ _ E0 rs KEEP HFr ltac:(hs_nw Usp)) as K;
    clear KEEP; rename K into KEEP end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Lemma ld_build : forall (fq : YK11.FPState) (F0 : bvmap 5 word) (C0 : bv 32) ly S W (regs0 : bvmap 5 word) mem0 md0 ch
  (h now hb hn i pc : Z) (H : list byte) (sr : list sv) (regs : bvmap 5 word) mem md,
  hs_pre ly S W regs0 mem0 md0 ch h now hb hn H ->
  hs_inv F0 C0 fq regs0 ly S W mem0 md0 h now H mem md ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 120) 8 3 ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 112) 8 (h + 440) ->
  0 <= i < n_of (hs_table H now) ->
  getr regs 2 = w64 (spZ regs0 - 128) -> getr regs 8 = w64 5000000000 -> getr regs 9 = w64 h ->
  getr regs 19 = w64 (h + 384) -> getr regs 22 = w64 SB_HS -> getr regs 23 = w64 (SB_HS + (h + 384) / 8) ->
  getr regs 24 = w64 (2 ^ 64 - 1 - h) -> getr regs 25 = w64 (48 * i) -> getr regs 26 = w64 i ->
  getr regs 27 = w64 432 -> regs_ok (ld_E regs h now i H) sr regs ->
  st_ok_pi SEGS VAL (ld_E regs h now i H) (ld_ss pc sr)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS Bx_HS SH_LD (ld_E regs h now i H) (mrestrict (w_H W) mem).
Proof.
intros fq F0 C0 ly S W regs0 mem0 md0 ch h now hb hn i pc H sr regs mem md HPRE HINV HSP8 HSP16 Hi
  R2 R8 R9 R19 R22 R23 R24 R25 R26 R27 HRO.
destruct HPRE as (HPRE & HROD & Hnow & Hh0 & Hh8 & Hin & Hhb & Hhe & HOK).
destruct HINV as ((lyc & Sc & HJ & HPerm) & HMOD & HBLK & HSAV & HRATES & HFK & HCSR).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (Hinc : In (hb, hn) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
destruct (al_blocks _ _ LAWS lyc Sc W mem md hb hn HAR Hinc) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & Hbpres & _).
destruct HMOD as (LT & TOK & LA). destruct HOK as (LH & _ & LOK & V0R).
pose proof TOK as (T1 & _). unfold tbl_T1 in T1.
assert (WS : REAC_HUNT_STEP_STK = 8464) by reflexivity.
pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as Rsp0. change (bv_modulus 64) with (2 ^ 64) in Rsp0.
fold (spZ regs0) in Rsp0.
assert (LB : length (hs_blk h H now) = 480%nat).
{ unfold hs_blk. rewrite !length_app, LT, LA, length_skipn.
  rewrite !disco_table.length_sub by (rewrite ?LH; lia). rewrite LH. reflexivity. }
assert (UR : forall (L : list byte) k n, 0 <= k -> (Z.to_nat k + n <= length L)%nat ->
  0 <= u_at L k n < 2 ^ (8 * Z.of_nat n)).
{ intros L k n Hk Hn. unfold u_at. pose proof (disco_table.ble_range (sub L k n)) as Rb.
  rewrite disco_table.length_sub in Rb by lia. exact Rb. }
assert (VB : forall k n, 0 <= k -> (Z.to_nat k + n <= 480)%nat ->
  val_mem SEGS (mrestrict (w_H W) mem) (h + k) n (u_at (hs_blk h H now) k n))
  by (intros k n Hk Hn; apply hs_vm; [exact HBLK | exact Hk | rewrite LB; exact Hn]).
assert (Hi7 : 0 <= i <= 7) by lia.
set (E := ld_E regs h now i H).
assert (HEI : img_env VAL A_LIM E) by (unfold E, ld_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ld_ex h now i H)) n)
  by (intros n Hn; unfold E, ld_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E19 : ew E 19 = getr regs 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
assert (E22 : ew E 22 = getr regs 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)).
assert (E23 : ew E 23 = getr regs 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 23 23%bv eq_refl)).
assert (E24 : ew E 24 = getr regs 24) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)).
assert (E25 : ew E 25 = getr regs 25) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 25 25%bv eq_refl)).
assert (E26 : ew E 26 = getr regs 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr regs 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (ld_ex h now i H) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth ld_ex map] in E32, E33, E34, E35, E36.
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 128)
  by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (Uh : bv_unsigned (ew E 9) = h) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; lia).
assert (Un : bv_unsigned (ew E 19) = h + 384) by (rewrite E19, R19; unfold w64; apply unsigned_lit_small; lia).
assert (Ue : bv_unsigned (ew E 32) = h + 48 * i) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = 48 * i)
  by (rewrite E25, R25; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SB_HS)
  by (rewrite E22, R22; unfold w64; apply unsigned_lit_small; unfold SB_HS; lia).
assert (HD : 0 <= (h + 384) / 8 <= HS_CEIL)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; unfold HS_CEIL in *; lia]).
assert (U23 : bv_unsigned (ew E 23) = SB_HS + (h + 384) / 8)
  by (rewrite E23, R23; unfold w64; apply unsigned_lit_small; unfold SB_HS, HS_CEIL in *; lia).
assert (TSUB : forall k n, 0 <= k -> (Z.to_nat k + n <= 400)%nat ->
  u_at (hs_blk h H now) k n = u_at (hs_table H now) k n)
  by (intros k n Hk Hn; unfold u_at; f_equal; apply hs_blk_T; assumption).
split.
- rewrite YA0o.restrict_mkst_fx. unfold ld_ss. apply pa_entry_st_ok_full.
  + exact HRO.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * unfold region_ok, ld_stack.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ _ 8 8 (SLit 3) 3);
         [cbn [sv_denot]; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia |].
         replace (spZ regs0 - 128 + 8) with (spZ regs0 - 120) by lia. exact HSP8.
      -- apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 9 440) (h + 440));
         [cbn [sv_denot]; rewrite E9, R9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
         | change (8 * Z.of_N 8) with 64; lia | lia |].
         replace (spZ regs0 - 128 + 16) with (spZ regs0 - 112) by lia. exact HSP16.
    * unfold region_ok, ld_ent.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Ue.
      split; [lia|]. split; [unfold HS_CEIL in *; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ _ 8 4 (SOff 33 0) (u_at (hs_table H now) (48 * i + 8) 4));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | apply UR; rewrite ?LT; lia | lia |].
         rewrite <- (TSUB (48 * i + 8) 4%nat ltac:(lia) ltac:(lia)).
         replace (h + 48 * i + 8) with (h + (48 * i + 8)) by lia. apply VB; lia.
      -- apply (chunk_ok_val SEGS E _ _ 20 4 (SOff 34 0) (u_at (hs_table H now) (48 * i + 20) 4));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | apply UR; rewrite ?LT; lia | lia |].
         rewrite <- (TSUB (48 * i + 20) 4%nat ltac:(lia) ltac:(lia)).
         replace (h + 48 * i + 20) with (h + (48 * i + 20)) by lia. apply VB; lia.
      -- apply (chunk_ok_val SEGS E _ _ 40 8 (SOff 35 0) (u_at (hs_table H now) (48 * i + 40) 8));
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | apply UR; rewrite ?LT; lia | lia |].
         rewrite <- (TSUB (48 * i + 40) 8%nat ltac:(lia) ltac:(lia)).
         replace (h + 48 * i + 40) with (h + (48 * i + 40)) by lia. apply VB; lia.
    * unfold region_ok, ld_nreg.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Un.
      split; [lia|]. split; [unfold HS_CEIL in *; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 36 0) (u_at (hs_table H now) 384 4));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | apply UR; rewrite ?LT; lia | lia |].
      rewrite <- (TSUB 384 4%nat ltac:(lia) ltac:(lia)). rewrite Z.add_0_r. apply VB; lia.
  + apply pairwise_disjoint_of_extents. unfold extent_of_region, ld_stack, ld_ent, ld_nreg.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Ue, Un.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold HS_CEIL in *. repeat split; lia.
  + split.
    * cbn [f_atoms ld_facts atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, Uh, Un, Ue, U22, U25, E8, R8, E24, R24, E26, R26, E27, R27.
      unfold w64. rewrite !unsigned_lit_small by (unfold HS_CEIL in *; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      unfold SB_HS, HS_CEIL in *. repeat split; try (exact I || lia).
      all: Z.div_mod_to_equations; lia.
    * split; [exact I|]. cbn [f_alias ld_facts alias_ok]. split; [|split; [|exact I]].
      -- apply U_inj. rewrite U_SAlu, !U_SOff. cbn [zalu_raw]. rewrite Uh, U25, Ue.
         unfold zcanon, M64. rewrite !Z.add_0_r, Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
      -- apply U_inj. rewrite U_SOff, U_SAlu, U_SAlu, !U_SOff, U_SLit. cbn [zalu_raw].
         rewrite U23, Un, U22. change (zcanon 3) with 3. change (Z.land 3 63) with 3.
         rewrite !Z.add_0_r. unfold zcanon, M64.
         rewrite (Z.mod_small (h + 384)) by (unfold HS_CEIL in *; lia).
         rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
         rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. f_equal. lia.
- unfold sh_ok, SH_LD. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E Bx_HS 32 hb (req_size hn) (h + 48 * i) 0 48).
    * exact (range_addressable_of_block SEGS B LAWS lyc Sc W mem md hb hn hb (req_size hn) HAR Hinc
        ltac:(lia) ltac:(lia)).
    * unfold Bx_HS. rewrite (U_atom E 22 SB_HS) by (first [rewrite E22, R22; reflexivity | unfold SB_HS; lia]).
      reflexivity.
    * rewrite (U_atom E 32 (h + 48 * i)) by (first [rewrite E32; reflexivity | unfold HS_CEIL in *; lia]).
      reflexivity.
    * lia.
    * lia.
    * intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. unfold HS_CEIL in *. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E Bx_HS 19 hb (req_size hn) (h + 384) 0 8).
    * exact (range_addressable_of_block SEGS B LAWS lyc Sc W mem md hb hn hb (req_size hn) HAR Hinc
        ltac:(lia) ltac:(lia)).
    * unfold Bx_HS. rewrite (U_atom E 22 SB_HS) by (first [rewrite E22, R22; reflexivity | unfold SB_HS; lia]).
      reflexivity.
    * rewrite (U_atom E 19 (h + 384)) by (first [rewrite E19, R19; reflexivity | unfold HS_CEIL in *; lia]).
      reflexivity.
    * lia.
    * lia.
    * intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. unfold HS_CEIL in *. lia.
Qed.
Lemma ld_region_kept : forall E (HH : word -> bool) (m m2 : word -> option byte) n b lo hi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS HH m2 a = aview SEGS HH m a) ->
  region_kept SEGS E (mrestrict HH m) (mrestrict HH m2) (YP09.mkRegion (Some n) lo hi 0 0 cs).
Proof.
intros E HH m m2 n b lo hi cs Hn Hav.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [|lia].
pose proof (Hav a Ha) as Hq. unfold aview in Hq.
destruct (mbyte SEGS (mrestrict HH m2) a) as [b2|] eqn:Q2; destruct (mbyte SEGS (mrestrict HH m) a) as [b1|] eqn:Q1;
cbn [option_map] in Hq; try discriminate; [|reflexivity].
injection Hq as Hq. f_equal. apply bv_eq. exact Hq.
Qed.
Lemma ld_shok : forall (E' : env) (W : world SEGS) (m' : word -> option byte) lyc Sc md' (hb hn h i : Z),
  AR SEGS B lyc Sc W m' md' -> In (hb, hn) (ablocks B lyc Sc) ->
  hb <= h -> h + 480 <= hb + req_size hn -> 0 <= i <= 7 ->
  bv_unsigned (ew E' 22) = SB_HS -> bv_unsigned (ew E' 32) = h + 48 * i -> bv_unsigned (ew E' 19) = h + 384 ->
  sh_ok SEGS Bx_HS SH_LD E' (mrestrict (w_H W) m').
Proof.
intros E' W m' lyc Sc md' hb hn h i HAR Hinc Hhb Hhe Hi U22 Ue Un.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W m' md' hb hn HAR Hinc) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & Hbpres & _).
assert (R64 : 0 <= h /\ h + 480 <= 140737488355327).
{ unfold in_app, kLowShadowBeg, kHighMemBeg in Hbh_ia. lia. }
assert (W22 : ew E' 22 = Z_to_bv 64 SB_HS).
{ apply bv_eq. rewrite U22. symmetry. apply unsigned_lit_small.
  unfold SB_HS. change (2 ^ 64) with 18446744073709551616. lia. }
assert (W32 : ew E' 32 = Z_to_bv 64 (h + 48 * i)).
{ apply bv_eq. rewrite Ue. symmetry. apply unsigned_lit_small.
  change (2 ^ 64) with 18446744073709551616. lia. }
assert (W19 : ew E' 19 = Z_to_bv 64 (h + 384)).
{ apply bv_eq. rewrite Un. symmetry. apply unsigned_lit_small.
  change (2 ^ 64) with 18446744073709551616. lia. }
unfold sh_ok, SH_LD. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS (w_H W) m' E' Bx_HS 32 hb (req_size hn) (h + 48 * i) 0 48).
  + exact (range_addressable_of_block SEGS B LAWS lyc Sc W m' md' hb hn hb (req_size hn) HAR Hinc
      ltac:(lia) ltac:(lia)).
  + unfold Bx_HS.
    rewrite (U_atom E' 22 SB_HS W22 ltac:(unfold SB_HS; change (2 ^ 64) with 18446744073709551616; lia)).
    reflexivity.
  + rewrite (U_atom E' 32 (h + 48 * i) W32 ltac:(change (2 ^ 64) with 18446744073709551616; lia)). reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
- apply (shent_ok_of_range SEGS (w_H W) m' E' Bx_HS 19 hb (req_size hn) (h + 384) 0 8).
  + exact (range_addressable_of_block SEGS B LAWS lyc Sc W m' md' hb hn hb (req_size hn) HAR Hinc
      ltac:(lia) ltac:(lia)).
  + unfold Bx_HS.
    rewrite (U_atom E' 22 SB_HS W22 ltac:(unfold SB_HS; change (2 ^ 64) with 18446744073709551616; lia)).
    reflexivity.
  + rewrite (U_atom E' 19 (h + 384) W19 ltac:(change (2 ^ 64) with 18446744073709551616; lia)). reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma ld_breq0 : forall E k (v : word), ew E k = v ->
  branch_taken BC_EQ (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = (bv_unsigned v =? 0).
Proof.
intros E k v Hk. rewrite branch_eq_U, U_SOff, U_SLit, Hk, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 v) as Hv. change (bv_modulus 64) with (2 ^ 64) in Hv.
rewrite (zcanon_id (bv_unsigned v)) by (unfold M64; lia). change (zcanon 0) with 0. reflexivity.
Qed.
Lemma ld_w64_0 : forall v : word, bv_unsigned v = 0 <-> v = w64 0.
Proof.
intros v. pose proof (bv_unsigned_in_range 64 v) as Hv. change (bv_modulus 64) with (2 ^ 64) in Hv.
split; intros Hq.
- apply bv_eq. rewrite Hq. unfold w64. symmetry. apply unsigned_lit_small. lia.
- rewrite Hq. unfold w64. apply unsigned_lit_small. lia.
Qed.
Lemma ld_breq : forall E k (x c : Z), ew E k = Z_to_bv 64 x -> 0 <= x <= 4294967295 -> 0 <= c <= 4294967295 ->
  branch_taken BC_EQ (sv_denot E (SOff k 0)) (sv_denot E (SLit c)) = (x =? c).
Proof.
intros E k x c Hk Hx Hc.
rewrite branch_eq_U, U_SLit, (U_atom E k x Hk ltac:(change (2 ^ 64) with 18446744073709551616; lia)).
rewrite (zcanon_id c) by (unfold M64; change (2 ^ 64) with 18446744073709551616; lia). reflexivity.
Qed.
Lemma ld_brlt : forall E k1 k2 (x u : Z), ew E k1 = Z_to_bv 64 x -> ew E k2 = Z_to_bv 64 u ->
  0 <= x <= 2147483647 -> 0 <= u <= 4294967295 ->
  branch_taken BC_LT (sv_denot E (SOff k1 1)) (sv_denot E (SExt true 32 (SOff k2 0))) = (x + 1 <? bv_swrap 32 u).
Proof.
intros E k1 k2 x u Hk1 Hk2 Hx Hu.
assert (Hu32 : 0 <= u < 2 ^ 32) by (change (2 ^ 32) with 4294967296; lia).
pose proof (hs_sw32 u) as Hs. change (2 ^ 31) with 2147483648 in Hs.
cbn [branch_taken]. unfold bv_lts.
change (bv_signed (sv_denot E (SOff k1 1))) with (Sg E (SOff k1 1)).
change (bv_signed (sv_denot E (SExt true 32 (SOff k2 0)))) with (Sg E (SExt true 32 (SOff k2 0))).
rewrite !S_of_U, U_SOff, (hs_U32 E k2 u Hk2 Hu32), Hk1.
rewrite (unsigned_lit_small x) by (change (2 ^ 64) with 18446744073709551616; lia).
rewrite (hs_sw64_zc (bv_swrap 32 u)) by (change (2 ^ 63) with 9223372036854775808; lia).
rewrite (hs_sw64_zc (x + 1)) by (change (2 ^ 63) with 9223372036854775808; lia).
reflexivity.
Qed.

Lemma ld_sub_u : forall E k1 k2 (x y : Z), ew E k1 = Z_to_bv 64 x -> ew E k2 = Z_to_bv 64 y ->
  0 <= x <= 18446744073709551615 -> 0 <= y <= x ->
  U E (SAlu ALU_ADD (SOff k1 0) (SMd M_MUL (SOff k2 0) (SLit (-1)))) = x - y.
Proof.
intros E k1 k2 x y Hk1 Hk2 Hx Hy.
rewrite U_SAlu, U_SMd, !U_SOff, U_SLit. cbn [zalu_raw zmd_raw].
rewrite Hk1, Hk2, !unsigned_lit_small by (change (2 ^ 64) with 18446744073709551616; lia).
rewrite !Z.add_0_r. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
replace ((-1) mod 18446744073709551616) with 18446744073709551615 by reflexivity.
rewrite (Z.mod_small x) by lia. rewrite (Z.mod_small y) by lia.
rewrite Zplus_mod_idemp_r.
replace (x + y * 18446744073709551615) with ((x - y) + y * 18446744073709551616) by lia.
rewrite (Z.mod_add (x - y) y 18446744073709551616) by lia. apply Z.mod_small. lia.
Qed.
Definition ld_next (F0 : bvmap 5 word) (C0 : bv 32) ly S (W : world SEGS) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (h now i : Z) (H : list byte) : Prop :=
  forall (fq' : YK11.FPState) (regs' : bvmap 5 word) mem' md',
  i + 1 < n_of (hs_table H now) ->
  (forall j, 0 <= j < i + 1 -> reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now j = false) ->
  hs_mid F0 C0 fq' regs0 ly S W mem0 md0 h now H regs' mem' md' ->
  val_mem SEGS (mrestrict (w_H W) mem') (spZ regs0 - 120) 8 3 ->
  getr regs' 8 = w64 5000000000 -> getr regs' 19 = w64 (h + 384) -> getr regs' 20 = w64 (h + 412) ->
  getr regs' 23 = w64 (SB_HS + (h + 384) / 8) -> getr regs' 24 = w64 (2 ^ 64 - 1 - h) ->
  getr regs' 25 = w64 (48 * (i + 1)) -> getr regs' 26 = w64 (i + 1) -> getr regs' 27 = w64 432 ->
  SRr SEGS W (mkCfg (mkst (fx := fq') regs' (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 516))) mem' (seg_rom SEGS)) md')
    (hs_post F0 C0 regs0 ly S W mem0 md0 h now H).
Lemma ld_tail : hs_postd_stmt ->
  forall (p : Z) (fq : YK11.FPState) (F0 : bvmap 5 word) (C0 : bv 32) ly S W (regs0 : bvmap 5 word) mem0 md0 ch
    (h now hb hn i : Z) (H : list byte) (regs : bvmap 5 word) mem md,
  ld_next F0 C0 ly S W regs0 mem0 md0 h now i H ->
  (p = 664 \/ p = 672) ->
  0 <= i < n_of (hs_table H now) ->
  (forall j, 0 <= j < i -> reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now j = false) ->
  reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now i = false ->
  hs_pre ly S W regs0 mem0 md0 ch h now hb hn H ->
  hs_mid F0 C0 fq regs0 ly S W mem0 md0 h now H regs mem md ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 120) 8 3 ->
  getr regs 8 = w64 5000000000 -> getr regs 19 = w64 (h + 384) -> getr regs 20 = w64 (h + 412) ->
  getr regs 23 = w64 (SB_HS + (h + 384) / 8) -> getr regs 24 = w64 (2 ^ 64 - 1 - h) ->
  getr regs 25 = w64 (48 * i) -> getr regs 26 = w64 i -> getr regs 27 = w64 432 ->
  s32_at H 432 = 0 -> s32_at (hs_arb h H now) 0 <> 2 ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + p))) mem (seg_rom SEGS)) md)
    (hs_post F0 C0 regs0 ly S W mem0 md0 h now H).
Proof.
intros POSTD p fq F0 C0 ly S W regs0 mem0 md0 ch h now hb hn i H regs mem md NEXT Hp Hi NW FDi HPRE HMID HSP8
  R8 R19 R20 R23 R24 R25 R26 R27 HP0 HSA2.
pose proof HPRE as HPRE'. pose proof HMID as HMID'.
destruct HMID as (HINV & HSPILL & R2 & R3 & R4 & R9 & R18 & R22).
pose proof HINV as HINV'.
destruct HINV as ((lyc & Sc & HJ0 & HPerm) & HMOD & HBLK & HSAV & HRATES & HFK & HCSR).
pose proof HPRE as (HPREa & HROD & Hnow & Hh0 & Hh8 & Hin & Hhb & Hhe & HOK).
pose proof HPREa as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HMOD as (LT & TOK & LA). pose proof TOK as (T1 & _). unfold tbl_T1 in T1.
pose proof HOK as (LH & _ & LOK & V0R).
pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as Rsp0. change (bv_modulus 64) with (2 ^ 64) in Rsp0.
fold (spZ regs0) in Rsp0.
pose proof (paj_run (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := ld_E regs h now i H) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ld_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ld_ex h now i H)) n)
  by (intros n Hn; unfold E, ld_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E25 : ew E 25 = getr regs 25) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 25 25%bv eq_refl)).
assert (E26 : ew E 26 = getr regs 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (ld_ex h now i H) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 4%nat ltac:(lia)) as E36. cbn [Nat.add nth ld_ex map] in E36.
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 128)
  by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (ld_ex h now i H)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | unfold E, ld_E; reflexivity]).
assert (HRO : regs_ok E sr_atoms regs) by (unfold E, ld_E; apply regs_ok_Eimg_Ereg).
assert (KEEP : ld_keep_p W (spZ regs0) mem mem) by (intros a _ _; reflexivity).
assert (UN32 : 0 <= u_at (hs_table H now) 384 4 <= 4294967295).
{ unfold u_at. pose proof (disco_table.ble_range (sub (hs_table H now) 384 4)) as Rb.
  rewrite disco_table.length_sub in Rb by (rewrite ?LT; lia).
  change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in Rb. lia. }
assert (NEQ : bv_swrap 32 (u_at (hs_table H now) 384 4) = n_of (hs_table H now)) by reflexivity.
assert (MID : forall (fq' : YK11.FPState) (E' : env) (ss' : sstate) (ms' : machine_state) md',
  st_ok_pi (fx := fq') SEGS VAL E' ss' (restrict (w_H W) ms') ->
  env_agree 32 (Ereg regs (ld_ex h now i H)) E' ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 27]%bv = true ->
  ld_keep_p W (spZ regs0) mem (ms_mem ms') ->
  freg_kept F0 (@YK11.fp_regs fq') -> hs_fc C0 fq' ->
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc Sc W (ms_mem ms') md' 0 ->
  hs_mid F0 C0 fq' regs0 ly S W mem0 md0 h now H (ms_regs ms') (ms_mem ms') md' /\
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms')) (spZ regs0 - 120) 8 3 /\
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 27]%bv -> getr (ms_regs ms') r = getr regs r)).
{ intros fq' E' ss' ms' md' HS' HAE' Hfb HK HFK' HCSR' HJ'.
  pose proof (regs_kept_of_st_ok_pi E' ss' (restrict (w_H W) ms') regs (ld_ex h now i H)
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 27]%bv HS' HAE' Hfb) as KR.
  cbn [ms_regs restrict] in KR.
  assert (HSP8' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms')) (spZ regs0 - 120) 8 3).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms')); [|exact HSP8].
    intros k Hk. apply HK; lia. }
  assert (HSP16' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms')) (spZ regs0 - 112) 8 (h + 440)).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms')); [|exact HSPILL].
    intros k Hk. apply HK; lia. }
  split; [|split; [exact HSP8' | exact KR]].
  split.
  { apply (hs_inv_kept F0 C0 fq' regs0 ly S W mem0 md0 ch h now hb hn H mem md (ms_mem ms') md' HPRE'
      ltac:(split; [exists lyc, Sc; split; [exact HJ0 | exact HPerm]|];
            split; [exact HMOD|]; split; [exact HBLK|]; split; [exact HSAV|]; split; [exact HRATES|];
            split; [exact HFK' | exact HCSR'])
      ltac:(apply (ld_keep_hs W (spZ regs0) mem (ms_mem ms')); exact HK));
    exists lyc, Sc; split; [exact HJ' | exact HPerm]. }
  split; [exact HSP16'|].
  rewrite !(KR 2%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 3%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 4%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 9%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 18%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 22%bv ltac:(repeat (first [left; reflexivity | right]))).
  repeat split; assumption. }
assert (NWS : forall j, 0 <= j < i + 1 -> reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now j = false).
{ intros j Hj. destruct (Z.eq_dec j i) as [->|Hne]; [exact FDi | apply NW; lia]. }
assert (BACK : forall (fq' : YK11.FPState) (E' : env) (ss' : sstate) (ms' : machine_state) md',
  st_ok_pi (fx := fq') SEGS VAL E' ss' (restrict (w_H W) ms') -> ss_resv ss' = None ->
  ss_pc ss' = AF_both3_reac_hunt_step + 516 ->
  env_agree 32 (Ereg regs (ld_ex h now i H)) E' ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 27]%bv = true ->
  getr (ms_regs ms') 25 = w64 (48 * (i + 1)) -> getr (ms_regs ms') 26 = w64 (i + 1) ->
  ld_keep_p W (spZ regs0) mem (ms_mem ms') ->
  freg_kept F0 (@YK11.fp_regs fq') -> hs_fc C0 fq' ->
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc Sc W (ms_mem ms') md' 0 ->
  i + 1 < n_of (hs_table H now) ->
  SRr SEGS W (mkCfg ms' md') (hs_post F0 C0 regs0 ly S W mem0 md0 h now H)).
{ intros fq' E' ss' ms' md' HS' Hrv Hpc HAE' Hfb Q25 Q26 HK HFK' HCSR' HJ' Hlt.
  destruct (MID fq' E' ss' ms' md' HS' HAE' Hfb HK HFK' HCSR' HJ') as (HM & HS8 & KR).
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS' Hrv), Hpc.
  apply (NEXT fq' (ms_regs ms') (ms_mem ms') md' Hlt NWS HM HS8);
  [ rewrite (KR 8%bv ltac:(repeat (first [left; reflexivity | right]))); exact R8
  | rewrite (KR 19%bv ltac:(repeat (first [left; reflexivity | right]))); exact R19
  | rewrite (KR 20%bv ltac:(repeat (first [left; reflexivity | right]))); exact R20
  | rewrite (KR 23%bv ltac:(repeat (first [left; reflexivity | right]))); exact R23
  | rewrite (KR 24%bv ltac:(repeat (first [left; reflexivity | right]))); exact R24
  | exact Q25 | exact Q26
  | rewrite (KR 27%bv ltac:(repeat (first [left; reflexivity | right]))); exact R27 ]. }
assert (EXIT : forall (fq' : YK11.FPState) (E' : env) (ss' : sstate) (ms' : machine_state) md',
  st_ok_pi (fx := fq') SEGS VAL E' ss' (restrict (w_H W) ms') -> ss_resv ss' = None ->
  ss_pc ss' = AF_both3_reac_hunt_step + 736 ->
  env_agree 32 (Ereg regs (ld_ex h now i H)) E' ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 27]%bv = true ->
  ld_keep_p W (spZ regs0) mem (ms_mem ms') ->
  freg_kept F0 (@YK11.fp_regs fq') -> hs_fc C0 fq' ->
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc Sc W (ms_mem ms') md' 0 ->
  n_of (hs_table H now) <= i + 1 ->
  SRr SEGS W (mkCfg ms' md') (hs_post F0 C0 regs0 ly S W mem0 md0 h now H)).
{ intros fq' E' ss' ms' md' HS' Hrv Hpc HAE' Hfb HK HFK' HCSR' HJ' Hge.
  destruct (MID fq' E' ss' ms' md' HS' HAE' Hfb HK HFK' HCSR' HJ') as (HM & HS8 & KR).
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS' Hrv), Hpc.
  apply (POSTD fq' F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H (ms_regs ms') (ms_mem ms') md' HPRE' HM);
  [ rewrite (KR 19%bv ltac:(repeat (first [left; reflexivity | right]))); exact R19
  | rewrite (KR 23%bv ltac:(repeat (first [left; reflexivity | right]))); exact R23
  | rewrite (KR 24%bv ltac:(repeat (first [left; reflexivity | right]))); exact R24
  | exact HP0 | exact HSA2
  | apply reac_hunt_step.hs_dgl_false; intros j Hj; apply NWS; lia ]. }
destruct Hp as [-> | ->].
- destruct (ld_build fq F0 C0 ly S W regs0 mem0 md0 ch h now hb hn i (AF_both3_reac_hunt_step + 664) H sr_atoms
    regs mem md HPRE' HINV' HSP8 HSPILL Hi R2 R8 R9 R19 R22 R23 R24 R25 R26 R27 HRO) as [HS SHOK].
  fold E in HS, SHOK.
  paj_run_tok RUN HS HJ0 SHOK Bspan_HS; [hs_awr Usp|]. ld_keep Usp.
  psrr_branch_tok RUN BR HS SHOK Bspan_HS.
  + lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      rewrite (ld_brlt Ex 26 36 i (u_at (hs_table H now) 384 4)
        ltac:(rewrite ?ew_ewset_other by lia; rewrite E26, R26; reflexivity)
        ltac:(rewrite ?ew_ewset_other by lia; rewrite E36; reflexivity)
        ltac:(lia) UN32) in Hc end.
    rewrite NEQ in Hc. apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ0 SHOK Bspan_HS (AF_both3_reac_hunt_step + 516); [hs_awr Usp|]. ld_keep Usp.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      prreg HS (25%bv : bv 5) Q25; prreg HS (26%bv : bv 5) Q26 end.
    eapply BACK;
    [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity
    | split; [intros n Hn; rewrite ?ew_ewset_other by lia; apply EL; unfold A_TEXT; lia | reflexivity]
    | vm_compute; reflexivity
    | rewrite Q25; rewrite ?ew_ewset_other by lia; rewrite E25, R25; unfold w64;
      rewrite (unsigned_lit_small (48 * i)) by (change (2 ^ 64) with 18446744073709551616; lia);
      f_equal; lia
    | rewrite Q26; rewrite ?ew_ewset_other by lia; rewrite E26, R26; unfold w64;
      rewrite (unsigned_lit_small i) by (change (2 ^ 64) with 18446744073709551616; lia);
      f_equal; lia
    | exact KEEP | exact HFK | exact HCSR | exact HJ0 | lia ].
  + lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      rewrite (ld_brlt Ex 26 36 i (u_at (hs_table H now) 384 4)
        ltac:(rewrite ?ew_ewset_other by lia; rewrite E26, R26; reflexivity)
        ltac:(rewrite ?ew_ewset_other by lia; rewrite E36; reflexivity)
        ltac:(lia) UN32) in Hc end.
    rewrite NEQ in Hc. apply Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ0 SHOK Bspan_HS (AF_both3_reac_hunt_step + 736); [hs_awr Usp|]. ld_keep Usp.
    eapply EXIT;
    [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity
    | split; [intros n Hn; rewrite ?ew_ewset_other by lia; apply EL; unfold A_TEXT; lia | reflexivity]
    | vm_compute; reflexivity | exact KEEP | exact HFK | exact HCSR | exact HJ0 | lia ].
- destruct (ld_build fq F0 C0 ly S W regs0 mem0 md0 ch h now hb hn i (AF_both3_reac_hunt_step + 672) H sr_atoms
    regs mem md HPRE' HINV' HSP8 HSPILL Hi R2 R8 R9 R19 R22 R23 R24 R25 R26 R27 HRO) as [HS SHOK].
  fold E in HS, SHOK.
  paj_run_tok RUN HS HJ0 SHOK Bspan_HS; [hs_awr Usp|]. ld_keep Usp.
  psrr_branch_tok RUN BR HS SHOK Bspan_HS.
  + lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      rewrite (ld_brlt Ex 26 36 i (u_at (hs_table H now) 384 4)
        ltac:(rewrite ?ew_ewset_other by lia; rewrite E26, R26; reflexivity)
        ltac:(rewrite ?ew_ewset_other by lia; rewrite E36; reflexivity)
        ltac:(lia) UN32) in Hc end.
    rewrite NEQ in Hc. apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ0 SHOK Bspan_HS (AF_both3_reac_hunt_step + 516); [hs_awr Usp|]. ld_keep Usp.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      prreg HS (25%bv : bv 5) Q25; prreg HS (26%bv : bv 5) Q26 end.
    eapply BACK;
    [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity
    | split; [intros n Hn; rewrite ?ew_ewset_other by lia; apply EL; unfold A_TEXT; lia | reflexivity]
    | vm_compute; reflexivity
    | rewrite Q25; rewrite ?ew_ewset_other by lia; rewrite E25, R25; unfold w64;
      rewrite (unsigned_lit_small (48 * i)) by (change (2 ^ 64) with 18446744073709551616; lia);
      f_equal; lia
    | rewrite Q26; rewrite ?ew_ewset_other by lia; rewrite E26, R26; unfold w64;
      rewrite (unsigned_lit_small i) by (change (2 ^ 64) with 18446744073709551616; lia);
      f_equal; lia
    | exact KEEP | exact HFK | exact HCSR | exact HJ0 | lia ].
  + lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      rewrite (ld_brlt Ex 26 36 i (u_at (hs_table H now) 384 4)
        ltac:(rewrite ?ew_ewset_other by lia; rewrite E26, R26; reflexivity)
        ltac:(rewrite ?ew_ewset_other by lia; rewrite E36; reflexivity)
        ltac:(lia) UN32) in Hc end.
    rewrite NEQ in Hc. apply Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ0 SHOK Bspan_HS (AF_both3_reac_hunt_step + 736); [hs_awr Usp|]. ld_keep Usp.
    eapply EXIT;
    [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity
    | split; [intros n Hn; rewrite ?ew_ewset_other by lia; apply EL; unfold A_TEXT; lia | reflexivity]
    | vm_compute; reflexivity | exact KEEP | exact HFK | exact HCSR | exact HJ0 | lia ].
Qed.


Lemma ld_live : hs_postd_stmt ->
  forall (fq : YK11.FPState) (F0 : bvmap 5 word) (C0 : bv 32) ly S W (regs0 : bvmap 5 word) mem0 md0 ch
    (h now hb hn i : Z) (H : list byte) (regs : bvmap 5 word) mem md,
  ld_next F0 C0 ly S W regs0 mem0 md0 h now i H ->
  0 <= i < n_of (hs_table H now) ->
  (forall j, 0 <= j < i -> reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now j = false) ->
  reac_disco_table_age_c.disco_stale (hs_table H now) i now = false ->
  hs_pre ly S W regs0 mem0 md0 ch h now hb hn H ->
  hs_mid F0 C0 fq regs0 ly S W mem0 md0 h now H regs mem md ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 120) 8 3 ->
  getr regs 8 = w64 5000000000 -> getr regs 19 = w64 (h + 384) -> getr regs 20 = w64 (h + 412) ->
  getr regs 21 = w64 (h + 48 * i) -> getr regs 23 = w64 (SB_HS + (h + 384) / 8) ->
  getr regs 24 = w64 (2 ^ 64 - 1 - h) -> getr regs 25 = w64 (48 * i) -> getr regs 26 = w64 i ->
  getr regs 27 = w64 432 -> s32_at H 432 = 0 -> s32_at (hs_arb h H now) 0 <> 2 ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 564))) mem (seg_rom SEGS)) md)
    (hs_post F0 C0 regs0 ly S W mem0 md0 h now H).
Proof.
intros POSTD fq F0 C0 ly S W regs0 mem0 md0 ch h now hb hn i H regs mem md NEXT Hi NW NST HPRE HMID HSP8
  R8 R19 R20 R21 R23 R24 R25 R26 R27 HP0 HSA2.
pose proof HPRE as HPRE'. pose proof HMID as HMID'.
destruct HMID as (HINV & HSPILL & R2 & R3 & R4 & R9 & R18 & R22).
pose proof HINV as HINV'.
destruct HINV as ((lyc & Sc & HJ0 & HPerm) & HMOD & HBLK & HSAV & HRATES & HFK & HCSR).
pose proof HPRE as (HPREa & HROD & Hnow & Hh0 & Hh8 & Hin & Hhb & Hhe & HOK).
pose proof HPREa as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof (paj_run (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof HMOD as (LT & TOK & LA). pose proof TOK as (T1 & _). unfold tbl_T1 in T1.
pose proof HOK as (LH & _ & LOK & V0R).
pose proof HJ0 as (HAR & _).
assert (Hinc : In (hb, hn) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
destruct (al_blocks _ _ LAWS lyc Sc W mem md hb hn HAR Hinc) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & Hbpres & _).
pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as Rsp0. change (bv_modulus 64) with (2 ^ 64) in Rsp0.
fold (spZ regs0) in Rsp0.
assert (WS : REAC_HUNT_STEP_STK = 8464) by reflexivity.
assert (Hi7 : 0 <= i <= 7) by lia.
assert (Hbnd : 0 <= h /\ h + 480 <= 140737488355327)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg in Hbh_ia; lia).
assert (LB : length (hs_blk h H now) = 480%nat).
{ unfold hs_blk. rewrite !length_app, LT, LA, length_skipn.
  rewrite !disco_table.length_sub by (rewrite ?LH; lia). rewrite LH. reflexivity. }
assert (UR : forall (L : list byte) k n, 0 <= k -> (Z.to_nat k + n <= length L)%nat ->
  0 <= u_at L k n < 2 ^ (8 * Z.of_nat n)).
{ intros L k n Hk Hn. unfold u_at. pose proof (disco_table.ble_range (sub L k n)) as Rb.
  rewrite disco_table.length_sub in Rb by lia. exact Rb. }
assert (TSUB : forall k n, 0 <= k -> (Z.to_nat k + n <= 400)%nat ->
  u_at (hs_blk h H now) k n = u_at (hs_table H now) k n)
  by (intros k n Hk Hn; unfold u_at; f_equal; apply hs_blk_T; assumption).
assert (RU8 : 0 <= u_at (hs_table H now) (48 * i + 8) 4 <= 4294967295).
{ pose proof (UR (hs_table H now) (48 * i + 8) 4%nat ltac:(lia) ltac:(rewrite LT; lia)) as Q.
  change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in Q. lia. }
assert (RU20 : 0 <= u_at (hs_table H now) (48 * i + 20) 4 <= 4294967295).
{ pose proof (UR (hs_table H now) (48 * i + 20) 4%nat ltac:(lia) ltac:(rewrite LT; lia)) as Q.
  change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in Q. lia. }
assert (RU12 : 0 <= hd_of (hs_table H now) i <= 255).
{ unfold hd_of. pose proof (UR (hs_table H now) (48 * i + 12) 1%nat ltac:(lia) ltac:(rewrite LT; lia)) as Q.
  change (2 ^ (8 * Z.of_nat 1)) with 256 in Q. lia. }
assert (RU16 : 0 <= reac_arbitrate_c.slots_of (hs_table H now) i <= 255).
{ unfold reac_arbitrate_c.slots_of.
  pose proof (UR (hs_table H now) (48 * i + 16) 1%nat ltac:(lia) ltac:(rewrite LT; lia)) as Q.
  change (2 ^ (8 * Z.of_nat 1)) with 256 in Q. lia. }
assert (RU32 : 0 <= fs_of (hs_table H now) i <= 18446744073709551615).
{ unfold fs_of. pose proof (UR (hs_table H now) (48 * i + 32) 8%nat ltac:(lia) ltac:(rewrite LT; lia)) as Q.
  change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616 in Q. lia. }
assert (RRR : -2147483648 <= role_of_e (hs_table H now) i <= 2147483647).
{ unfold role_of_e, s32_at. pose proof (hs_sw32 (u_at (hs_table H now) (48 * i + 8) 4)) as Q.
  change (2 ^ 31) with 2147483648 in Q. lia. }
set (E := ld_E regs h now i H) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ld_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ld_ex h now i H)) n)
  by (intros n Hn; unfold E, ld_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E18 : ew E 18 = getr regs 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
assert (E19 : ew E 19 = getr regs 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr regs 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 20 20%bv eq_refl)).
assert (E22 : ew E 22 = getr regs 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (ld_ex h now i H) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth ld_ex map] in E32, E33, E34, E35.
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 128)
  by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (Uh : bv_unsigned (ew E 9) = h)
  by (rewrite E9, R9; unfold w64; apply unsigned_lit_small;
      change (2 ^ 64) with 18446744073709551616; lia).
assert (Un : bv_unsigned (ew E 19) = h + 384)
  by (rewrite E19, R19; unfold w64; apply unsigned_lit_small;
      change (2 ^ 64) with 18446744073709551616; lia).
assert (Ue : bv_unsigned (ew E 32) = h + 48 * i)
  by (rewrite E32; unfold w64; apply unsigned_lit_small;
      change (2 ^ 64) with 18446744073709551616; lia).
assert (U22 : bv_unsigned (ew E 22) = SB_HS)
  by (rewrite E22, R22; unfold w64; apply unsigned_lit_small;
      unfold SB_HS; change (2 ^ 64) with 18446744073709551616; lia).
assert (HAE : env_agree 32 (Ereg regs (ld_ex h now i H)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | unfold E, ld_E; reflexivity]).
assert (HRO : regs_ok E (sr_set sr_atoms 21%bv (SOff 32 0)) regs).
{ apply (regs_ok_pin E sr_atoms regs 21%bv (SOff 32 0));
  [unfold E, ld_E; apply regs_ok_Eimg_Ereg | discriminate |].
  cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. exact R21. }
assert (KEEP : ld_keep_p W (spZ regs0) mem mem) by (intros a _ _; reflexivity).
assert (INVOF : forall m', ld_keep_p W (spZ regs0) mem m' ->
  garr8 SEGS (mrestrict (w_H W) m') h (map (fun b : byte => bv_unsigned b) (hs_blk h H now)) /\ hs_rates W m').
{ pose proof (pa_obj_img_all 65 ltac:(vm_compute; lia)) as O65.
  pose proof (pa_hi_img 99 ltac:(vm_compute; lia)) as HH99.
  pose proof (pa_hi_img 98 ltac:(vm_compute; lia)) as HH98.
  unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in O65, HH99, HH98.
  intros m' HK. split.
  - apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem m' h _); [|exact HBLK].
    intros a Ha. rewrite length_map, LB in Ha.
    apply HK; [change (2 ^ 64) with 18446744073709551616; lia | left; lia].
  - destruct HRATES as (Y1 & Y2 & Y3 & Y4). split; [|split; [|split]].
    + apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Y1].
      intros x Hx. unfold shadow_of_addr, SHADOW_OFF. apply HK;
      [change (2 ^ 64) with 18446744073709551616; Z.div_mod_to_equations; lia
      | left; Z.div_mod_to_equations; lia].
    + apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem m' _ _); [|exact Y2].
      intros a Ha. rewrite length_map in Ha. change (length RATES) with 12%nat in Ha.
      apply HK; [change (2 ^ 64) with 18446744073709551616; lia | left; lia].
    + apply (val_mem_kept SEGS (w_H W) (w_H W) mem m'); [|exact Y3].
      intros k Hk. apply HK; [change (2 ^ 64) with 18446744073709551616; lia | left; lia].
    + apply (val_mem_kept SEGS (w_H W) (w_H W) mem m'); [|exact Y4].
      intros k Hk. apply HK; [change (2 ^ 64) with 18446744073709551616; lia | left; lia]. }
assert (MID : forall (fq' : YK11.FPState) (E' : env) (ss' : sstate) (ms' : machine_state) md',
  st_ok_pi (fx := fq') SEGS VAL E' ss' (restrict (w_H W) ms') ->
  env_agree 32 (Ereg regs (ld_ex h now i H)) E' ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv = true ->
  ld_keep_p W (spZ regs0) mem (ms_mem ms') ->
  freg_kept F0 (@YK11.fp_regs fq') -> hs_fc C0 fq' ->
  (exists lyc' Sc', ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc' Sc' W
     (ms_mem ms') md' 0 /\ Permutation (ablocks B lyc' Sc') (ablocks B ly S)) ->
  hs_mid F0 C0 fq' regs0 ly S W mem0 md0 h now H (ms_regs ms') (ms_mem ms') md' /\
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms')) (spZ regs0 - 120) 8 3 /\
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv ->
     getr (ms_regs ms') r = getr regs r)).
{ intros fq' E' ss' ms' md' HS' HAE' Hfb HK HFK' HCSR' HJ'.
  pose proof (regs_kept_of_st_ok_pi E' ss' (restrict (w_H W) ms') regs (ld_ex h now i H)
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv HS' HAE' Hfb) as KR.
  cbn [ms_regs restrict] in KR.
  assert (HSP8' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms')) (spZ regs0 - 120) 8 3).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms')); [|exact HSP8].
    intros k Hk. apply HK; [change (2 ^ 64) with 18446744073709551616; lia | right; lia]. }
  assert (HSP16' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms')) (spZ regs0 - 112) 8 (h + 440)).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms')); [|exact HSPILL].
    intros k Hk. apply HK; [change (2 ^ 64) with 18446744073709551616; lia | right; lia]. }
  split; [|split; [exact HSP8' | exact KR]].
  split.
  { apply (hs_inv_kept F0 C0 fq' regs0 ly S W mem0 md0 ch h now hb hn H mem md (ms_mem ms') md' HPRE'
      ltac:(split; [exists lyc, Sc; split; [exact HJ0 | exact HPerm]|];
            split; [exact HMOD|]; split; [exact HBLK|]; split; [exact HSAV|]; split; [exact HRATES|];
            split; [exact HFK' | exact HCSR'])
      ltac:(apply (ld_keep_hs W (spZ regs0) mem (ms_mem ms')); exact HK) HJ'). }
  split; [exact HSP16'|].
  rewrite !(KR 2%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 3%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 4%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 9%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 18%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 22%bv ltac:(repeat (first [left; reflexivity | right]))).
  repeat split; assumption. }
assert (TAILX : forall (fq' : YK11.FPState) (E' : env) (ss' : sstate) (ms' : machine_state) md' (pp : Z),
  st_ok_pi (fx := fq') SEGS VAL E' ss' (restrict (w_H W) ms') -> ss_resv ss' = None ->
  ss_pc ss' = AF_both3_reac_hunt_step + pp -> (pp = 664 \/ pp = 672) ->
  env_agree 32 (Ereg regs (ld_ex h now i H)) E' ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv = true ->
  ld_keep_p W (spZ regs0) mem (ms_mem ms') ->
  freg_kept F0 (@YK11.fp_regs fq') -> hs_fc C0 fq' ->
  (exists lyc' Sc', ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc' Sc' W
     (ms_mem ms') md' 0 /\ Permutation (ablocks B lyc' Sc') (ablocks B ly S)) ->
  reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now i = false ->
  SRr SEGS W (mkCfg ms' md') (hs_post F0 C0 regs0 ly S W mem0 md0 h now H)).
{ intros fq' E' ss' ms' md' pp HS' Hrv Hpc Hpp HAE' Hfb HK HFK' HCSR' HJ' HFD.
  destruct (MID fq' E' ss' ms' md' HS' HAE' Hfb HK HFK' HCSR' HJ') as (HM & HS8 & KR).
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS' Hrv), Hpc.
  apply (ld_tail POSTD pp fq' F0 C0 ly S W regs0 mem0 md0 ch h now hb hn i H (ms_regs ms') (ms_mem ms') md'
    NEXT Hpp Hi NW HFD HPRE' HM HS8);
  [ rewrite (KR 8%bv ltac:(repeat (first [left; reflexivity | right]))); exact R8
  | rewrite (KR 19%bv ltac:(repeat (first [left; reflexivity | right]))); exact R19
  | rewrite (KR 20%bv ltac:(repeat (first [left; reflexivity | right]))); exact R20
  | rewrite (KR 23%bv ltac:(repeat (first [left; reflexivity | right]))); exact R23
  | rewrite (KR 24%bv ltac:(repeat (first [left; reflexivity | right]))); exact R24
  | rewrite (KR 25%bv ltac:(repeat (first [left; reflexivity | right]))); exact R25
  | rewrite (KR 26%bv ltac:(repeat (first [left; reflexivity | right]))); exact R26
  | rewrite (KR 27%bv ltac:(repeat (first [left; reflexivity | right]))); exact R27
  | exact HP0 | exact HSA2 ]. }
assert (EPIX : forall (fq' : YK11.FPState) (E' : env) (ss' : sstate) (ms' : machine_state) md',
  st_ok_pi (fx := fq') SEGS VAL E' ss' (restrict (w_H W) ms') -> ss_resv ss' = None ->
  ss_pc ss' = AF_both3_reac_hunt_step + 268 ->
  env_agree 32 (Ereg regs (ld_ex h now i H)) E' ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv = true ->
  ld_keep_p W (spZ regs0) mem (ms_mem ms') ->
  freg_kept F0 (@YK11.fp_regs fq') -> hs_fc C0 fq' ->
  (exists lyc' Sc', ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc' Sc' W
     (ms_mem ms') md' 0 /\ Permutation (ablocks B lyc' Sc') (ablocks B ly S)) ->
  getr (ms_regs ms') 11 = w64 0 -> reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now i = true ->
  SRr SEGS W (mkCfg ms' md') (hs_post F0 C0 regs0 ly S W mem0 md0 h now H)).
{ intros fq' E' ss' ms' md' HS' Hrv Hpc HAE' Hfb HK HFK' HCSR' HJ' Q11 HFD.
  destruct (MID fq' E' ss' ms' md' HS' HAE' Hfb HK HFK' HCSR' HJ') as (HM & HS8 & KR).
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS' Hrv), Hpc.
  apply (hs_epi (fx := fq') F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H (ms_regs ms') (ms_mem ms') md' 0
    HPRE' HM Q11).
  unfold hs_verdict. rewrite HP0, reac_hunt_step.hs_dm_unp.
  replace (s32_at (hs_arb h H now) 0 =? 2) with false by (symmetry; apply Z.eqb_neq; exact HSA2).
  rewrite (reac_hunt_step.hs_dgl_true h (hs_table H now) (sub H 412 6) now i ltac:(exact Hi) HFD).
  reflexivity. }
assert (ENTF : forall m', garr8 SEGS (mrestrict (w_H W) m') h (map (fun b : byte => bv_unsigned b) (hs_blk h H now)) ->
  val_mem SEGS (mrestrict (w_H W) m') (h + 48 * i + 8) 4 (role_of_e (hs_table H now) i) /\
  val_mem SEGS (mrestrict (w_H W) m') (h + 48 * i + 12) 1 (hd_of (hs_table H now) i) /\
  val_mem SEGS (mrestrict (w_H W) m') (h + 48 * i + 16) 1 (reac_arbitrate_c.slots_of (hs_table H now) i) /\
  val_mem SEGS (mrestrict (w_H W) m') (h + 48 * i + 20) 4 (reac_arbitrate_c.ch_of (hs_table H now) i) /\
  val_mem SEGS (mrestrict (w_H W) m') (h + 48 * i + 32) 8 (fs_of (hs_table H now) i)).
{ intros m' HG.
  assert (VB' : forall k n, 0 <= k -> (Z.to_nat k + n <= 480)%nat ->
    val_mem SEGS (mrestrict (w_H W) m') (h + k) n (u_at (hs_blk h H now) k n))
    by (intros k n Hk Hn; apply hs_vm; [exact HG | exact Hk | rewrite LB; exact Hn]).
  split; [|split; [|split; [|split]]].
  - unfold role_of_e, s32_at. apply ld_s32_vm.
    replace (h + 48 * i + 8) with (h + (48 * i + 8)) by lia.
    rewrite <- (TSUB (48 * i + 8) 4%nat ltac:(lia) ltac:(lia)). apply VB'; lia.
  - unfold hd_of. replace (h + 48 * i + 12) with (h + (48 * i + 12)) by lia.
    rewrite <- (TSUB (48 * i + 12) 1%nat ltac:(lia) ltac:(lia)). apply VB'; lia.
  - unfold reac_arbitrate_c.slots_of. replace (h + 48 * i + 16) with (h + (48 * i + 16)) by lia.
    rewrite <- (TSUB (48 * i + 16) 1%nat ltac:(lia) ltac:(lia)). apply VB'; lia.
  - unfold reac_arbitrate_c.ch_of. replace (h + 48 * i + 20) with (h + (48 * i + 20)) by lia.
    rewrite <- (TSUB (48 * i + 20) 4%nat ltac:(lia) ltac:(lia)). apply VB'; lia.
  - unfold fs_of. replace (h + 48 * i + 32) with (h + (48 * i + 32)) by lia.
    rewrite <- (TSUB (48 * i + 32) 8%nat ltac:(lia) ltac:(lia)). apply VB'; lia. }
destruct (ld_build fq F0 C0 ly S W regs0 mem0 md0 ch h now hb hn i (AF_both3_reac_hunt_step + 564) H
  (sr_set sr_atoms 21%bv (SOff 32 0)) regs mem md HPRE' HINV' HSP8 HSPILL Hi R2 R8 R9 R19 R22 R23 R24 R25 R26 R27 HRO)
  as [HS SHOK].
fold E in HS, SHOK.
paj_run_tok RUN HS HJ0 SHOK Bspan_HS; [hs_awr Usp|]. ld_keep Usp.
lazymatch goal with HSc : st_ok _ ?Ex _ (restrict _ ?msc) |- _ =>
  assert (A32 : ew Ex 32 = w64 (h + 48 * i)) by (rewrite ?ew_ewset_other by lia; exact E32);
  assert (A20 : ew Ex 20 = w64 (h + 412)) by (rewrite ?ew_ewset_other by lia; rewrite E20, R20; reflexivity);
  assert (A3 : ew Ex 3 = getr regs0 3) by (rewrite ?ew_ewset_other by lia; rewrite E3, R3; reflexivity);
  assert (A4 : ew Ex 4 = getr regs0 4) by (rewrite ?ew_ewset_other by lia; rewrite E4, R4; reflexivity);
  assert (Gsp : bv_unsigned (ew Ex 2) = spZ regs0 - 128) by (rewrite ?ew_ewset_other by lia; exact Usp);
  assert (Ge : bv_unsigned (ew Ex 32) = h + 48 * i) by (rewrite ?ew_ewset_other by lia; exact Ue);
  assert (Gn : bv_unsigned (ew Ex 19) = h + 384) by (rewrite ?ew_ewset_other by lia; exact Un);
  assert (Gb : bv_unsigned (ew Ex 22) = SB_HS) by (rewrite ?ew_ewset_other by lia; exact U22);
  prreg HSc (1%bv : bv 5) Pra; prreg HSc (2%bv : bv 5) Psp; prreg HSc (3%bv : bv 5) Pgp;
  prreg HSc (4%bv : bv 5) Ptp; prreg HSc (10%bv : bv 5) Pa0; prreg HSc (11%bv : bv 5) Pa1;
  prreg HSc (12%bv : bv 5) Pa2; rename HSc into HSK
end.
lazymatch goal with HSc : st_ok _ _ _ (restrict _ ?msc) |- _ =>
  set (memT := ms_mem msc) in *; set (regsT := ms_regs msc) in * end.
assert (HBLKT : garr8 SEGS (mrestrict (w_H W) memT) h (map (fun b : byte => bv_unsigned b) (hs_blk h H now))).
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem memT h _); [|exact HBLK].
  intros a Ha. rewrite length_map, LB in Ha.
  apply KEEP; [change (2 ^ 64) with 18446744073709551616; lia | left; lia]. }
assert (HAVT : forall a, h <= a < h + 480 -> aview SEGS (w_H W) memT a <> None).
{ intros a Ha. apply (ld_aview_some (w_H W) memT h (hs_blk h H now) a HBLKT). rewrite LB. lia. }
assert (HSPT : spZ regsT = spZ regs0 + -128).
{ unfold spZ at 1. rewrite Psp, Gsp. lia. }
pmkst HSK.
eapply SRr_bind.
{ eapply (aj_bcmp_at (fx := fq) SEGS B LAWS Hsegs (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fq) W
    regsT memT REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc Sc _ 0
    (h + 48 * i) (h + 412) 6 (-128) (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 580))) HJ0).
  - rewrite Pa0, A32. reflexivity.
  - rewrite Pa1, A20. reflexivity.
  - rewrite Pa2. reflexivity.
  - change (2 ^ 32) with 4294967296. lia.
  - lia.
  - change (2 ^ 63) with 9223372036854775808. lia.
  - lia.
  - change (2 ^ 63) with 9223372036854775808. lia.
  - exact HSPT.
  - reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite Pgp, A3. exact Hgp.
  - rewrite Ptp, A4. exact Htp.
  - rewrite Pra. reflexivity.
  - apply ret_ok_codeptr_v;
    [change (AF_both3_reac_hunt_step + 580) with 31104; change (2 ^ 40) with 1099511627776; lia
    | reflexivity].
  - intros a Ha. split; [apply HAVT; lia | rewrite HSPT; unfold ESTACK; lia].
  - intros a Ha. split; [apply HAVT; lia | rewrite HSPT; unfold ESTACK; lia].
  - intros a Ha. unfold ESTACK. lia.
  - intros a Ha. unfold ESTACK. lia.
  - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. lia.
  - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. lia.
  - exact (range_addressable_of_block SEGS B LAWS lyc Sc W memT _ hb hn (h + 48 * i) 6
      (proj1 HJ0) Hinc ltac:(lia) ltac:(lia)).
  - intros _. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W memT _ hb hn (h + 48 * i) 6
      (proj1 HJ0) Hinc ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (range_addressable_of_block SEGS B LAWS lyc Sc W memT _ hb hn (h + 412) 6
      (proj1 HJ0) Hinc ltac:(lia) ltac:(lia)).
  - intros _. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W memT _ hb hn (h + 412) 6
      (proj1 HJ0) Hinc ltac:(lia) ltac:(lia) ltac:(lia)). }
cbv beta. intros W2 c2 _ HPP.
destruct HPP as (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2).
assert (KEEP2 : ld_keep_p W (spZ regs0) mem mem2).
{ apply (ld_keep_call W (spZ regs0) mem memT mem2 (spZ regs0 - 128 - 8192) (spZ regs0 - 128) KEEP).
  - intros a Ha Hn. apply Hfr2; [exact Ha | intros X; apply Hn; unfold ESTACK in X; lia].
  - lia.
  - lia. }
assert (HMAC : v = w64 0 <-> reac_arbitrate_c.bytes_eqb (mac_of (hs_table H now) i) (sub H 412 6) = true).
{ rewrite reac_hunt_step.hs_beqb, Hcmp. unfold mac_of.
  rewrite <- (hs_blk_T h H now (48 * i) 6 LT ltac:(lia) ltac:(lia)).
  rewrite <- (hs_blk_H h H now 412 6 LT LH ltac:(lia) ltac:(lia)).
  rewrite <- (ld_bytes_eq (w_H W) memT h (hs_blk h H now) (48 * i) 412 6 HBLKT ltac:(lia) ltac:(lia)
    ltac:(rewrite LB; lia) ltac:(rewrite LB; lia)).
  split; intros Hq j Hj; apply Hq; lia. }
clear KEEP. rename KEEP2 into KEEP.
lazymatch type of HSK with st_ok _ ?Ex _ _ =>
  jafter_call_keep_pi HSK 37%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end;
  [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
    [ apply (ld_region_kept Ex (w_H W) memT mem2 2 (spZ regs0 - 128) 0 128 _ Gsp);
      intros a Ha; apply Hfr2; [change (2 ^ 64) with 18446744073709551616; lia
                               | intros X; unfold ESTACK in X; lia]
    | apply (ld_region_kept Ex (w_H W) memT mem2 32 (h + 48 * i) 0 48 _ Ge);
      intros a Ha; apply Hfr2; [change (2 ^ 64) with 18446744073709551616; lia
                               | intros X; unfold ESTACK in X; lia]
    | apply (ld_region_kept Ex (w_H W) memT mem2 19 (h + 384) 0 4 _ Gn);
      intros a Ha; apply Hfr2; [change (2 ^ 64) with 18446744073709551616; lia
                               | intros X; unfold ESTACK in X; lia] ]
  | idtac ];
  remember (havoc Ex 37 (map (getr regs2) CLOB)) as Eb eqn:HE2 in HS2;
  assert (HEI2 : img_env VAL A_LIM Eb) by (rewrite HE2; apply img_env_havoc; [assumption | cbv; lia]);
  assert (B22 : bv_unsigned (ew Eb 22) = SB_HS) by (rewrite HE2, ew_havoc_old by lia; exact Gb);
  assert (B32 : bv_unsigned (ew Eb 32) = h + 48 * i) by (rewrite HE2, ew_havoc_old by lia; exact Ge);
  assert (B19 : bv_unsigned (ew Eb 19) = h + 384) by (rewrite HE2, ew_havoc_old by lia; exact Gn);
  assert (B2 : bv_unsigned (ew Eb 2) = spZ regs0 - 128) by (rewrite HE2, ew_havoc_old by lia; exact Gsp);
  assert (B33 : ew Eb 33 = Z_to_bv 64 (u_at (hs_table H now) (48 * i + 8) 4))
    by (rewrite HE2, ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact E33);
  assert (B34 : ew Eb 34 = Z_to_bv 64 (u_at (hs_table H now) (48 * i + 20) 4))
    by (rewrite HE2, ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact E34);
  assert (B41 : ew Eb 41 = v)
    by (rewrite HE2; change 41%nat with (37 + 4)%nat;
        rewrite (ew_havoc_new Ex 37 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0))
          by (cbn [length map CLOB]; lia); cbn [map CLOB nth]; exact Hv);
  assert (Bw32 : ew Eb 32 = w64 (h + 48 * i)) by (rewrite HE2, ew_havoc_old by lia; exact A32);
  assert (Bw18 : ew Eb 18 = w64 now)
    by (rewrite HE2, ew_havoc_old by lia; ld_ewstrip; rewrite E18, R18; reflexivity);
  assert (Bw3 : ew Eb 3 = getr regs0 3) by (rewrite HE2, ew_havoc_old by lia; exact A3);
  assert (Bw4 : ew Eb 4 = getr regs0 4) by (rewrite HE2, ew_havoc_old by lia; exact A4);
  assert (Bw8 : ew Eb 8 = w64 5000000000)
    by (rewrite HE2, ew_havoc_old by lia; ld_ewstrip; rewrite E8, R8; reflexivity);
  assert (BAE : env_agree 32 (Ereg regs (ld_ex h now i H)) Eb)
    by (rewrite HE2; apply env_agree_havoc_ge; [lia|];
        split; [intros n Hn; rewrite ?ew_ewset_other by lia; apply EL; unfold A_TEXT; lia | reflexivity]);
  clear HE2
end.
assert (SHOK2 : sh_ok SEGS Bx_HS SH_LD Eb (mrestrict (w_H W) mem2)).
{ apply (ld_shok Eb W mem2 lyc Sc md2 hb hn h i (proj1 HJ2) Hinc Hhb Hhe Hi7 B22 B32 B19). }
rewrite <- YA0o.restrict_mkst_fx in HS2.
psrr_branch_tok RUN BR HS2 SHOK2 Bspan_HS.
- rewrite (ld_breq0 Eb 41 v B41) in Hc. apply Z.eqb_eq, ld_w64_0, HMAC in Hc.
  assert (HFD : reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now i = false).
  { unfold reac_hunt_step.hs_fd. rewrite Hc.
    destruct (reac_disco_table_age_c.disco_stale (hs_table H now) i now); reflexivity. }
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bspan_HS (AF_both3_reac_hunt_step + 664); [hs_awr Usp|]. ld_keep Usp.
  eapply (TAILX _ _ _ _ _ 664);
  [ exact HS2 | vm_compute; reflexivity | vm_compute; reflexivity | left; reflexivity
  | split; [intros n Hn; rewrite ?ew_ewset_other by lia; apply (proj1 BAE); lia | exact (proj2 BAE)]
  | vm_compute; reflexivity | exact KEEP | exact HFK | exact HCSR
  | exists lyc, Sc; split; [exact HJ2 | exact HPerm] | exact HFD ].
- rewrite (ld_breq0 Eb 41 v B41) in Hc. apply Z.eqb_neq in Hc.
  assert (HNE : reac_arbitrate_c.bytes_eqb (mac_of (hs_table H now) i) (sub H 412 6) = false).
  { destruct (reac_arbitrate_c.bytes_eqb (mac_of (hs_table H now) i) (sub H 412 6)) eqn:Hb;
    [exfalso; apply Hc; apply (proj2 (ld_w64_0 v)); apply (proj2 HMAC); reflexivity | reflexivity]. }
  clear Hc.
  paj_run_tok RUN HS2 HJ2 SHOK2 Bspan_HS; [hs_awr Usp|]. ld_keep Usp.
  psrr_branch_tok RUN BR HS2 SHOK2 Bspan_HS.
  + lazymatch type of HS2 with st_ok_pi _ _ ?Ez _ _ =>
      rewrite (proj2 (hs_br32 Ez 33 (u_at (hs_table H now) (48 * i + 8) 4) 0
        ltac:(ld_ewstrip; exact B33) ltac:(change (2 ^ 32) with 4294967296; lia)
        ltac:(change (2 ^ 31) with 2147483648; lia))) in Hc end.
    apply negb_true_iff, Z.eqb_neq in Hc.
    assert (HFD : reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now i = false).
    { unfold reac_hunt_step.hs_fd. unfold role_of_e, s32_at.
      replace (bv_swrap 32 (u_at (hs_table H now) (48 * i + 8) 4) =? 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hc).
      destruct (reac_disco_table_age_c.disco_stale (hs_table H now) i now);
      destruct (reac_arbitrate_c.bytes_eqb (mac_of (hs_table H now) i) (sub H 412 6)); reflexivity. }
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bspan_HS (AF_both3_reac_hunt_step + 664); [hs_awr Usp|]. ld_keep Usp.
    eapply (TAILX _ _ _ _ _ 664);
    [ exact HS2 | vm_compute; reflexivity | vm_compute; reflexivity | left; reflexivity
    | split; [intros n Hn; rewrite ?ew_ewset_other by lia; apply (proj1 BAE); lia | exact (proj2 BAE)]
    | vm_compute; reflexivity | exact KEEP | exact HFK | exact HCSR
    | exists lyc, Sc; split; [exact HJ2 | exact HPerm] | exact HFD ].
  + lazymatch type of HS2 with st_ok_pi _ _ ?Ez _ _ =>
      rewrite (proj2 (hs_br32 Ez 33 (u_at (hs_table H now) (48 * i + 8) 4) 0
        ltac:(ld_ewstrip; exact B33) ltac:(change (2 ^ 32) with 4294967296; lia)
        ltac:(change (2 ^ 31) with 2147483648; lia))) in Hc end.
    apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HROLE.
    paj_run_tok RUN HS2 HJ2 SHOK2 Bspan_HS; [hs_awr Usp|]. ld_keep Usp.
    psrr_branch_tok RUN BR HS2 SHOK2 Bspan_HS.
    * lazymatch type of HS2 with st_ok_pi _ _ ?Ez _ _ =>
        rewrite (proj1 (hs_br32 Ez 34 (u_at (hs_table H now) (48 * i + 20) 4) 0
          ltac:(ld_ewstrip; exact B34) ltac:(change (2 ^ 32) with 4294967296; lia)
          ltac:(change (2 ^ 31) with 2147483648; lia))) in Hc end.
      rewrite (reac_hunt_step.hs_swrap0 (u_at (hs_table H now) (48 * i + 20) 4)
        ltac:(change (2 ^ 32) with 4294967296; lia)) in Hc.
      apply Z.eqb_eq in Hc.
      assert (HFD : reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now i = false).
      { unfold reac_hunt_step.hs_fd, reac_arbitrate_c.ch_of. rewrite Hc.
        destruct (reac_disco_table_age_c.disco_stale (hs_table H now) i now);
        destruct (reac_arbitrate_c.bytes_eqb (mac_of (hs_table H now) i) (sub H 412 6));
        destruct (role_of_e (hs_table H now) i =? 0); reflexivity. }
      paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bspan_HS (AF_both3_reac_hunt_step + 672); [hs_awr Usp|]. ld_keep Usp.
      eapply (TAILX _ _ _ _ _ 672);
      [ exact HS2 | vm_compute; reflexivity | vm_compute; reflexivity | right; reflexivity
      | split; [intros n Hn; rewrite ?ew_ewset_other by lia; apply (proj1 BAE); lia | exact (proj2 BAE)]
      | vm_compute; reflexivity | exact KEEP | exact HFK | exact HCSR
      | exists lyc, Sc; split; [exact HJ2 | exact HPerm] | exact HFD ].
    * lazymatch type of HS2 with st_ok_pi _ _ ?Ez _ _ =>
        rewrite (proj1 (hs_br32 Ez 34 (u_at (hs_table H now) (48 * i + 20) 4) 0
          ltac:(ld_ewstrip; exact B34) ltac:(change (2 ^ 32) with 4294967296; lia)
          ltac:(change (2 ^ 31) with 2147483648; lia))) in Hc end.
      rewrite (reac_hunt_step.hs_swrap0 (u_at (hs_table H now) (48 * i + 20) 4)
        ltac:(change (2 ^ 32) with 4294967296; lia)) in Hc.
      apply Z.eqb_neq in Hc. rename Hc into HCH.
      paj_run_tok RUN HS2 HJ2 SHOK2 Bspan_HS; [hs_awr Usp|]. ld_keep Usp.
      lazymatch goal with HSs : st_ok _ ?Ey (setpc _ (pa_sigma AS_reac_sender_kind)) (restrict _ ?msy) |- _ =>
        assert (Cs22 : bv_unsigned (ew Ey 22) = SB_HS) by (ld_ewstrip; exact B22);
        assert (Cs32 : bv_unsigned (ew Ey 32) = h + 48 * i) by (ld_ewstrip; exact B32);
        assert (Cs19 : bv_unsigned (ew Ey 19) = h + 384) by (ld_ewstrip; exact B19);
        assert (Cs2 : bv_unsigned (ew Ey 2) = spZ regs0 - 128) by (ld_ewstrip; exact B2);
        assert (D32 : ew Ey 32 = w64 (h + 48 * i)) by (ld_ewstrip; exact Bw32);
        assert (D18 : ew Ey 18 = w64 now) by (ld_ewstrip; exact Bw18);
        assert (D3 : ew Ey 3 = getr regs0 3) by (ld_ewstrip; exact Bw3);
        assert (D4 : ew Ey 4 = getr regs0 4) by (ld_ewstrip; exact Bw4);
        assert (D8 : ew Ey 8 = w64 5000000000) by (ld_ewstrip; exact Bw8);
        assert (CAE : env_agree 32 (Ereg regs (ld_ex h now i H)) Ey)
          by (split; [intros n Hn; ld_ewstrip; apply (proj1 BAE); lia | exact (proj2 BAE)]);
        prreg HSs (1%bv : bv 5) Q1; prreg HSs (2%bv : bv 5) Q2; prreg HSs (3%bv : bv 5) Q3;
        prreg HSs (4%bv : bv 5) Q4; prreg HSs (8%bv : bv 5) Q8; prreg HSs (10%bv : bv 5) Q10;
        prreg HSs (11%bv : bv 5) Q11; prreg HSs (12%bv : bv 5) Q12;
        pose proof (YA0o.st_ok_restrict_mkst SEGS _ _ _ _ HSs eq_refl) as Hmsy;
        rewrite Hmsy in HSs |- *; clear Hmsy; cbn [ss_pc setpc] in HSs |- *;
        rewrite YA0o.restrict_mkst_fx in HSs;
        rewrite pa_sigma_reac_sender_kind;
        set (regsY := ms_regs msy) in *; set (memY := ms_mem msy) in *; rename HSs into HSY
      end.
      destruct (INVOF memY KEEP) as (HBLKY & HRATESY).
      assert (HSPY : spZ regsY = spZ regs0 + -128) by (unfold spZ at 1; rewrite Q2, Cs2; lia).
      assert (WSK : REAC_SENDER_KIND_STK = 4224) by reflexivity.
      assert (HRAY : getr regsY 1 = Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 656))) by (rewrite Q1; reflexivity).
      pose proof (pa_base_lo (PL := PL_both3_0) (PI := PI)) as HBlo. unfold YImgTop.IMG_LO in HBlo.
      pose proof (@pa_B_ok _ _ PI) as HBok. destruct HBok as (HBok1 & HBok2 & HBok3).
      change (2 ^ 40) with 1099511627776 in HBok2. change (2 ^ 64) with 18446744073709551616 in HBok2.
      eapply SRr_bind.
      { eapply (TSENDER fq lyc Sc W regsY memY _ [] (h + 48 * i) now 0
          (role_of_e (hs_table H now) i) (hd_of (hs_table H now) i)
          (reac_arbitrate_c.slots_of (hs_table H now) i) (reac_arbitrate_c.ch_of (hs_table H now) i)
          (fs_of (hs_table H now) i)).
        - eapply (afn_pre_at SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc Sc W memY _ 0
            regsY REAC_SENDER_KIND_STK (-128) [] HJ2).
          + exact HSPY.
          + reflexivity.
          + lia.
          + lia.
          + lia.
          + rewrite HRAY. apply ret_ok_codeptr_v;
            [change (AF_both3_reac_hunt_step + 656) with 31180; change (2 ^ 40) with 1099511627776; lia
            | reflexivity].
          + unfold raZ. rewrite HRAY, unsigned_lit_small
              by (change (AF_both3_reac_hunt_step + 656) with 31180;
                  change (2 ^ 64) with 18446744073709551616; lia).
            change (AF_both3_reac_hunt_step + 656) with 31180. lia.
          + rewrite Q3, D3. exact Hgp.
          + rewrite Q4, D4. exact Htp.
          + unfold s0Z. rewrite Q8, D8. unfold w64.
            rewrite unsigned_lit_small by (change (2 ^ 64) with 18446744073709551616; lia).
            apply achain_low. lia.
        - exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            HJ2 HROD).
        - rewrite Q10, D32. reflexivity.
        - change (2 ^ 64) with 18446744073709551616. lia.
        - lia.
        - rewrite Q11, D18. reflexivity.
        - exact Hnow.
        - rewrite Q12. reflexivity.
        - change (2 ^ 31) with 2147483648. lia.
        - intros _. destruct (ENTF memY HBLKY) as (M8 & M12 & M16 & M20 & M32).
          pose proof (blk_off_imgP B lyc Sc W memY _ hb hn (proj1 HJ2) Hinc) as HOI.
          unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HOI.
          split; [change (2 ^ 63) with 9223372036854775808; lia|].
          split; [apply (in_app_sub hb (req_size hn)); [exact Hbh_ia | lia | lia | lia]|].
          split; [unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP; lia|].
          split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc W memY _ hb hn (h + 48 * i + 8) 32
            (proj1 HJ2) Hinc ltac:(lia) ltac:(lia))|].
          split; [intros a Ha; destruct (al_blocks _ _ LAWS lyc Sc W memY _ hb hn (proj1 HJ2) Hinc)
            as (_ & _ & _ & _ & HpresY & _); exact (proj1 (HpresY a ltac:(lia)))|].
          split; [change (2 ^ 31) with 2147483648; lia|].
          split; [change (2 ^ 8) with 256; lia|].
          split; [change (2 ^ 8) with 256; lia|].
          split; [unfold reac_arbitrate_c.ch_of; change (2 ^ 32) with 4294967296; lia|].
          split; [change (2 ^ 64) with 18446744073709551616; lia|].
          split; [exact M8|]. split; [exact M12|]. split; [exact M16|]. split; [exact M20 | exact M32].
        - exact (proj1 HRATESY).
        - exact (proj1 (proj2 HRATESY)).
        - exact (proj1 (proj2 (proj2 HRATESY))).
        - exact (proj2 (proj2 (proj2 HRATESY))). }
      cbv beta. intros W3 c3 _ HPS.
      destruct HPS as (fqw & FK2 & FC2 & fq2 & ly3 & S3 & regs3 & mem3 & md3 & Hcf3 & Hfr3 & Hcsr3 & HJm & HPm & HAm & Hpm & HWm & Km).
      subst c3. subst W3.
      pose proof (ajournal_sub SEGS B LAWS Hsegs REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 []
        lyc Sc W memY _ 0 REAC_SENDER_KIND_STK (spZ regsY) [] [] ly3 S3 W mem3 md3 0 HJ2 HJm
        ltac:(lia) ltac:(lia) ltac:(intros a X; exfalso; exact (inFP_nil a X))) as HJ3.
      cbn [app] in HJ3. change (0 + 0) with 0 in HJ3.
      assert (KEEP3 : ld_keep_p W (spZ regs0) mem mem3).
      { intros a Ha Hb.
        rewrite (ld_aview_of_kept (w_H W) memY mem3 (spZ regsY - REAC_SENDER_KIND_STK) (spZ regsY) a Km
          ltac:(rewrite Z.mod_small by (change (2 ^ 64) with 18446744073709551616; lia);
                rewrite HSPY; intros X; destruct Hb; lia)).
        exact (KEEP a Ha Hb). }
      clear KEEP. rename KEEP3 into KEEP.
      pose proof (FpStep.fp_st_ok_fx SEGS fq fq2 _ _ _ _ _ _ HSY) as HSq. clear HSY.
      lazymatch type of HSq with st_ok _ ?Ey _ _ =>
        jafter_call_keep_pi HSq 53%nat regs3 (mrestrict (w_H W) mem3) HPm [0; 1; 2]%nat HS3;
        match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end;
        [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
          [ apply (ld_region_kept Ey (w_H W) memY mem3 2 (spZ regs0 - 128) 0 128 _ Cs2)
          | apply (ld_region_kept Ey (w_H W) memY mem3 32 (h + 48 * i) 0 48 _ Cs32)
          | apply (ld_region_kept Ey (w_H W) memY mem3 19 (h + 384) 0 4 _ Cs19) ];
          intros a Ha; apply (ld_aview_of_kept (w_H W) memY mem3 (spZ regsY - REAC_SENDER_KIND_STK) (spZ regsY) a Km);
          rewrite Z.mod_small by (change (2 ^ 64) with 18446744073709551616; lia); rewrite HSPY; lia
        | idtac ];
        remember (havoc Ey 53 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS3;
        assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [assumption | cbv; lia]);
        assert (F22 : bv_unsigned (ew Ec 22) = SB_HS) by (rewrite HEc, ew_havoc_old by lia; exact Cs22);
        assert (F32 : bv_unsigned (ew Ec 32) = h + 48 * i) by (rewrite HEc, ew_havoc_old by lia; exact Cs32);
        assert (F19 : bv_unsigned (ew Ec 19) = h + 384) by (rewrite HEc, ew_havoc_old by lia; exact Cs19);
        assert (F57 : ew Ec 57 = Z_to_bv 64 (hs_kind h (hs_table H now) now i))
          by (rewrite HEc; change 57%nat with (53 + 4)%nat;
              rewrite (ew_havoc_new Ey 53 (map (getr regs3) CLOB) 4 (Z_to_bv 64 0))
                by (cbn [length map CLOB]; lia); cbn [map CLOB nth]; exact HAm);
        assert (FAE : env_agree 32 (Ereg regs (ld_ex h now i H)) Ec)
          by (rewrite HEc; apply env_agree_havoc_ge; [lia | exact CAE]);
        clear HEc
      end.
      assert (SHOK3 : sh_ok SEGS Bx_HS SH_LD Ec (mrestrict (w_H W) mem3)).
      { apply (ld_shok Ec W mem3 ly3 S3 md3 hb hn h i (proj1 HJ3) ltac:(apply (Permutation_in _ (Permutation_sym
          (Permutation_trans Hpm HPerm))); exact Hin) Hhb Hhe Hi7 F22 F32 F19). }
      rewrite <- YA0o.restrict_mkst_fx in HS3.
      assert (HFK2 : freg_kept F0 (@YK11.fp_regs fq2))
        by (apply (hs_fk_apost F0 fqw fq2); [apply (reac_hunt_step.hs_freg_trans F0 (@YK11.fp_regs fq)); [exact HFK | exact FK2] | exact Hfr3]).
      assert (HCSR2 : hs_fc C0 fq2)
        by (apply (hs_fc_apost C0 fqw fq2); [apply (hs_fc_apost C0 fq fqw HCSR); left; exact FC2 | exact Hcsr3]).
      assert (HPerm3 : Permutation (ablocks B ly3 S3) (ablocks B ly S))
        by (apply (Permutation_trans Hpm HPerm)).
      pose proof (reac_hunt_step.hs_sk_range (h + 48 * i) (role_of_e (hs_table H now) i)
        (hd_of (hs_table H now) i) (reac_arbitrate_c.slots_of (hs_table H now) i)
        (reac_arbitrate_c.ch_of (hs_table H now) i) (fs_of (hs_table H now) i) now) as KR4.
      change (reac_sender_kind_c.reac_sender_kind_model (h + 48 * i) (role_of_e (hs_table H now) i)
        (hd_of (hs_table H now) i) (reac_arbitrate_c.slots_of (hs_table H now) i)
        (reac_arbitrate_c.ch_of (hs_table H now) i) (fs_of (hs_table H now) i) now)
        with (hs_kind h (hs_table H now) now i) in KR4.
      pose proof (paj_run (fx := fq2) (PL := PL_both3_0) (PI := PI) B LAWS) as RUN2.
      pose proof (paj_run_to (fx := fq2) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO2.
      pose proof (paj_branch (fx := fq2) (PI := PI)) as BR2.
      rewrite HRAY.
      paj_run_tok RUN2 HS3 HJ3 SHOK3 Bspan_HS; [hs_awr Usp|]. ld_keep Usp.
      psrr_branch_tok RUN2 BR2 HS3 SHOK3 Bspan_HS.
      -- lazymatch type of HS3 with st_ok_pi _ _ ?Ez _ _ =>
          rewrite (ld_breq Ez 57 (hs_kind h (hs_table H now) now i) 3
            ltac:(ld_ewstrip; exact F57) ltac:(lia) ltac:(lia)) in Hc end.
        apply Z.eqb_eq in Hc.
        assert (HFD : reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now i = true).
        { unfold reac_hunt_step.hs_fd, role_of_e, s32_at. rewrite NST, HNE, HROLE, Hc.
          replace (reac_arbitrate_c.ch_of (hs_table H now) i =? 0) with false
            by (symmetry; apply Z.eqb_neq; exact HCH).
          reflexivity. }
        paj_run_to_tok RUNTO2 HS3 HJ3 SHOK3 Bspan_HS (AF_both3_reac_hunt_step + 268); [hs_awr Usp|]. ld_keep Usp.
        lazymatch type of HS3 with st_ok_pi _ _ ?Ez _ _ => prreg HS3 (11%bv : bv 5) Z11 end.
        eapply EPIX;
        [ exact HS3 | vm_compute; reflexivity | vm_compute; reflexivity
        | split; [intros n Hn; ld_ewstrip; apply (proj1 FAE); lia | exact (proj2 FAE)]
        | vm_compute; reflexivity | exact KEEP | exact HFK2 | exact HCSR2
        | exists ly3, S3; split; [exact HJ3 | exact HPerm3]
        | rewrite Z11; reflexivity | exact HFD ].
      -- lazymatch type of HS3 with st_ok_pi _ _ ?Ez _ _ =>
          rewrite (ld_breq Ez 57 (hs_kind h (hs_table H now) now i) 3
            ltac:(ld_ewstrip; exact F57) ltac:(lia) ltac:(lia)) in Hc end.
        apply Z.eqb_neq in Hc.
        assert (HFD : reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now i = false).
        { unfold reac_hunt_step.hs_fd.
          replace (hs_kind h (hs_table H now) now i =? 3) with false
            by (symmetry; apply Z.eqb_neq; exact Hc).
          destruct (negb (reac_disco_table_age_c.disco_stale (hs_table H now) i now) &&
                    negb (reac_arbitrate_c.bytes_eqb (mac_of (hs_table H now) i) (sub H 412 6)) &&
                    (role_of_e (hs_table H now) i =? 0) &&
                    negb (reac_arbitrate_c.ch_of (hs_table H now) i =? 0)); reflexivity. }
        paj_run_to_tok RUNTO2 HS3 HJ3 SHOK3 Bspan_HS (AF_both3_reac_hunt_step + 664); [hs_awr Usp|]. ld_keep Usp.
        eapply (TAILX _ _ _ _ _ 664);
        [ exact HS3 | vm_compute; reflexivity | vm_compute; reflexivity | left; reflexivity
        | split; [intros n Hn; ld_ewstrip; apply (proj1 FAE); lia | exact (proj2 FAE)]
        | vm_compute; reflexivity | exact KEEP | exact HFK2 | exact HCSR2
        | exists ly3, S3; split; [exact HJ3 | exact HPerm3] | exact HFD ].
Qed.

Theorem pb_hs_loopd : hs_postd_stmt -> hs_loopd_stmt.
Proof.
intros POSTD. unfold hs_loopd_stmt.
intros k. induction k as [|k IH];
intros i fq F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H regs mem md Hk Hi NW HPRE HMID HSP8
  R8 R19 R20 R23 R24 R25 R26 R27 HP0 HSA2; [lia|].
assert (NEXT : ld_next F0 C0 ly S W regs0 mem0 md0 h now i H).
{ intros fq' regs' mem' md' Hlt NWS HM HS8 Q8 Q19 Q20 Q23 Q24 Q25 Q26 Q27.
  exact (IH (i + 1) fq' F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H regs' mem' md'
    ltac:(lia) ltac:(lia) NWS HPRE HM HS8 Q8 Q19 Q20 Q23 Q24 Q25 Q26 Q27 HP0 HSA2). }
pose proof HPRE as HPRE'. pose proof HMID as HMID'.
destruct HMID as (HINV & HSPILL & R2 & R3 & R4 & R9 & R18 & R22).
pose proof HINV as HINV'.
destruct HINV as ((lyc & Sc & HJ0 & HPerm) & HMOD & HBLK & HSAV & HRATES & HFK & HCSR).
pose proof HPRE as (HPREa & HROD & Hnow & Hh0 & Hh8 & Hin & Hhb & Hhe & HOK).
pose proof HPREa as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HMOD as (LT & TOK & LA). pose proof TOK as (T1 & _). unfold tbl_T1 in T1.
pose proof HOK as (LH & _ & LOK & V0R).
pose proof HJ0 as (HAR & _).
assert (Hinc : In (hb, hn) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
destruct (al_blocks _ _ LAWS lyc Sc W mem md hb hn HAR Hinc) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & Hbpres & _).
pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as Rsp0. change (bv_modulus 64) with (2 ^ 64) in Rsp0.
fold (spZ regs0) in Rsp0.
assert (Hi7 : 0 <= i <= 7) by lia.
assert (LB : length (hs_blk h H now) = 480%nat).
{ unfold hs_blk. rewrite !length_app, LT, LA, length_skipn.
  rewrite !disco_table.length_sub by (rewrite ?LH; lia). rewrite LH. reflexivity. }
assert (UR : forall (L : list byte) kk n, 0 <= kk -> (Z.to_nat kk + n <= length L)%nat ->
  0 <= u_at L kk n < 2 ^ (8 * Z.of_nat n)).
{ intros L kk n Hkk Hn. unfold u_at. pose proof (disco_table.ble_range (sub L kk n)) as Rb.
  rewrite disco_table.length_sub in Rb by lia. exact Rb. }
assert (RU40 : 0 <= u_at (hs_table H now) (48 * i + 40) 8 <= 18446744073709551615).
{ pose proof (UR (hs_table H now) (48 * i + 40) 8%nat ltac:(lia) ltac:(rewrite LT; lia)) as Q.
  change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616 in Q. lia. }
pose proof (paj_run (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := ld_E regs h now i H) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ld_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ld_ex h now i H)) n)
  by (intros n Hn; unfold E, ld_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E18 : ew E 18 = getr regs 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j (ld_ex h now i H) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth ld_ex map] in E32, E35.
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 128)
  by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (HRO : regs_ok E sr_atoms regs) by (unfold E, ld_E; apply regs_ok_Eimg_Ereg).
assert (KEEP : ld_keep_p W (spZ regs0) mem mem) by (intros a _ _; reflexivity).
assert (MIDK : forall (E' : env) (ss' : sstate) (ms' : machine_state) md',
  st_ok_pi (fx := fq) SEGS VAL E' ss' (restrict (w_H W) ms') ->
  env_agree 32 (Ereg regs (ld_ex h now i H)) E' ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv = true ->
  ld_keep_p W (spZ regs0) mem (ms_mem ms') ->
  (exists lyc' Sc', ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc' Sc' W
     (ms_mem ms') md' 0 /\ Permutation (ablocks B lyc' Sc') (ablocks B ly S)) ->
  hs_mid F0 C0 fq regs0 ly S W mem0 md0 h now H (ms_regs ms') (ms_mem ms') md' /\
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms')) (spZ regs0 - 120) 8 3 /\
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv ->
     getr (ms_regs ms') r = getr regs r)).
{ intros E' ss' ms' md' HS' HAE' Hfb HK HJ'.
  pose proof (regs_kept_of_st_ok_pi E' ss' (restrict (w_H W) ms') regs (ld_ex h now i H)
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv HS' HAE' Hfb) as KR.
  cbn [ms_regs restrict] in KR.
  assert (HSP8' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms')) (spZ regs0 - 120) 8 3).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms')); [|exact HSP8].
    intros kk Hkk. apply HK; [change (2 ^ 64) with 18446744073709551616; lia | right; lia]. }
  assert (HSP16' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms')) (spZ regs0 - 112) 8 (h + 440)).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms')); [|exact HSPILL].
    intros kk Hkk. apply HK; [change (2 ^ 64) with 18446744073709551616; lia | right; lia]. }
  split; [|split; [exact HSP8' | exact KR]].
  split.
  { apply (hs_inv_kept F0 C0 fq regs0 ly S W mem0 md0 ch h now hb hn H mem md (ms_mem ms') md' HPRE' HINV'
      ltac:(apply (ld_keep_hs W (spZ regs0) mem (ms_mem ms')); exact HK) HJ'). }
  split; [exact HSP16'|].
  rewrite !(KR 2%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 3%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 4%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 9%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 18%bv ltac:(repeat (first [left; reflexivity | right]))).
  rewrite !(KR 22%bv ltac:(repeat (first [left; reflexivity | right]))).
  repeat split; assumption. }
destruct (ld_build fq F0 C0 ly S W regs0 mem0 md0 ch h now hb hn i (AF_both3_reac_hunt_step + 516) H sr_atoms
  regs mem md HPRE' HINV' HSP8 HSPILL Hi R2 R8 R9 R19 R22 R23 R24 R25 R26 R27 HRO) as [HS SHOK].
fold E in HS, SHOK.
paj_run_tok RUN HS HJ0 SHOK Bspan_HS; [hs_awr Usp|]. ld_keep Usp.
psrr_branch_tok RUN BR HS SHOK Bspan_HS.
- assert (NST : reac_disco_table_age_c.disco_stale (hs_table H now) i now = false).
  { apply reac_hunt_step.hs_st1. unfold last_of.
    lazymatch type of HS with st_ok_pi _ _ ?Ez _ _ =>
      rewrite branch_geu_U,
        (U_atom Ez 35 (u_at (hs_table H now) (48 * i + 40) 8)
          ltac:(ld_ewstrip; exact E35) ltac:(change (2 ^ 64) with 18446744073709551616; lia)),
        (U_atom Ez 18 now ltac:(ld_ewstrip; rewrite E18, R18; reflexivity)
          ltac:(change (2 ^ 64) with 18446744073709551616; lia)) in Hc end.
    apply negb_true_iff, Z.ltb_ge in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ0 SHOK Bspan_HS (AF_both3_reac_hunt_step + 564); [hs_awr Usp|]. ld_keep Usp.
  lazymatch type of HS with st_ok_pi _ _ ?Ez _ _ =>
    assert (FAE : env_agree 32 (Ereg regs (ld_ex h now i H)) Ez)
      by (split; [intros n Hn; ld_ewstrip; apply EL; unfold A_TEXT; lia | reflexivity]) end.
  destruct (MIDK _ _ _ _ HS FAE ltac:(vm_compute; reflexivity) KEEP
    ltac:(exists lyc, Sc; split; [exact HJ0 | exact HPerm])) as (HM & HS8 & KR).
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS ltac:(vm_compute; reflexivity)).
  change (ss_pc _) with (AF_both3_reac_hunt_step + 564).
  apply (ld_live POSTD fq F0 C0 ly S W regs0 mem0 md0 ch h now hb hn i H _ _ _ NEXT Hi NW NST HPRE' HM HS8);
  [ rewrite (KR 8%bv ltac:(repeat (first [left; reflexivity | right]))); exact R8
  | rewrite (KR 19%bv ltac:(repeat (first [left; reflexivity | right]))); exact R19
  | rewrite (KR 20%bv ltac:(repeat (first [left; reflexivity | right]))); exact R20
  | lazymatch type of HS with st_ok_pi _ _ ?Ez _ _ =>
      prreg HS (21%bv : bv 5) Z21; rewrite Z21; ld_ewstrip; exact E32 end
  | rewrite (KR 23%bv ltac:(repeat (first [left; reflexivity | right]))); exact R23
  | rewrite (KR 24%bv ltac:(repeat (first [left; reflexivity | right]))); exact R24
  | rewrite (KR 25%bv ltac:(repeat (first [left; reflexivity | right]))); exact R25
  | rewrite (KR 26%bv ltac:(repeat (first [left; reflexivity | right]))); exact R26
  | rewrite (KR 27%bv ltac:(repeat (first [left; reflexivity | right]))); exact R27
  | exact HP0 | exact HSA2 ].
- lazymatch type of HS with st_ok_pi _ _ ?Ez _ _ =>
    rewrite branch_geu_U,
      (U_atom Ez 35 (u_at (hs_table H now) (48 * i + 40) 8)
        ltac:(ld_ewstrip; exact E35) ltac:(change (2 ^ 64) with 18446744073709551616; lia)),
      (U_atom Ez 18 now ltac:(ld_ewstrip; rewrite E18, R18; reflexivity)
        ltac:(change (2 ^ 64) with 18446744073709551616; lia)) in Hc end.
  apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into HLT.
  pose proof (reac_hunt_step.hs_st2 (hs_table H now) i now ltac:(unfold last_of; exact HLT)) as HST2.
  paj_run_tok RUN HS HJ0 SHOK Bspan_HS; [hs_awr Usp|]. ld_keep Usp.
  psrr_branch_tok RUN BR HS SHOK Bspan_HS.
  + assert (NST : reac_disco_table_age_c.disco_stale (hs_table H now) i now = true).
    { rewrite HST2. apply Z.ltb_lt.
      lazymatch type of HS with st_ok_pi _ _ ?Ez _ _ =>
        rewrite branch_ltu_U,
          (U_atom Ez 8 5000000000 ltac:(ld_ewstrip; rewrite E8, R8; reflexivity)
            ltac:(change (2 ^ 64) with 18446744073709551616; lia)),
          (ld_sub_u Ez 18 35 now (u_at (hs_table H now) (48 * i + 40) 8)
            ltac:(ld_ewstrip; rewrite E18, R18; reflexivity) ltac:(ld_ewstrip; exact E35)
            ltac:(change (2 ^ 64) with 18446744073709551616; lia)
            ltac:(unfold last_of in HLT; lia)) in Hc end.
      apply Z.ltb_lt in Hc. unfold last_of. lia. }
    assert (HFD : reac_hunt_step.hs_fd h (hs_table H now) (sub H 412 6) now i = false).
    { unfold reac_hunt_step.hs_fd. rewrite NST. reflexivity. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ0 SHOK Bspan_HS (AF_both3_reac_hunt_step + 664); [hs_awr Usp|]. ld_keep Usp.
    lazymatch type of HS with st_ok_pi _ _ ?Ez _ _ =>
      assert (FAE : env_agree 32 (Ereg regs (ld_ex h now i H)) Ez)
        by (split; [intros n Hn; ld_ewstrip; apply EL; unfold A_TEXT; lia | reflexivity]) end.
    destruct (MIDK _ _ _ _ HS FAE ltac:(vm_compute; reflexivity) KEEP
      ltac:(exists lyc, Sc; split; [exact HJ0 | exact HPerm])) as (HM & HS8 & KR).
    rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS ltac:(vm_compute; reflexivity)).
    change (ss_pc _) with (AF_both3_reac_hunt_step + 664).
    apply (ld_tail POSTD 664 fq F0 C0 ly S W regs0 mem0 md0 ch h now hb hn i H _ _ _ NEXT
      ltac:(left; reflexivity) Hi NW HFD HPRE' HM HS8);
    [ rewrite (KR 8%bv ltac:(repeat (first [left; reflexivity | right]))); exact R8
    | rewrite (KR 19%bv ltac:(repeat (first [left; reflexivity | right]))); exact R19
    | rewrite (KR 20%bv ltac:(repeat (first [left; reflexivity | right]))); exact R20
    | rewrite (KR 23%bv ltac:(repeat (first [left; reflexivity | right]))); exact R23
    | rewrite (KR 24%bv ltac:(repeat (first [left; reflexivity | right]))); exact R24
    | rewrite (KR 25%bv ltac:(repeat (first [left; reflexivity | right]))); exact R25
    | rewrite (KR 26%bv ltac:(repeat (first [left; reflexivity | right]))); exact R26
    | rewrite (KR 27%bv ltac:(repeat (first [left; reflexivity | right]))); exact R27
    | exact HP0 | exact HSA2 ].
  + assert (NST : reac_disco_table_age_c.disco_stale (hs_table H now) i now = false).
    { rewrite HST2. apply Z.ltb_ge.
      lazymatch type of HS with st_ok_pi _ _ ?Ez _ _ =>
        rewrite branch_ltu_U,
          (U_atom Ez 8 5000000000 ltac:(ld_ewstrip; rewrite E8, R8; reflexivity)
            ltac:(change (2 ^ 64) with 18446744073709551616; lia)),
          (ld_sub_u Ez 18 35 now (u_at (hs_table H now) (48 * i + 40) 8)
            ltac:(ld_ewstrip; rewrite E18, R18; reflexivity) ltac:(ld_ewstrip; exact E35)
            ltac:(change (2 ^ 64) with 18446744073709551616; lia)
            ltac:(unfold last_of in HLT; lia)) in Hc end.
      apply Z.ltb_ge in Hc. unfold last_of. lia. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ0 SHOK Bspan_HS (AF_both3_reac_hunt_step + 564); [hs_awr Usp|]. ld_keep Usp.
    lazymatch type of HS with st_ok_pi _ _ ?Ez _ _ =>
      assert (FAE : env_agree 32 (Ereg regs (ld_ex h now i H)) Ez)
        by (split; [intros n Hn; ld_ewstrip; apply EL; unfold A_TEXT; lia | reflexivity]) end.
    destruct (MIDK _ _ _ _ HS FAE ltac:(vm_compute; reflexivity) KEEP
      ltac:(exists lyc, Sc; split; [exact HJ0 | exact HPerm])) as (HM & HS8 & KR).
    rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS ltac:(vm_compute; reflexivity)).
    change (ss_pc _) with (AF_both3_reac_hunt_step + 564).
    apply (ld_live POSTD fq F0 C0 ly S W regs0 mem0 md0 ch h now hb hn i H _ _ _ NEXT Hi NW NST HPRE' HM HS8);
    [ rewrite (KR 8%bv ltac:(repeat (first [left; reflexivity | right]))); exact R8
    | rewrite (KR 19%bv ltac:(repeat (first [left; reflexivity | right]))); exact R19
    | rewrite (KR 20%bv ltac:(repeat (first [left; reflexivity | right]))); exact R20
    | lazymatch type of HS with st_ok_pi _ _ ?Ez _ _ =>
        prreg HS (21%bv : bv 5) Z21; rewrite Z21; ld_ewstrip; exact E32 end
    | rewrite (KR 23%bv ltac:(repeat (first [left; reflexivity | right]))); exact R23
    | rewrite (KR 24%bv ltac:(repeat (first [left; reflexivity | right]))); exact R24
    | rewrite (KR 25%bv ltac:(repeat (first [left; reflexivity | right]))); exact R25
    | rewrite (KR 26%bv ltac:(repeat (first [left; reflexivity | right]))); exact R26
    | rewrite (KR 27%bv ltac:(repeat (first [left; reflexivity | right]))); exact R27
    | exact HP0 | exact HSA2 ].
Qed.

End hs_ld.
Section hs_lb.
Definition hs_lb_P (k : nat) (i : Z) (fq : YK11.FPState) : Prop :=
  forall (F0 : bvmap 5 word) (C0 : bv 32) ly S W (regs0 : bvmap 5 word) mem0 md0 ch
    (h now hb hn : Z) (H : list byte) (regs : bvmap 5 word) mem md,
  Z.of_nat k = n_of (hs_table H now) - i -> 0 <= i < n_of (hs_table H now) ->
  (forall j, 0 <= j < i -> reac_hunt_step.hs_fb h (hs_table H now) now j = false) ->
  hs_pre ly S W regs0 mem0 md0 ch h now hb hn H ->
  hs_mid F0 C0 fq regs0 ly S W mem0 md0 h now H regs mem md ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 120) 8 3 ->
  getr regs 8 = w64 (48 * i) -> getr regs 19 = w64 (h + 384) -> getr regs 20 = w64 i -> getr regs 21 = w64 432 ->
  getr regs 23 = w64 (SB_HS + (h + 384) / 8) -> getr regs 24 = w64 (2 ^ 64 - 1 - h) ->
  getr regs 25 = w64 2 -> getr regs 26 = w64 1 -> getr regs 27 = w64 5000000000 ->
  s32_at H 432 = 0 -> s32_at (hs_arb h H now) 0 <> 2 ->
  desk_geometry_live h (hs_table H now) (sub H 412 6) now = false ->
  s32_at H 420 = 0 -> ((now - u_at H 424 8) mod 2 ^ 64 <? REAC_HUNT_WINDOW_NS) = false ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 892))) mem (seg_rom SEGS)) md)
    (hs_post F0 C0 regs0 ly S W mem0 md0 h now H).
Definition hs_lb_stack : YP09.region := YP09.mkRegion (Some 2%nat) 0 128 0 0
  [YP09.mkChunk 8 (CVal 8 (SLit 3)); YP09.mkChunk 16 (CVal 8 (SOff 9 440))].
Definition hs_lb_n : YP09.region := YP09.mkRegion (Some 9%nat) 384 388 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 35 0))].
Definition hs_lb_e : YP09.region := YP09.mkRegion (Some 32%nat) 0 48 0 0
  [YP09.mkChunk 8 (CVal 4 (SOff 34 0)); YP09.mkChunk 40 (CVal 8 (SOff 33 0))].
Definition hs_lb_s7 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 384) (SLit 3)) (SOff 22 0).
Definition ss_lb : sstate := mkSS (AF_both3_reac_hunt_step + 892)
  (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 19%bv (SOff 9 384)) 21%bv (SLit 432)) 23%bv hs_lb_s7)
    25%bv (SLit 2)) 26%bv (SLit 1)) 27%bv (SLit 5000000000))
  [hs_lb_stack; hs_lb_n; hs_lb_e] None
  (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 0 336 0); (9%nat, mkAF 4096 HS_CEIL 3); (20%nat, mkAF 0 7 0);
    (22%nat, mkAF SB_HS SB_HS 0); (24%nat, mkAF (2 ^ 64 - 1 - HS_CEIL) (2 ^ 64 - 1 - 4096) 0); (32%nat, mkAF 4096 HS_CEIL 3)]
    [] [(SAlu ALU_ADD (SOff 9 0) (SOff 8 0), SOff 32 0)]).
Definition SH_LB : list shent := [mkSHE 9 0 480; mkSHE 32 0 48].
Definition hs_lb_ex (h i : Z) (T : list byte) : list word :=
  map w64 [h + 48 * i; last_of T i; u_at T (48 * i + 8) 4; u_at T 384 4].
Lemma hs_lb_bt : forall (b : bool) (P : Prop), (b = true <-> P) -> b = true -> P.
Proof. intros b P HP Hb. apply HP. exact Hb. Qed.
Lemma hs_lb_bf : forall (b : bool) (P : Prop), (b = true <-> P) -> b = false -> ~ P.
Proof. intros b P HP Hb X. apply HP in X. congruence. Qed.
Lemma hs_lb_c928 : forall E lst now, ew E 33 = Z_to_bv 64 lst -> ew E 18 = Z_to_bv 64 now ->
  0 <= lst < 2 ^ 64 -> 0 <= now < 2 ^ 64 ->
  (branch_taken BC_GEU (sv_denot E (SOff 33 0)) (sv_denot E (SOff 18 0)) = true <-> now <= lst).
Proof.
intros E lst now H33 H18 R1 R2. rewrite branch_geu_U, (U_atom E 33 lst H33 R1), (U_atom E 18 now H18 R2).
rewrite negb_true_iff, Z.ltb_ge. reflexivity.
Qed.
Lemma hs_lb_c936 : forall E lst now, ew E 33 = Z_to_bv 64 lst -> ew E 18 = Z_to_bv 64 now ->
  0 <= lst < now -> now < 2 ^ 64 ->
  (branch_taken BC_LTU (sv_denot E (SLit 5000000000))
     (sv_denot E (SAlu ALU_ADD (SOff 18 0) (SMd M_MUL (SOff 33 0) (SLit (-1))))) = true <-> 5000000000 < now - lst).
Proof.
intros E lst now H33 H18 R1 R2. rewrite branch_ltu_U, U_lit by lia.
rewrite U_SAlu, U_SMd, U_SLit, (U_atom E 18 now H18), (U_atom E 33 lst H33) by lia. cbn [zalu_raw zmd_raw].
assert (X : zcanon (now + zcanon (lst * zcanon (-1))) = now - lst).
{ unfold zcanon, M64. rewrite Zplus_mod_idemp_r. replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  replace (now + lst * (2 ^ 64 - 1)) with ((now - lst) + lst * 2 ^ 64) by ring. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
rewrite X. apply Z.ltb_lt.
Qed.
Lemma hs_lb_crole : forall E (T : list byte) i c, ew E 34 = Z_to_bv 64 (u_at T (48 * i + 8) 4) ->
  0 <= u_at T (48 * i + 8) 4 < 2 ^ 32 -> 0 <= c < 2 ^ 31 ->
  (branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff 34 0))) (sv_denot E (SLit c)) = true <-> role_of_e T i = c).
Proof. intros E T i c Hk Hu Hc. rewrite (proj1 (hs_br32 E 34 _ c Hk Hu Hc)). apply Z.eqb_eq. Qed.
Lemma hs_lb_ckind : forall E kd, ew E 40 = Z_to_bv 64 kd -> 0 <= kd < 2 ^ 64 ->
  (branch_taken BC_EQ (sv_denot E (SOff 40 0)) (sv_denot E (SLit 2)) = true <-> kd = 2).
Proof. intros E kd Hk Hr. rewrite branch_eq_U, (U_atom E 40 kd Hk Hr), U_lit by lia. apply Z.eqb_eq. Qed.
Lemma hs_lb_cn : forall E (T : list byte) j, ew E 20 = Z_to_bv 64 j -> 0 <= j <= 7 ->
  ew E 35 = Z_to_bv 64 (u_at T 384 4) -> 0 <= u_at T 384 4 < 2 ^ 32 ->
  (branch_taken BC_LT (sv_denot E (SOff 20 1)) (sv_denot E (SExt true 32 (SOff 35 0))) = true <-> j + 1 < n_of T).
Proof.
intros E T j H20 Hj H35 Hu. pose proof (hs_sw32 (u_at T 384 4)) as Hs. cbn [branch_taken]. unfold bv_lts.
change (bv_signed (sv_denot E (SOff 20 1))) with (Sg E (SOff 20 1)).
change (bv_signed (sv_denot E (SExt true 32 (SOff 35 0)))) with (Sg E (SExt true 32 (SOff 35 0))).
rewrite !S_of_U, (U_atom_off E 20 j 1 H20) by lia. rewrite (hs_U32 E 35 _ H35 Hu). rewrite (hs_sw64_zc (bv_swrap 32 _)) by lia.
assert (X : bv_swrap 64 (j + 1) = j + 1).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia. }
rewrite X. apply Z.ltb_lt.
Qed.
Lemma hs_lb_v1 : forall h H now i, s32_at H 432 = 0 -> s32_at (hs_arb h H now) 0 <> 2 ->
  desk_geometry_live h (hs_table H now) (sub H 412 6) now = false -> s32_at H 420 = 0 ->
  ((now - u_at H 424 8) mod 2 ^ 64 <? REAC_HUNT_WINDOW_NS) = false ->
  0 <= i < n_of (hs_table H now) -> reac_hunt_step.hs_fb h (hs_table H now) now i = true -> hs_verdict h H now = 1.
Proof.
intros h H now i P0 S2 DGL SL0 WC Hi FB. unfold hs_verdict. rewrite P0, reac_hunt_step.hs_dm_unp.
replace (s32_at (hs_arb h H now) 0 =? 2) with false by (symmetry; apply Z.eqb_neq; exact S2).
rewrite DGL, SL0, WC. rewrite (reac_hunt_step.hs_bp_true h (hs_table H now) now i Hi FB). reflexivity.
Qed.
Lemma hs_lb_v0 : forall h H now, s32_at H 432 = 0 -> s32_at (hs_arb h H now) 0 <> 2 ->
  desk_geometry_live h (hs_table H now) (sub H 412 6) now = false -> s32_at H 420 = 0 ->
  ((now - u_at H 424 8) mod 2 ^ 64 <? REAC_HUNT_WINDOW_NS) = false ->
  (forall j, 0 <= j < n_of (hs_table H now) -> reac_hunt_step.hs_fb h (hs_table H now) now j = false) ->
  hs_verdict h H now = 0.
Proof.
intros h H now P0 S2 DGL SL0 WC NF. unfold hs_verdict. rewrite P0, reac_hunt_step.hs_dm_unp.
replace (s32_at (hs_arb h H now) 0 =? 2) with false by (symmetry; apply Z.eqb_neq; exact S2).
rewrite DGL, SL0, WC. rewrite (reac_hunt_step.hs_bp_false h (hs_table H now) now NF). reflexivity.
Qed.
Lemma hs_lb_s7_val : forall E h, ew E 9 = Z_to_bv 64 h -> 0 <= h <= HS_CEIL -> ew E 22 = Z_to_bv 64 SB_HS ->
  sv_denot E hs_lb_s7 = w64 (SB_HS + (h + 384) / 8).
Proof.
intros E h H9 Hh H22. rewrite denot_lit_U. unfold w64. f_equal. unfold hs_lb_s7, HS_CEIL, SB_HS in *.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E 9 h 384 H9) by lia. rewrite (U_atom E 22 _ H22) by lia.
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Q : 0 <= (h + 384) / 8 <= 140737479966720) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
unfold zcanon, M64. rewrite (Z.mod_small ((h + 384) / 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma hs_lb_inv_fq : forall F0 C0 (fa fb : YK11.FPState) regs0 ly S W mem0 md0 h now H mem md,
  hs_inv F0 C0 fa regs0 ly S W mem0 md0 h now H mem md ->
  freg_kept (@YK11.fp_regs fa) (@YK11.fp_regs fb) -> hs_fc (@YK11.fp_csr fa) fb ->
  hs_inv F0 C0 fb regs0 ly S W mem0 md0 h now H mem md.
Proof.
intros F0 C0 fa fb regs0 ly S W mem0 md0 h now H mem md (HJ & HM & HB & HS & HR & HF & HC) FK FC.
split; [exact HJ|]. split; [exact HM|]. split; [exact HB|]. split; [exact HS|]. split; [exact HR|].
split; [exact (reac_hunt_step.hs_freg_trans _ _ _ HF FK) | exact (hs_fc_apost C0 fa fb HC FC)].
Qed.
Lemma hs_lb_keep_call : forall W sp0 (mem m1 m2 : word -> option byte) lo hi,
  hs_keep_p W sp0 mem m1 -> (forall y : word, ~ (lo <= bv_unsigned y < hi) -> m2 y = m1 y) ->
  alloc_ceiling <= lo -> hi <= sp0 - 104 -> hs_keep_p W sp0 mem m2.
Proof.
intros W sp0 mem m1 m2 lo hi K1 K2 Hlo Hhi a Ha Hb. rewrite <- (K1 a Ha Hb).
apply (sk_view_kept (w_H W) m1 m2 lo hi a K2). rewrite Z.mod_small by lia. lia.
Qed.
Lemma hs_lb_vm : forall (m : word -> option byte) h H now k n,
  garr8 SEGS m h (map (fun b : byte => bv_unsigned b) (hs_blk h H now)) -> length (hs_table H now) = 400%nat ->
  0 <= k -> (Z.to_nat k + n <= 400)%nat -> val_mem SEGS m (h + k) n (u_at (hs_table H now) k n).
Proof.
intros m h H now k n HB LT Hk Hn. unfold u_at. rewrite <- (hs_blk_T h H now k n LT Hk Hn).
apply (hs_vm SEGS m h (hs_blk h H now) k n HB Hk). unfold hs_blk. rewrite !length_app, LT. lia.
Qed.
Lemma hs_lb_urange : forall (T : list byte) k n, length T = 400%nat -> 0 <= k -> (Z.to_nat k + n <= 400)%nat ->
  0 <= u_at T k n < 2 ^ (8 * Z.of_nat n).
Proof.
intros T k n LT Hk Hn. unfold u_at. pose proof (disco_table.ble_range (sub T k n)) as R.
rewrite disco_table.length_sub in R by (rewrite ?LT; lia). exact R.
Qed.
Lemma hs_lb_s32u : forall u, 0 <= u < 2 ^ 32 -> 0 <= bv_swrap 32 u < 2 ^ 31 -> bv_swrap 32 u = u.
Proof.
intros u Hu Hs. unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 32) with (2 ^ 31) in *.
change (bv_modulus 32) with (2 ^ 32) in *. Z.div_mod_to_equations. lia.
Qed.
Ltac lb_app L Hc := first [apply (hs_lb_bt _ _ L) in Hc | apply (hs_lb_bf _ _ L) in Hc].
Ltac lb_conv :=
  lazymatch goal with
  | Hc : branch_taken BC_GEU (sv_denot ?E (SOff 33 0)) (sv_denot ?E (SOff 18 0)) = _ |- _ =>
    lb_app (hs_lb_c928 E _ _ ltac:(eassumption) ltac:(eassumption) ltac:(lia) ltac:(lia)) Hc
  | Hc : branch_taken BC_LTU (sv_denot ?E (SLit 5000000000)) _ = _ |- _ =>
    lb_app (hs_lb_c936 E _ _ ltac:(eassumption) ltac:(eassumption) ltac:(lia) ltac:(lia)) Hc
  | Hc : branch_taken BC_EQ (sv_denot ?E (SExt true 32 (SOff 34 0))) (sv_denot ?E (SLit ?c)) = _ |- _ =>
    lb_app (hs_lb_crole E _ _ c ltac:(eassumption) ltac:(eassumption) ltac:(lia)) Hc
  | Hc : branch_taken BC_EQ (sv_denot ?E (SOff 40 0)) (sv_denot ?E (SLit 2)) = _ |- _ =>
    lb_app (hs_lb_ckind E _ ltac:(eassumption) ltac:(eassumption)) Hc
  | Hc : branch_taken BC_LT (sv_denot ?E (SOff 20 1)) (sv_denot ?E (SExt true 32 (SOff 35 0))) = _ |- _ =>
    lb_app (hs_lb_cn E _ _ ltac:(eassumption) ltac:(lia) ltac:(eassumption) ltac:(eassumption)) Hc
  end.
Ltac lb_seg runto Usp stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_to_tok runto HS HJ SHOK Bspan_HS stop; [hs_awr Usp|]; hs_keep Usp
  end.
Ltac lb_go run runto br Usp :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ ?ss _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    let p := eval vm_compute in (ss_pc ss) in
    lazymatch p with
    | 30792%Z => idtac
    | 31416%Z => idtac
    | _ =>
      let st1 := lazymatch p with 31536%Z => constr:(31416%Z) | _ => constr:(30792%Z) end in
      psrr_branch_tok run br HS SHOK Bspan_HS;
      [ lb_conv; lb_seg runto Usp st1; lb_go run runto br Usp
      | lb_conv; lb_seg runto Usp 30792%Z; lb_go run runto br Usp ]
    end
  | _ => idtac
  end.
Ltac lb_fb :=
  lazymatch goal with |- reac_hunt_step.hs_fb ?h ?T ?n ?j = _ =>
    unfold reac_hunt_step.hs_fb;
    destruct (Z_le_gt_dec n (last_of T j));
    [rewrite (reac_hunt_step.hs_st1 T j n) by lia | rewrite (reac_hunt_step.hs_st2 T j n) by lia];
    repeat match goal with
      | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
      | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
      end;
    cbn [negb andb orb]; first [reflexivity | exfalso; lia]
  end.
Section x.
Context {fx : YK11.FPState}.
Lemma hs_lb_slot3 : forall E ss (ms : machine_state) (W : world SEGS) r sp,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) 0 = Some r ->
  YP09.r_base r = Some 2%nat -> In (YP09.mkChunk 8 (CVal 8 (SLit 3))) (YP09.r_chunks r) ->
  bv_unsigned (ew E 2) = sp -> val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (sp + 8) 8 3.
Proof.
intros E ss ms W r sp HS Hn Hb Hc Hsp.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS Hn) as (_ & _ & _ & RC).
rewrite Forall_forall in RC. specialize (RC _ Hc). cbn [ms_mem restrict] in RC. rewrite Hb in RC. cbn [base_val] in RC. rewrite Hsp in RC.
apply (val_of_chunk_ok SEGS E _ _ 8 8 (SLit 3) 3) in RC; [exact RC | reflexivity | change (8 * Z.of_N 8) with 64; lia | lia].
Qed.
End x.
Section y.
Context {fx : YK11.FPState}.
Let RUN := paj_run (PL := PL_both3_0) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (PL := PL_both3_0) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Lemma hs_lb_callsk : forall F0 C0 ly S W (regs0 : bvmap 5 word) mem0 md0 ch (h now hb hn : Z) (H : list byte) (i : Z) lyc Sc
  (regsc : bvmap 5 word) memc mdc Q,
  hs_pre ly S W regs0 mem0 md0 ch h now hb hn H -> 0 <= i < n_of (hs_table H now) ->
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc Sc W memc mdc 0 ->
  Permutation (ablocks B lyc Sc) (ablocks B ly S) ->
  hs_inv F0 C0 fx regs0 ly S W mem0 md0 h now H memc mdc ->
  getr regsc 1 = Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 988)) ->
  spZ regsc = spZ regs0 - 128 -> getr regsc 3 = getr regs0 3 -> getr regsc 4 = getr regs0 4 ->
  getr regsc 8 = Z_to_bv 64 (48 * i) -> getr regsc 10 = Z_to_bv 64 (h + 48 * i) ->
  getr regsc 11 = Z_to_bv 64 now -> getr regsc 12 = Z_to_bv 64 0 ->
  (forall (fq' : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
     freg_kept (@YK11.fp_regs fx) (@YK11.fp_regs fq') -> hs_fc (@YK11.fp_csr fx) fq' ->
     ajournal SEGS B REAC_SENDER_KIND_STK (spZ regs0 - 128) [] lyc Sc W memc mdc [] ly2 S2 W mem2 md2 0 ->
     aregs_preserved regsc regs2 ->
     getr regs2 10 = w64 (hs_kind h (hs_table H now) now i) ->
     Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
     (forall a : word, ~ (spZ regs0 - 128 - REAC_SENDER_KIND_STK <= bv_unsigned a < spZ regs0 - 128) -> mem2 a = memc a) ->
     SRr SEGS W (mkCfg (mkst (fx := fq') regs2 (getr regsc 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst (fx := fx) regsc (Z_to_bv 64 (BASE + AF_both3_reac_sender_kind)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H i lyc Sc regsc memc mdc Q HPRE Hi HJ HPerm HINV Q1 Qsp Q3 Q4 Q8 Q10 Q11 Q12 K.
destruct HPRE as (HPRE0 & HROD & Hnow & Hh0 & Hh8 & Hin & Hhb & Hhe & HOK).
destruct HINV as (_ & (LT & TOK & LA) & HBLK & _ & (RT1 & RT2 & RT3 & RT4) & _ & _).
pose proof HPRE0 as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _).
assert (Hinc : In (hb, hn) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc hb hn HAR Hinc) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & Hbpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ hb hn HAR Hinc) as Hbimg.
pose proof TOK as (T1 & T2 & _). unfold tbl_T1 in T1.
pose proof (T2 i Hi) as RL.
pose proof (pa_base_lo (PL := PL_both3_0) (PI := PI)) as HBlo. pose proof (@pa_B_ok _ _ PI) as HBok. unfold YImgTop.IMG_LO in HBlo.
pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as Rsp0. change (bv_modulus 64) with (2 ^ 64) in Rsp0. fold (spZ regs0) in Rsp0.
assert (HCE : h + 480 <= HS_CEIL) by (unfold HS_CEIL; lia).
assert (Ri : 0 <= i <= 7) by lia.
pose proof (hs_lb_urange (hs_table H now) (48 * i + 8) 4 LT ltac:(lia) ltac:(lia)) as RuR. change (8 * Z.of_nat 4) with 32 in RuR.
pose proof (hs_lb_urange (hs_table H now) (48 * i + 12) 1 LT ltac:(lia) ltac:(lia)) as Rd. change (8 * Z.of_nat 1) with 8 in Rd.
pose proof (hs_lb_urange (hs_table H now) (48 * i + 16) 1 LT ltac:(lia) ltac:(lia)) as Rs. change (8 * Z.of_nat 1) with 8 in Rs.
pose proof (hs_lb_urange (hs_table H now) (48 * i + 20) 4 LT ltac:(lia) ltac:(lia)) as Rc. change (8 * Z.of_nat 4) with 32 in Rc.
pose proof (hs_lb_urange (hs_table H now) (48 * i + 32) 8 LT ltac:(lia) ltac:(lia)) as Rf. change (8 * Z.of_nat 8) with 64 in Rf.
pose proof (hs_sw32 (u_at (hs_table H now) (48 * i + 8) 4)) as Hsw.
assert (RRu : role_of_e (hs_table H now) i = u_at (hs_table H now) (48 * i + 8) 4).
{ unfold role_of_e, s32_at in *. apply hs_lb_s32u; [exact RuR | lia]. }
eapply SRr_bind.
{ eapply (TSENDER fx lyc Sc W regsc memc mdc [] (h + 48 * i) now 0 (role_of_e (hs_table H now) i) (hd_of (hs_table H now) i)
    (reac_arbitrate_c.slots_of (hs_table H now) i) (reac_arbitrate_c.ch_of (hs_table H now) i) (fs_of (hs_table H now) i)).
  - eapply (afn_pre_at SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-128) [] HJ).
    + rewrite Qsp. lia.
    + reflexivity.
    + lia.
    + change REAC_SENDER_KIND_STK with 4224. lia.
    + change REAC_SENDER_KIND_STK with 4224. change REAC_HUNT_STEP_STK with 8464. lia.
    + rewrite Q1. apply ret_ok_codeptr_v; [unfold AF_both3_reac_hunt_step; lia | reflexivity].
    + unfold raZ. rewrite Q1, unsigned_lit_small by (unfold AF_both3_reac_hunt_step; lia). unfold AF_both3_reac_hunt_step. lia.
    + rewrite Q3. exact Hgp.
    + rewrite Q4. exact Htp.
    + unfold s0Z. rewrite Q8, unsigned_lit_small by lia. apply achain_low. lia.
  - exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD).
  - exact Q10.
  - lia.
  - replace (h + 48 * i) with (h + (6 * i) * 8) by ring. rewrite Z_mod_plus_full. exact Hh8.
  - exact Q11.
  - exact Hnow.
  - exact Q12.
  - lia.
  - intros _. split; [lia|]. split; [apply (in_app_sub hb (req_size hn)); [exact Hbh_ia | lia | lia | lia]|].
    split; [unfold off_img in *; lia|].
    split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc hb hn (h + 48 * i + 8) 32 HAR Hinc ltac:(lia) ltac:(lia))|].
    split; [intros a Ha; exact (proj1 (Hbpres a ltac:(lia)))|].
    split; [unfold role_of_e, s32_at; lia|].
    split; [exact Rd|]. split; [exact Rs|]. split; [exact Rc|]. split; [exact Rf|].
    split; [rewrite RRu; replace (h + 48 * i + 8) with (h + (48 * i + 8)) by lia; exact (hs_lb_vm _ h H now (48 * i + 8) 4 HBLK LT ltac:(lia) ltac:(lia))|].
    split; [replace (h + 48 * i + 12) with (h + (48 * i + 12)) by lia; exact (hs_lb_vm _ h H now (48 * i + 12) 1 HBLK LT ltac:(lia) ltac:(lia))|].
    split; [replace (h + 48 * i + 16) with (h + (48 * i + 16)) by lia; exact (hs_lb_vm _ h H now (48 * i + 16) 1 HBLK LT ltac:(lia) ltac:(lia))|].
    split; [replace (h + 48 * i + 20) with (h + (48 * i + 20)) by lia; exact (hs_lb_vm _ h H now (48 * i + 20) 4 HBLK LT ltac:(lia) ltac:(lia))|].
    replace (h + 48 * i + 32) with (h + (48 * i + 32)) by lia. exact (hs_lb_vm _ h H now (48 * i + 32) 8 HBLK LT ltac:(lia) ltac:(lia)).
  - exact RT1.
  - exact RT2.
  - exact RT3.
  - exact RT4. }
cbv beta. intros W2 c2 _ (fqw & FK & FC & fq' & ly2 & S2 & regs2 & mem2 & md2 & Hcf & Hfr & Hcsr & HJm & HPm & HAm & Hpm & HWm & Km).
subst c2 W2. rewrite Qsp in HJm, Km.
exact (K fq' ly2 S2 regs2 mem2 md2 (hs_fk_apost (@YK11.fp_regs fx) fqw fq' FK Hfr)
  (hs_fc_apost (@YK11.fp_csr fx) fqw fq' (or_introl FC) Hcsr) HJm HPm HAm Hpm Km).
Qed.
Lemma hs_lb_step : forall (k : nat) (i : Z), (forall i' fq', hs_lb_P k i' fq') -> hs_lb_P (S k) i fx.
Proof.
intros k i IH F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H regs mem md Hk Hi NB HPRE HMID V120 R8 R19 R20 R21 R23 R24
  R25 R26 R27 P0 S2 DGL SL0 WC.
pose proof HPRE as (HPRE0 & HROD & Hnow & Hh0 & Hh8 & Hin & Hhb & Hhe & HOK).
pose proof HMID as (HINV & HSPILL & R2 & R3 & R4 & R9 & R18 & R22).
pose proof HINV as ((lyc & Sc & HJ & HPerm) & HMOD & HBLK & HSAV & HRATES & HFK & HCSR).
pose proof HPRE0 as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof HJ as (HAR & _).
assert (Hinc : In (hb, hn) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
destruct (al_blocks _ _ LAWS lyc Sc W mem md hb hn HAR Hinc) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & Hbpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ hb hn HAR Hinc) as Hbimg.
pose proof HMOD as (LT & TOK & LA).
pose proof HOK as (LH & _ & LOK & V0R).
pose proof TOK as (T1 & T2 & _). unfold tbl_T1 in T1.
assert (WS : REAC_HUNT_STEP_STK = 8464) by reflexivity.
pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as Rsp0. change (bv_modulus 64) with (2 ^ 64) in Rsp0. fold (spZ regs0) in Rsp0.
assert (Hi7 : 0 <= i <= 7) by lia.
assert (HCE : h + 480 <= HS_CEIL) by (unfold HS_CEIL; lia).
pose proof (hs_lb_urange (hs_table H now) (48 * i + 8) 4 LT ltac:(lia) ltac:(lia)) as RuR. change (8 * Z.of_nat 4) with 32 in RuR.
pose proof (hs_lb_urange (hs_table H now) 384 4 LT ltac:(lia) ltac:(lia)) as RuN. change (8 * Z.of_nat 4) with 32 in RuN.
pose proof (hs_lb_urange (hs_table H now) (48 * i + 40) 8 LT ltac:(lia) ltac:(lia)) as R33. change (8 * Z.of_nat 8) with 64 in R33.
fold (last_of (hs_table H now) i) in R33.
remember (Eimg (Ereg regs (hs_lb_ex h i (hs_table H now)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (hs_lb_ex h i (hs_table H now))) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (X2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 128))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (X3 : ew E 3 = getr regs0 3) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact R3).
assert (X4 : ew E 4 = getr regs0 4) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact R4).
assert (X8 : ew E 8 = Z_to_bv 64 (48 * i)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (X9 : ew E 9 = Z_to_bv 64 h) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (X18 : ew E 18 = Z_to_bv 64 now) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (X20 : ew E 20 = Z_to_bv 64 i) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact R20).
assert (X22 : ew E 22 = Z_to_bv 64 SB_HS) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (X24 : ew E 24 = Z_to_bv 64 (2 ^ 64 - 1 - h))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (hs_lb_ex h i (hs_table H now)) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as X32. pose proof (EX 1%nat ltac:(lia)) as X33.
pose proof (EX 2%nat ltac:(lia)) as X34. pose proof (EX 3%nat ltac:(lia)) as X35.
cbn [Nat.add nth hs_lb_ex map] in X32, X33, X34, X35. unfold w64 in X32, X33, X34, X35.
assert (HAE : env_agree 32 (Ereg regs (hs_lb_ex h i (hs_table H now))) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (HRO : regs_ok E sr_atoms regs) by (subst E; apply regs_ok_Eimg_Ereg).
clear HE EL EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 128) by (rewrite X2; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = 48 * i) by (rewrite X8; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = h) by (rewrite X9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = i) by (rewrite X20; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = h + 48 * i) by (rewrite X32; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_lb
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 892))) mem (seg_rom SEGS)))).
{ rewrite YA0o.restrict_mkst_fx. unfold ss_lb. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
      [exact HRO | intros X; discriminate X | ] | intros X; discriminate X | ] | intros X; discriminate X | ]
      | intros X; discriminate X | ] | intros X; discriminate X | ] | intros X; discriminate X | ].
    + rewrite R19, denot_lit_U, (U_atom_off E 9 h 384 X9) by lia. reflexivity.
    + rewrite R21. reflexivity.
    + rewrite R23. symmetry. apply hs_lb_s7_val; [exact X9 | lia | exact X22].
    + rewrite R25. reflexivity.
    + rewrite R26. reflexivity.
    + rewrite R27. reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold region_ok, hs_lb_stack. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E _ _ 8 8 (SLit 3) 3); [reflexivity | change (8 * Z.of_N 8) with 64; lia | lia |].
        replace (spZ regs0 - 128 + 8) with (spZ regs0 - 120) by lia. exact V120.
      * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 9 440) (h + 440));
          [cbn [sv_denot]; rewrite U9; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia |].
        replace (spZ regs0 - 128 + 16) with (spZ regs0 - 112) by lia. exact HSPILL.
    + unfold region_ok, hs_lb_n. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 384 4 (SOff 35 0) (u_at (hs_table H now) 384 4));
        [cbn [sv_denot]; rewrite X35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact RuN | lia |].
      exact (hs_lb_vm _ h H now 384 4 HBLK LT ltac:(lia) ltac:(lia)).
    + unfold region_ok, hs_lb_e. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E _ _ 8 4 (SOff 34 0) (u_at (hs_table H now) (48 * i + 8) 4));
          [cbn [sv_denot]; rewrite X34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact RuR | lia |].
        replace (h + 48 * i + 8) with (h + (48 * i + 8)) by lia. exact (hs_lb_vm _ h H now (48 * i + 8) 4 HBLK LT ltac:(lia) ltac:(lia)).
      * apply (chunk_ok_val SEGS E _ _ 40 8 (SOff 33 0) (last_of (hs_table H now) i));
          [cbn [sv_denot]; rewrite X33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact R33 | lia |].
        replace (h + 48 * i + 40) with (h + (48 * i + 40)) by lia. exact (hs_lb_vm _ h H now (48 * i + 40) 8 HBLK LT ltac:(lia) ltac:(lia)).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region, hs_lb_stack, hs_lb_n, hs_lb_e.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U8, U9, U20, U32, X22, X24. unfold SB_HS, HS_CEIL in *. rewrite !unsigned_lit_small by lia.
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      repeat split. all: try (exact I || lia). all: Z.div_mod_to_equations; lia.
    + cbn [f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 9 h X9), (U_atom E 8 (48 * i) X8), (U_atom E 32 _ X32) by lia.
      apply zcanon_id. unfold M64. lia. }
assert (SHOK : sh_ok SEGS Bx_HS SH_LB E (mrestrict (w_H W) mem)).
{ unfold sh_ok, SH_LB. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_ok_of_range SEGS (w_H W) mem E Bx_HS 9 hb (req_size hn) h 0 480).
    + exact (range_addressable_of_block SEGS B LAWS lyc Sc W mem md hb hn hb (req_size hn) HAR Hinc ltac:(lia) ltac:(lia)).
    + unfold Bx_HS. rewrite (U_atom E 22 SB_HS X22) by (unfold SB_HS; lia). reflexivity.
    + rewrite (U_atom E 9 h X9) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W) mem E Bx_HS 32 hb (req_size hn) (h + 48 * i) 0 48).
    + exact (range_addressable_of_block SEGS B LAWS lyc Sc W mem md hb hn hb (req_size hn) HAR Hinc ltac:(lia) ltac:(lia)).
    + unfold Bx_HS. rewrite (U_atom E 22 SB_HS X22) by (unfold SB_HS; lia). reflexivity.
    + rewrite (U_atom E 32 _ X32) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (KEEP : hs_keep_p W (spZ regs0) mem mem) by (intros a _ _; reflexivity).
clear HRO.
lb_seg RUNTO Usp 30792%Z.
lb_go RUN RUNTO BR Usp.
all: lazymatch goal with HSc : st_ok _ _ (setpc _ (pa_sigma AS_reac_sender_kind)) _ |- _ => idtac | _ => shelve end.
all: lazymatch goal with HSc : st_ok _ _ (setpc _ (pa_sigma AS_reac_sender_kind)) (restrict _ ?msc) |- _ =>
  prreg HSc (1%bv : bv 5) C1r; prreg HSc (2%bv : bv 5) C2r; prreg HSc (3%bv : bv 5) C3r; prreg HSc (4%bv : bv 5) C4r;
  prreg HSc (8%bv : bv 5) C8r; prreg HSc (10%bv : bv 5) C10r; prreg HSc (11%bv : bv 5) C11r; prreg HSc (12%bv : bv 5) C12r;
  pose proof (YA0o.st_ok_restrict_mkst SEGS _ _ _ _ HSc eq_refl) as Hms;
  rewrite Hms in HSc |- *; clear Hms; cbn [ss_pc setpc] in HSc |- *;
  rewrite YA0o.restrict_mkst_fx in HSc; rewrite pa_sigma_reac_sender_kind;
  assert (Qsp : spZ (ms_regs msc) = spZ regs0 - 128)
    by (unfold spZ at 1; rewrite C2r, X2; apply unsigned_lit_small; lia);
  pose proof (hs_inv_kept F0 C0 fx regs0 ly S W mem0 md0 ch h now hb hn H mem md (ms_mem msc) _ HPRE HINV KEEP
    (ex_intro _ _ (ex_intro _ _ (conj HJ HPerm)))) as HINVc
end.
all: eapply (hs_lb_callsk F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H i _ _ _ _ _ _ HPRE Hi HJ HPerm HINVc);
  [ rewrite C1r; reflexivity | exact Qsp | rewrite C3r; exact X3 | rewrite C4r; exact X4 | rewrite C8r; exact X8
  | rewrite C10r; exact X32 | rewrite C11r; exact X18 | exact C12r | ].
all: intros fq' lyq Sq regs2 mem2 md2 FK FC HJm HPm HAm Hpm Km.
all: pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJm
  ltac:(rewrite WS; change REAC_SENDER_KIND_STK with 4224; lia) ltac:(lia) ltac:(intros a X; exfalso; exact (inFP_nil _ X))) as HJ3.
all: cbn [app] in HJ3; change (0 + 0) with 0 in HJ3.
all: lazymatch goal with HSc : st_ok _ _ _ _ |- _ => pose proof (FpStep.fp_st_ok_fx SEGS fx fq' _ _ _ _ _ _ HSc) as HSq; clear HSc end.
all: jafter_call_keep_pi HSq 36%nat regs2 (mrestrict (w_H W) mem2) HPm [0; 1]%nat HS2.
all: match type of HS2 with ?tq -> _ => assert (HRK : tq) by
  (apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
   (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U9; intros a Ha;
    [ unfold mbyte, mrestrict; rewrite (Km (Z_to_bv 64 a)); [reflexivity|]; rewrite unsigned_lit_small by lia;
      change REAC_SENDER_KIND_STK with 4224; lia
    | exfalso; lia ])); specialize (HS2 HRK); clear HRK end.
all: clear HSq; rewrite <- YA0o.restrict_mkst_fx in HS2; rewrite C1r.
all: lazymatch type of HS2 with st_ok_pi _ _ (havoc ?Ex 36 ?ws) _ _ =>
  remember (havoc Ex 36 ws) as E' eqn:HE' in HS2;
  assert (OLD : forall n, (n < 36)%nat -> ew E' n = ew Ex n) by (intros n Hn; rewrite HE'; apply ew_havoc_old; exact Hn);
  assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [assumption | cbv; lia]);
  assert (X40 : ew E' 40 = getr regs2 10) by (rewrite HE'; reflexivity)
end.
all: rewrite HAm in X40; unfold w64 in X40.
all: rewrite <- (OLD 2%nat ltac:(lia)) in X2, Usp; rewrite <- (OLD 3%nat ltac:(lia)) in X3; rewrite <- (OLD 4%nat ltac:(lia)) in X4;
  rewrite <- (OLD 8%nat ltac:(lia)) in X8, U8; rewrite <- (OLD 9%nat ltac:(lia)) in X9, U9; rewrite <- (OLD 18%nat ltac:(lia)) in X18;
  rewrite <- (OLD 20%nat ltac:(lia)) in X20, U20; rewrite <- (OLD 22%nat ltac:(lia)) in X22; rewrite <- (OLD 24%nat ltac:(lia)) in X24;
  rewrite <- (OLD 32%nat ltac:(lia)) in X32, U32; rewrite <- (OLD 33%nat ltac:(lia)) in X33;
  rewrite <- (OLD 34%nat ltac:(lia)) in X34; rewrite <- (OLD 35%nat ltac:(lia)) in X35.
all: clear HE' OLD.
all: assert (Rkd : 0 <= hs_kind h (hs_table H now) now i < 2 ^ 64)
  by (unfold hs_kind; pose proof (reac_hunt_step.hs_sk_range (h + 48 * i) (role_of_e (hs_table H now) i) (hd_of (hs_table H now) i)
        (reac_arbitrate_c.slots_of (hs_table H now) i) (reac_arbitrate_c.ch_of (hs_table H now) i) (fs_of (hs_table H now) i) now); lia).
all: pose proof (hs_lb_inv_fq F0 C0 fx fq' regs0 ly S W mem0 md0 h now H mem md HINV FK FC) as HINV2; clear HINV; rename HINV2 into HINV.
all: pose proof (hs_lb_keep_call W (spZ regs0) mem _ mem2 _ _ KEEP Km ltac:(change REAC_SENDER_KIND_STK with 4224; lia) ltac:(lia)) as KEEP2;
  clear KEEP; rename KEEP2 into KEEP.
all: pose proof (Permutation_trans Hpm HPerm) as HPerm2; clear HPerm; rename HPerm2 into HPerm.
all: clear HJ HJm HINVc; rename HJ3 into HJ.
all: assert (Hinc2 : In (hb, hn) (ablocks B lyq Sq)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
all: clear SHOK.
all: assert (SHOK : sh_ok SEGS Bx_HS SH_LB E' (mrestrict (w_H W) mem2)) by
  (unfold sh_ok, SH_LB; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
   [ apply (shent_ok_of_range SEGS (w_H W) mem2 E' Bx_HS 9 hb (req_size hn) h 0 480);
     [ exact (range_addressable_of_block SEGS B LAWS lyq Sq W mem2 md2 hb hn hb (req_size hn) (proj1 HJ) Hinc2 ltac:(lia) ltac:(lia))
     | unfold Bx_HS; rewrite (U_atom E' 22 SB_HS X22) by (unfold SB_HS; lia); reflexivity
     | rewrite (U_atom E' 9 h X9) by lia; reflexivity | lia | lia
     | intros x Hx; unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia ]
   | apply (shent_ok_of_range SEGS (w_H W) mem2 E' Bx_HS 32 hb (req_size hn) (h + 48 * i) 0 48);
     [ exact (range_addressable_of_block SEGS B LAWS lyq Sq W mem2 md2 hb hn hb (req_size hn) (proj1 HJ) Hinc2 ltac:(lia) ltac:(lia))
     | unfold Bx_HS; rewrite (U_atom E' 22 SB_HS X22) by (unfold SB_HS; lia); reflexivity
     | rewrite (U_atom E' 32 _ X32) by lia; reflexivity | lia | lia
     | intros x Hx; unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia ] ]).
all: rename HS2 into HS.
all: lb_seg (paj_run_to (fx := fq') (PL := PL_both3_0) (PI := PI) B LAWS) Usp 30792%Z.
all: lb_go (paj_run (fx := fq') (PL := PL_both3_0) (PI := PI) B LAWS) (paj_run_to (fx := fq') (PL := PL_both3_0) (PI := PI) B LAWS)
  (paj_branch (fx := fq') (PI := PI)) Usp.
Unshelve.
all: lazymatch goal with HS : st_ok_pi _ _ _ ?ss _ |- _ => let p := eval vm_compute in (ss_pc ss) in
  lazymatch p with 30792%Z => idtac | _ => shelve end end.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HS) as Q11;
  let e := eval vm_compute in (sr_get (ss_regs ssx) 11%bv) in change (sr_get (ss_regs ssx) 11%bv) with e in Q11;
  cbn [ms_regs restrict mkst] in Q11; rewrite denot_lit_U in Q11;
  pose proof (hs_spill_of Ex ssx msx W _ (spZ regs0 - 128) h HS eq_refl eq_refl
    ltac:(repeat (first [left; reflexivity | right])) Usp X9 ltac:(lia) ltac:(lia)) as SP
end.
all: prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
  prreg HS (9%bv : bv 5) Q9; prreg HS (18%bv : bv 5) Q18; prreg HS (22%bv : bv 5) Q22.
all: pmkst HS; change 30792 with (AF_both3_reac_hunt_step + 268).
all: eapply (hs_epi F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H _ _ _ _ HPRE);
  [ unfold hs_mid;
    split; [exact (hs_inv_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPRE HINV KEEP (ex_intro _ _ (ex_intro _ _ (conj HJ HPerm))))|];
    split; [replace (spZ regs0 - 112) with (spZ regs0 - 128 + 16) by lia; exact SP|];
    rewrite Q2, Q3, Q4, Q9, Q18, Q22, X2, X3, X4, X9, X18, X22; repeat split; reflexivity
  | exact Q11 | ].
all: first [rewrite U_lit by lia | rewrite (hs_U32 _ 34 _ X34 RuR)].
all: try (change (bv_swrap 32 (u_at (hs_table H now) (48 * i + 8) 4)) with (role_of_e (hs_table H now) i);
  match goal with Hr : role_of_e _ _ = 1 |- _ => rewrite Hr end; change (zcanon 1) with 1).
all: lazymatch goal with
  | |- 0 = _ => symmetry; apply (hs_lb_v0 h H now); try assumption;
      intros j Hj; destruct (Z.eq_dec j i) as [->|Hji]; [lb_fb | apply NB; lia]
  | |- 1 = _ => symmetry; apply (hs_lb_v1 h H now i); try assumption; first [lia | lb_fb]
  end.
Unshelve.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as Q23;
  let e := eval vm_compute in (sr_get (ss_regs ssx) 23%bv) in change (sr_get (ss_regs ssx) 23%bv) with e in Q23;
  cbn [ms_regs restrict mkst] in Q23;
  pose proof (hs_spill_of Ex ssx msx W _ (spZ regs0 - 128) h HS eq_refl eq_refl
    ltac:(repeat (first [left; reflexivity | right])) Usp X9 ltac:(lia) ltac:(lia)) as SP;
  pose proof (hs_lb_slot3 Ex ssx msx W _ (spZ regs0 - 128) HS eq_refl eq_refl
    ltac:(repeat (first [left; reflexivity | right])) Usp) as SL3
end.
all: prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
  prreg HS (9%bv : bv 5) Q9; prreg HS (18%bv : bv 5) Q18; prreg HS (22%bv : bv 5) Q22;
  prreg HS (8%bv : bv 5) Q8; prreg HS (19%bv : bv 5) Q19; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21;
  prreg HS (24%bv : bv 5) Q24; prreg HS (25%bv : bv 5) Q25; prreg HS (26%bv : bv 5) Q26; prreg HS (27%bv : bv 5) Q27.
all: pmkst HS; change 31416 with (AF_both3_reac_hunt_step + 892).
all: eapply (IH (i + 1) _ F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H _ _ _);
  [ lia | lia | intros j Hj; destruct (Z.eq_dec j i) as [->|Hji]; [lb_fb | apply NB; lia] | exact HPRE
  | unfold hs_mid;
    split; [exact (hs_inv_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPRE HINV KEEP (ex_intro _ _ (ex_intro _ _ (conj HJ HPerm))))|];
    split; [replace (spZ regs0 - 112) with (spZ regs0 - 128 + 16) by lia; exact SP|];
    rewrite Q2, Q3, Q4, Q9, Q18, Q22, X2, X3, X4, X9, X18, X22; repeat split; reflexivity
  | replace (spZ regs0 - 120) with (spZ regs0 - 128 + 8) by lia; exact SL3
  | rewrite Q8, U8; unfold w64; f_equal; lia
  | rewrite Q19, U9; reflexivity
  | rewrite Q20, U20; reflexivity
  | exact Q21
  | rewrite Q23; apply hs_lb_s7_val; [exact X9 | unfold HS_CEIL; lia | exact X22]
  | rewrite Q24, X24; reflexivity
  | exact Q25 | exact Q26 | exact Q27
  | exact P0 | exact S2 | exact DGL | exact SL0 | exact WC ].
Qed.
End y.
Theorem pb_hs_loopb : hs_loopb_stmt.
Proof.
unfold hs_loopb_stmt. intros k. induction k as [|k IH]; intros i fq.
- intros F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H regs mem md Hk Hi. lia.
- exact (hs_lb_step (fx := fq) k i IH).
Qed.
End hs_lb.
Section w1s.
Context {fx : YK11.FPState}.
Lemma hs_slot_of : forall E ss (ms : machine_state) (W : world SEGS) r sp off v z,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) 0 = Some r ->
  YP09.r_base r = Some 2%nat -> In (YP09.mkChunk off (CVal 8 v)) (YP09.r_chunks r) ->
  bv_unsigned (ew E 2) = sp -> sv_denot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (sp + off) 8 z.
Proof.
intros E ss ms W r sp off v z HS Hn Hb Hc Hsp Hv Hz.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS Hn) as (_ & _ & _ & RC).
rewrite Forall_forall in RC. specialize (RC _ Hc). cbn [ms_mem restrict] in RC. rewrite Hb in RC. cbn [base_val] in RC. rewrite Hsp in RC.
apply (val_of_chunk_ok SEGS E _ _ off 8 v z) in RC; [exact RC | exact Hv | change (8 * Z.of_N 8) with 64; lia | lia].
Qed.
End w1s.
Ltac hs_sl HS3 Usp3 HAE3 :=
  lazymatch goal with |- val_mem _ _ (spZ ?rg - 128 + ?off) 8 (bv_unsigned (getr ?rg ?r)) =>
    let o := eval vm_compute in (off - 128) in
    let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    replace (spZ rg - 128 + off) with (spZ rg + o) by lia;
    lazymatch type of HS3 with st_ok_pi _ _ ?E3 ?ss3 (restrict _ ?ms3) =>
      apply (hs_slot_of E3 ss3 ms3 _ _ (spZ rg) o (SOff k 0) _ HS3 eq_refl eq_refl
        ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])) Usp3);
      [ cbn [sv_denot]; rewrite (proj1 HAE3 k ltac:(lia)), (ew_Ereg_nat rg _ k r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr rg r)) as Hbr; change (bv_modulus 64) with (2 ^ 64) in Hbr; exact Hbr ]
    end
  end.
Section w2.
Context {fx : YK11.FPState}.
Let RUN := paj_run (PL := PL_both3_0) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (PL := PL_both3_0) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Lemma hs_xor_m1 : forall h, 0 <= h < 2 ^ 64 -> Z.lxor h (2 ^ 64 - 1) = 2 ^ 64 - 1 - h.
Proof.
intros h Hh. change (2 ^ 64 - 1) with (Z.ones 64).
rewrite <- (Z.mod_small h (2 ^ 64)) at 1 by lia.
transitivity (Z.land (Z.lnot h) (Z.ones 64)).
- apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases n 64) as [Hl|Hg].
  + rewrite Z.mod_pow2_bits_low by lia. rewrite Z.ones_spec_low by lia. destruct (Z.testbit h n); reflexivity.
  + rewrite Z.mod_pow2_bits_high by lia. rewrite Z.ones_spec_high by lia. destruct (Z.testbit h n); reflexivity.
- rewrite Z.land_ones by lia. unfold Z.lnot. change (Z.ones 64) with (2 ^ 64 - 1).
  rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Ltac hs_reg HS r :=
  let Q := fresh "Q" in pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as Q;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ =>
    let e := eval vm_compute in (sr_get (ss_regs ss1) r) in change (sr_get (ss_regs ss1) r) with e in Q end;
  rewrite Q, denot_lit_U; unfold w64; f_equal; clear Q.
Ltac hs_r0 :=
  eexists; split; [reflexivity | split; [reflexivity | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])]].
Ltac hs_leaf LEAF HS KEEP HJ :=
  lazymatch type of HS with st_ok_pi _ _ ?E0 ?ss1 _ =>
    let e := eval vm_compute in (sr_get (ss_regs ss1) 11%bv) in
    let Q := fresh "Q" in pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HS) as Q;
    change (sr_get (ss_regs ss1) 11%bv) with e in Q;
    apply (LEAF ss1 _ _ (U E0 e) HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(hs_r0) KEEP HJ
      ltac:(rewrite Q, denot_lit_U; reflexivity)); clear Q
  end.
Lemma hs_s2 : hs_postd_stmt -> hs_loopd_stmt -> forall F0 C0 ly S W (regs0 : bvmap 5 word) mem0 md0 ch (h now hb hn : Z) (H : list byte) (regs : bvmap 5 word) mem md,
  hs_pre ly S W regs0 mem0 md0 ch h now hb hn H ->
  hs_inv F0 C0 fx regs0 ly S W mem0 md0 h now H mem md ->
  getr regs 2 = w64 (spZ regs0 - 128) -> getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  getr regs 9 = w64 h -> getr regs 18 = w64 now -> getr regs 19 = w64 (h + 444) -> getr regs 20 = w64 (h + 412) ->
  getr regs 22 = w64 SB_HS ->
  SRr SEGS W (mkCfg (mkst (fx := fx) regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 132))) mem (seg_rom SEGS)) md)
    (hs_post F0 C0 regs0 ly S W mem0 md0 h now H).
Proof.
intros PD LD F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H regs mem md HPRE HINV R2 R3 R4 R9 R18 R19 R20 R22.
pose proof HPRE as HPRE'. pose proof HINV as HINV'.
destruct HPRE as (HPRE & HROD & Hnow & Hh0 & Hh8 & Hin & Hhb & Hhe & HOK).
destruct HINV as ((lyc & Sc & HJ & HPerm) & HMOD & HBLK & HSAV & HRATES & HFK & HCSR).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof HJ as (HAR & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (Hinc : In (hb, hn) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
destruct (al_blocks _ _ LAWS lyc Sc W mem md hb hn HAR Hinc) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & Hbpres & _).
pose proof HMOD as (LT & TOK & LA). pose proof HOK as (LH & _ & LOK & V0R).
assert (WS : REAC_HUNT_STEP_STK = 8464) by reflexivity.
pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as Rsp0. change (bv_modulus 64) with (2 ^ 64) in Rsp0. fold (spZ regs0) in Rsp0.
assert (LB : length (hs_blk h H now) = 480%nat).
{ unfold hs_blk. rewrite !length_app, LT, LA, length_skipn. rewrite !disco_table.length_sub by (rewrite ?LH; lia). rewrite LH. reflexivity. }
assert (VB : forall k n, 0 <= k -> (Z.to_nat k + n <= 480)%nat ->
  val_mem SEGS (mrestrict (w_H W) mem) (h + k) n (u_at (hs_blk h H now) k n))
  by (intros k n Hk Hn; apply hs_vm; [exact HBLK | exact Hk | rewrite LB; exact Hn]).
assert (UR : forall (L : list byte) k n, 0 <= k -> (Z.to_nat k + n <= length L)%nat -> 0 <= u_at L k n < 2 ^ (8 * Z.of_nat n)).
{ intros L k n Hk Hn. unfold u_at. pose proof (disco_table.ble_range (sub L k n)) as Rb.
  rewrite disco_table.length_sub in Rb by lia. exact Rb. }
remember (Eimg (Ereg regs (hs_s2_ex h now H))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (hs_s2_ex h now H)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E22 : ew E 22 = getr regs 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)).
assert (EX : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (hs_s2_ex h now H) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
cbn [Nat.add nth hs_s2_ex map] in E32, E33, E34, E35, E36, E37, E38, E39.
assert (HAE : env_agree 32 (Ereg regs (hs_s2_ex h now H)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (HRO : regs_ok E (sr_set (sr_set sr_atoms 19%bv (SOff 9 444)) 20%bv (SOff 9 412)) regs).
{ subst E. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate |] | discriminate |].
  - cbn [sv_denot]. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9, R19.
    unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - cbn [sv_denot]. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9, R20.
    unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
clear HE EL EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 128) by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (Uh : bv_unsigned (ew E 9) = h) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; lia).
assert (Usb : bv_unsigned (ew E 22) = SB_HS) by (rewrite E22, R22; unfold w64; apply unsigned_lit_small; unfold SB_HS; lia).
assert (U23 : U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 384) (SLit 3)) (SOff 22 0)) = SB_HS + (h + 384) / 8).
{ rewrite !U_SAlu, !U_SOff, U_SLit, Uh, Usb. cbn [zalu_raw].
  rewrite (zcanon_id (h + 384)) by (unfold M64; lia). change (Z.land (zcanon 3) 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite Z.add_0_r.
  rewrite (zcanon_id SB_HS) by (unfold M64, SB_HS; lia).
  rewrite (zcanon_id ((h + 384) / 8)) by (unfold M64; Z.div_mod_to_equations; lia).
  rewrite zcanon_id by (unfold M64, SB_HS; Z.div_mod_to_equations; lia). lia. }
assert (U24 : U E (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) = 2 ^ 64 - 1 - h).
{ rewrite U_SAlu, U_SOff, U_SLit, Uh, Z.add_0_r. cbn [zalu_raw]. rewrite (zcanon_id h) by (unfold M64; lia).
  change (zcanon (-1)) with (2 ^ 64 - 1). rewrite hs_xor_m1 by lia. apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok_pi SEGS VAL E ss_s2 (restrict (w_H W) (mkst (fx := fx) regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 132))) mem (seg_rom SEGS)))).
{ rewrite YA0o.restrict_mkst_fx. unfold ss_s2. apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, hs_s2_stack. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HJpres. lia.
    + unfold region_ok, hs_s2_h. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uh.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 432 4 (SOff 32 0) (u_at H 432 4)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply UR; rewrite ?LH; lia | lia |].
        unfold u_at at 1. rewrite <- (hs_blk_H h H now 432 4 LT LH) by lia. exact (VB 432 4%nat ltac:(lia) ltac:(lia)).
      * apply (chunk_ok_val SEGS E _ _ 436 4 (SOff 33 0) (u_at H 436 4)); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply UR; rewrite ?LH; lia | lia |].
        unfold u_at at 1. rewrite <- (hs_blk_H h H now 436 4 LT LH) by lia. exact (VB 436 4%nat ltac:(lia) ltac:(lia)).
      * apply (chunk_ok_val SEGS E _ _ 440 4 (SOff 34 0) (u_at H 440 4)); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply UR; rewrite ?LH; lia | lia |].
        unfold u_at at 1. rewrite <- (hs_blk_440 h H now LT LH). exact (VB 440 4%nat ltac:(lia) ltac:(lia)).
      * apply (chunk_ok_val SEGS E _ _ 420 4 (SOff 35 0) (u_at H 420 4)); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply UR; rewrite ?LH; lia | lia |].
        unfold u_at at 1. rewrite <- (hs_blk_H h H now 420 4 LT LH) by lia. exact (VB 420 4%nat ltac:(lia) ltac:(lia)).
      * apply (chunk_ok_val SEGS E _ _ 424 8 (SOff 36 0) (u_at H 424 8)); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply UR; rewrite ?LH; lia | lia |].
        unfold u_at at 1. rewrite <- (hs_blk_H h H now 424 8 LT LH) by lia. exact (VB 424 8%nat ltac:(lia) ltac:(lia)).
      * apply (chunk_ok_val SEGS E _ _ 384 4 (SOff 37 0) (u_at (hs_table H now) 384 4)); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply UR; rewrite ?LT; lia | lia |].
        unfold u_at at 1. rewrite <- (hs_blk_T h H now 384 4 LT) by lia. exact (VB 384 4%nat ltac:(lia) ltac:(lia)).
      * apply (chunk_ok_val SEGS E _ _ 444 4 (SOff 38 0) (u_at (hs_arb h H now) 0 4)); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply UR; rewrite ?LA; lia | lia |].
        unfold u_at at 1. replace 0 with (444 - 444) at 1 by lia. rewrite <- (hs_blk_A h H now 444 4 LT LH LA) by lia. exact (VB 444 4%nat ltac:(lia) ltac:(lia)).
      * apply (chunk_ok_val SEGS E _ _ 468 4 (SOff 39 0) (u_at (hs_arb h H now) 24 4)); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply UR; rewrite ?LA; lia | lia |].
        unfold u_at at 1. replace 24 with (468 - 444) at 1 by lia. rewrite <- (hs_blk_A h H now 468 4 LT LH LA) by lia. exact (VB 468 4%nat ltac:(lia) ltac:(lia)).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region, hs_s2_stack, hs_s2_h.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uh.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uh, E22, R22. unfold w64. rewrite unsigned_lit_small by (unfold SB_HS; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    unfold SB_HS, HS_CEIL. repeat split. all: try (exact I || lia). all: Z.div_mod_to_equations; lia. }
assert (SHOK : sh_ok SEGS Bx_HS SH_S2 E (mrestrict (w_H W) mem)).
{ unfold sh_ok, SH_S2. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E Bx_HS 9 hb (req_size hn) h 0 480).
  - exact (range_addressable_of_block SEGS B LAWS lyc Sc W mem md hb hn hb (req_size hn) HAR Hinc ltac:(lia) ltac:(lia)).
  - unfold Bx_HS. rewrite (U_atom E 22 SB_HS) by (first [rewrite E22, R22; reflexivity | unfold SB_HS; lia]). reflexivity.
  - rewrite (U_atom E 9 h) by (first [rewrite E9, R9; reflexivity | lia]). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (KEEP : hs_keep_p W (spZ regs0) mem mem) by (intros a _ _; reflexivity).
assert (MIDOF : forall ss' ms' md',
  st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms') ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 9; 18; 22]%bv = true ->
  (exists r, nth_error (ss_mem ss') 0 = Some r /\ YP09.r_base r = Some 2%nat /\ In (YP09.mkChunk 16 (CVal 8 (SOff 9 440))) (YP09.r_chunks r)) ->
  hs_keep_p W (spZ regs0) mem (ms_mem ms') ->
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc Sc W (ms_mem ms') md' 0 ->
  hs_mid F0 C0 fx regs0 ly S W mem0 md0 h now H (ms_regs ms') (ms_mem ms') md').
{ intros ss' ms' md' HS' Hfb (r & Hn & Hb & Hc) HK HJ'.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 9; 18; 22]%bv HS' HAE Hfb) as HK2. cbn [ms_regs restrict] in HK2.
  pose proof (hs_spill_of E ss' ms' W r (spZ regs0 - 128) h HS' Hn Hb Hc Usp ltac:(rewrite E9; exact R9) ltac:(lia) ltac:(lia)) as SP.
  replace (spZ regs0 - 128 + 16) with (spZ regs0 - 112) in SP by lia.
  split; [apply (hs_inv_kept F0 C0 fx regs0 ly S W mem0 md0 ch h now hb hn H mem md (ms_mem ms') md' HPRE' HINV' HK); exists lyc, Sc; split; [exact HJ' | exact HPerm]|].
  split; [exact SP|].
  rewrite !HK2 by (repeat (first [left; reflexivity | right])).
  repeat split; assumption. }
assert (LEAF : forall ss' ms' md' (v : Z),
  st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms') -> ss_resv ss' = None -> ss_pc ss' = AF_both3_reac_hunt_step + 268 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 9; 18; 22]%bv = true ->
  (exists r, nth_error (ss_mem ss') 0 = Some r /\ YP09.r_base r = Some 2%nat /\ In (YP09.mkChunk 16 (CVal 8 (SOff 9 440))) (YP09.r_chunks r)) ->
  hs_keep_p W (spZ regs0) mem (ms_mem ms') ->
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc Sc W (ms_mem ms') md' 0 ->
  getr (ms_regs ms') 11 = w64 v -> v = hs_verdict h H now ->
  SRr SEGS W (mkCfg ms' md') (hs_post F0 C0 regs0 ly S W mem0 md0 h now H)).
{ intros ss' ms' md' v HS' Hrv Hpc Hfb Hr HK HJ' H11 Hv.
  pose proof (MIDOF ss' ms' md' HS' Hfb Hr HK HJ') as HM.
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS' Hrv), Hpc.
  exact (hs_epi F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H (ms_regs ms') (ms_mem ms') md' v HPRE' HM H11 Hv). }
assert (UQ : 0 <= u_at H 436 4 < 2 ^ 32) by (apply UR; rewrite ?LH; lia).
pose proof (hs_sw32 (u_at H 436 4)) as SQ. change (bv_swrap 32 (u_at H 436 4)) with (s32_at H 436) in SQ.
assert (HV0 : hs_verdict h H now = decide_model (s32_at H 432) (s32_at H 436) (s32_at (hs_arb h H now) 0)
  (s32_at (hs_arb h H now) 24) (s32_at H 420) (u_at H 424 8) (s32_at H 440) now
  (desk_geometry_live h (hs_table H now) (sub H 412 6) now) (box_present h (hs_table H now) now)) by reflexivity.
paj_run_tok RUN HS HJ SHOK Bspan_HS; [hs_awr Usp|]. hs_keep Usp.
assert (UP : 0 <= u_at H 432 4 < 2 ^ 32) by (apply UR; rewrite ?LH; lia).
assert (UST : 0 <= u_at (hs_arb h H now) 0 4 < 2 ^ 32) by (apply UR; rewrite ?LA; lia).
assert (URV : 0 <= u_at (hs_arb h H now) 24 4 < 2 ^ 32) by (apply UR; rewrite ?LA; lia).
assert (UN : 0 <= u_at (hs_table H now) 384 4 < 2 ^ 32) by (apply UR; rewrite ?LT; lia).
assert (UV0 : 0 <= u_at H 440 4 < 2 ^ 32) by (apply UR; rewrite ?LH; lia).
pose proof (hs_sw32 (u_at (hs_arb h H now) 24 4)) as SRV. change (bv_swrap 32 (u_at (hs_arb h H now) 24 4)) with (s32_at (hs_arb h H now) 24) in SRV.
psrr_branch_tok RUN BR HS SHOK Bspan_HS.
- rewrite (proj1 (hs_br32 E 32 (u_at H 432 4) 0 E32 UP ltac:(lia))) in Hc.
  apply Z.eqb_eq in Hc. change (bv_swrap 32 (u_at H 432 4)) with (s32_at H 432) in Hc. rename Hc into P0.
  paj_run_tok RUN HS HJ SHOK Bspan_HS; [hs_awr Usp|]. hs_keep Usp.
  psrr_branch_tok RUN BR HS SHOK Bspan_HS.
  + rewrite (proj2 (hs_br32 E 38 (u_at (hs_arb h H now) 0 4) 2 E38 UST ltac:(lia))) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc. change (bv_swrap 32 (u_at (hs_arb h H now) 0 4)) with (s32_at (hs_arb h H now) 0) in Hc.
    rename Hc into S2N.
    paj_run_tok RUN HS HJ SHOK Bspan_HS; [hs_awr Usp|]. hs_keep Usp.
    psrr_branch_tok RUN BR HS SHOK Bspan_HS.
    * rewrite (hs_brge0 E 37 (u_at (hs_table H now) 384 4) E37 UN) in Hc.
      apply Z.leb_le in Hc. change (bv_swrap 32 (u_at (hs_table H now) 384 4)) with (n_of (hs_table H now)) in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_HS (AF_both3_reac_hunt_step + 736); [hs_awr Usp|]. hs_keep Usp.
      pose proof (MIDOF _ ms _ HS ltac:(vm_compute; reflexivity) ltac:(hs_r0) KEEP HJ) as HM.
      assert (X19 : getr (ms_regs ms) 19 = w64 (h + 384)) by (hs_reg HS (19%bv : bv 5); rewrite U_SOff, Uh; apply zcanon_id; unfold M64; lia).
      assert (X23 : getr (ms_regs ms) 23 = w64 (SB_HS + (h + 384) / 8)) by (hs_reg HS (23%bv : bv 5); exact U23).
      assert (X24 : getr (ms_regs ms) 24 = w64 (2 ^ 64 - 1 - h)) by (hs_reg HS (24%bv : bv 5); exact U24).
      rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). change (ss_pc _) with (AF_both3_reac_hunt_step + 736).
      apply (PD fx F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H (ms_regs ms) (ms_mem ms) _ HPRE' HM X19 X23 X24 P0 S2N).
      apply reac_hunt_step.hs_dgl_false. intros j Hj. lia.
    * rewrite (hs_brge0 E 37 (u_at (hs_table H now) 384 4) E37 UN) in Hc.
      apply Z.leb_gt in Hc. change (bv_swrap 32 (u_at (hs_table H now) 384 4)) with (n_of (hs_table H now)) in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_HS (AF_both3_reac_hunt_step + 516); [hs_awr Usp|]. hs_keep Usp.
      pose proof (MIDOF _ ms _ HS ltac:(vm_compute; reflexivity) ltac:(hs_r0) KEEP HJ) as HM.
      assert (X19 : getr (ms_regs ms) 19 = w64 (h + 384)) by (hs_reg HS (19%bv : bv 5); rewrite U_SOff, Uh; apply zcanon_id; unfold M64; lia).
      assert (X20 : getr (ms_regs ms) 20 = w64 (h + 412)) by (hs_reg HS (20%bv : bv 5); rewrite U_SOff, Uh; apply zcanon_id; unfold M64; lia).
      assert (X23 : getr (ms_regs ms) 23 = w64 (SB_HS + (h + 384) / 8)) by (hs_reg HS (23%bv : bv 5); exact U23).
      assert (X24 : getr (ms_regs ms) 24 = w64 (2 ^ 64 - 1 - h)) by (hs_reg HS (24%bv : bv 5); exact U24).
      assert (X8 : getr (ms_regs ms) 8 = w64 5000000000) by (hs_reg HS (8%bv : bv 5); rewrite U_SLit; reflexivity).
      assert (X25 : getr (ms_regs ms) 25 = w64 (48 * 0)) by (hs_reg HS (25%bv : bv 5); rewrite U_SLit; reflexivity).
      assert (X26 : getr (ms_regs ms) 26 = w64 0) by (hs_reg HS (26%bv : bv 5); rewrite U_SLit; reflexivity).
      assert (X27 : getr (ms_regs ms) 27 = w64 432) by (hs_reg HS (27%bv : bv 5); rewrite U_SLit; reflexivity).
      assert (SLOT : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs0 - 120) 8 3).
      { replace (spZ regs0 - 120) with (spZ regs0 - 128 + 8) by lia.
        lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ =>
          apply (hs_slot_of E ss1 ms W _ (spZ regs0 - 128) 8 (SLit 3) 3 HS eq_refl eq_refl
            ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])) Usp eq_refl ltac:(lia)) end. }
      rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). change (ss_pc _) with (AF_both3_reac_hunt_step + 516).
      apply (LD (Z.to_nat (n_of (hs_table H now))) 0 fx F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H (ms_regs ms) (ms_mem ms) _
        ltac:(lia) ltac:(lia) ltac:(intros j Hj; lia) HPRE' HM SLOT X8 X19 X20 X23 X24 X25 X26 X27 P0 S2N).
  + rewrite (proj2 (hs_br32 E 38 (u_at (hs_arb h H now) 0 4) 2 E38 UST ltac:(lia))) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc. change (bv_swrap 32 (u_at (hs_arb h H now) 0 4)) with (s32_at (hs_arb h H now) 0) in Hc.
    rename Hc into S2E.
    paj_run_tok RUN HS HJ SHOK Bspan_HS; [hs_awr Usp|]. hs_keep Usp.
    psrr_branch_tok RUN BR HS SHOK Bspan_HS.
    * rewrite (proj2 (hs_br32 E 39 (u_at (hs_arb h H now) 24 4) 4 E39 URV ltac:(lia))) in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. change (bv_swrap 32 (u_at (hs_arb h H now) 24 4)) with (s32_at (hs_arb h H now) 24) in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_HS (AF_both3_reac_hunt_step + 268); [hs_awr Usp|]. hs_keep Usp.
      hs_leaf LEAF HS KEEP HJ.
      rewrite HV0, P0, reac_hunt_step.hs_dm_unp.
      replace (s32_at (hs_arb h H now) 0 =? 2) with true by (symmetry; apply Z.eqb_eq; exact S2E).
      replace (s32_at (hs_arb h H now) 24 =? 4) with false by (symmetry; apply Z.eqb_neq; exact Hc).
      rewrite !U_SAlu. cbn [zalu_raw]. rewrite (hs_U32 E 39 (u_at (hs_arb h H now) 24 4) E39 URV), !U_SLit.
      change (bv_swrap 32 (u_at (hs_arb h H now) 24 4)) with (s32_at (hs_arb h H now) 24).
      rewrite hs_zc_m3 by lia. destruct (Z.eqb_spec (s32_at (hs_arb h H now) 24) 3); reflexivity.
    * rewrite (proj2 (hs_br32 E 39 (u_at (hs_arb h H now) 24 4) 4 E39 URV ltac:(lia))) in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. change (bv_swrap 32 (u_at (hs_arb h H now) 24 4)) with (s32_at (hs_arb h H now) 24) in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_HS (AF_both3_reac_hunt_step + 268); [hs_awr Usp|]. hs_keep Usp.
      hs_leaf LEAF HS KEEP HJ.
      rewrite HV0, P0, reac_hunt_step.hs_dm_unp.
      replace (s32_at (hs_arb h H now) 0 =? 2) with true by (symmetry; apply Z.eqb_eq; exact S2E).
      replace (s32_at (hs_arb h H now) 24 =? 4) with true by (symmetry; apply Z.eqb_eq; exact Hc).
      rewrite (hs_U32 E 34 (u_at H 440 4) E34 UV0). change (bv_swrap 32 (u_at H 440 4)) with (s32_at H 440).
      unfold zcanon, M64. apply Z.mod_small. lia.
- rewrite (proj1 (hs_br32 E 32 (u_at H 432 4) 0 E32 UP ltac:(lia))) in Hc.
  apply Z.eqb_neq in Hc. change (bv_swrap 32 (u_at H 432 4)) with (s32_at H 432) in Hc. rename Hc into P1N.
  paj_run_tok RUN HS HJ SHOK Bspan_HS; [hs_awr Usp|]. hs_keep Usp.
  psrr_branch_tok RUN BR HS SHOK Bspan_HS.
  + rewrite (proj2 (hs_br32 E 33 (u_at H 436 4) 0 E33 UQ ltac:(lia))) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc. change (bv_swrap 32 (u_at H 436 4)) with (s32_at H 436) in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan_HS (AF_both3_reac_hunt_step + 268); [hs_awr Usp|]. hs_keep Usp.
    hs_leaf LEAF HS KEEP HJ.
    rewrite HV0, reac_hunt_step.hs_dm_pinned by exact P1N.
    replace (s32_at H 436 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc). cbn [andb].
    rewrite !U_SAlu. cbn [zalu_raw]. rewrite (hs_U32 E 33 (u_at H 436 4) E33 UQ), !U_SLit.
    change (bv_swrap 32 (u_at H 436 4)) with (s32_at H 436).
    rewrite hs_zc_m1 by lia. destruct (Z.eqb_spec (s32_at H 436) 1); reflexivity.
  + rewrite (proj2 (hs_br32 E 33 (u_at H 436 4) 0 E33 UQ ltac:(lia))) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc. change (bv_swrap 32 (u_at H 436 4)) with (s32_at H 436) in Hc. rename Hc into Q0.
    paj_run_tok RUN HS HJ SHOK Bspan_HS; [hs_awr Usp|]. hs_keep Usp.
    psrr_branch_tok RUN BR HS SHOK Bspan_HS.
    * rewrite (proj2 (hs_br32 E 38 (u_at (hs_arb h H now) 0 4) 2 E38 UST ltac:(lia))) in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. change (bv_swrap 32 (u_at (hs_arb h H now) 0 4)) with (s32_at (hs_arb h H now) 0) in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_HS (AF_both3_reac_hunt_step + 268); [hs_awr Usp|]. hs_keep Usp.
      hs_leaf LEAF HS KEEP HJ.
      rewrite HV0, reac_hunt_step.hs_dm_pinned by exact P1N. rewrite Q0.
      replace (s32_at (hs_arb h H now) 0 =? 2) with false by (symmetry; apply Z.eqb_neq; exact Hc). cbn [andb].
      rewrite !U_SAlu. cbn [zalu_raw]. rewrite (hs_U32 E 33 (u_at H 436 4) E33 UQ), !U_SLit.
      change (bv_swrap 32 (u_at H 436 4)) with (s32_at H 436). rewrite Q0. reflexivity.
    * rewrite (proj2 (hs_br32 E 38 (u_at (hs_arb h H now) 0 4) 2 E38 UST ltac:(lia))) in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. change (bv_swrap 32 (u_at (hs_arb h H now) 0 4)) with (s32_at (hs_arb h H now) 0) in Hc.
      rename Hc into S2E.
      paj_run_tok RUN HS HJ SHOK Bspan_HS; [hs_awr Usp|]. hs_keep Usp.
      psrr_branch_tok RUN BR HS SHOK Bspan_HS.
      -- rewrite (proj1 (hs_br32 E 39 (u_at (hs_arb h H now) 24 4) 2 E39 URV ltac:(lia))) in Hc.
         apply Z.eqb_eq in Hc. change (bv_swrap 32 (u_at (hs_arb h H now) 24 4)) with (s32_at (hs_arb h H now) 24) in Hc.
         paj_run_to_tok RUNTO HS HJ SHOK Bspan_HS (AF_both3_reac_hunt_step + 268); [hs_awr Usp|]. hs_keep Usp.
         hs_leaf LEAF HS KEEP HJ.
         rewrite HV0, reac_hunt_step.hs_dm_pinned by exact P1N. rewrite Q0, S2E, Hc. reflexivity.
      -- rewrite (proj1 (hs_br32 E 39 (u_at (hs_arb h H now) 24 4) 2 E39 URV ltac:(lia))) in Hc.
         apply Z.eqb_neq in Hc. change (bv_swrap 32 (u_at (hs_arb h H now) 24 4)) with (s32_at (hs_arb h H now) 24) in Hc.
         paj_run_to_tok RUNTO HS HJ SHOK Bspan_HS (AF_both3_reac_hunt_step + 268); [hs_awr Usp|]. hs_keep Usp.
         hs_leaf LEAF HS KEEP HJ.
         rewrite HV0, reac_hunt_step.hs_dm_pinned by exact P1N. rewrite Q0, S2E.
         replace (s32_at (hs_arb h H now) 24 =? 2) with false by (symmetry; apply Z.eqb_neq; exact Hc). cbn [andb].
         rewrite !U_SAlu. cbn [zalu_raw]. rewrite (hs_U32 E 33 (u_at H 436 4) E33 UQ), !U_SLit.
         change (bv_swrap 32 (u_at H 436 4)) with (s32_at H 436). rewrite Q0. reflexivity.
Qed.
Definition hs_regions0 : smem := [stack_region 128; got_regionP; bcell_regionP 32].
Definition hs_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 HS_CEIL 3); (32%nat, mkAF SB_HS SB_HS 0)] [] [].
Definition ss_hs0 : sstate := mkSS AF_both3_reac_hunt_step sr_atoms hs_regions0 None hs_facts0.
Definition Bx0_HS : sv := SOff 32 0.
Lemma hs_entry : forall ly S W (regs : bvmap 5 word) mem md ch h,
  afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
  getr regs 10 = w64 h -> 4096 <= h <= HS_CEIL -> h mod 8 = 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 SB_HS])) ss_hs0
    (restrict (w_H W) (mkst (fx := fx) regs (Z_to_bv 64 (BASE + AF_both3_reac_hunt_step)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch h HPRE H10 Rh Hh8.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8464) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_val_range (A_OBJ 0)) as VR0. pose proof (pa_val_range (A_OBJ 12)) as VR12.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
rewrite YA0o.restrict_mkst_fx.
set (E := Eimg (Ereg regs [w64 SB_HS])).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [w64 SB_HS]) n) by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 h) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB_HS) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E43 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_hs0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold hs_regions0, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E43) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB_HS);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; unfold SB_HS; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold hs_regions0, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E43) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear.
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [hs_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E10, E32, !unsigned_lit_small by (unfold SB_HS, HS_CEIL in *; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Rh Hh8. clear.
  unfold SB_HS, HS_CEIL. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
Definition hs_pd_ex (h now : Z) (H : list byte) : list word :=
  map w64 [u_at H 420 4; u_at H 424 8; u_at (hs_table H now) 384 4].
Definition hs_pd_h : YP09.region := YP09.mkRegion (Some 9%nat) 0 480 0 0
  [YP09.mkChunk 420 (CVal 4 (SOff 32 0)); YP09.mkChunk 424 (CVal 8 (SOff 33 0)); YP09.mkChunk 384 (CVal 4 (SOff 34 0))].
Definition hs_pd_stack : YP09.region := YP09.mkRegion (Some 2%nat) 0 128 8 24 [YP09.mkChunk 16 (CVal 8 (SOff 9 440))].
Definition hs_pd_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 19%bv (SOff 9 384)) 23%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 384) (SLit 3)) (SOff 22 0)))
    24%bv (SAlu ALU_XOR (SOff 9 0) (SLit (-1))).
Definition ss_pd : sstate := mkSS (AF_both3_reac_hunt_step + 736) hs_pd_regs [hs_pd_stack; hs_pd_h] None
  (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF 4096 HS_CEIL 3); (22%nat, mkAF SB_HS SB_HS 0)] [] []).
Lemma hs_postd_w : hs_loopb_stmt ->
  forall F0 C0 ly S W (regs0 : bvmap 5 word) mem0 md0 ch (h now hb hn : Z) (H : list byte) (regs : bvmap 5 word) mem md,
  hs_pre ly S W regs0 mem0 md0 ch h now hb hn H ->
  hs_mid F0 C0 fx regs0 ly S W mem0 md0 h now H regs mem md ->
  getr regs 19 = w64 (h + 384) -> getr regs 23 = w64 (SB_HS + (h + 384) / 8) -> getr regs 24 = w64 (2 ^ 64 - 1 - h) ->
  s32_at H 432 = 0 -> s32_at (hs_arb h H now) 0 <> 2 ->
  desk_geometry_live h (hs_table H now) (sub H 412 6) now = false ->
  SRr SEGS W (mkCfg (mkst (fx := fx) regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 736))) mem (seg_rom SEGS)) md)
    (hs_post F0 C0 regs0 ly S W mem0 md0 h now H).
Proof.
intros LBs F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H regs mem md HPRE HMID R19 R23 R24 P0 S2N DGL.
pose proof HPRE as HPRE'.
destruct HMID as (HINV & HSPILL & R2 & R3 & R4 & R9 & R18 & R22).
pose proof HINV as HINV'.
destruct HPRE as (HPRE & HROD & Hnow & Hh0 & Hh8 & Hin & Hhb & Hhe & HOK).
destruct HINV as ((lyc & Sc & HJ & HPerm) & HMOD & HBLK & HSAV & HRATES & HFK & HCSR).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof HJ as (HAR & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (Hinc : In (hb, hn) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
destruct (al_blocks _ _ LAWS lyc Sc W mem md hb hn HAR Hinc) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & Hbpres & _).
pose proof HMOD as (LT & TOK & LA). pose proof HOK as (LH & _ & LOK & V0R).
assert (WS : REAC_HUNT_STEP_STK = 8464) by reflexivity.
pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as Rsp0. change (bv_modulus 64) with (2 ^ 64) in Rsp0. fold (spZ regs0) in Rsp0.
assert (LB : length (hs_blk h H now) = 480%nat).
{ unfold hs_blk. rewrite !length_app, LT, LA, length_skipn. rewrite !disco_table.length_sub by (rewrite ?LH; lia). rewrite LH. reflexivity. }
assert (VB : forall k n, 0 <= k -> (Z.to_nat k + n <= 480)%nat ->
  val_mem SEGS (mrestrict (w_H W) mem) (h + k) n (u_at (hs_blk h H now) k n))
  by (intros k n Hk Hn; apply hs_vm; [exact HBLK | exact Hk | rewrite LB; exact Hn]).
assert (UR : forall (L : list byte) k n, 0 <= k -> (Z.to_nat k + n <= length L)%nat -> 0 <= u_at L k n < 2 ^ (8 * Z.of_nat n)).
{ intros L k n Hk Hn. unfold u_at. pose proof (disco_table.ble_range (sub L k n)) as Rb.
  rewrite disco_table.length_sub in Rb by lia. exact Rb. }
remember (Eimg (Ereg regs (hs_pd_ex h now H))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HRO0 : regs_ok E sr_atoms regs) by (subst E; apply regs_ok_Eimg_Ereg).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (hs_pd_ex h now H)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E18 : ew E 18 = getr regs 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
assert (E22 : ew E 22 = getr regs 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (hs_pd_ex h now H) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth hs_pd_ex map] in E32, E33, E34.
assert (HAE : env_agree 32 (Ereg regs (hs_pd_ex h now H)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 128) by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (Uh : bv_unsigned (ew E 9) = h) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; lia).
assert (Usb : bv_unsigned (ew E 22) = SB_HS) by (rewrite E22, R22; unfold w64; apply unsigned_lit_small; unfold SB_HS; lia).
assert (Unow : bv_unsigned (ew E 18) = now) by (rewrite E18, R18; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 384) (SLit 3)) (SOff 22 0)) = SB_HS + (h + 384) / 8).
{ rewrite !U_SAlu, !U_SOff, U_SLit, Uh, Usb. cbn [zalu_raw].
  rewrite (zcanon_id (h + 384)) by (unfold M64; lia). change (Z.land (zcanon 3) 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite Z.add_0_r.
  rewrite (zcanon_id SB_HS) by (unfold M64, SB_HS; lia).
  rewrite (zcanon_id ((h + 384) / 8)) by (unfold M64; Z.div_mod_to_equations; lia).
  rewrite zcanon_id by (unfold M64, SB_HS; Z.div_mod_to_equations; lia). lia. }
assert (U24 : U E (SAlu ALU_XOR (SOff 9 0) (SLit (-1))) = 2 ^ 64 - 1 - h).
{ rewrite U_SAlu, U_SOff, U_SLit, Uh, Z.add_0_r. cbn [zalu_raw]. rewrite (zcanon_id h) by (unfold M64; lia).
  change (zcanon (-1)) with (2 ^ 64 - 1). rewrite hs_xor_m1 by lia. apply zcanon_id. unfold M64. lia. }
assert (HRO : regs_ok E hs_pd_regs regs).
{ unfold hs_pd_regs. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HRO0 | discriminate |] | discriminate |] | discriminate |].
  all: symmetry; rewrite denot_lit_U; first
    [ rewrite U23, R23; reflexivity
    | rewrite U24, R24; reflexivity
    | rewrite U_SOff, Uh, R19; unfold w64; f_equal; apply zcanon_id; unfold M64; lia ]. }
assert (HS : st_ok_pi SEGS VAL E ss_pd (restrict (w_H W) (mkst (fx := fx) regs (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 736))) mem (seg_rom SEGS)))).
{ rewrite YA0o.restrict_mkst_fx. unfold ss_pd. apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, hs_pd_stack. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply HJpres. lia.
      * constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 9 440) (h + 440));
        [ cbn [sv_denot]; rewrite E9, R9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia
        | replace (spZ regs0 - 128 + 16) with (spZ regs0 - 112) by lia; exact HSPILL ].
    + unfold region_ok, hs_pd_h. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uh.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 420 4 (SOff 32 0) (u_at H 420 4)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply UR; rewrite ?LH; lia | lia |].
        unfold u_at at 1. rewrite <- (hs_blk_H h H now 420 4 LT LH) by lia. exact (VB 420 4%nat ltac:(lia) ltac:(lia)).
      * apply (chunk_ok_val SEGS E _ _ 424 8 (SOff 33 0) (u_at H 424 8)); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply UR; rewrite ?LH; lia | lia |].
        unfold u_at at 1. rewrite <- (hs_blk_H h H now 424 8 LT LH) by lia. exact (VB 424 8%nat ltac:(lia) ltac:(lia)).
      * apply (chunk_ok_val SEGS E _ _ 384 4 (SOff 34 0) (u_at (hs_table H now) 384 4)); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply UR; rewrite ?LT; lia | lia |].
        unfold u_at at 1. rewrite <- (hs_blk_T h H now 384 4 LT) by lia. exact (VB 384 4%nat ltac:(lia) ltac:(lia)).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region, hs_pd_stack, hs_pd_h.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uh.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uh, E22, R22. unfold w64. rewrite unsigned_lit_small by (unfold SB_HS; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    unfold SB_HS, HS_CEIL. repeat split. all: try (exact I || lia). all: Z.div_mod_to_equations; lia. }
assert (SHOK : sh_ok SEGS Bx_HS SH_S2 E (mrestrict (w_H W) mem)).
{ unfold sh_ok, SH_S2. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E Bx_HS 9 hb (req_size hn) h 0 480).
  - exact (range_addressable_of_block SEGS B LAWS lyc Sc W mem md hb hn hb (req_size hn) HAR Hinc ltac:(lia) ltac:(lia)).
  - unfold Bx_HS. rewrite (U_atom E 22 SB_HS) by (first [rewrite E22, R22; reflexivity | unfold SB_HS; lia]). reflexivity.
  - rewrite (U_atom E 9 h) by (first [rewrite E9, R9; reflexivity | lia]). reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (KEEP : hs_keep_p W (spZ regs0) mem mem) by (intros a _ _; reflexivity).
assert (MIDOF : forall ss' ms' md',
  st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms') ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 9; 18; 22]%bv = true ->
  (exists r, nth_error (ss_mem ss') 0 = Some r /\ YP09.r_base r = Some 2%nat /\ In (YP09.mkChunk 16 (CVal 8 (SOff 9 440))) (YP09.r_chunks r)) ->
  hs_keep_p W (spZ regs0) mem (ms_mem ms') ->
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc Sc W (ms_mem ms') md' 0 ->
  hs_mid F0 C0 fx regs0 ly S W mem0 md0 h now H (ms_regs ms') (ms_mem ms') md').
{ intros ss' ms' md' HS' Hfb (r & Hn & Hb & Hc) HK HJ'.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 9; 18; 22]%bv HS' HAE Hfb) as HK2. cbn [ms_regs restrict] in HK2.
  pose proof (hs_spill_of E ss' ms' W r (spZ regs0 - 128) h HS' Hn Hb Hc Usp ltac:(rewrite E9; exact R9) ltac:(lia) ltac:(lia)) as SP.
  replace (spZ regs0 - 128 + 16) with (spZ regs0 - 112) in SP by lia.
  split; [apply (hs_inv_kept F0 C0 fx regs0 ly S W mem0 md0 ch h now hb hn H mem md (ms_mem ms') md' HPRE' HINV' HK); exists lyc, Sc; split; [exact HJ' | exact HPerm]|].
  split; [exact SP|].
  rewrite !HK2 by (repeat (first [left; reflexivity | right])).
  repeat split; assumption. }
assert (LEAF : forall ss' ms' md' (v : Z),
  st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms') -> ss_resv ss' = None -> ss_pc ss' = AF_both3_reac_hunt_step + 268 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 9; 18; 22]%bv = true ->
  (exists r, nth_error (ss_mem ss') 0 = Some r /\ YP09.r_base r = Some 2%nat /\ In (YP09.mkChunk 16 (CVal 8 (SOff 9 440))) (YP09.r_chunks r)) ->
  hs_keep_p W (spZ regs0) mem (ms_mem ms') ->
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs0) (HS_FP h) ly S W mem0 md0 [] lyc Sc W (ms_mem ms') md' 0 ->
  getr (ms_regs ms') 11 = w64 v -> v = hs_verdict h H now ->
  SRr SEGS W (mkCfg ms' md') (hs_post F0 C0 regs0 ly S W mem0 md0 h now H)).
{ intros ss' ms' md' v HS' Hrv Hpc Hfb Hr HK HJ' H11 Hv.
  pose proof (MIDOF ss' ms' md' HS' Hfb Hr HK HJ') as HM.
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS' Hrv), Hpc.
  exact (hs_epi F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H (ms_regs ms') (ms_mem ms') md' v HPRE' HM H11 Hv). }
assert (U420 : 0 <= u_at H 420 4 < 2 ^ 32) by (apply UR; rewrite ?LH; lia).
pose proof (UR H 424 8%nat ltac:(lia) ltac:(rewrite LH; lia)) as U424. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in U424.
assert (UN : 0 <= u_at (hs_table H now) 384 4 < 2 ^ 32) by (apply UR; rewrite ?LT; lia).
assert (HV0 : hs_verdict h H now = decide_model (s32_at H 432) (s32_at H 436) (s32_at (hs_arb h H now) 0)
  (s32_at (hs_arb h H now) 24) (s32_at H 420) (u_at H 424 8) (s32_at H 440) now
  (desk_geometry_live h (hs_table H now) (sub H 412 6) now) (box_present h (hs_table H now) now)) by reflexivity.
rewrite P0, reac_hunt_step.hs_dm_unp, DGL in HV0.
replace (s32_at (hs_arb h H now) 0 =? 2) with false in HV0 by (symmetry; apply Z.eqb_neq; exact S2N).
paj_run_tok RUN HS HJ SHOK Bspan_HS; [hs_awr Usp|]. hs_keep Usp.
psrr_branch_tok RUN BR HS SHOK Bspan_HS.
- rewrite (proj1 (hs_br32 E 32 (u_at H 420 4) 0 E32 U420 ltac:(lia))) in Hc.
  apply Z.eqb_eq in Hc. change (bv_swrap 32 (u_at H 420 4)) with (s32_at H 420) in Hc. rename Hc into SIL0.
  rewrite SIL0 in HV0. cbn [negb Z.eqb] in HV0.
  paj_run_tok RUN HS HJ SHOK Bspan_HS; [hs_awr Usp|]. hs_keep Usp.
  assert (UW : U E (SAlu ALU_ADD (SOff 18 0) (SMd M_MUL (SOff 33 0) (SLit (-1)))) = (now - u_at H 424 8) mod 2 ^ 64).
  { rewrite U_SAlu, U_SMd, U_SLit, (U_atom E 18 now) by (first [rewrite E18, R18; reflexivity | lia]).
    rewrite (U_atom E 33 (u_at H 424 8) E33) by lia. cbn [zalu_raw zmd_raw].
    unfold zcanon, M64. rewrite Zplus_mod_idemp_r. replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
    replace (now + u_at H 424 8 * (2 ^ 64 - 1)) with ((now - u_at H 424 8) + u_at H 424 8 * 2 ^ 64) by ring.
    rewrite Z_mod_plus_full. reflexivity. }
  psrr_branch_tok RUN BR HS SHOK Bspan_HS.
  + rewrite branch_ltu_U, UW, U_SLit in Hc. change (zcanon 3000000000) with REAC_HUNT_WINDOW_NS in Hc.
    rewrite Hc in HV0.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan_HS (AF_both3_reac_hunt_step + 268); [hs_awr Usp|]. hs_keep Usp.
    hs_leaf LEAF HS KEEP HJ.
    rewrite HV0. rewrite U_SLit. reflexivity.
  + rewrite branch_ltu_U, UW, U_SLit in Hc. change (zcanon 3000000000) with REAC_HUNT_WINDOW_NS in Hc.
    rename Hc into WINF. rewrite WINF in HV0.
    paj_run_tok RUN HS HJ SHOK Bspan_HS; [hs_awr Usp|]. hs_keep Usp.
    psrr_branch_tok RUN BR HS SHOK Bspan_HS.
    * rewrite (hs_brge0 E 34 (u_at (hs_table H now) 384 4) E34 UN) in Hc.
      apply Z.leb_le in Hc. change (bv_swrap 32 (u_at (hs_table H now) 384 4)) with (n_of (hs_table H now)) in Hc.
      rewrite (reac_hunt_step.hs_bp_false h (hs_table H now) now ltac:(intros j Hj; lia)) in HV0.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_HS (AF_both3_reac_hunt_step + 268); [hs_awr Usp|]. hs_keep Usp.
      hs_leaf LEAF HS KEEP HJ.
      rewrite HV0. rewrite U_SLit. reflexivity.
    * rewrite (hs_brge0 E 34 (u_at (hs_table H now) 384 4) E34 UN) in Hc.
      apply Z.leb_gt in Hc. change (bv_swrap 32 (u_at (hs_table H now) 384 4)) with (n_of (hs_table H now)) in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan_HS (AF_both3_reac_hunt_step + 892); [hs_awr Usp|]. hs_keep Usp.
      pose proof (MIDOF _ ms _ HS ltac:(vm_compute; reflexivity) ltac:(hs_r0) KEEP HJ) as HM.
      assert (X8 : getr (ms_regs ms) 8 = w64 (48 * 0)) by (hs_reg HS (8%bv : bv 5); rewrite U_SLit; reflexivity).
      assert (X19 : getr (ms_regs ms) 19 = w64 (h + 384)) by (hs_reg HS (19%bv : bv 5); rewrite U_SOff, Uh; apply zcanon_id; unfold M64; lia).
      assert (X20 : getr (ms_regs ms) 20 = w64 0) by (hs_reg HS (20%bv : bv 5); rewrite U_SLit; reflexivity).
      assert (X21 : getr (ms_regs ms) 21 = w64 432) by (hs_reg HS (21%bv : bv 5); rewrite U_SLit; reflexivity).
      assert (X23 : getr (ms_regs ms) 23 = w64 (SB_HS + (h + 384) / 8)) by (hs_reg HS (23%bv : bv 5); exact U23).
      assert (X24 : getr (ms_regs ms) 24 = w64 (2 ^ 64 - 1 - h)) by (hs_reg HS (24%bv : bv 5); exact U24).
      assert (X25 : getr (ms_regs ms) 25 = w64 2) by (hs_reg HS (25%bv : bv 5); rewrite U_SLit; reflexivity).
      assert (X26 : getr (ms_regs ms) 26 = w64 1) by (hs_reg HS (26%bv : bv 5); rewrite U_SLit; reflexivity).
      assert (X27 : getr (ms_regs ms) 27 = w64 5000000000) by (hs_reg HS (27%bv : bv 5); rewrite U_SLit; reflexivity).
      assert (SLOT : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs0 - 120) 8 3).
      { replace (spZ regs0 - 120) with (spZ regs0 - 128 + 8) by lia.
        lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ =>
          apply (hs_slot_of E ss1 ms W _ (spZ regs0 - 128) 8 (SLit 3) 3 HS eq_refl eq_refl
            ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])) Usp eq_refl ltac:(lia)) end. }
      rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). change (ss_pc _) with (AF_both3_reac_hunt_step + 892).
      apply (LBs (Z.to_nat (n_of (hs_table H now))) 0 fx F0 C0 ly S W regs0 mem0 md0 ch h now hb hn H (ms_regs ms) (ms_mem ms) _
        ltac:(lia) ltac:(lia) ltac:(intros j Hj; lia) HPRE' HM SLOT X8 X19 X20 X21 X23 X24 X25 X26 X27 P0 S2N DGL SIL0 WINF).
- rewrite (proj1 (hs_br32 E 32 (u_at H 420 4) 0 E32 U420 ltac:(lia))) in Hc.
  apply Z.eqb_neq in Hc. change (bv_swrap 32 (u_at H 420 4)) with (s32_at H 420) in Hc.
  replace (s32_at H 420 =? 0) with false in HV0 by (symmetry; apply Z.eqb_neq; exact Hc). cbn [negb] in HV0.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan_HS (AF_both3_reac_hunt_step + 268); [hs_awr Usp|]. hs_keep Usp.
  hs_leaf LEAF HS KEEP HJ.
  rewrite HV0. rewrite U_SLit. reflexivity.
Qed.
End w2.
Section w3.
Context {fx : YK11.FPState}.
Let RUN := paj_run (PL := PL_both3_0) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (PL := PL_both3_0) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Ltac hs_awr0 Usp :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
      [ reflexivity | cbn [ew ewset Nat.eqb extK]; rewrite Usp; lia
      | cbn [YP09.r_wlo YP09.r_whi]; unfold REAC_HUNT_STEP_STK, REAC_ARBITRATE_STK, ESTACK; lia
      | cbn [YP09.r_wlo YP09.r_whi]; lia | ] ].
Lemma hs_walk : hs_postd_stmt -> hs_loopd_stmt ->
  forall ly S W (regs : bvmap 5 word) mem md ch (h now hb hn : Z) (H : list byte),
  afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 h -> getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
  0 < h -> h mod 8 = 0 ->
  In (hb, hn) (ablocks B ly S) -> hb <= h -> h + 480 <= hb + req_size hn ->
  hunt_ok H ->
  garr8 SEGS (mrestrict (w_H W) mem) h (map (fun b : byte => bv_unsigned b) H) ->
  hs_rates W mem ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_both3_reac_hunt_step) regs mem md)
    (treac_hunt_step_post fx regs ly S W mem md h now H).
Proof.
intros PD LD ly S W regs mem md ch h now hb hn H HPRE HROD H10 H11 Rnow Hh0 Hh8 Hin Hhb Hhe HOK HG HRATES.
assert (HPRE' : hs_pre ly S W regs mem md ch h now hb hn H)
  by exact (conj HPRE (conj HROD (conj Rnow (conj Hh0 (conj Hh8 (conj Hin (conj Hhb (conj Hhe HOK)))))))).
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8464) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & Hbpres & _).
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp0. change (bv_modulus 64) with (2 ^ 64) in Rsp0. fold (spZ regs) in Rsp0.
pose proof (ajournal_init SEGS B REAC_HUNT_STEP_STK (HS_FP h) ly S W regs mem md ch HPRE) as HJ.
pose proof (hs_entry (fx := fx) ly S W regs mem md ch h HPRE H10 ltac:(unfold HS_CEIL; lia) Hh8) as HS.
remember (Eimg (Ereg regs [w64 SB_HS])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [w64 SB_HS]) n) by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 h) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 now) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB_HS) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs [w64 SB_HS]) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
assert (SHOK : sh_ok SEGS Bx0_HS [] E (mrestrict (w_H W) mem)) by constructor.
assert (KEEP : hs_keep_p W (spZ regs + 104) mem mem) by (intros a _ _; reflexivity).
pose proof (pa_base_lo (PL := PL_both3_0) (PI := PI)) as HBlo. pose proof (@pa_B_ok _ _ PI) as HBok.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_hunt_step)) with (Z_to_bv 64 (BASE + AF_both3_reac_hunt_step)).
paj_run_tok RUN HS HJ SHOK Bspan_HS; [hs_awr0 Usp|]. hs_keep Usp.
lazymatch goal with HS' : st_ok _ ?Ex (setpc ?ssc _) (restrict _ ?msc) |- _ =>
  prreg HS' (1%bv : bv 5) Q1; prreg HS' (2%bv : bv 5) Q2; prreg HS' (3%bv : bv 5) Q3; prreg HS' (4%bv : bv 5) Q4;
  prreg HS' (10%bv : bv 5) Q10; prreg HS' (11%bv : bv 5) Q11;
  pose proof (YA0o.st_ok_restrict_mkst SEGS _ _ _ _ HS' eq_refl) as Hms;
  rewrite Hms in HS' |- *; clear Hms; cbn [ss_pc setpc] in HS' |- *;
  rewrite YA0o.restrict_mkst_fx in HS';
  rewrite pa_sigma_reac_disco_table_age;
  set (regsc := ms_regs msc) in *; set (memc := ms_mem msc) in *; rename HS' into HSc
end.
assert (Qsp : spZ regsc = spZ regs - 128).
{ unfold spZ at 1. rewrite Q2, Usp. rewrite unsigned_lit_small by lia. lia. }
assert (HRA : getr regsc 1 = Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 96))) by (rewrite Q1; reflexivity).
pose proof HJ as (HARc & _).
destruct HOK as (LH & TOK0 & LOK0 & V0R0).
assert (KX : hs_kx W (spZ regs) h mem memc) by (intros a Ha Hb _ _; apply KEEP; [exact Ha | lia]).
assert (HGc : garr8 SEGS (mrestrict (w_H W) memc) h (map (fun b : byte => bv_unsigned b) H)).
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem memc h _); [|exact HG].
  intros a Ha. rewrite length_map, LH in Ha. apply KEEP; lia. }
assert (HG0 : garr8 SEGS (mrestrict (w_H W) memc) h (map (fun b : byte => bv_unsigned b) (sub H 0 400))).
{ assert (EH : map (fun b : byte => bv_unsigned b) H =
    map (fun b : byte => bv_unsigned b) (sub H 0 400) ++ map (fun b : byte => bv_unsigned b) (skipn 400 H)).
  { rewrite <- map_app. f_equal. unfold sub. cbn [Z.to_nat]. rewrite skipn_O. symmetry. apply firstn_skipn. }
  rewrite EH in HGc. apply garr8_app in HGc as [G1 _]. exact G1. }
eapply SRr_bind.
{ eapply (TAGE fx REAC_HUNT_STEP_STK (spZ regs) (HS_FP h) ly S W mem md [] ly S W memc _ 0 regsc h now (sub H 0 400) HJ).
  - exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD).
  - rewrite HRA. change (AF_both3_reac_hunt_step + 96) with 30620. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite HRA. change (AF_both3_reac_hunt_step + 96) with 30620. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, E3. exact Hgp.
  - rewrite Q4, E4. exact Htp.
  - rewrite Q10, E10. reflexivity.
  - rewrite Q11, E11. reflexivity.
  - exact Rnow.
  - rewrite Qsp. replace (spZ regs - 128) with (spZ regs + (-8) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - rewrite Qsp, WS. unfold REAC_DISCO_TABLE_AGE_STK, ESTACK. lia.
  - rewrite Qsp. lia.
  - lia.
  - exact Hh8.
  - lia.
  - exact (amem_range_of_block SEGS B LAWS ly S W memc _ hb hn h 400 HARc Hin ltac:(lia) ltac:(lia)).
  - right. rewrite Qsp. unfold REAC_DISCO_TABLE_AGE_STK, ESTACK. lia.
  - intros a Ha.
    assert (Hw : awr_byte REAC_HUNT_STEP_STK (spZ regs) (HS_FP h) (ablocks B ly S) (ablocks B ly S) ly [] a).
    { right. left. split.
      - exists (h, h + 400). split; [unfold HS_FP; left; reflexivity | cbn [fst snd]; lia].
      - exists hb, hn. split; [exact Hin | lia]. }
    split; [exact Hw | exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw))].
  - exact (range_addressable_of_block SEGS B LAWS ly S W memc _ hb hn h 400 HARc Hin ltac:(lia) ltac:(lia)).
  - exact (shadow_hull_vis_of_block SEGS B LAWS ly S W memc _ hb hn h 400 HARc Hin ltac:(lia) ltac:(lia) ltac:(lia)).
  - apply disco_table.length_sub; rewrite ?LH; lia.
  - unfold sub. cbn [Z.to_nat]. rewrite skipn_O. exact TOK0.
  - exact HG0. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & T' & removed & Hcf & HJ2 & HP2 & H10' & Hfr & Hperm & Hkept & HW2 & HK2 & HG2 & Hage & Hapost).
subst c2 W2.
assert (KX2 : hs_kx W (spZ regs) h mem mem2).
{ apply (hs_kx_call W (spZ regs) h mem memc mem2 h (h + 400) (spZ regsc - REAC_DISCO_TABLE_AGE_STK) (spZ regsc) KX HK2).
  intros a Hb H1 H2. split; [exact H1 | rewrite Qsp; unfold REAC_DISCO_TABLE_AGE_STK, ESTACK; lia]. }
clear KX KEEP Hkept.
destruct Hapost as (LT' & _ & _ & _ & _ & _ & TOK' & _).
jafter_call_keep_pi HSc 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_cons; [|apply Forall_nil]. cbn [ms_mem mkst].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply hs_mb_of_av. pose proof (HK2 (Z_to_bv 64 a)) as K. rewrite unsigned_lit_small in K by lia.
    apply K; [lia | rewrite Qsp; unfold REAC_DISCO_TABLE_AGE_STK, ESTACK; lia].
  - intros _. apply (apresent_writable SEGS).
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp & _). apply HJp. lia. }
clear HK2.
rewrite <- YA0o.restrict_mkst_fx in HS2. change (AF_both3_reac_hunt_step + 96) with 30620 in HRA. rewrite HRA.
remember (havoc E 33 (map (getr regs2) CLOB)) as E' eqn:HE' in HS2.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (HAE' : env_agree 32 (Ereg regs [w64 SB_HS]) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite HE', ew_havoc_old by lia; exact Usp).
assert (E1' : ew E' 1 = getr regs 1) by (rewrite HE', ew_havoc_old by lia; exact E1).
assert (E3' : ew E' 3 = getr regs 3) by (rewrite HE', ew_havoc_old by lia; exact E3).
assert (E4' : ew E' 4 = getr regs 4) by (rewrite HE', ew_havoc_old by lia; exact E4).
assert (E8' : ew E' 8 = getr regs 8) by (rewrite HE', ew_havoc_old by lia; exact E8).
assert (E10' : ew E' 10 = Z_to_bv 64 h) by (rewrite HE', ew_havoc_old by lia; exact E10).
assert (E11' : ew E' 11 = Z_to_bv 64 now) by (rewrite HE', ew_havoc_old by lia; exact E11).
assert (E32' : ew E' 32 = Z_to_bv 64 SB_HS) by (rewrite HE', ew_havoc_old by lia; exact E32).
clear HE'.
repeat match goal with Hs : sh_ok _ _ _ _ _ |- _ => clear Hs end.
assert (SHOK : sh_ok SEGS Bx0_HS [] E' (mrestrict (w_H W) mem2)) by constructor.
paj_run_tok RUN HS2 HJ2 SHOK Bspan_HS; [hs_awr0 Usp'|].
lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict _ mem2) (mrestrict _ ?m1) |- _ =>
  assert (HG2a : garr8 SEGS (mrestrict (w_H W) m1) h (map (fun b : byte => bv_unsigned b) T'));
  [ apply (garr8_frame SEGS _ _ h _ HG2); intros x Hx; rewrite length_map, LT' in Hx;
    apply (hs_fr_mbyte SEGS E0 rs _ _ x HFr); [lia | hs_nw1 Usp'] |] end.
hs_kxs Usp'.
match goal with Hk : hs_kx _ _ _ _ _ |- _ => rename Hk into KXa end.
lazymatch goal with HS' : st_ok _ ?Ex (setpc ?ssc _) (restrict _ ?msa) |- _ =>
  prreg HS' (1%bv : bv 5) A1; prreg HS' (2%bv : bv 5) A2; prreg HS' (3%bv : bv 5) A3; prreg HS' (4%bv : bv 5) A4;
  prreg HS' (8%bv : bv 5) A8;
  prreg HS' (10%bv : bv 5) A10; prreg HS' (11%bv : bv 5) A11; prreg HS' (12%bv : bv 5) A12;
  prreg HS' (13%bv : bv 5) A13; prreg HS' (14%bv : bv 5) A14; prreg HS' (15%bv : bv 5) A15;
  pose proof (YA0o.st_ok_restrict_mkst SEGS _ _ _ _ HS' eq_refl) as Hms;
  rewrite Hms in HS' |- *; clear Hms; cbn [ss_pc setpc] in HS' |- *;
  rewrite YA0o.restrict_mkst_fx in HS';
  rewrite pa_sigma_reac_arbitrate;
  set (regsa := ms_regs msa) in *; set (mema := ms_mem msa) in *; rename HS' into HSa
end.
assert (Qspa : spZ regsa = spZ regs - 128).
{ unfold spZ at 1. rewrite A2, Usp'. rewrite unsigned_lit_small by lia. lia. }
assert (HRA2 : getr regsa 1 = Z_to_bv 64 (BASE + 30656)) by (rewrite A1; reflexivity).
pose proof HJ2 as (HAR2 & _).
assert (Hin2 : In (hb, hn) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
assert (HGP : garr8 SEGS (mrestrict (w_H W) mema) (h + 412) (map (fun b : byte => bv_unsigned b) (sub H 412 6))).
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mema (h + 412) _).
  - intros a Ha. rewrite length_map, disco_table.length_sub in Ha by (rewrite ?LH; lia). apply KXa; lia.
  - exact (hs_g8_sub SEGS _ h H 412 6 HG ltac:(lia) ltac:(rewrite LH; lia)). }
eapply SRr_bind.
{ eapply (TARB fx ly2 S2 W regsa mema _ ch h (h + 412) 0 0 now (h + 444) hb hn hb hn hb hn T' (sub H 412 6)).
  - eapply (afn_pre_at SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-128) ch HJ2).
    + rewrite Qspa. lia.
    + reflexivity.
    + lia.
    + unfold REAC_ARBITRATE_STK, ESTACK. lia.
    + rewrite WS. unfold REAC_ARBITRATE_STK, ESTACK. lia.
    + rewrite HRA2. apply ret_ok_codeptr_v; [lia | reflexivity].
    + unfold raZ. rewrite HRA2, unsigned_lit_small by lia. lia.
    + rewrite A3, E3'. exact Hgp.
    + rewrite A4, E4'. exact Htp.
    + unfold s0Z. rewrite A8, E8', Qspa. fold (s0Z regs).
      apply (achain_lower ly2 _ (spZ regs)); [|lia].
      apply (achain_ly_top ly ly2); [pose proof HJ2 as (_ & Hly & _); pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _); congruence|].
      apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) _ ch (spZ regs) Hch); [lia | lia |].
      intros a Ha. apply KXa; lia.
  - exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROD).
  - rewrite A10, E10'. reflexivity.
  - rewrite A11, E10', unsigned_lit_small by lia. reflexivity.
  - rewrite A12. reflexivity.
  - rewrite A13. reflexivity.
  - rewrite A14, E11'. reflexivity.
  - rewrite A15, E10', unsigned_lit_small by lia. reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact Rnow.
  - lia.
  - exact Hin2.
  - lia.
  - lia.
  - lia.
  - intros _. split; [exact Hin2|]. split; [lia|]. split; [lia|]. split; [exact Hh8|].
    split; [exact LT'|]. split; [exact HG2a|]. split; [exact TOK'|]. right. lia.
  - intros _. split; [exact Hin2|]. split; [lia|]. split; [lia|].
    split; [apply disco_table.length_sub; rewrite ?LH; lia|]. split; [exact HGP|]. right. lia. }
cbv beta. intros W3 c3 _ Hpost. unfold treac_arbitrate_post, apost_base in Hpost.
destruct Hpost as (fq2 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfr2 & Hcsr2 & HJ3 & HP3 & R1' & Hperm3 & HGA & HGT & HGP' & HW3 & HK3).
subst c3 W3.
rewrite Qspa in HJ3, HK3.
pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HJ3
  ltac:(rewrite WS; unfold REAC_ARBITRATE_STK, ESTACK; lia) ltac:(lia)
  ltac:(intros a (r0 & Hr0 & Hra0); cbn [In] in Hr0; destruct Hr0 as [<-|[]]; cbn [fst snd] in Hra0; left; split;
        [exists (h + 440, h + 476); split; [unfold HS_FP; right; left; reflexivity | cbn [fst snd]; lia]
        | exists hb, hn; split; [exact Hin2 | lia]])) as HJ4.
cbn [app] in HJ4. change (0 + 0) with 0 in HJ4.
assert (KX3 : hs_kx W (spZ regs) h mem mem3).
{ apply (hs_kx_call W (spZ regs) h mem mema mem3 (h + 444) (h + 444 + 32) (spZ regs - 128 - REAC_ARBITRATE_STK) (spZ regs - 128) KXa HK3).
  intros a Hb H1 H2. split; [lia | unfold REAC_ARBITRATE_STK, ESTACK; lia]. }
pose proof (FpStep.fp_st_ok_fx SEGS fx fq2 _ _ _ _ _ _ HSa) as HSq. clear HSa. rename HSq into HSa.
jafter_call_keep_pi HSa 49%nat regs3 (mrestrict (w_H W) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ apply Forall_cons; [|apply Forall_nil]. cbn [ms_mem mkst].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp'; intros a Ha.
  - apply hs_mb_of_av. pose proof (HK3 (Z_to_bv 64 a)) as K. rewrite unsigned_lit_small in K by lia.
    apply K; [lia | unfold REAC_ARBITRATE_STK, ESTACK; lia].
  - intros _. apply (apresent_writable SEGS).
    pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp & _). apply HJp. lia. }
clear HK3.
rewrite <- YA0o.restrict_mkst_fx in HS3. rewrite HRA2.
prreg HS3 (2%bv : bv 5) B2; prreg HS3 (3%bv : bv 5) B3; prreg HS3 (4%bv : bv 5) B4; prreg HS3 (9%bv : bv 5) B9;
prreg HS3 (18%bv : bv 5) B18; prreg HS3 (19%bv : bv 5) B19; prreg HS3 (20%bv : bv 5) B20; prreg HS3 (22%bv : bv 5) B22.
remember (havoc E' 49 (map (getr regs3) CLOB)) as Ev3 eqn:HEv3 in HS3.
assert (HAE3 : env_agree 32 (Ereg regs [w64 SB_HS]) Ev3) by (rewrite HEv3; apply env_agree_havoc_ge; [lia | exact HAE']).
assert (Usp3 : bv_unsigned (ew Ev3 2) = spZ regs) by (rewrite HEv3, ew_havoc_old by lia; exact Usp').
assert (EHT : hs_table H now = T') by (unfold hs_table; rewrite Hage; reflexivity).
assert (EHA : hs_arb h H now = reac_arbitrate_c.arb_model h (h + 412) T' (sub H 412 6) 0 0 now) by (unfold hs_arb; rewrite EHT; reflexivity).
assert (LP : length (sub H 412 6) = 6%nat) by (apply disco_table.length_sub; rewrite ?LH; lia).
assert (LA : length (reac_arbitrate_c.arb_model h (h + 412) T' (sub H 412 6) 0 0 now) = 32%nat)
  by (apply reac_hunt_step.hs_len_arb; [exact LT' | exact LP | exact (proj1 TOK')]).
assert (HM3 : hs_inv (@YK11.fp_regs fx) (@YK11.fp_csr fx) fq2 regs ly S W mem md h now H mem3 md3).
{ split. { exists ly3, S3. split; [exact HJ4 | exact (Permutation_trans Hperm3 Hperm)]. }
  split. { unfold hs_mod. rewrite EHT, EHA. split; [exact LT'|]. split; [exact TOK' | exact LA]. }
  split.
  { unfold hs_blk. rewrite EHT, EHA. rewrite !map_app.
    apply garr8_app. split; [exact (HGT ltac:(lia))|]. rewrite length_map, LT'.
    apply garr8_app. split.
    { apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem3 _ _).
      - intros a Ha. rewrite length_map, disco_table.length_sub in Ha by (rewrite ?LH; lia). apply KX3; lia.
      - replace (h + Z.of_nat 400) with (h + 400) by lia. exact (hs_g8_sub SEGS _ h H 400 40 HG ltac:(lia) ltac:(rewrite LH; lia)). }
    rewrite length_map, disco_table.length_sub by (rewrite ?LH; lia).
    apply garr8_app. split.
    { apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem3 _ _).
      - intros a Ha. rewrite length_map, disco_table.length_sub in Ha by (rewrite ?LH; lia). apply KX3; lia.
      - replace (h + Z.of_nat 400 + Z.of_nat 40) with (h + 440) by lia. exact (hs_g8_sub SEGS _ h H 440 4 HG ltac:(lia) ltac:(rewrite LH; lia)). }
    rewrite length_map, disco_table.length_sub by (rewrite ?LH; lia).
    apply garr8_app. split.
    { replace (h + Z.of_nat 400 + Z.of_nat 40 + Z.of_nat 4) with (h + 444) by lia. exact HGA. }
    rewrite length_map, LA.
    assert (ES : skipn 476 H = sub H 476 4) by (unfold sub; cbn [Z.to_nat Pos.to_nat]; symmetry; apply firstn_all2; rewrite length_skipn, LH; lia).
    rewrite ES.
    apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem3 _ _).
    - intros a Ha. rewrite length_map, disco_table.length_sub in Ha by (rewrite ?LH; lia). apply KX3; lia.
    - replace (h + Z.of_nat 400 + Z.of_nat 40 + Z.of_nat 4 + Z.of_nat 32) with (h + 476) by lia.
      exact (hs_g8_sub SEGS _ h H 476 4 HG ltac:(lia) ltac:(rewrite LH; lia)). }
  split.
  { unfold hs_saved. rewrite Forall_forall. intros p Hp. cbv [HS_SLOTS In] in Hp.
    repeat destruct Hp as [<-|Hp]; [ cbn [fst snd]; hs_sl HS3 Usp3 HAE3 .. | destruct Hp ]. }
  split.
  { destruct HRATES as (Ra1 & Ra2 & Ra3 & Ra4). pose proof hs_rates_img_ok as (IR1 & IR2).
    pose proof (pa_obj_img_all 65 ltac:(vm_compute; lia)) as O65. pose proof (pa_hi_img 99 ltac:(vm_compute; lia)) as H99.
    pose proof (pa_hi_img 98 ltac:(vm_compute; lia)) as H98. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in O65, H99, H98.
    assert (NB : forall a, in_img SEGS a -> ~ (hb <= a < hb + req_size hn)).
    { intros a Ha Hr. exact (blk_img SEGS B LAWS _ _ _ _ _ _ _ a HAR Hin Hr Ha). }
    unfold in_app, kLowShadowBeg, kHighMemBeg in Hbh_ia.
    split; [|split; [|split]].
    - apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Ra1].
      intros x Hx. unfold shadow_of_addr, SHADOW_OFF. apply KX3; lia.
    - apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem3 _ _); [|exact Ra2].
      intros a Ha. change (length (map (fun b : byte => bv_unsigned b) RATES)) with 12%nat in Ha.
      assert (IA : in_img SEGS a) by (replace a with (VAL (A_OBJ 65) + (a - VAL (A_OBJ 65))) by lia; apply IR1; lia).
      apply KX3; [lia | lia | intros Hc; apply (NB a IA); lia | intros Hc; apply (NB a IA); lia].
    - apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3); [|exact Ra3]. intros k Hk.
      assert (IA : in_img SEGS (VAL (A_HI 99) + 1608 + k)) by (apply (proj1 (IR2 k ltac:(lia)))).
      apply KX3; [lia | lia | intros Hc; apply (NB _ IA); lia | intros Hc; apply (NB _ IA); lia].
    - apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3); [|exact Ra4]. intros k Hk.
      assert (IA : in_img SEGS (VAL (A_HI 98) + 1812 + k)) by (apply (proj2 (IR2 k ltac:(lia)))).
      apply KX3; [lia | lia | intros Hc; apply (NB _ IA); lia | intros Hc; apply (NB _ IA); lia]. }
  split; [exact (hs_fk_apost (@YK11.fp_regs fx) fx fq2 (reac_hunt_step.hs_freg_refl _) Hfr2)
         | exact (hs_fc_apost (@YK11.fp_csr fx) fx fq2 (or_introl eq_refl) Hcsr2)]. }
change (Z_to_bv 64 (BASE + 30656)) with (Z_to_bv 64 (BASE + (AF_both3_reac_hunt_step + 132))).
change (treac_hunt_step_post fx regs ly S W mem md h now H)
  with (hs_post (@YK11.fp_regs fx) (@YK11.fp_csr fx) regs ly S W mem md h now H).
apply (hs_s2 (fx := fq2) PD LD (@YK11.fp_regs fx) (@YK11.fp_csr fx) ly S W regs mem md ch h now hb hn H regs3 mem3 md3 HPRE' HM3).
- rewrite B2, Usp'. unfold w64. f_equal; lia.
- rewrite B3, E3'. reflexivity.
- rewrite B4, E4'. reflexivity.
- rewrite B9, E10'. reflexivity.
- rewrite B18, E11'. reflexivity.
- rewrite B19, E10', unsigned_lit_small by lia. reflexivity.
- rewrite B20, E10', unsigned_lit_small by lia. reflexivity.
- rewrite B22, E32'. reflexivity.
Qed.
End w3.
Lemma hs_postd : hs_loopb_stmt -> hs_postd_stmt.
Proof. intros LBs fq. exact (hs_postd_w (fx := fq) LBs). Qed.
Lemma hs_compose : hs_postd_stmt -> hs_loopd_stmt -> treac_hunt_step_spec.
Proof.
intros PD LD fq ly S W regs mem md ch h now hb hn H HPRE HROD H10 H11 Rnow Hh0 Hh8 Hin Hhb Hhe HOK HG Ra Rb Rc Rd.
exact (hs_walk (fx := fq) PD LD ly S W regs mem md ch h now hb hn H HPRE HROD H10 H11 Rnow Hh0 Hh8 Hin Hhb Hhe HOK HG
  (conj Ra (conj Rb (conj Rc Rd)))).
Qed.
Theorem pb_reac_hunt_step : treac_hunt_step_spec.
Proof. exact (hs_compose (hs_postd pb_hs_loopb) (pb_hs_loopd (hs_postd pb_hs_loopb))). Qed.
End h.
End f.
End d.
