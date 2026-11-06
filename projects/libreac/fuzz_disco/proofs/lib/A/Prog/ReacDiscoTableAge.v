(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 2047 of its 2116 lines of code are new or changed and 300 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YA0o YCbm YA0q YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase
DiscoFrame YC45 YC1g YC1h YC81 YC4b YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c reac_disco_table_age_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_age.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem Bytes PropExec.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import AcpySameDef.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma ble_cons : forall (b : byte) (bs : list byte),
bytes_le_to_Z (b :: bs) = bv_unsigned b + 256 * bytes_le_to_Z bs.
Proof.
intros b bs. cbn [bytes_le_to_Z]. apply Bytes.lor_shiftl8_add.
- pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia.
- apply PropExec.bytes_le_to_Z_nonneg.
Qed.
Lemma ble_nth : forall (bs : list byte) j, (j < length bs)%nat ->
Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat j) mod 256 = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b bs IH]; intros j Hj; cbn [length] in Hj; [lia|].
rewrite ble_cons. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg bs) as Hr.
destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
- cbn [nth]. replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia.
  assert (Hd : Z.shiftr (bv_unsigned b + 256 * bytes_le_to_Z bs) (8 + 8 * Z.of_nat j)
               = Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat j)).
  { rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite <- Z.div_div by lia.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs)
      by (symmetry; Z.div_mod_to_equations; lia).
    reflexivity. }
  rewrite Hd. apply IH. cbn [length] in Hj. lia.
Qed.
Lemma u_at_byte : forall (A : list byte) (k : Z) (n j : nat), 0 <= k -> (Z.to_nat k + n <= length A)%nat -> (j < n)%nat ->
Z_to_bv 8 (YO0f.le_byte (u_at A k n) n j) = nth (Z.to_nat k + j) A (Z_to_bv 8 0).
Proof.
intros A k n j Hk Hn Hj.
assert (LS : length (sub A k n) = n).
{ unfold sub. rewrite length_firstn, length_skipn. lia. }
pose proof (PropExec.bytes_le_to_Z_bound (sub A k n)) as Hb. rewrite LS in Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg (sub A k n)) as Hb0.
rewrite (YI04.le_byte_small (u_at A k n) n j) by (unfold u_at; lia).
assert (E : nth j (sub A k n) (Z_to_bv 8 0) = nth (Z.to_nat k + j) A (Z_to_bv 8 0)).
{ pose proof (reac_disco_table_age.nth_sub A k n j Hk ltac:(lia)) as HN.
  destruct (nth_error A (Z.to_nat k + j)) as [x|] eqn:EA.
  - rewrite (nth_error_nth _ _ (Z_to_bv 8 0) HN), (nth_error_nth _ _ (Z_to_bv 8 0) EA). reflexivity.
  - apply nth_error_None in EA. lia. }
rewrite <- E. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite <- (ble_nth (sub A k n) j ltac:(lia)). unfold u_at. reflexivity.
Qed.
Lemma nth_le_bytes : forall n z j, (j < n)%nat ->
nth j (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat j)).
Proof.
induction n as [|n IH]; intros z j Hj; [lia|].
destruct j as [|j]; cbn [Z_to_le_bytes nth].
- rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
- rewrite (IH (Z.shiftr z 8) j ltac:(cbn [length] in Hj; lia)).
  rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma nth_map_bv : forall (A : list byte) j,
nth j (map (fun b : byte => bv_unsigned b) A) 0 = bv_unsigned (nth j A (Z_to_bv 8 0)).
Proof.
intros A j. rewrite <- (map_nth (fun b : byte => bv_unsigned b) A (Z_to_bv 8 0) j). reflexivity.
Qed.
Lemma mbytes_of_garr8 : forall (m : word -> option byte) (p : Z) (A : list byte),
garr8 SEGS m p (map (fun b : byte => bv_unsigned b) A) ->
forall j, (j < length A)%nat -> mbyte SEGS m (p + Z.of_nat j) = Some (nth j A (Z_to_bv 8 0)).
Proof.
intros m p A HG j Hj.
rewrite (garr8_mbyte SEGS m p _ j HG ltac:(rewrite length_map; exact Hj)).
f_equal. rewrite nth_map_bv. apply Z_to_bv_bv_unsigned.
Qed.
Lemma garr8_of_mbytes : forall (m : word -> option byte) (p : Z) (A : list byte),
(forall j, (j < length A)%nat -> mbyte SEGS m (p + Z.of_nat j) = Some (nth j A (Z_to_bv 8 0))) ->
garr8 SEGS m p (map (fun b : byte => bv_unsigned b) A).
Proof.
intros m p A HM j Hj. rewrite length_map in Hj. rewrite nth_map_bv.
pose proof (bv_unsigned_in_range 8 (nth j A (Z_to_bv 8 0))) as HR. change (bv_modulus 8) with 256 in HR.
split; [|exact HR].
intros i Hi. destruct i as [|i]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (HM j Hj). f_equal. rewrite YC88.le_byte_1_0 by exact HR. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma age_val : forall (m : word -> option byte) (A : list byte) (p k : Z) (n : nat),
garr8 SEGS m p (map (fun b : byte => bv_unsigned b) A) -> 0 <= k -> (Z.to_nat k + n <= length A)%nat ->
val_mem SEGS m (p + k) n (u_at A k n).
Proof.
intros m A p k n HG Hk Hn j Hj.
rewrite (u_at_byte A k n j Hk Hn Hj).
replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia.
apply (mbytes_of_garr8 m p A HG). lia.
Qed.
Lemma age_garr8_upd : forall (m m' : word -> option byte) (A v : list byte) (p k : Z),
garr8 SEGS m p (map (fun b : byte => bv_unsigned b) A) ->
0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length A) ->
(forall j, (j < length v)%nat -> mbyte SEGS m' (p + k + Z.of_nat j) = Some (nth j v (Z_to_bv 8 0))) ->
(forall a, p <= a < p + Z.of_nat (length A) -> ~ (p + k <= a < p + k + Z.of_nat (length v)) ->
 mbyte SEGS m' a = mbyte SEGS m a) ->
garr8 SEGS m' p (map (fun b : byte => bv_unsigned b) (upd A k v)).
Proof.
intros m m' A v p k HG Hk Hv HIN HOUT.
assert (LU : length (upd A k v) = length A) by (apply reac_disco_table_age.length_upd; lia).
apply garr8_of_mbytes. intros j Hj. rewrite LU in Hj.
pose proof (reac_disco_table_age.nth_upd A k v j Hk Hv Hj) as HN.
destruct (nth_error (upd A k v) j) as [x|] eqn:EU; [|apply nth_error_None in EU; exfalso; lia].
rewrite (nth_error_nth _ _ (Z_to_bv 8 0) EU).
destruct ((Z.to_nat k <=? j)%nat && (j <? Z.to_nat k + length v)%nat)%bool eqn:EB.
- apply andb_prop in EB as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
  replace (p + Z.of_nat j) with (p + k + Z.of_nat (j - Z.to_nat k)%nat) by lia.
  rewrite (HIN (j - Z.to_nat k)%nat ltac:(lia)).
  f_equal. exact (nth_error_nth _ _ (Z_to_bv 8 0) (eq_sym HN)).
- rewrite HOUT; [ | lia |
    apply Bool.andb_false_iff in EB as [E1 | E1];
    [apply Nat.leb_gt in E1 | apply Nat.ltb_ge in E1]; lia ].
  rewrite (mbytes_of_garr8 m p A HG j ltac:(lia)).
  f_equal. exact (nth_error_nth _ _ (Z_to_bv 8 0) (eq_sym HN)).
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis AMEMCPYEQ : forall fq : YK11.FPState, acpy_same_realizes (fx := fq) SEGS B (SIGMA DS___asan_memcpy).
Definition REAC_DISCO_TABLE_AGE_STK : Z := 80 + ESTACK.
Definition treac_disco_table_age_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (sp t : Z) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_TABLE_AGE_STK <= a < sp) -> ~ (t <= a < t + 400) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (t <= b + i < t + 400) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ (t <= a < t + 400) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_TABLE_AGE_STK <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, sp - REAC_DISCO_TABLE_AGE_STK <= a < sp -> apresent (w_H W2) mem2 a).
Definition treac_disco_table_age_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z))
  (ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (t now : Z) (T : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (T' : list byte) (removed : Z),
    c2 = mkCfg (mkst (fx := fq) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ getr regs2 10 = w64 removed /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    treac_disco_table_age_kept lyc Sc W memc W2 mem2 (spZ regs) t /\
    W2 = W /\
    (forall a : word, ~ (t <= bv_unsigned a < t + 400) ->
       ~ (spZ regs - REAC_DISCO_TABLE_AGE_STK <= bv_unsigned a < spZ regs) ->
       aview SEGS (w_H W) mem2 (bv_unsigned a) = aview SEGS (w_H W) memc (bv_unsigned a)) /\
    garr8 SEGS (mrestrict (w_H W2) mem2) t (map (fun b : byte => bv_unsigned b) T') /\
    age_model T now = (T', removed) /\ age_post T now T' removed.
Definition treac_disco_table_age_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (t now : Z) (T : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_TABLE_AGE_STK -> spZ regs <= sp0 ->
  0 < t -> t mod 8 = 0 -> t + 400 <= 2 ^ 63 -> amem_range t 400 ->
  (spZ regs <= t \/ t + 400 <= spZ regs - REAC_DISCO_TABLE_AGE_STK) ->
  (forall a, t <= a < t + 400 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF t 400 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) t 400 ->
  length T = 400%nat -> table_ok T ->
  garr8 SEGS (mrestrict (w_H W) memc) t (map (fun b : byte => bv_unsigned b) T) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_disco_table_age) regs memc mdc)
    (treac_disco_table_age_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs t now T).
Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Definition AGE_Bx : sv := SOff 32 0.
Definition AGE_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition age_regions : smem := [ stack_region 80; got_regionP; bcell_regionP 32;
  YP09.mkRegion (Some 10%nat) 384 400 384 384 [YP09.mkChunk 384 (CVal 4 (SOff 33 0))] ].
Definition age_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 8 (2 ^ 47 - 400) 3);
            (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 8 0) ] [] [].
Definition ss_age : sstate := mkSS AF_reac_disco_table_age sr_atoms age_regions None age_facts.
Definition age_SH : list shent := [mkSHE 10 0 400].
Definition age_extra (T : list byte) : list word := map (Z_to_bv 64) [SB; n_of T].
Definition EA (regs : bvmap 5 word) (T : list byte) : env := Eimg (Ereg regs (age_extra T)).
Lemma u_of_n : forall T : list byte, length T = 400%nat -> 0 <= n_of T -> u_at T 384 4 = n_of T.
Proof.
intros T LT Hn. unfold n_of, s32_at in *.
assert (LS : length (sub T 384 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn; lia).
pose proof (PropExec.bytes_le_to_Z_bound (sub T 384 4)) as Hb. rewrite LS in Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg (sub T 384 4)) as Hb0.
unfold u_at in *. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb.
unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 32) with (2 ^ 31) in *.
change (bv_modulus 32) with (2 ^ 32) in *. Z.div_mod_to_equations. lia.
Qed.
Lemma age_kept_of : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 mem2 md2 k2 (sp t : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem2 md2 k2 ->
sp0 - STK <= sp - REAC_DISCO_TABLE_AGE_STK -> sp <= sp0 ->
(t + 400 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= t) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_TABLE_AGE_STK <= a < sp) -> ~ (t <= a < t + 400) ->
   aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
treac_disco_table_age_kept lyc Sc W memc W mem2 sp t.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 mem2 md2 k2 sp t
  HJ HJ2 Hwlo Hwhi Hoff HKEPT HPRES.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HIMGT : YImgTop.IMG_TOP = 6283264) by reflexivity.
assert (HIMGL : YImgTop.IMG_LO = 65536) by reflexivity.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof Hstatic as (Hsp016 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof pa_segs_low as Hsegs.
assert (HS1 : REAC_DISCO_TABLE_AGE_STK = 4176) by reflexivity.
assert (Hlo : alloc_ceiling <= sp - REAC_DISCO_TABLE_AGE_STK) by lia.
split; [intros a Ha Hw Ht; apply HKEPT; [lia | exact Hw | exact Ht]|].
split.
{ intros b m i Hb Hi Ht.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4096 & Hbceil & _ & _ & _).
  apply HKEPT; [lia | lia | exact Ht]. }
split.
{ intros a Himg Hown Herr. pose proof (Hsegs a Himg) as Hsl.
  pose proof (pa_img_range a Himg) as Hir.
  apply HKEPT; [unfold kLowMemEnd in Hsl; lia | unfold kLowMemEnd in Hsl; lia | lia]. }
split.
{ intros cid pos a Hf Hcase Ht.
  destruct (frames_bounds _ _ LAWS lyc Sc W memc mdc cid pos HAR Hf) as (Hf4096 & Hfceil & _).
  unfold in_zr, frame_rng in Hcase. cbn [fst snd] in Hcase.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  destruct Hcase as [Hfr | Hsh].
  - apply HKEPT; [lia | lia | exact Ht].
  - unfold shadow_addr, SHADOW_OFF in Hsh. cbn [fst snd] in Hsh.
    assert (HA1 : 0 <= a < 2 ^ 64 /\ ~ (sp - REAC_DISCO_TABLE_AGE_STK <= a < sp)).
    { clear - Hsh Hf4096 Hfceil Hfb C1 Hceil Hslo Hwlo Hwhi HS1.
      unfold REAC_DISCO_TABLE_AGE_STK in *. Z.div_mod_to_equations. lia. }
    apply HKEPT; [exact (proj1 HA1) | exact (proj2 HA1) | exact Ht]. }
split; [intros a Ha Hw Hp; apply HPRES; exact Hp|].
intros a Ha. apply Hpres2. lia.
Qed.
Section w. Context {fx : YK11.FPState}.
Lemma age_t_app : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (t : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
0 < t -> t mod 8 = 0 -> amem_range t 400 -> 8 <= t /\ t + 400 <= 2 ^ 47 /\
(forall x, t <= x < t + 400 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k t HJ Ht0 Ht8 HAM.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity. rewrite HSO.
assert (H8 : 8 <= t) by (Z.div_mod_to_equations; lia).
split; [exact H8|]. split; [lia|]. intros x Hx. lia.
Qed.
Lemma age_t_off : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (t : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(forall a, t <= a < t + 400 ->
   awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
t + 400 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= t.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k t HJ HWR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HIMGT : YImgTop.IMG_TOP = 6283264) by reflexivity.
assert (HIMGL : YImgTop.IMG_LO = 65536) by reflexivity.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
destruct (Z.le_gt_cases (t + 400) YImgTop.IMG_LO) as [HL|H1]; [left; exact HL|].
destruct (Z.le_gt_cases YImgTop.IMG_TOP t) as [HT|H2]; [right; exact HT|]. exfalso.
set (a := Z.max t YImgTop.IMG_LO) in *.
assert (Ha : t <= a < t + 400) by (unfold a; lia).
assert (Hin : YImgTop.IMG_LO <= a < YImgTop.IMG_TOP) by (unfold a; lia).
destruct (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ
  (proj1 (HWR a Ha))) as (_ & [Hst | [ (Happ & b & n & Hb & Hr & _) | (cid & pos & Hf & Hcase) ]]).
- lia.
- pose proof (blk_off_imgP _ _ _ _ _ _ b n HAR Hb) as Hoff. unfold off_img in Hoff. lia.
- assert (Hf' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hf).
  pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hf') as Hoff.
  unfold off_img in Hoff. unfold in_zr, frame_rng in Hcase. cbn [fst snd] in Hcase.
  destruct Hcase as [(_ & Hfr) | (Hsh & _)]; lia.
Qed.
Definition XE : sv :=
  SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SUB (SAlu ALU_SLL (SOff 35 0) (SLit 6)) (SAlu ALU_SLL (SOff 35 0) (SLit 4))).
Definition LP_Bx : sv := SOff 34 0.
Definition SH5 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 384) (SLit 3)) (SOff 34 0).
Definition age_sh5 (t : Z) : word :=
  alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (t + 384)) (Z_to_bv 64 3)) (Z_to_bv 64 SB).
Definition lp_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    8%bv (SOff 36 0)) 9%bv (SOff 32 384)) 18%bv (SOff 32 0)) 19%bv (SOff 33 0)) 20%bv (SOff 34 0))
    21%bv SH5) 22%bv (SOff 35 0)) 23%bv (SLit 5000000001)) 24%bv (SLit 3)) 12%bv (SOff 37 0).
Definition lp_stack : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 80 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 50 0)); YP09.mkChunk 8 (CVal 8 (SOff 49 0));
     YP09.mkChunk 16 (CVal 8 (SOff 48 0)); YP09.mkChunk 24 (CVal 8 (SOff 47 0));
     YP09.mkChunk 32 (CVal 8 (SOff 46 0)); YP09.mkChunk 40 (CVal 8 (SOff 45 0));
     YP09.mkChunk 48 (CVal 8 (SOff 44 0)); YP09.mkChunk 56 (CVal 8 (SOff 43 0));
     YP09.mkChunk 64 (CVal 8 (SOff 42 0)); YP09.mkChunk 72 (CVal 8 (SOff 41 0))].
Definition lp_regions : smem := [ lp_stack; got_regionP; bcell_regionP 34;
  YP09.mkRegion (Some 32%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 37 0))];
  YP09.mkRegion (Some 32%nat) 392 396 392 396 [YP09.mkChunk 392 (CVal 4 (SOff 40 0))];
  YP09.mkRegion (Some 38%nat) 0 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 39 0))] ].
Definition lp_facts : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF 8 (2 ^ 47 - 400) 3);
    (33%nat, mkAF 0 (2 ^ 64 - 1) 0); (34%nat, mkAF SB SB 0);
    (35%nat, mkAF 0 7 0); (36%nat, mkAF 0 8 0); (37%nat, mkAF 0 8 0);
    (38%nat, mkAF 8 (2 ^ 47 - 64) 3); (39%nat, mkAF 0 (2 ^ 64 - 1) 0); (40%nat, mkAF 0 (2 ^ 32 - 1) 0) ]
  [ mkAC BC_LT (SOff 35 0) (SOff 37 0) ] [ (XE, SOff 38 0) ].
Definition ss_lp : sstate := mkSS (AF_reac_disco_table_age + 124) lp_regs lp_regions None lp_facts.
Definition lp_SH : list shent := [mkSHE 32 0 400; mkSHE 38 0 48].
Definition lp_extra (regs : bvmap 5 word) (t now i mm r e lst sq : Z) : list word :=
  map (Z_to_bv 64) [t; now; SB; i; r; mm; e; lst; sq] ++
  [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20;
   getr regs 21; getr regs 22; getr regs 23; getr regs 24].
Definition EL (regsL regs : bvmap 5 word) (t now i mm r e lst sq : Z) : env :=
  Eimg (Ereg regsL (lp_extra regs t now i mm r e lst sq)).
Lemma branch_lt_S : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_lts, Sg. reflexivity. Qed.
Lemma branch_ge_S : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_lts, Sg. reflexivity. Qed.
Lemma S_small : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 62 -> - 2 ^ 62 <= c < 2 ^ 62 ->
Sg E (SOff n c) = v + c.
Proof.
intros E n v c H Hv Hc. rewrite S_SOff, H, unsigned_lit_small by lia.
apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia.
Qed.
Lemma ra_transfer : forall (m m' : word -> option byte) (W : world SEGS) (a n : Z),
(forall x, a <= x < a + n -> aview SEGS (w_H W) m' (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W) m (shadow_of_addr SHADOW_OFF x)) ->
range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n ->
range_addressable (aview SEGS (w_H W) m') SHADOW_OFF a n.
Proof.
intros m m' W a n HE HRA x Hx. destruct (HRA x Hx) as (sv & Hsv & Hok).
exists sv. split; [rewrite (HE x Hx); exact Hsv | exact Hok].
Qed.
Definition lp_frame (m : word -> option byte) (sp : Z) (regs : bvmap 5 word) : Prop :=
  val_mem SEGS m (sp - 80 + 0) 8 (bv_unsigned (getr regs 24)) /\
  val_mem SEGS m (sp - 80 + 8) 8 (bv_unsigned (getr regs 23)) /\
  val_mem SEGS m (sp - 80 + 16) 8 (bv_unsigned (getr regs 22)) /\
  val_mem SEGS m (sp - 80 + 24) 8 (bv_unsigned (getr regs 21)) /\
  val_mem SEGS m (sp - 80 + 32) 8 (bv_unsigned (getr regs 20)) /\
  val_mem SEGS m (sp - 80 + 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem SEGS m (sp - 80 + 48) 8 (bv_unsigned (getr regs 18)) /\
  val_mem SEGS m (sp - 80 + 56) 8 (bv_unsigned (getr regs 9)) /\
  val_mem SEGS m (sp - 80 + 64) 8 (bv_unsigned (getr regs 8)) /\
  val_mem SEGS m (sp - 80 + 72) 8 (bv_unsigned (getr regs 1)).
Lemma age_lp_entry : forall lyc Sc (W : world SEGS) memL mdL (regsL regs : bvmap 5 word)
  (t now i mm r : Z) (X : list byte),
AR SEGS B lyc Sc W memL mdL ->
8 <= t -> t + 400 <= 2 ^ 47 -> t mod 8 = 0 -> 0 <= now < 2 ^ 64 ->
(t + 400 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= t) -> amem_range t 400 ->
0 <= i -> i < mm -> mm <= 8 -> 0 <= r <= 8 ->
2 ^ 46 + 4176 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(spZ regs <= t \/ t + 400 <= spZ regs - REAC_DISCO_TABLE_AGE_STK) ->
getr regsL 2 = w64 (spZ regs - 80) ->
getr regsL 8 = w64 r -> getr regsL 9 = w64 (t + 384) -> getr regsL 18 = w64 t ->
getr regsL 19 = w64 now -> getr regsL 20 = w64 SB -> getr regsL 21 = age_sh5 t ->
getr regsL 22 = w64 i -> getr regsL 23 = w64 5000000001 -> getr regsL 24 = w64 3 ->
getr regsL 12 = w64 mm ->
length X = 400%nat -> n_of X = mm ->
garr8 SEGS (mrestrict (w_H W) memL) t (map (fun b : byte => bv_unsigned b) X) ->
(forall a, t <= a < t + 400 -> apresent (w_H W) memL a) ->
range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF t 400 ->
lp_frame (mrestrict (w_H W) memL) (spZ regs) regs ->
st_ok_pi SEGS VAL (EL regsL regs t now i mm r (t + 48 * i) (last_of X i) (seq_of X)) ss_lp
  (restrict (w_H W) (mkst (fx := fx) regsL (Z_to_bv 64 (BASE + (AF_reac_disco_table_age + 124))) memL (seg_rom SEGS)))
/\ sh_ok SEGS LP_Bx lp_SH (EL regsL regs t now i mm r (t + 48 * i) (last_of X i) (seq_of X))
     (mrestrict (w_H W) memL).
Proof.
intros lyc Sc W memL mdL regsL regs t now i mm r X HAR Ht8 Ht47 Htal Hnow Hoff HAM Hi0 Him Hmm Hr
  Hsprng Hsp16 Hside R2 R8 R9 R18 R19 R20 R21 R22 R23 R24 R12 LX HnX HG HPR HRA HFR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HIMGT : YImgTop.IMG_TOP = 6283264) by reflexivity.
assert (HIMGL : YImgTop.IMG_LO = 65536) by reflexivity.
assert (HS1 : REAC_DISCO_TABLE_AGE_STK = 4176) by reflexivity.
assert (Hband : forall x, t <= x < t + 400 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
  assert (HSO : SHADOW_OFF = 2147450880) by reflexivity. rewrite HSO. intros x Hx. lia. }
pose proof (reac_disco_table_age.last_range X i LX ltac:(lia)) as HLR.
pose proof (reac_disco_table_age.seq_range X) as HSR.
destruct (al_const _ _ LAWS lyc Sc W memL mdL HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR.
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
destruct HFR as (F80 & F72 & F64 & F56 & F48 & F40 & F32 & F24 & F16 & F8).
rewrite restrict_mkst_fx.
set (E := EL regsL regs t now i mm r (t + 48 * i) (last_of X i) (seq_of X)) in *.
assert (EL0 : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsL (lp_extra regs t now i mm r (t + 48 * i) (last_of X i) (seq_of X))) n)
by (intros n Hn; subst E; unfold EL; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 19)%nat -> ew E (32 + j)%nat = nth j (lp_extra regs t now i mm r (t + 48 * i) (last_of X i) (seq_of X)) (Z_to_bv 64 0))
by (intros j Hj; rewrite EL0 by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E2 : ew E 2 = getr regsL 2) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41.
pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44. pose proof (EX 13%nat ltac:(lia)) as E45.
pose proof (EX 14%nat ltac:(lia)) as E46. pose proof (EX 15%nat ltac:(lia)) as E47.
pose proof (EX 16%nat ltac:(lia)) as E48. pose proof (EX 17%nat ltac:(lia)) as E49.
pose proof (EX 18%nat ltac:(lia)) as E50.
cbn [lp_extra map app nth Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50.
assert (Eo66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; unfold EL; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EL; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 80) by (rewrite E2, R2; apply unsigned_lit_small; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (HU38 : U E (SOff 38 0) = t + 48 * i) by (apply (U_atom E 38 (t + 48 * i) E38); lia).
assert (HU35 : U E (SOff 35 0) = i) by (apply (U_atom E 35 i E35); lia).
assert (HU32 : U E (SOff 32 0) = t) by (apply (U_atom E 32 t E32); lia).
split.
- unfold ss_lp. apply pa_entry_st_ok_full.
  + unfold lp_regs.
    repeat (apply regs_ok_pin;
      [ | intros XX; discriminate XX
      | cbn [sv_denot SH5]; rewrite ?E32, ?E33, ?E34, ?E35, ?E36, ?E37;
        rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
        first [ exact R8 | exact R9 | exact R18 | exact R19 | exact R20 | exact R22 | exact R23 | exact R24 | exact R12
              | rewrite R21; unfold age_sh5; rewrite !unsigned_lit_small by lia; reflexivity
              | rewrite unsigned_lit_small by lia; exact R9
              | match goal with |- ?g => idtac "REGSOKFAIL" g end ] ]).
    apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold lp_regions, lp_stack, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 2%nat (spZ regs - 80) ltac:(rewrite E2, R2; reflexivity) ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat (apply Forall_cons;
        [ eapply (chunk_ok_val SEGS E _ (spZ regs - 80) _ 8 _ _);
          [ cbn [sv_denot]; rewrite ?E41, ?E42, ?E43, ?E44, ?E45, ?E46, ?E47, ?E48, ?E49, ?E50, Z.add_0_r; reflexivity
          | match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as HBR end;
            unfold bv_modulus in HBR; cbn in HBR; cbn; lia
          | zside
          | first [ exact F80 | exact F72 | exact F64 | exact F56 | exact F48 | exact F40 | exact F32 | exact F24 | exact F16 | exact F8 ] ] |]).
      apply Forall_nil.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
      [cbn [sv_denot]; rewrite Eo66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memL _ _ Kgot).
    * rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Eo66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 LP_Bx SB);
      [cbn [sv_denot LP_Bx]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memL _ _ Kcell).
    * rewrite (VB 32%nat t E32) by lia.
      split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPR; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ t 384 4 (SOff 37 0) mm);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite <- HnX. rewrite <- (u_of_n X LX ltac:(lia)).
      apply (age_val _ X t 384 4 HG); [lia | rewrite LX; cbn; lia].
    * rewrite (VB 32%nat t E32) by lia.
      split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPR; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ t 392 4 (SOff 40 0) (seq_of X));
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      unfold seq_of. apply (age_val _ X t 392 4 HG); [lia | rewrite LX; cbn; lia].
    * rewrite (VB 38%nat (t + 48 * i) E38) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (t + 48 * i) 40 8 (SOff 39 0) (last_of X i));
      [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      unfold last_of. replace (t + 48 * i + 40) with (t + (48 * i + 40)) by lia.
      apply (age_val _ X t (48 * i + 40) 8 HG); [lia | rewrite LX; lia].
  + apply pairwise_disjoint_of_extents. unfold lp_regions, lp_stack, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 32%nat t E32) by lia. rewrite (VB 38%nat (t + 48 * i) E38) by lia.
    rewrite (VB 2%nat (spZ regs - 80) ltac:(rewrite E2, R2; reflexivity) ltac:(lia)).
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Eo66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hside Hoff HcellR HgcD HgotR HIMGT HIMGL Hsprng Ht8 Ht47 Hi0 Him Hmm C1 HS1. clear. intros.
    repeat split; lia.
  + split.
    { cbn [lp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E32, E33, E34, E35, E36, E37, E38, E39, E40, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      revert Hsprng Hsp16 Ht8 Ht47 Htal Hnow Hi0 Him Hmm Hr HLR HSR. unfold SB. clear. intros.
      repeat match goal with |- _ /\ _ => split end;
      first [lia | exact I | (Z.div_mod_to_equations; lia)]. }
    split.
    { cbn [lp_facts f_conds conds_ok]. split; [|exact I].
      unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite branch_lt_S. rewrite (S_SOff E 35 0), (S_SOff E 37 0), E35, E37, !unsigned_lit_small by lia.
      rewrite !Z.add_0_r, !(bv_swrap_small 64) by (change (bv_half_modulus 64) with (2 ^ 63); lia). apply Z.ltb_lt. lia. }
    { cbn [lp_facts f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite HU38. unfold XE. rewrite U_SAlu. cbn [zalu_raw].
      rewrite HU32. rewrite U_SAlu. cbn [zalu_raw].
      rewrite !U_SAlu. cbn [zalu_raw]. rewrite HU35, !U_SLit.
      rewrite !(zcanon_id 6), !(zcanon_id 4) by (unfold M64; lia).
      change (Z.land 6 63) with 6. change (Z.land 4 63) with 4.
      rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64. change (2 ^ 4) with 16.
      rewrite !(zcanon_id (i * 64)), !(zcanon_id (i * 16)) by (unfold M64; lia).
      rewrite (zcanon_id (i * 64 - i * 16)) by (unfold M64; lia).
      replace (i * 64 - i * 16) with (48 * i) by lia.
      apply zcanon_id. unfold M64. lia. }
- unfold sh_ok, lp_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) memL E LP_Bx 32 t 400 t 0 400 HRA).
    * unfold U, LP_Bx. cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * exact HU32.
    * lia.
    * lia.
    * intros x Hx. apply Hband. lia.
  + apply (shent_ok_of_range SEGS (w_H W) memL E LP_Bx 38 t 400 (t + 48 * i) 0 48 HRA).
    * unfold U, LP_Bx. cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * exact HU38.
    * lia.
    * lia.
    * intros x Hx. apply Hband. lia.
Qed.
Lemma age_preserved : forall (regs regs2 : bvmap 5 word),
getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
getr regs2 18 = getr regs 18 -> getr regs2 19 = getr regs 19 -> getr regs2 20 = getr regs 20 ->
getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 -> getr regs2 23 = getr regs 23 ->
getr regs2 24 = getr regs 24 -> getr regs2 25 = getr regs 25 -> getr regs2 26 = getr regs 26 ->
getr regs2 27 = getr regs 27 ->
aregs_preserved regs regs2.
Proof.
intros regs regs2 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 rr Hr.
unfold acallee_saved in Hr.
assert (HC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
             rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
repeat (destruct HC as [-> | HC]); try (subst rr);
  match goal with |- getr _ ?x = getr _ ?x => let y := eval vm_compute in x in change x with y end;
  assumption.
Qed.
Lemma ra_sub : forall rd (a n a' n' : Z), range_addressable rd SHADOW_OFF a n ->
a <= a' -> a' + n' <= a + n -> range_addressable rd SHADOW_OFF a' n'.
Proof. intros rd a n a' n' H Hlo Hhi x Hx. apply H. lia. Qed.
Lemma amem_sub : forall (a n a' n' : Z), amem_range a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> amem_range a' n'.
Proof. intros a n a' n' H Hlo Hn Hhi. unfold amem_range in *. lia. Qed.
Lemma hull_sub : forall rd (a n a' n' : Z), shadow_hull_vis rd a n ->
a <= a' -> 0 < n' -> a' + n' <= a + n -> shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' H Hlo Hn Hhi s Hs. apply H.
pose proof (shadow_mono a a' Hlo) as M1.
pose proof (shadow_mono (a' + n' - 1) (a + n - 1) ltac:(lia)) as M2.
pose proof (Z.div_le_mono (shadow_addr a) (shadow_addr a') 8 ltac:(lia) M1) as D1.
pose proof (Z.div_le_mono (shadow_addr (a' + n' - 1)) (shadow_addr (a + n - 1)) 8 ltac:(lia) M2) as D2.
lia.
Qed.
Lemma hull_transfer : forall (m m' : word -> option byte) (W : world SEGS) (a n : Z),
(forall s, shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
   aview SEGS (w_H W) m' s = aview SEGS (w_H W) m s) ->
shadow_hull_vis (aview SEGS (w_H W) m) a n -> shadow_hull_vis (aview SEGS (w_H W) m') a n.
Proof. intros m m' W a n HE H s Hs. rewrite (HE s Hs). apply H. exact Hs. Qed.
Lemma age_store4 : forall (m m' : word -> option byte) (X : list byte) (t k v : Z),
garr8 SEGS m t (map (fun b : byte => bv_unsigned b) X) -> length X = 400%nat ->
0 <= k -> k + 4 <= 400 -> 0 <= v < 2 ^ 32 ->
val_mem SEGS m' (t + k) 4 v ->
(forall a, t <= a < t + 400 -> ~ (t + k <= a < t + k + 4) -> mbyte SEGS m' a = mbyte SEGS m a) ->
garr8 SEGS m' t (map (fun b : byte => bv_unsigned b) (upd X k (Mem.le4 (Z_to_bv 64 v)))).
Proof.
intros m m' X t k v HG LX Hk Hk4 Hv HV HOUT.
assert (L4 : length (Mem.le4 (Z_to_bv 64 v)) = 4%nat) by apply Mem.length_le4.
apply (age_garr8_upd m m' X (Mem.le4 (Z_to_bv 64 v)) t k HG Hk ltac:(rewrite L4, LX; lia)).
- intros j Hj. rewrite L4 in Hj.
  replace (t + k + Z.of_nat j) with (t + k + Z.of_nat j) by lia.
  rewrite (HV j Hj). f_equal.
  unfold Mem.le4. rewrite (nth_le_bytes 4 (bv_unsigned (Z_to_bv 64 v)) j Hj).
  rewrite unsigned_lit_small by lia.
  rewrite (YI04.le_byte_small v 4 j ltac:(change (8 * Z.of_nat 4) with 32; lia) Hj). reflexivity.
- intros a Ha Hna. rewrite L4 in Hna. rewrite LX in Ha. apply HOUT; lia.
Qed.
Lemma le4_byte : forall v j, 0 <= v < 2 ^ 32 -> (j < 4)%nat ->
nth j (Mem.le4 (Z_to_bv 64 v)) (Z_to_bv 8 0) = Z_to_bv 8 (YO0f.le_byte v 4 j).
Proof.
intros v j Hv Hj. unfold Mem.le4. rewrite (nth_le_bytes 4 (bv_unsigned (Z_to_bv 64 v)) j Hj).
rewrite unsigned_lit_small by lia.
rewrite (YI04.le_byte_small v 4 j ltac:(change (8 * Z.of_nat 4) with 32; lia) Hj). reflexivity.
Qed.
Lemma le4_ble : forall L : list byte, length L = 4%nat -> Mem.le4 (Z_to_bv 64 (bytes_le_to_Z L)) = L.
Proof.
intros L HL. pose proof (PropExec.bytes_le_to_Z_bound L) as Hb. rewrite HL in Hb.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb. pose proof (PropExec.bytes_le_to_Z_nonneg L) as Hb0.
apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [rewrite Mem.length_le4, HL; reflexivity|].
intros j Hj. rewrite Mem.length_le4 in Hj. unfold Mem.le4.
rewrite (nth_le_bytes 4 _ j Hj). rewrite unsigned_lit_small by lia.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply (ble_nth L j). lia.
Qed.
Lemma upd_seq_self : forall Y : list byte, length Y = 400%nat -> upd Y 392 (Mem.le4 (Z_to_bv 64 (seq_of Y))) = Y.
Proof.
intros Y LY. unfold seq_of, u_at.
rewrite le4_ble by (unfold sub; rewrite length_firstn, length_skipn; lia).
apply reac_disco_table_age.upd_self; rewrite ?LY; lia.
Qed.
Lemma age_garr8_same : forall (m m' : word -> option byte) (X : list byte) (t nv sv : Z),
garr8 SEGS m t (map (fun b : byte => bv_unsigned b) X) -> length X = 400%nat ->
(forall a, t <= a < t + 400 -> ~ (t + 384 <= a < t + 388) -> ~ (t + 392 <= a < t + 396) ->
 mbyte SEGS m' a = mbyte SEGS m a) ->
val_mem SEGS m (t + 384) 4 nv -> val_mem SEGS m' (t + 384) 4 nv ->
val_mem SEGS m (t + 392) 4 sv -> val_mem SEGS m' (t + 392) 4 sv ->
garr8 SEGS m' t (map (fun b : byte => bv_unsigned b) X).
Proof.
intros m m' X t nv sv HG LX HOUT V1 V1' V2 V2'.
apply (garr8_frame SEGS m m' t _ HG). intros a Ha. rewrite length_map, LX in Ha.
destruct (Z_lt_le_dec a (t + 384)) as [Ha1|Ha1]; [apply HOUT; lia|].
destruct (Z_lt_le_dec a (t + 388)) as [Ha2|Ha2].
{ replace a with (t + 384 + Z.of_nat (Z.to_nat (a - (t + 384)))) by lia.
  rewrite (V1 (Z.to_nat (a - (t + 384))) ltac:(lia)), (V1' (Z.to_nat (a - (t + 384))) ltac:(lia)). reflexivity. }
destruct (Z_lt_le_dec a (t + 392)) as [Ha3|Ha3]; [apply HOUT; lia|].
destruct (Z_lt_le_dec a (t + 396)) as [Ha4|Ha4]; [|apply HOUT; lia].
replace a with (t + 392 + Z.of_nat (Z.to_nat (a - (t + 392)))) by lia.
rewrite (V2 (Z.to_nat (a - (t + 392))) ltac:(lia)), (V2' (Z.to_nat (a - (t + 392))) ltac:(lia)). reflexivity.
Qed.
Lemma age_garr8_fields : forall (m m' : word -> option byte) (X : list byte) (t nv sv : Z),
garr8 SEGS m t (map (fun b : byte => bv_unsigned b) X) -> length X = 400%nat ->
0 <= nv < 2 ^ 32 -> 0 <= sv < 2 ^ 32 ->
(forall a, t <= a < t + 400 -> ~ (t + 384 <= a < t + 388) -> ~ (t + 392 <= a < t + 396) ->
 mbyte SEGS m' a = mbyte SEGS m a) ->
val_mem SEGS m' (t + 384) 4 nv -> val_mem SEGS m' (t + 392) 4 sv ->
garr8 SEGS m' t (map (fun b : byte => bv_unsigned b)
  (upd (upd X 384 (Mem.le4 (Z_to_bv 64 nv))) 392 (Mem.le4 (Z_to_bv 64 sv)))).
Proof.
intros m m' X t nv sv HG LX Hnv Hsv HOUT V1 V2.
set (v1 := Mem.le4 (Z_to_bv 64 nv)). set (v2 := Mem.le4 (Z_to_bv 64 sv)).
assert (L1 : length v1 = 4%nat) by apply Mem.length_le4.
assert (L2 : length v2 = 4%nat) by apply Mem.length_le4.
assert (LY : length (upd X 384 v1) = 400%nat) by (rewrite reac_disco_table_age.length_upd; rewrite ?L1, ?LX; lia).
assert (LZ : length (upd (upd X 384 v1) 392 v2) = 400%nat) by (rewrite reac_disco_table_age.length_upd; rewrite ?L2, ?LY; lia).
apply garr8_of_mbytes. intros j Hj. rewrite LZ in Hj.
pose proof (reac_disco_table_age.nth_upd (upd X 384 v1) 392 v2 j ltac:(lia) ltac:(rewrite L2, LY; lia) ltac:(lia)) as HN2.
pose proof (reac_disco_table_age.nth_upd X 384 v1 j ltac:(lia) ltac:(rewrite L1, LX; lia) ltac:(lia)) as HN1.
rewrite L2 in HN2. rewrite L1 in HN1. change (Z.to_nat 392) with 392%nat in HN2. change (Z.to_nat 384) with 384%nat in HN1.
destruct (nth_error (upd (upd X 384 v1) 392 v2) j) as [x|] eqn:EU; [|apply nth_error_None in EU; exfalso; lia].
rewrite (nth_error_nth _ _ (Z_to_bv 8 0) EU).
destruct ((392 <=? j)%nat && (j <? 392 + 4)%nat)%bool eqn:EB2.
- apply andb_prop in EB2 as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
  replace (t + Z.of_nat j) with (t + 392 + Z.of_nat (j - 392)%nat) by lia.
  rewrite (V2 (j - 392)%nat ltac:(lia)). f_equal.
  rewrite <- (le4_byte sv (j - 392)%nat Hsv ltac:(lia)). fold v2.
  exact (nth_error_nth _ _ (Z_to_bv 8 0) (eq_sym HN2)).
- rewrite HN1 in HN2.
  destruct ((384 <=? j)%nat && (j <? 384 + 4)%nat)%bool eqn:EB1.
  + apply andb_prop in EB1 as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
    replace (t + Z.of_nat j) with (t + 384 + Z.of_nat (j - 384)%nat) by lia.
    rewrite (V1 (j - 384)%nat ltac:(lia)). f_equal.
    rewrite <- (le4_byte nv (j - 384)%nat Hnv ltac:(lia)). fold v1.
    exact (nth_error_nth _ _ (Z_to_bv 8 0) (eq_sym HN2)).
  + rewrite HOUT; [ | lia
    | apply Bool.andb_false_iff in EB1 as [E1 | E1]; [apply Nat.leb_gt in E1 | apply Nat.ltb_ge in E1]; lia
    | apply Bool.andb_false_iff in EB2 as [E1 | E1]; [apply Nat.leb_gt in E1 | apply Nat.ltb_ge in E1]; lia ].
    rewrite (mbytes_of_garr8 m t X HG j ltac:(lia)).
    f_equal. exact (nth_error_nth _ _ (Z_to_bv 8 0) (eq_sym HN2)).
Qed.
Lemma age_shadow_kept : forall (m memc : word -> option byte) (W : world SEGS) (sp t : Z),
2 ^ 46 + 4176 <= sp <= 2 ^ 47 -> 8 <= t -> t + 400 <= 2 ^ 47 -> amem_range t 400 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_TABLE_AGE_STK <= a < sp) -> ~ (t <= a < t + 400) ->
   aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF t 400 -> shadow_hull_vis (aview SEGS (w_H W) memc) t 400 ->
range_addressable (aview SEGS (w_H W) m) SHADOW_OFF t 400 /\ shadow_hull_vis (aview SEGS (w_H W) m) t 400.
Proof.
intros m memc W sp t Hsp Ht8 Ht47 HAM HK HRA HHV.
assert (HS1 : REAC_DISCO_TABLE_AGE_STK = 4176) by reflexivity.
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
split.
- apply (ra_transfer memc m W t 400); [|exact HRA].
  intros x Hx. unfold shadow_of_addr. rewrite HSO.
  assert (HA : 0 <= 2147450880 + x / 8 < 2 ^ 64 /\ ~ (sp - REAC_DISCO_TABLE_AGE_STK <= 2147450880 + x / 8 < sp) /\
               ~ (t <= 2147450880 + x / 8 < t + 400)).
  { rewrite HS1. clear - Hsp Ht8 Ht47 HAM Hx. Z.div_mod_to_equations. lia. }
  destruct HA as (HA1 & HA2 & HA3). apply HK; assumption.
- apply (hull_transfer memc m W t 400); [|exact HHV].
  intros s Hs. unfold shadow_addr in Hs. rewrite HSO in Hs.
  assert (HA : 0 <= s < 2 ^ 64 /\ ~ (sp - REAC_DISCO_TABLE_AGE_STK <= s < sp) /\ ~ (t <= s < t + 400)).
  { rewrite HS1. clear - Hsp Ht8 Ht47 HAM Hs. Z.div_mod_to_equations. lia. }
  destruct HA as (HA1 & HA2 & HA3). apply HK; assumption.
Qed.
Lemma age_final : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs regs2 : bvmap 5 word) mem2 md2 (t now : Z) (T T' : list byte) (rr : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
sp0 - STK <= spZ regs - REAC_DISCO_TABLE_AGE_STK -> spZ regs <= sp0 ->
(t + 400 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= t) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_DISCO_TABLE_AGE_STK <= a < spZ regs) -> ~ (t <= a < t + 400) ->
   aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
aregs_preserved regs regs2 -> getr regs2 10 = w64 rr ->
garr8 SEGS (mrestrict (w_H W) mem2) t (map (fun b : byte => bv_unsigned b) T') ->
age_model T now = (T', rr) -> age_post T now T' rr ->
treac_disco_table_age_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs t now T
  W (mkCfg (mkst (fx := fx) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 t now T T' rr
  HJ HJ2 Hwlo Hwhi Hoff HKEPT HPRES HP Ha0 HG HAM HAP.
exists lyc, Sc, regs2, mem2, md2, T', rr.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Ha0|].
split; [reflexivity|]. split; [apply Permutation_refl|].
split; [exact (age_kept_of STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc Sc mem2 md2 k
  (spZ regs) t HJ HJ2 Hwlo Hwhi Hoff HKEPT HPRES)|].
split; [reflexivity|].
split.
{ intros a Ha1 Ha2. apply HKEPT; [apply bv_unsigned_in_range | exact Ha2 | exact Ha1]. }
split; [exact HG|]. split; [exact HAM | exact HAP].
Qed.
Lemma age_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (t : Z) (T : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 t ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_TABLE_AGE_STK -> spZ regs <= sp0 ->
0 < t -> t mod 8 = 0 -> amem_range t 400 ->
(spZ regs <= t \/ t + 400 <= spZ regs - REAC_DISCO_TABLE_AGE_STK) ->
(t + 400 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= t) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF t 400 ->
length T = 400%nat -> tbl_T1 T ->
garr8 SEGS (mrestrict (w_H W) memc) t (map (fun b : byte => bv_unsigned b) T) ->
st_ok_pi SEGS VAL (EA regs T) ss_age
  (restrict (w_H W) (mkst (fx := fx) regs (Z_to_bv 64 (BASE + AF_reac_disco_table_age)) memc (seg_rom SEGS)))
/\ sh_ok SEGS AGE_Bx age_SH (EA regs T) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t T
  HJ H10 Hal16 Hwlo Hwhi Ht0 Ht8 HAM Hside Hoff HRA LT T1 HG.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (age_t_app STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k t HJ Ht0 Ht8 HAM) as (Ht4096 & Ht47 & Hband).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp016 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HS1 : REAC_DISCO_TABLE_AGE_STK = 4176) by reflexivity.
assert (Hsplo : 2 ^ 46 <= spZ regs) by lia.
assert (Hsphi : spZ regs <= 2 ^ 47) by lia.
unfold tbl_T1 in T1.
assert (HnT : u_at T 384 4 = n_of T) by (apply u_of_n; [exact LT | lia]).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR.
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
assert (HIMGT : YImgTop.IMG_TOP = 6283264) by reflexivity.
assert (HIMGL : YImgTop.IMG_LO = 65536) by reflexivity.
rewrite restrict_mkst_fx.
set (E := EA regs T) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (age_extra T)) n)
by (intros n Hn; subst E; unfold EA; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (n_of T)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Eo66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; unfold EA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_age. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold age_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
      [cbn [sv_denot]; rewrite Eo66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Eo66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 AGE_Bx SB);
      [cbn [sv_denot AGE_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * rewrite (VB 10%nat t E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ t 384 4 (SOff 33 0) (n_of T));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite <- HnT. apply (age_val _ T t 384 4 HG); [lia | rewrite LT; cbn; lia].
  + apply pairwise_disjoint_of_extents. unfold age_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat t E10) by lia.
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Eo66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hside Hoff HcellR HgcD HgotR HIMGT HIMGL Hsplo Hsphi Ht4096 Ht47 C1 HS1. clear. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [age_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hsplo Hsphi Hal16 Ht4096 Ht47 Ht8 T1. unfold SB. clear. intros.
    repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
- unfold sh_ok, age_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) memc E AGE_Bx 10 t 400 t 0 400 HRA).
  + unfold U, AGE_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. apply Hband. lia.
Qed.
Lemma region_chunk_val : forall E ss ms (i n : nat) b lo hi wlo whi cs off (w : N) e,
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal w e)) cs -> Z.of_N w <= 8 ->
val_mem SEGS (ms_mem ms) (b + off) (N.to_nat w) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros E ss ms i n b lo hi wlo whi cs off w e HS Hnth Hb Hin Hw.
assert (HR : region_ok SEGS E (ms_mem ms) (YP09.mkRegion (Some n) lo hi wlo whi cs)).
{ apply (st_ok_region_nth E (abs_ss VAL ss) ms i _ HS). destruct ss; exact Hnth. }
exact (field_of_region_any (segs := SEGS) E (ms_mem ms) n b cs lo hi wlo whi off w e HR Hb Hin Hw).
Qed.
Lemma atom_mod : forall E n v w, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
bv_unsigned (sv_denot E (SOff n 0)) mod 2 ^ (8 * Z.of_N w) = v.
Proof.
intros E n v w H Hv Hw. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (split; [lia|]; apply (Z.lt_le_trans _ (2 ^ (8 * Z.of_N w))); [lia | apply Z.pow_le_mono_r; lia]).
apply Z.mod_small. exact Hv.
Qed.
Lemma sext_add1_mod : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1))) mod 2 ^ (8 * Z.of_N 4) = (v + 1) mod 2 ^ 32.
Proof.
intros E n v H Hv. change (bv_unsigned (sv_denot E ?x)) with (U E x).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SExt, (U_atom E n v H), U_SLit by lia.
change (8 * Z.of_N 4) with 32. change (2 ^ Z.of_N 32) with (2 ^ 32).
unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
Z.div_mod_to_equations. lia.
Qed.
Lemma age_seq_eq : forall T now A i m r (v : list byte), length T = 400%nat -> tbl_T1 T ->
reac_disco_table_age.age_inv T now A i m r -> length v = 4%nat -> seq_of (upd A 384 v) = seq_of T.
Proof.
intros T now A i m r v LT T1 HI Lv. pose proof HI as (LA & _ & _ & _ & _ & _ & _ & Hfr).
unfold tbl_T1 in T1.
rewrite reac_disco_table_age.seq_of_upd_out by (rewrite ?Lv; lia).
unfold seq_of, u_at. f_equal. apply reac_disco_table_age.sub_frame; rewrite ?LA, ?LT; try lia.
intros kk Hk. apply Hfr. lia.
Qed.
Lemma lp_frame_kept : forall (W : world SEGS) (m m' : word -> option byte) sp (regs : bvmap 5 word) (Zs : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
(forall a, sp - 80 <= a < sp -> 0 <= a < 2 ^ 64 /\ ~ Zs a) ->
lp_frame (mrestrict (w_H W) m) sp regs -> lp_frame (mrestrict (w_H W) m') sp regs.
Proof.
intros W m m' sp regs Zs HK HZ (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
assert (T : forall k v, 0 <= k <= 72 -> val_mem SEGS (mrestrict (w_H W) m) (sp - 80 + k) 8 v ->
  val_mem SEGS (mrestrict (w_H W) m') (sp - 80 + k) 8 v).
{ intros k v Hk Hv. apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) m m'); [|exact Hv].
  intros x Hx. cbn in Hx. destruct (HZ x ltac:(lia)) as [Hx1 Hx2]. exact (HK x Hx1 Hx2). }
repeat split; apply T; first [lia | assumption].
Qed.
Lemma U_diff : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
0 <= vb -> vb < va -> va < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff a 0) (SMd M_MUL (SOff b 0) (SLit (-1)))) = va - vb.
Proof.
intros E a b va vb Ha Hb H0 H1 H2. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a va Ha) by lia. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E b vb Hb) by lia. rewrite U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1).
unfold zcanon, M64. Z.div_mod_to_equations. lia.
Qed.
Lemma U_src : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
48 <= va -> 1 <= vb <= 8 -> va + 48 * vb < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff a (-48)) (SMd M_MUL (SOff b 0) (SLit 48))) = va + 48 * (vb - 1).
Proof.
intros E a b va vb Ha Hb H0 H1 H2. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SOff, Ha, unsigned_lit_small by lia. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E b vb Hb) by lia. rewrite U_SLit.
unfold zcanon, M64. Z.div_mod_to_equations. lia.
Qed.
Lemma aj_cpy_same_at : forall pc, acpy_same_realizes (fx := fx) SEGS B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 d -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) d n) ->
src_ok SEGS W regsT memT d n ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview SEGS (w_H W) mem2 (d + i) = aview SEGS (w_H W) memT (d + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
   aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n o raw
  HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
  rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok SEGS B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
  destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
  split; [apply (apresent_writable SEGS); exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d d n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull
    (conj Hd0 (conj Hdn (conj Hsrc (conj eq_refl (conj Hamr (conj Hra_d Hhull))))))). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS Hsegs STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; lia].
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr | exact Hpres2].
Qed.
Lemma mbyte_of_aview_x : forall (h : word -> bool) (m m' : word -> option byte) a a',
aview SEGS h m' a = aview SEGS h m a' -> mbyte SEGS (mrestrict h m') a = mbyte SEGS (mrestrict h m) a'.
Proof.
intros h m m' a a' Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict h m') a) as [b|] eqn:E1; destruct (mbyte SEGS (mrestrict h m) a') as [b'|] eqn:E2;
cbn in Hv; try discriminate; [|reflexivity]. injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.
Lemma val_mem_bytes_eq : forall (m m' : word -> option byte) a v,
val_mem SEGS m a 4 v -> val_mem SEGS m' a 4 v -> forall x, a <= x < a + 4 -> mbyte SEGS m' x = mbyte SEGS m x.
Proof.
intros m m' a v H H' x Hx. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (H (Z.to_nat (x - a)) ltac:(lia)), (H' (Z.to_nat (x - a)) ltac:(lia)). reflexivity.
Qed.
Let RUN := paj_run (L := disco_listing) B LAWS.
Let RUNTO := paj_run_to (L := disco_listing) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_disco) (PI := PI).
Lemma kept_trans : forall (Zs : Z -> Prop) (W : world SEGS) (m1 m2 m3 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m3 a = aview SEGS (w_H W) m2 a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m3 a = aview SEGS (w_H W) m1 a.
Proof. intros Zs W m1 m2 m3 H12 H23 a Ha HZ. rewrite (H23 a Ha HZ). exact (H12 a Ha HZ). Qed.
Ltac age_win HFr tt E32u KS :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
     (fun a => tt + 384 <= a < tt + 388 \/ tt + 392 <= a < tt + 396) HFr
     ltac:(let b := fresh "b" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
           let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
           intros b wl wh aa Hin Hrr; vm_compute in Hin;
           repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
                   [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?E32u in Hrr; lia |]);
           destruct Hin)) as KS.
Ltac age_awr E32u HWR :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_gen;
    [ reflexivity | exact E32u
    | cbn [YP09.r_wlo YP09.r_whi]; let aa := fresh "aa" in let Haa := fresh "Haa" in
      intros aa Haa; apply (proj1 (HWR aa ltac:(lia)))
    | ] ].
Ltac age_pp0 HG PP W memL :=
  lazymatch type of HG with mem_grows (mrestrict _ _) (mrestrict _ ?m2) =>
    assert (PP : forall a, apresent (w_H W) memL a -> apresent (w_H W) m2 a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (apresent_grows _ _ _ _ HG); exact Ha) end.
Ltac age_pp HG PP W memL :=
  lazymatch type of HG with mem_grows (mrestrict _ _) (mrestrict _ ?m2) =>
    let P2 := fresh "PP" in
    assert (P2 : forall a, apresent (w_H W) memL a -> apresent (w_H W) m2 a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (apresent_grows _ _ _ _ HG); apply PP; exact Ha);
    clear PP; rename P2 into PP end.
Ltac age_kk HFr tt E32u KK W :=
  let K2 := fresh "K2" in age_win HFr tt E32u K2;
  let KK2 := fresh "KK" in pose proof (kept_trans _ W _ _ _ KK K2) as KK2; clear KK K2; rename KK2 into KK.
Ltac age_step HF HFr HG KK PP tt E32u W memL :=
  age_kk HFr tt E32u KK W; age_pp HG PP W memL; clear HF HFr HG.
Definition age_stale_iter_P : Prop :=
forall (fuel : nat) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs regsL : bvmap 5 word) memL mdL (t now i mm r : Z) (T A : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memL mdL k ->
YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_TABLE_AGE_STK -> spZ regs <= sp0 ->
0 < t -> t mod 8 = 0 -> amem_range t 400 ->
(spZ regs <= t \/ t + 400 <= spZ regs - REAC_DISCO_TABLE_AGE_STK) ->
(forall a, t <= a < t + 400 ->
   awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF t 400 ->
shadow_hull_vis (aview SEGS (w_H W) memc) t 400 ->
0 <= now < 2 ^ 64 -> length T = 400%nat -> table_ok T ->
Z.of_nat (Datatypes.S fuel) = mm - i -> i < mm ->
reac_disco_table_age.age_inv T now A i mm r ->
age_loop (Datatypes.S fuel) A now i mm r = age_loop (Z.to_nat (n_of T)) T now 0 (n_of T) 0 ->
getr regsL 2 = w64 (spZ regs - 80) ->
getr regsL 3 = getr regs 3 -> getr regsL 4 = getr regs 4 ->
getr regsL 25 = getr regs 25 -> getr regsL 26 = getr regs 26 -> getr regsL 27 = getr regs 27 ->
getr regsL 8 = w64 r -> getr regsL 9 = w64 (t + 384) -> getr regsL 18 = w64 t ->
getr regsL 19 = w64 now -> getr regsL 20 = w64 SB -> getr regsL 21 = age_sh5 t ->
getr regsL 22 = w64 i -> getr regsL 23 = w64 5000000001 -> getr regsL 24 = w64 3 ->
getr regsL 12 = w64 mm ->
lp_frame (mrestrict (w_H W) memL) (spZ regs) regs ->
garr8 SEGS (mrestrict (w_H W) memL) t (map (fun b : byte => bv_unsigned b) (upd A 384 (Mem.le4 (Z_to_bv 64 mm)))) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_DISCO_TABLE_AGE_STK <= a < spZ regs) -> ~ (t <= a < t + 400) ->
   aview SEGS (w_H W) memL a = aview SEGS (w_H W) memc a) ->
(forall a, apresent (w_H W) memc a -> apresent (w_H W) memL a) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
disco_stale A i now = true ->
SRr SEGS W (mkCfg (mkst (fx := fx) regsL (Z_to_bv 64 (BASE + (AF_reac_disco_table_age + 124))) memL (seg_rom SEGS)) mdL)
  (fun W2 c2 =>
     treac_disco_table_age_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs t now T W2 c2 \/
     (W2 = W /\ i < mm - 1 /\ exists regsL2 memL2 mdL2,
        c2 = mkCfg (mkst (fx := fx) regsL2 (Z_to_bv 64 (BASE + (AF_reac_disco_table_age + 124))) memL2 (seg_rom SEGS)) mdL2 /\
        ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memL2 mdL2 k /\
        getr regsL2 2 = w64 (spZ regs - 80) /\
        getr regsL2 3 = getr regs 3 /\ getr regsL2 4 = getr regs 4 /\
        getr regsL2 25 = getr regs 25 /\ getr regsL2 26 = getr regs 26 /\ getr regsL2 27 = getr regs 27 /\
        getr regsL2 8 = w64 (r + 1) /\ getr regsL2 9 = w64 (t + 384) /\ getr regsL2 18 = w64 t /\
        getr regsL2 19 = w64 now /\ getr regsL2 20 = w64 SB /\ getr regsL2 21 = age_sh5 t /\
        getr regsL2 22 = w64 i /\ getr regsL2 23 = w64 5000000001 /\ getr regsL2 24 = w64 3 /\
        getr regsL2 12 = w64 (mm - 1) /\
        lp_frame (mrestrict (w_H W) memL2) (spZ regs) regs /\
        garr8 SEGS (mrestrict (w_H W) memL2) t (map (fun b : byte => bv_unsigned b)
          (upd (upd A (48 * i) (entry_of A (mm - 1))) 384 (Mem.le4 (Z_to_bv 64 (mm - 1))))) /\
        (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_DISCO_TABLE_AGE_STK <= a < spZ regs) -> ~ (t <= a < t + 400) ->
           aview SEGS (w_H W) memL2 a = aview SEGS (w_H W) memc a) /\
        (forall a, apresent (w_H W) memc a -> apresent (w_H W) memL2 a))).
Lemma ast_off_mod : forall E n v c (w : N), ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
0 <= v + c < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
bv_unsigned (sv_denot E (SOff n c)) mod 2 ^ (8 * Z.of_N w) = v + c.
Proof.
intros E n v c w H Hv Hvc Hw.
assert (Hle : 2 ^ (8 * Z.of_N w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
change (bv_unsigned (sv_denot E ?x)) with (U E x).
rewrite U_SOff, H, unsigned_lit_small by lia.
unfold zcanon, M64. rewrite (Z.mod_small (v + c) (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.
Lemma ast_nth_sub : forall (A : list byte) (a : Z) (n j : nat), 0 <= a -> (Z.to_nat a + n <= length A)%nat -> (j < n)%nat ->
nth j (sub A a n) (Z_to_bv 8 0) = nth (Z.to_nat a + j) A (Z_to_bv 8 0).
Proof.
intros A a n j Ha Hn Hj.
pose proof (reac_disco_table_age.nth_sub A a n j Ha Hj) as HN.
destruct (nth_error A (Z.to_nat a + j)) as [x|] eqn:EA.
- rewrite (nth_error_nth _ _ (Z_to_bv 8 0) HN), (nth_error_nth _ _ (Z_to_bv 8 0) EA). reflexivity.
- apply nth_error_None in EA. lia.
Qed.
Lemma ast_chunk_val : forall E ss ms (i n : nat) b lo hi wlo whi cs off (w : N) e,
st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal w e)) cs -> Z.of_N w <= 8 ->
val_mem SEGS (ms_mem ms) (b + off) (N.to_nat w) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros E ss ms i n b lo hi wlo whi cs off w e HS Hnth Hb Hin Hw.
exact (field_of_region_any (segs := SEGS) E (ms_mem ms) n b cs lo hi wlo whi off w e
  (st_ok_region_nth E ss ms i _ HS Hnth) Hb Hin Hw).
Qed.
Lemma ast_garr8_cpy : forall (m m' : word -> option byte) (X : list byte) (t i j : Z),
garr8 SEGS m t (map (fun b : byte => bv_unsigned b) X) -> length X = 400%nat -> 0 <= i < 8 -> 0 <= j < 8 ->
(forall o, 0 <= o < 48 -> mbyte SEGS m' (t + 48 * i + o) = mbyte SEGS m (t + 48 * j + o)) ->
(forall a, t <= a < t + 400 -> ~ (t + 48 * i <= a < t + 48 * i + 48) -> mbyte SEGS m' a = mbyte SEGS m a) ->
garr8 SEGS m' t (map (fun b : byte => bv_unsigned b) (upd X (48 * i) (entry_of X j))).
Proof.
intros m m' X t i j HG LX Hi Hj HIN HOUT.
assert (LE : length (entry_of X j) = 48%nat) by (unfold entry_of, sub; rewrite length_firstn, length_skipn, LX; lia).
apply (age_garr8_upd m m' X (entry_of X j) t (48 * i) HG ltac:(lia) ltac:(rewrite LE, LX; lia)).
- intros q Hq. rewrite LE in Hq. rewrite (HIN (Z.of_nat q) ltac:(lia)).
  replace (t + 48 * j + Z.of_nat q) with (t + Z.of_nat (Z.to_nat (48 * j) + q)) by lia.
  rewrite (mbytes_of_garr8 m t X HG (Z.to_nat (48 * j) + q)%nat ltac:(rewrite LX; lia)).
  f_equal. unfold entry_of. symmetry. apply (ast_nth_sub X (48 * j) 48%nat q ltac:(lia) ltac:(rewrite LX; lia) ltac:(lia)).
- intros a Ha Hna. rewrite LE in Hna. rewrite LX in Ha. apply HOUT; lia.
Qed.
Lemma ast_src : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
0 <= va -> 1 <= vb <= 8 -> va + 48 * vb < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff a (-48)) (SMd M_MUL (SOff b 0) (SLit 48))) = va + 48 * (vb - 1).
Proof.
intros E a b va vb Ha Hb H0 H1 H2. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SOff, Ha, unsigned_lit_small by lia. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E b vb Hb) by lia. rewrite U_SLit.
unfold zcanon, M64. Z.div_mod_to_equations. lia.
Qed.
Lemma ast_cpy_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) d n) ->
0 <= x -> x + n <= 2 ^ 63 -> src_ok SEGS W regsT memT x n -> (x = d \/ d + n <= x \/ x + n <= d) -> amem_range x n ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA DS___asan_memcpy)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview SEGS (w_H W) mem2 (d + i) = aview SEGS (w_H W) memT (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
   aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
  HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hx0 Hxn Hsrc Hdisj Hamx Hrax Hhx.
destruct Hdisj as [-> | Hdisj].
- eapply SRr_mono.
  { exact (aj_cpy_same_at _ (AMEMCPYEQ fx) W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n o raw
      HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc). }
  cbv beta. intros W2 c2 _ H. exact H.
- eapply SRr_mono.
  { exact (aj_intrin_at SEGS B LAWS pa_segs_low OCpy _ (AMEMCPY fx) W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
      HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull
      (conj Hx0 (conj Hxn (conj Hsrc (conj Hdisj (conj Hamx (conj Hrax Hhx))))))). }
  cbv beta. intros W2 c2 _ H. exact H.
Qed.
Lemma age_stale_iter : age_stale_iter_P.
Proof.
intros fuel STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsL memL mdL t now i mm r T A
  HJ0 HJL Hra Hsp16 Hwlo Hwhi Ht0 Ht8 HAM Hside HWR HRA HHV Hnow LT TOK Hfuel Him HI HRES
  R2 R3 R4 R25 R26 R27 R8 R9 R18 R19 R20 R21 R22 R23 R24 R12 HFR HGA HKEPT HPRES Hgp Htp STL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (HS1 : REAC_DISCO_TABLE_AGE_STK = 4176) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (age_t_app STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k t HJ0 Ht0 Ht8 HAM) as (Ht4096 & Ht47 & Hband).
pose proof (age_t_off STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k t HJ0 HWR) as Hoff.
pose proof HJ0 as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp016 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJL as (HARL & _).
assert (Hsprng : 2 ^ 46 + 4176 <= spZ regs <= 2 ^ 47) by lia.
pose proof TOK as (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
pose proof HI as (LA & Hi0 & Hmn & Hrr & _).
assert (Hmm8 : mm <= 8) by lia.
assert (Hr8 : 0 <= r <= 8) by lia.
set (X := upd A 384 (Mem.le4 (Z_to_bv 64 mm))) in *.
assert (LX : length X = 400%nat) by (unfold X; rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LA; lia).
assert (HnX : n_of X = mm) by (unfold X; apply reac_disco_table_age.n_of_set; [exact LA | lia]).
assert (HPRL : forall a, t <= a < t + 400 -> apresent (w_H W) memL a) by (intros a Ha; apply HPRES; apply (HWR a Ha)).
destruct (age_shadow_kept memL memc W (spZ regs) t Hsprng Ht4096 Ht47 HAM HKEPT HRA HHV) as [HRAL HHVL].
destruct (age_lp_entry lyc Sc W memL mdL regsL regs t now i mm r X HARL Ht4096 Ht47 Ht8 Hnow Hoff HAM (proj1 Hi0) Him Hmm8 Hr8
  Hsprng Hsp16 Hside R2 R8 R9 R18 R19 R20 R21 R22 R23 R24 R12 LX HnX HGA HPRL HRAL HFR) as [HS SHOK].
set (E := EL regsL regs t now i mm r (t + 48 * i) (last_of X i) (seq_of X)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EL; apply Eimg_env).
assert (EL0 : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsL (lp_extra regs t now i mm r (t + 48 * i) (last_of X i) (seq_of X))) n)
by (intros n Hn; subst E; unfold EL; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 19)%nat -> ew E (32 + j)%nat = nth j (lp_extra regs t now i mm r (t + 48 * i) (last_of X i) (seq_of X)) (Z_to_bv 64 0))
by (intros j Hj; rewrite EL0 by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41.
pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44. pose proof (EX 13%nat ltac:(lia)) as E45.
pose proof (EX 14%nat ltac:(lia)) as E46. pose proof (EX 15%nat ltac:(lia)) as E47.
pose proof (EX 16%nat ltac:(lia)) as E48. pose proof (EX 17%nat ltac:(lia)) as E49.
pose proof (EX 18%nat ltac:(lia)) as E50.
cbn [lp_extra map app nth Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50.
assert (E2 : ew E 2 = getr regsL 2) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsL 3) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsL 4) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 4 4%bv eq_refl)).
assert (E25 : ew E 25 = getr regsL 25) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 25 25%bv eq_refl)).
assert (E26 : ew E 26 = getr regsL 26) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr regsL 27) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 27 27%bv eq_refl)).
assert (E32u : bv_unsigned (ew E 32) = t) by (rewrite E32; apply unsigned_lit_small; lia).
clear EX EL0.
paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
age_win HFr t E32u KK. age_pp0 HG PP W memL. clear HF HFr HG.
pose proof (reac_disco_table_age.last_range X i LX ltac:(lia)) as HLR.
assert (SX : disco_stale X i now = disco_stale A i now).
{ apply reac_disco_table_age.stale_ent; [exact LX | exact LA | lia | lia |].
  unfold X. apply reac_disco_table_age.entry_upd_hi; rewrite ?Mem.length_le4; lia. }
psrr_branch_tok RUN BR HS SHOK AGE_span.
{ rewrite branch_geu_U, (U_atom E 39 (last_of X i) E39), (U_atom E 33 now E33) in Hc by lia.
  assert (Hge : now <= last_of X i) by (destruct (Z.ltb_spec (last_of X i) now); [cbn in Hc; discriminate | lia]).
  exfalso. rewrite <- SX in STL. unfold disco_stale in STL.
  rewrite (proj2 (Z.ltb_ge (last_of X i) now) Hge) in STL. cbn in STL. discriminate STL. }
rewrite branch_geu_U, (U_atom E 39 (last_of X i) E39), (U_atom E 33 now E33) in Hc by lia.
assert (Hlt0 : last_of X i < now) by (destruct (Z.ltb_spec (last_of X i) now); [lia | cbn in Hc; discriminate]).
clear Hc.
paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
age_step HF HFr HG KK PP t E32u W memL.
assert (HDIFF : U E (SAlu ALU_ADD (SOff 33 0) (SMd M_MUL (SOff 39 0) (SLit (-1)))) = now - last_of X i)
  by (apply U_diff; [exact E33 | exact E39 | lia | lia | lia]).
psrr_branch_tok RUN BR HS SHOK AGE_span.
{ rewrite branch_ltu_U, HDIFF, U_lit in Hc by lia. apply Z.ltb_lt in Hc. exfalso.
  rewrite <- SX in STL. unfold disco_stale, REAC_DISCO_STALE_NS in STL.
  rewrite (proj2 (Z.ltb_ge 5000000000 (now - last_of X i)) ltac:(lia)), andb_false_r in STL. discriminate STL. }
rewrite branch_ltu_U, HDIFF, U_lit in Hc by lia. apply Z.ltb_ge in Hc. clear Hc.
paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
age_step HF HFr HG KK PP t E32u W memL.
assert (Eo66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; unfold EL; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EL; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
assert (HIMGT : YImgTop.IMG_TOP = 6283264) by reflexivity.
assert (HIMGL : YImgTop.IMG_LO = 65536) by reflexivity.
prreg HS (10%bv : bv 5) Ra0. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
assert (Ra1 : getr (ms_regs ms1) 11 = Z_to_bv 64 (t + 48 * (mm - 1))).
{ refine (eq_trans (st_ok_restrict_reg SEGS (w_H W) E _ ms1 11%bv HS) _).
  change (sv_denot E (SAlu ALU_ADD (SOff 32 (-48)) (SMd M_MUL (SOff 37 0) (SLit 48))) = Z_to_bv 64 (t + 48 * (mm - 1))).
  rewrite denot_lit_U. f_equal. apply ast_src; [exact E32 | exact E37 | lia | lia | lia]. }
assert (HspT : spZ (ms_regs ms1) = spZ regs - 80).
{ change (spZ (ms_regs ms1)) with (bv_unsigned (getr (ms_regs ms1) 2)). rewrite Rsp, E2, R2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
destruct (age_shadow_kept (ms_mem ms1) memc W (spZ regs) t Hsprng Ht4096 Ht47 HAM
  (fun a Ha Hw Ht => eq_trans (KK a Ha ltac:(cbv beta; lia)) (HKEPT a Ha Hw Ht)) HRA HHV) as [HRAT HHVT].
pose proof (ast_chunk_val E _ _ 3 32 t _ _ _ _ _ 384 4%N (SOff 37 0) HS eq_refl E32u
  ltac:(left; reflexivity) ltac:(lia)) as V1c.
pose proof (ast_chunk_val E _ _ 4 32 t _ _ _ _ _ 392 4%N (SOff 40 0) HS eq_refl E32u
  ltac:(left; reflexivity) ltac:(lia)) as V2c.
rewrite (atom_mod E 37 mm 4 E37) in V1c by (cbn; lia).
rewrite (atom_mod E 40 (seq_of X) 4 E40) in V2c by (cbn; pose proof (reac_disco_table_age.seq_range X); lia).
cbn [ms_mem restrict] in V1c, V2c.
assert (HG1 : garr8 SEGS (mrestrict (w_H W) (ms_mem ms1)) t (map (fun b : byte => bv_unsigned b) X)).
{ apply (age_garr8_same (mrestrict (w_H W) memL) _ X t mm (seq_of X) HGA LX).
  - intros a Ha Ha1 Ha2. apply (mbyte_of_aview SEGS). apply KK; [lia | cbv beta; lia].
  - rewrite <- HnX, <- (u_of_n X LX ltac:(lia)). apply (age_val _ X t 384 4 HGA); [lia | rewrite LX; cbn; lia].
  - exact V1c.
  - unfold seq_of. apply (age_val _ X t 392 4 HGA); [lia | rewrite LX; cbn; lia].
  - exact V2c. }
pmkst HS.
eapply SRr_bind.
{ apply (ast_cpy_at W (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (t + 48 * i) (t + 48 * (mm - 1)) 48
    (spZ regs - 80 - sp0) (Z_to_bv 64 (BASE + 23024)) HJL).
  - rewrite Ra0, E38. reflexivity.
  - exact Ra1.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite HspT. lia.
  - clear - Hsp16 Hsp016. Z.div_mod_to_equations. lia.
  - lia.
  - rewrite Hes. lia.
  - rewrite Rgp, E3, R3. exact Hgp.
  - rewrite Rtp, E4, R4. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [exact (proj1 (HWR a ltac:(lia))) | rewrite Hes; lia].
  - apply (amem_sub t 400); [exact HAM | lia | lia | lia].
  - apply (ra_sub _ t 400); [exact HRAT | lia | lia].
  - intros _. apply (hull_sub _ t 400); [exact HHVT | lia | lia | lia].
  - lia.
  - lia.
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply PP; apply HPRL; lia | rewrite HspT, Hes; lia].
  - lia.
  - apply (amem_sub t 400); [exact HAM | lia | lia | lia].
  - apply (ra_sub _ t 400); [exact HRAT | lia | lia].
  - intros _. apply (hull_sub _ t 400); [exact HHVT | lia | lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2).
assert (LE : length (entry_of X (mm - 1)) = 48%nat) by (unfold entry_of, sub; rewrite length_firstn, length_skipn, LX; lia).
set (Y := upd X (48 * i) (entry_of X (mm - 1))) in *.
assert (LY : length Y = 400%nat) by
  (unfold Y; rewrite (reac_disco_table_age.length_upd X (48 * i) (entry_of X (mm - 1)) ltac:(lia) ltac:(rewrite LE, LX; lia)); exact LX).
assert (HG2 : garr8 SEGS (mrestrict (w_H W) mem2) t (map (fun b : byte => bv_unsigned b) Y)).
{ unfold Y. apply (ast_garr8_cpy (mrestrict (w_H W) (ms_mem ms1)) _ X t i (mm - 1) HG1 LX ltac:(lia) ltac:(lia)).
  - intros o Ho. apply (mbyte_of_aview_x (w_H W)). exact (Heff o ltac:(lia)).
  - intros a Ha Hna. apply (mbyte_of_aview_x (w_H W)). apply Hfr; [lia | lia | lia]. }
jafter_call_keep_pi HS 60%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [|specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply region_kept_aview;
      [ rewrite E2, R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
      | intros a Ha; apply Hfr; lia | exact Hpres2 ].
  - eapply region_kept_aview;
      [ change (ew E 242) with (ew E (A_OBJ 1)); rewrite Eo1, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 1)); lia); reflexivity
      | intros a Ha; apply Hfr; lia | exact Hpres2 ].
  - eapply region_kept_aview;
      [ change (ew E 307) with (ew E (A_OBJ 66)); rewrite Eo66, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 66)); lia); reflexivity
      | intros a Ha; apply Hfr; lia | exact Hpres2 ].
  - eapply region_kept_aview; [ exact E32u | intros a Ha; apply Hfr; lia | exact Hpres2 ].
  - eapply region_kept_aview; [ exact E32u | intros a Ha; apply Hfr; lia | exact Hpres2 ]. }
rewrite <- restrict_mkst_fx in HS2. clear HS SHOK. rename HS2 into HS.
set (E' := havoc E 60 (map (getr regs2) CLOB)) in HS.
assert (HEIc : img_env VAL A_LIM E') by (apply img_env_havoc; [exact HEI | rewrite length_map; unfold CLOB, A_TEXT; cbn [length]; lia]).
assert (EH : forall n, (n < 60)%nat -> ew E' n = ew E n) by (intros n Hn; unfold E'; apply ew_havoc_old; exact Hn).
rewrite <- (EH 32%nat ltac:(lia)) in E32, E32u. rewrite <- (EH 33%nat ltac:(lia)) in E33.
rewrite <- (EH 34%nat ltac:(lia)) in E34. rewrite <- (EH 35%nat ltac:(lia)) in E35.
rewrite <- (EH 36%nat ltac:(lia)) in E36. rewrite <- (EH 37%nat ltac:(lia)) in E37.
rewrite <- (EH 38%nat ltac:(lia)) in E38. rewrite <- (EH 39%nat ltac:(lia)) in E39.
rewrite <- (EH 40%nat ltac:(lia)) in E40. rewrite <- (EH 41%nat ltac:(lia)) in E41.
rewrite <- (EH 42%nat ltac:(lia)) in E42. rewrite <- (EH 43%nat ltac:(lia)) in E43.
rewrite <- (EH 44%nat ltac:(lia)) in E44. rewrite <- (EH 45%nat ltac:(lia)) in E45.
rewrite <- (EH 46%nat ltac:(lia)) in E46. rewrite <- (EH 47%nat ltac:(lia)) in E47.
rewrite <- (EH 48%nat ltac:(lia)) in E48. rewrite <- (EH 49%nat ltac:(lia)) in E49.
rewrite <- (EH 50%nat ltac:(lia)) in E50. rewrite <- (EH 2%nat ltac:(lia)) in E2.
rewrite <- (EH 3%nat ltac:(lia)) in E3. rewrite <- (EH 4%nat ltac:(lia)) in E4.
rewrite <- (EH 25%nat ltac:(lia)) in E25. rewrite <- (EH 26%nat ltac:(lia)) in E26.
rewrite <- (EH 27%nat ltac:(lia)) in E27.
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_DISCO_TABLE_AGE_STK <= a < spZ regs) -> ~ (t <= a < t + 400) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hw Ht. rewrite (Hfr a Ha ltac:(lia) ltac:(lia)). rewrite (KK a Ha ltac:(cbv beta; lia)). exact (HKEPT a Ha Hw Ht). }
destruct (age_shadow_kept mem2 memc W (spZ regs) t Hsprng Ht4096 Ht47 HAM KM2 HRA HHV) as [HRA2 HHV2].
assert (SHOK : sh_ok SEGS LP_Bx lp_SH E' (mrestrict (w_H W) mem2)).
{ unfold sh_ok, lp_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem2 E' LP_Bx 32 t 400 t 0 400 HRA2).
    * unfold U, LP_Bx. cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * apply (U_atom E' 32 t E32). lia.
    * lia.
    * lia.
    * intros x Hx. apply Hband. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem2 E' LP_Bx 38 t 400 (t + 48 * i) 0 48 HRA2).
    * unfold U, LP_Bx. cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * apply (U_atom E' 38 (t + 48 * i) E38). lia.
    * lia.
    * lia.
    * intros x Hx. apply Hband. lia. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (VAL A_TEXT + 23024)) mem2 (seg_rom SEGS))) in HJ2.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
paj_run_tok RUN HS HJ2 SHOK AGE_span; [age_awr E32u HWR|].
age_win HFr t E32u KK2. age_pp0 HG PP2 W mem2. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK AGE_span.
- rewrite branch_ge_S, (S_small E' 35 i 0 E35), (S_small E' 37 mm (-1) E37) in Hc by lia.
  assert (Hend : i = mm - 1) by (destruct (Z.ltb_spec (i + 0) (mm + -1)); [discriminate | lia]). clear Hc.
  paj_run_tok RUN HS HJ2 SHOK AGE_span; [age_awr E32u HWR|].
  age_step HF HFr HG KK2 PP2 t E32u W mem2.
  pose proof (region_chunk_val E' _ _ 3 32 t _ _ _ _ _ 384 4%N (SOff 37 (-1)) HS eq_refl E32u
    ltac:(left; reflexivity) ltac:(lia)) as V1f.
  pose proof (region_chunk_val E' _ _ 4 32 t _ _ _ _ _ 392 4%N (SAlu ALU_ADD (SExt true 32 (SOff 40 0)) (SLit 1)) HS eq_refl E32u
    ltac:(left; reflexivity) ltac:(lia)) as V2f.
  rewrite (ast_off_mod E' 37 mm (-1) 4%N E37 ltac:(lia) ltac:(cbn; lia) ltac:(lia)) in V1f.
  rewrite (sext_add1_mod E' 40 (seq_of X) E40) in V2f by (pose proof (reac_disco_table_age.seq_range X); lia).
  cbn [ms_mem restrict] in V1f, V2f.
  prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2.
  prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
  prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  cbv beta. rewrite Q1, E41, Hra.
  assert (SQ : seq_of X = seq_of T) by (unfold X; apply (age_seq_eq T now A i mm r); [exact LT | exact T1 | exact HI | apply Mem.length_le4]).
  set (A2 := upd A (48 * i) (entry_of A (mm - 1))) in *.
  set (T' := upd (upd A2 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))) 392 (Mem.le4 (Z_to_bv 64 (seq_of T + 1)))).
  assert (AL : age_loop (Z.to_nat (n_of T)) T now 0 (n_of T) 0 = (A2, mm - 1, r + 1)).
  { rewrite <- HRES. rewrite reac_disco_table_age.age_loop_stale by (exact STL || lia).
    apply reac_disco_table_age.age_loop_end. lia. }
  assert (AM : age_model T now = (T', r + 1)).
  { rewrite (reac_disco_table_age.age_model_of T now A2 (mm - 1) (r + 1) AL).
    replace (0 <? r + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  left.
  apply (age_final STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ t now T T' (r + 1) HJ0).
  + apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ2.
  + exact Hwlo.
  + exact Hwhi.
  + exact Hoff.
  + intros a Ha Hw Ht. rewrite (KK2 a Ha ltac:(cbv beta; lia)). exact (KM2 a Ha Hw Ht).
  + intros a Ha. apply PP2. apply Hpres2. apply PP. apply HPRES. exact Ha.
  + apply age_preserved;
      first [ rewrite Q2, E2, R2; unfold w64; rewrite unsigned_lit_small by lia;
              replace (spZ regs - 80 + 80) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
            | rewrite Q3, E3; exact R3 | rewrite Q4, E4; exact R4
            | rewrite Q25, E25; exact R25 | rewrite Q26, E26; exact R26 | rewrite Q27, E27; exact R27
            | rewrite Q8, E42; reflexivity | rewrite Q9, E43; reflexivity | rewrite Q18, E44; reflexivity
            | rewrite Q19, E45; reflexivity | rewrite Q20, E46; reflexivity | rewrite Q21, E47; reflexivity
            | rewrite Q22, E48; reflexivity | rewrite Q23, E49; reflexivity | rewrite Q24, E50; reflexivity ].
  + rewrite Q10, E36, unsigned_lit_small by lia. reflexivity.
  + pose proof (reac_disco_table_age.seq_range X) as HSR.
    pose proof (age_garr8_fields (mrestrict (w_H W) mem2) _ Y t (mm - 1) ((seq_of X + 1) mod 2 ^ 32) HG2 LY
      ltac:(lia) ltac:(pose proof (Z.mod_pos_bound (seq_of X + 1) (2 ^ 32) ltac:(lia)); lia)
      ltac:(intros a Ha Ha1 Ha2; apply (mbyte_of_aview SEGS); apply KK2; [lia | cbv beta; lia]) V1f V2f) as G.
    replace (upd Y 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))) with (upd A2 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))) in G.
    * replace (Mem.le4 (Z_to_bv 64 ((seq_of X + 1) mod 2 ^ 32))) with (Mem.le4 (Z_to_bv 64 (seq_of T + 1))) in G.
      -- exact G.
      -- apply reac_disco_table_age.le4_eq_mod. rewrite SQ, !unsigned_lit_small.
         ++ rewrite Z.mod_mod by lia. reflexivity.
         ++ pose proof (Z.mod_pos_bound (seq_of T + 1) (2 ^ 32) ltac:(lia)); lia.
         ++ pose proof (reac_disco_table_age.seq_range T); lia.
    * unfold Y, A2, X. symmetry. apply reac_disco_table_age.tbl_mem_step; rewrite ?Mem.length_le4, ?LA; lia.
  + exact AM.
  + apply reac_disco_table_age.age_model_post; [exact LT | exact TOK | exact AM].
- rewrite branch_ge_S, (S_small E' 35 i 0 E35), (S_small E' 37 mm (-1) E37) in Hc by lia.
  assert (Hlt : i < mm - 1) by (destruct (Z.ltb_spec (i + 0) (mm + -1)); [lia | discriminate]). clear Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK AGE_span (AF_reac_disco_table_age + 124); [age_awr E32u HWR|].
  age_step HF HFr HG KK2 PP2 t E32u W mem2.
  pose proof (region_chunk_val E' _ _ 3 32 t _ _ _ _ _ 384 4%N (SOff 37 (-1)) HS eq_refl E32u
    ltac:(left; reflexivity) ltac:(lia)) as V1f.
  pose proof (region_chunk_val E' _ _ 4 32 t _ _ _ _ _ 392 4%N (SOff 40 0) HS eq_refl E32u
    ltac:(left; reflexivity) ltac:(lia)) as V2f.
  rewrite (ast_off_mod E' 37 mm (-1) 4%N E37 ltac:(lia) ltac:(cbn; lia) ltac:(lia)) in V1f.
  rewrite (atom_mod E' 40 (seq_of X) 4 E40) in V2f by (cbn; pose proof (reac_disco_table_age.seq_range X); lia).
  cbn [ms_mem restrict] in V1f, V2f.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (12%bv : bv 5) Q12.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  prreg HS (27%bv : bv 5) Q27.
  pmkst HS.
  change (VAL A_TEXT + 22944) with (BASE + (AF_reac_disco_table_age + 124)).
  apply SRr_ret. right. split; [reflexivity|]. split; [exact Hlt|].
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?mmx _) ?mdx = _ /\ _ => exists rg, mmx, mdx end.
  split; [reflexivity|]. split; [exact HJ2|].
  split; [rewrite Q2, E2; exact R2|].
  split; [rewrite Q3, E3; exact R3|].
  split; [rewrite Q4, E4; exact R4|].
  split; [rewrite Q25, E25; exact R25|].
  split; [rewrite Q26, E26; exact R26|].
  split; [rewrite Q27, E27; exact R27|].
  split; [rewrite Q8, E36, unsigned_lit_small by lia; reflexivity|].
  split; [rewrite Q9, E32, unsigned_lit_small by lia; reflexivity|].
  split; [rewrite Q18, E32; reflexivity|].
  split; [rewrite Q19, E33; reflexivity|].
  split; [rewrite Q20, E34; reflexivity|].
  split; [rewrite Q21, E32, E34, unsigned_lit_small by lia; reflexivity|].
  split; [rewrite Q22, E35; reflexivity|].
  split; [rewrite Q23; reflexivity|].
  split; [rewrite Q24; reflexivity|].
  split; [rewrite Q12, E37, unsigned_lit_small by lia; f_equal; lia|].
  split.
  { apply (lp_frame_kept W memL _ (spZ regs) regs
      (fun a => (t + 384 <= a < t + 388 \/ t + 392 <= a < t + 396) \/
                (t + 48 * i <= a < t + 48 * i + 48) \/ (spZ regs - 80 - 4096 <= a < spZ regs - 80))).
    - intros a Ha HZ. cbv beta in HZ.
      rewrite (KK2 a Ha ltac:(cbv beta; lia)). rewrite (Hfr a Ha ltac:(lia) ltac:(lia)).
      apply (KK a Ha ltac:(cbv beta; lia)).
    - intros a Ha. split; [lia | cbv beta; lia].
    - exact HFR. }
  split.
  { pose proof (age_garr8_fields (mrestrict (w_H W) mem2) _ Y t (mm - 1) (seq_of X) HG2 LY
      ltac:(lia) ltac:(pose proof (reac_disco_table_age.seq_range X); lia)
      ltac:(intros a Ha Ha1 Ha2; apply (mbyte_of_aview SEGS); apply KK2; [lia | cbv beta; lia]) V1f V2f) as G.
    assert (LZ : length (upd Y 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))) = 400%nat) by
      (rewrite (reac_disco_table_age.length_upd Y 384 (Mem.le4 (Z_to_bv 64 (mm - 1))) ltac:(lia) ltac:(rewrite Mem.length_le4, LY; lia)); exact LY).
    assert (SQY : seq_of (upd Y 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))) = seq_of X).
    { rewrite reac_disco_table_age.seq_of_upd_out by (rewrite ?Mem.length_le4, ?LY; lia).
      unfold Y. rewrite reac_disco_table_age.seq_of_upd_out by (rewrite ?LE, ?LX; lia). reflexivity. }
    replace (upd (upd Y 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))) 392 (Mem.le4 (Z_to_bv 64 (seq_of X))))
      with (upd Y 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))) in G.
    - replace (upd Y 384 (Mem.le4 (Z_to_bv 64 (mm - 1))))
        with (upd (upd A (48 * i) (entry_of A (mm - 1))) 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))) in G.
      + exact G.
      + unfold Y, X. symmetry. apply reac_disco_table_age.tbl_mem_step; rewrite ?Mem.length_le4, ?LA; lia.
    - rewrite <- SQY. symmetry. apply upd_seq_self. exact LZ. }
  split.
  { intros a Ha Hw Ht. rewrite (KK2 a Ha ltac:(cbv beta; lia)). exact (KM2 a Ha Hw Ht). }
  intros a Ha. apply PP2. apply Hpres2. apply PP. apply HPRES. exact Ha.
Qed.
Lemma age_loop_walk : age_stale_iter_P -> forall (fuel : nat) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs regsL : bvmap 5 word) memL mdL (t now i mm r : Z) (T A : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memL mdL k ->
YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_TABLE_AGE_STK -> spZ regs <= sp0 ->
0 < t -> t mod 8 = 0 -> amem_range t 400 ->
(spZ regs <= t \/ t + 400 <= spZ regs - REAC_DISCO_TABLE_AGE_STK) ->
(forall a, t <= a < t + 400 ->
   awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF t 400 ->
shadow_hull_vis (aview SEGS (w_H W) memc) t 400 ->
0 <= now < 2 ^ 64 -> length T = 400%nat -> table_ok T ->
Z.of_nat fuel = mm - i -> i < mm ->
reac_disco_table_age.age_inv T now A i mm r ->
age_loop fuel A now i mm r = age_loop (Z.to_nat (n_of T)) T now 0 (n_of T) 0 ->
getr regsL 2 = w64 (spZ regs - 80) ->
getr regsL 3 = getr regs 3 -> getr regsL 4 = getr regs 4 ->
getr regsL 25 = getr regs 25 -> getr regsL 26 = getr regs 26 -> getr regsL 27 = getr regs 27 ->
getr regsL 8 = w64 r -> getr regsL 9 = w64 (t + 384) -> getr regsL 18 = w64 t ->
getr regsL 19 = w64 now -> getr regsL 20 = w64 SB -> getr regsL 21 = age_sh5 t ->
getr regsL 22 = w64 i -> getr regsL 23 = w64 5000000001 -> getr regsL 24 = w64 3 ->
getr regsL 12 = w64 mm ->
lp_frame (mrestrict (w_H W) memL) (spZ regs) regs ->
garr8 SEGS (mrestrict (w_H W) memL) t (map (fun b : byte => bv_unsigned b) (upd A 384 (Mem.le4 (Z_to_bv 64 mm)))) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_DISCO_TABLE_AGE_STK <= a < spZ regs) -> ~ (t <= a < t + 400) ->
   aview SEGS (w_H W) memL a = aview SEGS (w_H W) memc a) ->
(forall a, apresent (w_H W) memc a -> apresent (w_H W) memL a) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
SRr SEGS W (mkCfg (mkst (fx := fx) regsL (Z_to_bv 64 (BASE + (AF_reac_disco_table_age + 124))) memL (seg_rom SEGS)) mdL)
  (treac_disco_table_age_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs t now T).
Proof.
intros STALE.
induction fuel as [|fuel IH];
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsL memL mdL t now i mm r T A
  HJ0 HJL Hra Hsp16 Hwlo Hwhi Ht0 Ht8 HAM Hside HWR HRA HHV Hnow LT TOK Hfuel Him HI HRES
  R2 R3 R4 R25 R26 R27 R8 R9 R18 R19 R20 R21 R22 R23 R24 R12 HFR HGA HKEPT HPRES Hgp Htp; [lia|].
destruct (disco_stale A i now) eqn:STL.
{ eapply SRr_bind.
  { exact (STALE fuel STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsL memL mdL t now i mm r T A
      HJ0 HJL Hra Hsp16 Hwlo Hwhi Ht0 Ht8 HAM Hside HWR HRA HHV Hnow LT TOK Hfuel Him HI HRES
      R2 R3 R4 R25 R26 R27 R8 R9 R18 R19 R20 R21 R22 R23 R24 R12 HFR HGA HKEPT HPRES Hgp Htp STL). }
  intros W2 c2 _ [HP | (-> & Hlt & regsL2 & memL2 & mdL2 & -> & HJ2 & Q2 & Q3 & Q4 & Q25 & Q26 & Q27 & Q8 & Q9 &
    Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q12 & HFR2 & HGA2 & HK2 & HP2)].
  - apply SRr_ret. exact HP.
  - pose proof TOK as (T1 & _).
    apply (IH STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsL2 memL2 mdL2 t now i (mm - 1) (r + 1) T
      (upd A (48 * i) (entry_of A (mm - 1)))
      HJ0 HJ2 Hra Hsp16 Hwlo Hwhi Ht0 Ht8 HAM Hside HWR HRA HHV Hnow LT TOK ltac:(lia) Hlt
      (reac_disco_table_age.age_inv_stale T now A i mm r LT T1 HI Him STL)
      ltac:(rewrite <- HRES; symmetry; apply reac_disco_table_age.age_loop_stale; [lia | exact STL])
      Q2 Q3 Q4 Q25 Q26 Q27 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q12 HFR2 HGA2 HK2 HP2 Hgp Htp). }
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (HS1 : REAC_DISCO_TABLE_AGE_STK = 4176) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (age_t_app STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k t HJ0 Ht0 Ht8 HAM) as (Ht4096 & Ht47 & Hband).
pose proof (age_t_off STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k t HJ0 HWR) as Hoff.
pose proof HJ0 as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp016 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJL as (HARL & _).
assert (Hsprng : 2 ^ 46 + 4176 <= spZ regs <= 2 ^ 47) by lia.
pose proof TOK as (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
pose proof HI as (LA & Hi0 & Hmn & Hrr & _).
assert (Hmm8 : mm <= 8) by lia.
assert (Hr8 : 0 <= r <= 8) by lia.
set (X := upd A 384 (Mem.le4 (Z_to_bv 64 mm))) in *.
assert (LX : length X = 400%nat) by (unfold X; rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LA; lia).
assert (HnX : n_of X = mm) by (unfold X; apply reac_disco_table_age.n_of_set; [exact LA | lia]).
assert (HPRL : forall a, t <= a < t + 400 -> apresent (w_H W) memL a) by (intros a Ha; apply HPRES; apply (HWR a Ha)).
destruct (age_shadow_kept memL memc W (spZ regs) t Hsprng Ht4096 Ht47 HAM HKEPT HRA HHV) as [HRAL HHVL].
destruct (age_lp_entry lyc Sc W memL mdL regsL regs t now i mm r X HARL Ht4096 Ht47 Ht8 Hnow Hoff HAM (proj1 Hi0) Him Hmm8 Hr8
  Hsprng Hsp16 Hside R2 R8 R9 R18 R19 R20 R21 R22 R23 R24 R12 LX HnX HGA HPRL HRAL HFR) as [HS SHOK].
set (E := EL regsL regs t now i mm r (t + 48 * i) (last_of X i) (seq_of X)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EL; apply Eimg_env).
assert (EL0 : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsL (lp_extra regs t now i mm r (t + 48 * i) (last_of X i) (seq_of X))) n)
by (intros n Hn; subst E; unfold EL; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 19)%nat -> ew E (32 + j)%nat = nth j (lp_extra regs t now i mm r (t + 48 * i) (last_of X i) (seq_of X)) (Z_to_bv 64 0))
by (intros j Hj; rewrite EL0 by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41.
pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44. pose proof (EX 13%nat ltac:(lia)) as E45.
pose proof (EX 14%nat ltac:(lia)) as E46. pose proof (EX 15%nat ltac:(lia)) as E47.
pose proof (EX 16%nat ltac:(lia)) as E48. pose proof (EX 17%nat ltac:(lia)) as E49.
pose proof (EX 18%nat ltac:(lia)) as E50.
cbn [lp_extra map app nth Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50.
assert (E2 : ew E 2 = getr regsL 2) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsL 3) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsL 4) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 4 4%bv eq_refl)).
assert (E25 : ew E 25 = getr regsL 25) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 25 25%bv eq_refl)).
assert (E26 : ew E 26 = getr regsL 26) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr regsL 27) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ 27 27%bv eq_refl)).
assert (E32u : bv_unsigned (ew E 32) = t) by (rewrite E32; apply unsigned_lit_small; lia).
clear EX EL0.
paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
age_win HFr t E32u KK. age_pp0 HG PP W memL. clear HF HFr HG.
pose proof (reac_disco_table_age.last_range X i LX ltac:(lia)) as HLR.
assert (SX : disco_stale X i now = disco_stale A i now).
{ apply reac_disco_table_age.stale_ent; [exact LX | exact LA | lia | lia |].
  unfold X. apply reac_disco_table_age.entry_upd_hi; rewrite ?Mem.length_le4; lia. }
psrr_branch_tok RUN BR HS SHOK AGE_span.
- rewrite branch_geu_U, (U_atom E 39 (last_of X i) E39), (U_atom E 33 now E33) in Hc by lia.
  assert (NS : disco_stale A i now = false).
  { rewrite <- SX. unfold disco_stale. destruct (Z.ltb_spec (last_of X i) now); [cbn in Hc; discriminate | reflexivity]. }
  clear Hc.
  paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
  age_step HF HFr HG KK PP t E32u W memL.
  psrr_branch_tok RUN BR HS SHOK AGE_span.
  + rewrite branch_ge_S, (S_small E 35 i 1 E35), (S_small E 37 mm 0 E37) in Hc by lia.
    assert (Hend : mm = i + 1) by (destruct (Z.ltb_spec (i + 1) (mm + 0)); [discriminate | lia]). clear Hc.
    paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
    age_step HF HFr HG KK PP t E32u W memL.
    psrr_branch_tok RUN BR HS SHOK AGE_span.
    * rewrite branch_eq_U, (U_atom E 36 r E36), U_lit in Hc by lia.
      assert (Hr0 : r = 0) by (destruct (Z.eqb_spec r 0); [lia | discriminate]). clear Hc.
      paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
      age_step HF HFr HG KK PP t E32u W memL.
      pose proof (region_chunk_val E _ _ 3 32 t _ _ _ _ _ 384 4%N (SOff 37 0) HS eq_refl E32u
        ltac:(left; reflexivity) ltac:(lia)) as V1f.
      pose proof (region_chunk_val E _ _ 4 32 t _ _ _ _ _ 392 4%N (SOff 40 0) HS eq_refl E32u
        ltac:(left; reflexivity) ltac:(lia)) as V2f.
      rewrite (atom_mod E 37 mm 4 E37) in V1f by (cbn; lia).
      rewrite (atom_mod E 40 (seq_of X) 4 E40) in V2f by (cbn; pose proof (reac_disco_table_age.seq_range X); lia).
      cbn [ms_mem restrict] in V1f, V2f.
      prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2.
      prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
      prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
      prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
      prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
      prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
      rewrite Q1, E41, Hra.
      assert (AM : age_model T now = (X, r)).
      { rewrite (reac_disco_table_age.age_model_of T now A mm r).
        - rewrite Hr0. reflexivity.
        - rewrite <- HRES. rewrite reac_disco_table_age.age_loop_keep by (exact NS || lia).
          apply reac_disco_table_age.age_loop_end. lia. }
      apply (age_final STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ t now T X r HJ0).
      -- apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJL.
      -- exact Hwlo.
      -- exact Hwhi.
      -- exact Hoff.
      -- intros a Ha Hw Ht. rewrite (KK a Ha ltac:(cbv beta; lia)). exact (HKEPT a Ha Hw Ht).
      -- intros a Ha. apply PP. apply HPRES. exact Ha.
      -- apply age_preserved;
           first [ rewrite Q2, E2, R2; unfold w64; rewrite unsigned_lit_small by lia;
                   replace (spZ regs - 80 + 80) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
                 | rewrite Q3, E3; exact R3 | rewrite Q4, E4; exact R4
                 | rewrite Q25, E25; exact R25 | rewrite Q26, E26; exact R26 | rewrite Q27, E27; exact R27
                 | rewrite Q8, E42; reflexivity | rewrite Q9, E43; reflexivity | rewrite Q18, E44; reflexivity
                 | rewrite Q19, E45; reflexivity | rewrite Q20, E46; reflexivity | rewrite Q21, E47; reflexivity
                 | rewrite Q22, E48; reflexivity | rewrite Q23, E49; reflexivity | rewrite Q24, E50; reflexivity ].
      -- rewrite Q10, E36. reflexivity.
      -- apply (age_garr8_same (mrestrict (w_H W) memL) _ X t mm (seq_of X) HGA LX).
         ++ intros a Ha Ha1 Ha2. apply (mbyte_of_aview SEGS). apply KK; [lia | cbv beta; lia].
         ++ rewrite <- HnX, <- (u_of_n X LX ltac:(lia)). apply (age_val _ X t 384 4 HGA); [lia | rewrite LX; cbn; lia].
         ++ exact V1f.
         ++ unfold seq_of. apply (age_val _ X t 392 4 HGA); [lia | rewrite LX; cbn; lia].
         ++ exact V2f.
      -- exact AM.
      -- apply reac_disco_table_age.age_model_post; [exact LT | exact TOK | exact AM].
    * rewrite branch_eq_U, (U_atom E 36 r E36), U_lit in Hc by lia.
      assert (Hr0 : r <> 0) by (destruct (Z.eqb_spec r 0); [discriminate | lia]). clear Hc.
      paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
      age_step HF HFr HG KK PP t E32u W memL.
      pose proof (region_chunk_val E _ _ 3 32 t _ _ _ _ _ 384 4%N (SOff 37 0) HS eq_refl E32u
        ltac:(left; reflexivity) ltac:(lia)) as V1f.
      pose proof (region_chunk_val E _ _ 4 32 t _ _ _ _ _ 392 4%N (SAlu ALU_ADD (SExt true 32 (SOff 40 0)) (SLit 1)) HS eq_refl E32u
        ltac:(left; reflexivity) ltac:(lia)) as V2f.
      rewrite (atom_mod E 37 mm 4 E37) in V1f by (cbn; lia).
      rewrite (sext_add1_mod E 40 (seq_of X) E40) in V2f by (pose proof (reac_disco_table_age.seq_range X); lia).
      cbn [ms_mem restrict] in V1f, V2f.
      prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2.
      prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
      prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
      prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
      prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
      prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
      rewrite Q1, E41, Hra.
      assert (SQ : seq_of X = seq_of T) by (unfold X; apply (age_seq_eq T now A i mm r); [exact LT | exact T1 | exact HI | apply Mem.length_le4]).
      set (T' := upd X 392 (Mem.le4 (Z_to_bv 64 (seq_of T + 1)))).
      assert (AM : age_model T now = (T', r)).
      { rewrite (reac_disco_table_age.age_model_of T now A mm r).
        - replace (0 <? r) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
        - rewrite <- HRES. rewrite reac_disco_table_age.age_loop_keep by (exact NS || lia).
          apply reac_disco_table_age.age_loop_end. lia. }
      apply (age_final STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ t now T T' r HJ0).
      -- apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJL.
      -- exact Hwlo.
      -- exact Hwhi.
      -- exact Hoff.
      -- intros a Ha Hw Ht. rewrite (KK a Ha ltac:(cbv beta; lia)). exact (HKEPT a Ha Hw Ht).
      -- intros a Ha. apply PP. apply HPRES. exact Ha.
      -- apply age_preserved;
           first [ rewrite Q2, E2, R2; unfold w64; rewrite unsigned_lit_small by lia;
                   replace (spZ regs - 80 + 80) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
                 | rewrite Q3, E3; exact R3 | rewrite Q4, E4; exact R4
                 | rewrite Q25, E25; exact R25 | rewrite Q26, E26; exact R26 | rewrite Q27, E27; exact R27
                 | rewrite Q8, E42; reflexivity | rewrite Q9, E43; reflexivity | rewrite Q18, E44; reflexivity
                 | rewrite Q19, E45; reflexivity | rewrite Q20, E46; reflexivity | rewrite Q21, E47; reflexivity
                 | rewrite Q22, E48; reflexivity | rewrite Q23, E49; reflexivity | rewrite Q24, E50; reflexivity ].
      -- rewrite Q10, E36. reflexivity.
      -- pose proof (reac_disco_table_age.seq_range X) as HSR.
         pose proof (age_garr8_fields (mrestrict (w_H W) memL) _ X t mm ((seq_of X + 1) mod 2 ^ 32) HGA LX
           ltac:(lia) ltac:(pose proof (Z.mod_pos_bound (seq_of X + 1) (2 ^ 32) ltac:(lia)); lia)
           ltac:(intros a Ha Ha1 Ha2; apply (mbyte_of_aview SEGS); apply KK; [lia | cbv beta; lia]) V1f
           V2f) as G.
         replace (upd X 384 (Mem.le4 (Z_to_bv 64 mm))) with X in G
           by (unfold X; symmetry; apply reac_disco_table_age.upd_upd; rewrite ?Mem.length_le4, ?LA; lia).
         replace (Mem.le4 (Z_to_bv 64 ((seq_of X + 1) mod 2 ^ 32))) with (Mem.le4 (Z_to_bv 64 (seq_of T + 1))) in G.
         ++ exact G.
         ++ apply reac_disco_table_age.le4_eq_mod. rewrite SQ, !unsigned_lit_small.
            ** rewrite Z.mod_mod by lia. reflexivity.
            ** pose proof (Z.mod_pos_bound (seq_of T + 1) (2 ^ 32) ltac:(lia)); lia.
            ** pose proof (reac_disco_table_age.seq_range T); lia.
      -- exact AM.
      -- apply reac_disco_table_age.age_model_post; [exact LT | exact TOK | exact AM].
  + rewrite branch_ge_S, (S_small E 35 i 1 E35), (S_small E 37 mm 0 E37) in Hc by lia.
    assert (Hlt : i + 1 < mm) by (destruct (Z.ltb_spec (i + 1) (mm + 0)); [lia | discriminate]). clear Hc.
    paj_run_to_tok RUNTO HS HJL SHOK AGE_span (AF_reac_disco_table_age + 124); [age_awr E32u HWR|].
    age_step HF HFr HG KK PP t E32u W memL.
    pose proof (region_chunk_val E _ _ 3 32 t _ _ _ _ _ 384 4%N (SOff 37 0) HS eq_refl E32u
      ltac:(left; reflexivity) ltac:(lia)) as V1f.
    pose proof (region_chunk_val E _ _ 4 32 t _ _ _ _ _ 392 4%N (SOff 40 0) HS eq_refl E32u
      ltac:(left; reflexivity) ltac:(lia)) as V2f.
    rewrite (atom_mod E 37 mm 4 E37) in V1f by (cbn; lia).
    rewrite (atom_mod E 40 (seq_of X) 4 E40) in V2f by (cbn; pose proof (reac_disco_table_age.seq_range X); lia).
    cbn [ms_mem restrict] in V1f, V2f.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (12%bv : bv 5) Q12.
    prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
    prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
    prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
    prreg HS (27%bv : bv 5) Q27.
    pmkst HS.
    change (VAL A_TEXT + 22944) with (BASE + (AF_reac_disco_table_age + 124)).
    eapply (IH STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ t now (i + 1) mm r T A
      HJ0 HJL Hra Hsp16 Hwlo Hwhi Ht0 Ht8 HAM Hside HWR HRA HHV Hnow LT TOK).
    * lia.
    * exact Hlt.
    * exact (reac_disco_table_age.age_inv_keep T now A i mm r HI Him NS).
    * rewrite <- HRES. symmetry. apply reac_disco_table_age.age_loop_keep; [lia | exact NS].
    * rewrite Q2, E2. exact R2.
    * rewrite Q3, E3. exact R3.
    * rewrite Q4, E4. exact R4.
    * rewrite Q25, E25. exact R25.
    * rewrite Q26, E26. exact R26.
    * rewrite Q27, E27. exact R27.
    * rewrite Q8, E36. reflexivity.
    * rewrite Q9, E32, unsigned_lit_small by lia. reflexivity.
    * rewrite Q18, E32. reflexivity.
    * rewrite Q19, E33. reflexivity.
    * rewrite Q20, E34. reflexivity.
    * rewrite Q21, E32, E34, unsigned_lit_small by lia. reflexivity.
    * rewrite Q22, E35, unsigned_lit_small by lia. reflexivity.
    * rewrite Q23. reflexivity.
    * rewrite Q24. reflexivity.
    * rewrite Q12, E37. reflexivity.
    * apply (lp_frame_kept W memL _ (spZ regs) regs _ KK); [|exact HFR].
      intros a Ha. split; [lia | cbv beta; lia].
    * apply (age_garr8_same (mrestrict (w_H W) memL) _ X t mm (seq_of X) HGA LX).
      -- intros a Ha Ha1 Ha2. apply (mbyte_of_aview SEGS). apply KK; [lia | cbv beta; lia].
      -- rewrite <- HnX, <- (u_of_n X LX ltac:(lia)). apply (age_val _ X t 384 4 HGA); [lia | rewrite LX; cbn; lia].
      -- exact V1f.
      -- unfold seq_of. apply (age_val _ X t 392 4 HGA); [lia | rewrite LX; cbn; lia].
      -- exact V2f.
    * intros a Ha Hw Ht. rewrite (KK a Ha ltac:(cbv beta; lia)). exact (HKEPT a Ha Hw Ht).
    * intros a Ha. apply PP. apply HPRES. exact Ha.
    * exact Hgp.
    * exact Htp.
- rewrite branch_geu_U, (U_atom E 39 (last_of X i) E39), (U_atom E 33 now E33) in Hc by lia.
  assert (Hlt0 : last_of X i < now) by (destruct (Z.ltb_spec (last_of X i) now); [lia | cbn in Hc; discriminate]).
  clear Hc.
  paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
  age_step HF HFr HG KK PP t E32u W memL.
  assert (HDIFF : U E (SAlu ALU_ADD (SOff 33 0) (SMd M_MUL (SOff 39 0) (SLit (-1)))) = now - last_of X i)
    by (apply U_diff; [exact E33 | exact E39 | lia | lia | lia]).
  psrr_branch_tok RUN BR HS SHOK AGE_span.
  + rewrite branch_ltu_U, HDIFF, U_lit in Hc by lia. apply Z.ltb_lt in Hc.
    assert (NS : disco_stale A i now = false).
    { rewrite <- SX. unfold disco_stale, REAC_DISCO_STALE_NS.
      rewrite (proj2 (Z.ltb_ge 5000000000 (now - last_of X i)) ltac:(lia)). apply andb_false_r. }
    clear Hc.
    paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
    age_step HF HFr HG KK PP t E32u W memL.
    { psrr_branch_tok RUN BR HS SHOK AGE_span.
      + rewrite branch_ge_S, (S_small E 35 i 1 E35), (S_small E 37 mm 0 E37) in Hc by lia.
        assert (Hend : mm = i + 1) by (destruct (Z.ltb_spec (i + 1) (mm + 0)); [discriminate | lia]). clear Hc.
        paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
        age_step HF HFr HG KK PP t E32u W memL.
        psrr_branch_tok RUN BR HS SHOK AGE_span.
        * rewrite branch_eq_U, (U_atom E 36 r E36), U_lit in Hc by lia.
          assert (Hr0 : r = 0) by (destruct (Z.eqb_spec r 0); [lia | discriminate]). clear Hc.
          paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
          age_step HF HFr HG KK PP t E32u W memL.
          pose proof (region_chunk_val E _ _ 3 32 t _ _ _ _ _ 384 4%N (SOff 37 0) HS eq_refl E32u
            ltac:(left; reflexivity) ltac:(lia)) as V1f.
          pose proof (region_chunk_val E _ _ 4 32 t _ _ _ _ _ 392 4%N (SOff 40 0) HS eq_refl E32u
            ltac:(left; reflexivity) ltac:(lia)) as V2f.
          rewrite (atom_mod E 37 mm 4 E37) in V1f by (cbn; lia).
          rewrite (atom_mod E 40 (seq_of X) 4 E40) in V2f by (cbn; pose proof (reac_disco_table_age.seq_range X); lia).
          cbn [ms_mem restrict] in V1f, V2f.
          prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2.
          prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
          prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
          prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
          prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
          prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
          eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
          rewrite Q1, E41, Hra.
          assert (AM : age_model T now = (X, r)).
          { rewrite (reac_disco_table_age.age_model_of T now A mm r).
            - rewrite Hr0. reflexivity.
            - rewrite <- HRES. rewrite reac_disco_table_age.age_loop_keep by (exact NS || lia).
              apply reac_disco_table_age.age_loop_end. lia. }
          apply (age_final STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ t now T X r HJ0).
          -- apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJL.
          -- exact Hwlo.
          -- exact Hwhi.
          -- exact Hoff.
          -- intros a Ha Hw Ht. rewrite (KK a Ha ltac:(cbv beta; lia)). exact (HKEPT a Ha Hw Ht).
          -- intros a Ha. apply PP. apply HPRES. exact Ha.
          -- apply age_preserved;
               first [ rewrite Q2, E2, R2; unfold w64; rewrite unsigned_lit_small by lia;
                       replace (spZ regs - 80 + 80) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
                     | rewrite Q3, E3; exact R3 | rewrite Q4, E4; exact R4
                     | rewrite Q25, E25; exact R25 | rewrite Q26, E26; exact R26 | rewrite Q27, E27; exact R27
                     | rewrite Q8, E42; reflexivity | rewrite Q9, E43; reflexivity | rewrite Q18, E44; reflexivity
                     | rewrite Q19, E45; reflexivity | rewrite Q20, E46; reflexivity | rewrite Q21, E47; reflexivity
                     | rewrite Q22, E48; reflexivity | rewrite Q23, E49; reflexivity | rewrite Q24, E50; reflexivity ].
          -- rewrite Q10, E36. reflexivity.
          -- apply (age_garr8_same (mrestrict (w_H W) memL) _ X t mm (seq_of X) HGA LX).
             ++ intros a Ha Ha1 Ha2. apply (mbyte_of_aview SEGS). apply KK; [lia | cbv beta; lia].
             ++ rewrite <- HnX, <- (u_of_n X LX ltac:(lia)). apply (age_val _ X t 384 4 HGA); [lia | rewrite LX; cbn; lia].
             ++ exact V1f.
             ++ unfold seq_of. apply (age_val _ X t 392 4 HGA); [lia | rewrite LX; cbn; lia].
             ++ exact V2f.
          -- exact AM.
          -- apply reac_disco_table_age.age_model_post; [exact LT | exact TOK | exact AM].
        * rewrite branch_eq_U, (U_atom E 36 r E36), U_lit in Hc by lia.
          assert (Hr0 : r <> 0) by (destruct (Z.eqb_spec r 0); [discriminate | lia]). clear Hc.
          paj_run_tok RUN HS HJL SHOK AGE_span; [age_awr E32u HWR|].
          age_step HF HFr HG KK PP t E32u W memL.
          pose proof (region_chunk_val E _ _ 3 32 t _ _ _ _ _ 384 4%N (SOff 37 0) HS eq_refl E32u
            ltac:(left; reflexivity) ltac:(lia)) as V1f.
          pose proof (region_chunk_val E _ _ 4 32 t _ _ _ _ _ 392 4%N (SAlu ALU_ADD (SExt true 32 (SOff 40 0)) (SLit 1)) HS eq_refl E32u
            ltac:(left; reflexivity) ltac:(lia)) as V2f.
          rewrite (atom_mod E 37 mm 4 E37) in V1f by (cbn; lia).
          rewrite (sext_add1_mod E 40 (seq_of X) E40) in V2f by (pose proof (reac_disco_table_age.seq_range X); lia).
          cbn [ms_mem restrict] in V1f, V2f.
          prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2.
          prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
          prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
          prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
          prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
          prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
          eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
          rewrite Q1, E41, Hra.
          assert (SQ : seq_of X = seq_of T) by (unfold X; apply (age_seq_eq T now A i mm r); [exact LT | exact T1 | exact HI | apply Mem.length_le4]).
          set (T' := upd X 392 (Mem.le4 (Z_to_bv 64 (seq_of T + 1)))).
          assert (AM : age_model T now = (T', r)).
          { rewrite (reac_disco_table_age.age_model_of T now A mm r).
            - replace (0 <? r) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
            - rewrite <- HRES. rewrite reac_disco_table_age.age_loop_keep by (exact NS || lia).
              apply reac_disco_table_age.age_loop_end. lia. }
          apply (age_final STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ t now T T' r HJ0).
          -- apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJL.
          -- exact Hwlo.
          -- exact Hwhi.
          -- exact Hoff.
          -- intros a Ha Hw Ht. rewrite (KK a Ha ltac:(cbv beta; lia)). exact (HKEPT a Ha Hw Ht).
          -- intros a Ha. apply PP. apply HPRES. exact Ha.
          -- apply age_preserved;
               first [ rewrite Q2, E2, R2; unfold w64; rewrite unsigned_lit_small by lia;
                       replace (spZ regs - 80 + 80) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
                     | rewrite Q3, E3; exact R3 | rewrite Q4, E4; exact R4
                     | rewrite Q25, E25; exact R25 | rewrite Q26, E26; exact R26 | rewrite Q27, E27; exact R27
                     | rewrite Q8, E42; reflexivity | rewrite Q9, E43; reflexivity | rewrite Q18, E44; reflexivity
                     | rewrite Q19, E45; reflexivity | rewrite Q20, E46; reflexivity | rewrite Q21, E47; reflexivity
                     | rewrite Q22, E48; reflexivity | rewrite Q23, E49; reflexivity | rewrite Q24, E50; reflexivity ].
          -- rewrite Q10, E36. reflexivity.
          -- pose proof (reac_disco_table_age.seq_range X) as HSR.
             pose proof (age_garr8_fields (mrestrict (w_H W) memL) _ X t mm ((seq_of X + 1) mod 2 ^ 32) HGA LX
               ltac:(lia) ltac:(pose proof (Z.mod_pos_bound (seq_of X + 1) (2 ^ 32) ltac:(lia)); lia)
               ltac:(intros a Ha Ha1 Ha2; apply (mbyte_of_aview SEGS); apply KK; [lia | cbv beta; lia]) V1f
               V2f) as G.
             replace (upd X 384 (Mem.le4 (Z_to_bv 64 mm))) with X in G
               by (unfold X; symmetry; apply reac_disco_table_age.upd_upd; rewrite ?Mem.length_le4, ?LA; lia).
             replace (Mem.le4 (Z_to_bv 64 ((seq_of X + 1) mod 2 ^ 32))) with (Mem.le4 (Z_to_bv 64 (seq_of T + 1))) in G.
             ++ exact G.
             ++ apply reac_disco_table_age.le4_eq_mod. rewrite SQ, !unsigned_lit_small.
                ** rewrite Z.mod_mod by lia. reflexivity.
                ** pose proof (Z.mod_pos_bound (seq_of T + 1) (2 ^ 32) ltac:(lia)); lia.
                ** pose proof (reac_disco_table_age.seq_range T); lia.
          -- exact AM.
          -- apply reac_disco_table_age.age_model_post; [exact LT | exact TOK | exact AM].
      + rewrite branch_ge_S, (S_small E 35 i 1 E35), (S_small E 37 mm 0 E37) in Hc by lia.
        assert (Hlt : i + 1 < mm) by (destruct (Z.ltb_spec (i + 1) (mm + 0)); [lia | discriminate]). clear Hc.
        paj_run_to_tok RUNTO HS HJL SHOK AGE_span (AF_reac_disco_table_age + 124); [age_awr E32u HWR|].
        age_step HF HFr HG KK PP t E32u W memL.
        pose proof (region_chunk_val E _ _ 3 32 t _ _ _ _ _ 384 4%N (SOff 37 0) HS eq_refl E32u
          ltac:(left; reflexivity) ltac:(lia)) as V1f.
        pose proof (region_chunk_val E _ _ 4 32 t _ _ _ _ _ 392 4%N (SOff 40 0) HS eq_refl E32u
          ltac:(left; reflexivity) ltac:(lia)) as V2f.
        rewrite (atom_mod E 37 mm 4 E37) in V1f by (cbn; lia).
        rewrite (atom_mod E 40 (seq_of X) 4 E40) in V2f by (cbn; pose proof (reac_disco_table_age.seq_range X); lia).
        cbn [ms_mem restrict] in V1f, V2f.
        prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
        prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (12%bv : bv 5) Q12.
        prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
        prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
        prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
        prreg HS (27%bv : bv 5) Q27.
        pmkst HS.
        change (VAL A_TEXT + 22944) with (BASE + (AF_reac_disco_table_age + 124)).
        eapply (IH STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ t now (i + 1) mm r T A
          HJ0 HJL Hra Hsp16 Hwlo Hwhi Ht0 Ht8 HAM Hside HWR HRA HHV Hnow LT TOK).
        * lia.
        * exact Hlt.
        * exact (reac_disco_table_age.age_inv_keep T now A i mm r HI Him NS).
        * rewrite <- HRES. symmetry. apply reac_disco_table_age.age_loop_keep; [lia | exact NS].
        * rewrite Q2, E2. exact R2.
        * rewrite Q3, E3. exact R3.
        * rewrite Q4, E4. exact R4.
        * rewrite Q25, E25. exact R25.
        * rewrite Q26, E26. exact R26.
        * rewrite Q27, E27. exact R27.
        * rewrite Q8, E36. reflexivity.
        * rewrite Q9, E32, unsigned_lit_small by lia. reflexivity.
        * rewrite Q18, E32. reflexivity.
        * rewrite Q19, E33. reflexivity.
        * rewrite Q20, E34. reflexivity.
        * rewrite Q21, E32, E34, unsigned_lit_small by lia. reflexivity.
        * rewrite Q22, E35, unsigned_lit_small by lia. reflexivity.
        * rewrite Q23. reflexivity.
        * rewrite Q24. reflexivity.
        * rewrite Q12, E37. reflexivity.
        * apply (lp_frame_kept W memL _ (spZ regs) regs _ KK); [|exact HFR].
          intros a Ha. split; [lia | cbv beta; lia].
        * apply (age_garr8_same (mrestrict (w_H W) memL) _ X t mm (seq_of X) HGA LX).
          -- intros a Ha Ha1 Ha2. apply (mbyte_of_aview SEGS). apply KK; [lia | cbv beta; lia].
          -- rewrite <- HnX, <- (u_of_n X LX ltac:(lia)). apply (age_val _ X t 384 4 HGA); [lia | rewrite LX; cbn; lia].
          -- exact V1f.
          -- unfold seq_of. apply (age_val _ X t 392 4 HGA); [lia | rewrite LX; cbn; lia].
          -- exact V2f.
        * intros a Ha Hw Ht. rewrite (KK a Ha ltac:(cbv beta; lia)). exact (HKEPT a Ha Hw Ht).
        * intros a Ha. apply PP. apply HPRES. exact Ha.
        * exact Hgp.
        * exact Htp. }
  + rewrite branch_ltu_U, HDIFF, U_lit in Hc by lia. apply Z.ltb_ge in Hc. exfalso.
    rewrite <- SX in STL. unfold disco_stale, REAC_DISCO_STALE_NS in STL.
    rewrite (proj2 (Z.ltb_lt (last_of X i) now) Hlt0), (proj2 (Z.ltb_lt 5000000000 (now - last_of X i)) ltac:(lia)) in STL.
    discriminate STL.
Qed.
Lemma reg_chunk : forall E k, bv_unsigned (sv_denot E (SOff k 0)) mod 2 ^ (8 * Z.of_N 8) = bv_unsigned (ew E k).
Proof.
intros E k. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply Z.mod_small. pose proof (bv_unsigned_in_range 64 (ew E k)) as H. exact H.
Qed.
Ltac age_win0 HFr Usp sp KS :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => sp - 80 <= a < sp) HFr
     ltac:(let b := fresh "b" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
           let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
           intros b wl wh aa Hin Hrr; vm_compute in Hin;
           repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
                   [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia |]);
           destruct Hin)) as KS.
Ltac age_awr0 Usp spv sp0v :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?spx ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk spx fp b0 bc ly0 own0) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0v)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |];
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|] ].
Lemma frame_chunk : forall E ss ms lo hi wlo whi cs spv o (kk : nat) (kb : bv 5) (regs : bvmap 5 word),
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = spv -> In (YP09.mkChunk o (CVal 8 (SOff kk 0))) cs -> ew E kk = getr regs kb ->
val_mem SEGS (ms_mem ms) (spv + o) 8 (bv_unsigned (getr regs kb)).
Proof.
intros E ss ms lo hi wlo whi cs spv o kk kb regs HS Hn Hb Hin Hk.
pose proof (region_chunk_val E ss ms 0 2 spv lo hi wlo whi cs o 8%N (SOff kk 0) HS Hn Hb Hin ltac:(lia)) as V.
rewrite reg_chunk, Hk in V. exact V.
Qed.
Lemma age_main : age_stale_iter_P -> forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (t now : Z) (T : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 t -> getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_TABLE_AGE_STK -> spZ regs <= sp0 ->
0 < t -> t mod 8 = 0 -> amem_range t 400 ->
(spZ regs <= t \/ t + 400 <= spZ regs - REAC_DISCO_TABLE_AGE_STK) ->
(forall a, t <= a < t + 400 ->
   awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF t 400 ->
shadow_hull_vis (aview SEGS (w_H W) memc) t 400 ->
length T = 400%nat -> table_ok T ->
garr8 SEGS (mrestrict (w_H W) memc) t (map (fun b : byte => bv_unsigned b) T) ->
SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_reac_disco_table_age) regs memc mdc)
  (treac_disco_table_age_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs t now T).
Proof.
intros STALE STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t now T
  HJ0 Hra Hgp Htp H10 H11 Hnow Hsp16 Hwlo Hwhi Ht0 Ht8 HAM Hside HWR HRA HHV LT TOK HG0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (HS1 : REAC_DISCO_TABLE_AGE_STK = 4176) by reflexivity.
pose proof (age_t_app STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k t HJ0 Ht0 Ht8 HAM) as (Ht4096 & Ht47 & Hband).
pose proof (age_t_off STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k t HJ0 HWR) as Hoff.
pose proof HJ0 as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp016 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (Hsprng : 2 ^ 46 + 4176 <= spZ regs <= 2 ^ 47) by lia.
pose proof TOK as (T1 & T2 & T3 & T4).
pose proof T1 as T1'. unfold tbl_T1 in T1'.
destruct (age_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t T
  HJ0 H10 Hsp16 Hwlo Hwhi Ht0 Ht8 HAM Hside Hoff HRA LT T1 HG0) as [HS SHOK].
set (E := EA regs T) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EA; apply Eimg_env).
assert (EL0 : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (age_extra T)) n)
by (intros n Hn; subst E; unfold EA; apply Eimg_low; exact Hn).
assert (ER : forall (n : nat) (r : bv 5), (n < 32)%nat -> bv_unsigned r = Z.of_nat n -> ew E n = getr regs r).
{ intros n r Hn Hr. rewrite EL0 by (unfold A_TEXT; lia). apply ew_Ereg_nat. symmetry. exact Hr. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (n_of T)) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E2 : ew E 2 = getr regs 2) by (apply ER; [lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (ER 10%nat 10%bv) by (lia || reflexivity); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear EL0.
unfold cfg_at. change (w64 (BASE + AF_reac_disco_table_age)) with (Z_to_bv 64 (BASE + AF_reac_disco_table_age)).
pose proof HJ0 as HJ.
paj_run_tok RUN HS HJ SHOK AGE_span; [age_awr0 Usp (spZ regs) sp0|].
age_win0 HFr Usp (spZ regs) KK. age_pp0 HG PP W memc. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK AGE_span.
- rewrite branch_ge_S, S_SLit, (S_small E 33 (n_of T) 0 E33) in Hc by lia.
  rewrite (bv_swrap_small 64 0) in Hc by (change (bv_half_modulus 64) with (2 ^ 63); lia).
  assert (Hn0 : n_of T = 0) by (destruct (Z.ltb_spec 0 (n_of T + 0)); [discriminate | lia]). clear Hc.
  paj_run_tok RUN HS HJ SHOK AGE_span; [age_awr0 Usp (spZ regs) sp0|].
  age_win0 HFr Usp (spZ regs) K2. pose proof (kept_trans _ W _ _ _ KK K2) as KK2. clear KK K2. rename KK2 into KK.
  age_pp HG PP W memc. clear HF HFr HG.
  prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2.
  prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  rewrite Q1, (ER 1%nat 1%bv ltac:(lia) eq_refl), Hra.
  assert (U0 : upd T 384 (Mem.le4 (Z_to_bv 64 0)) = T)
    by (rewrite <- Hn0; apply reac_disco_table_age.upd_n_self; exact LT).
  assert (AM : age_model T now = (T, 0)).
  { rewrite (reac_disco_table_age.age_model_of T now T 0 0) by (rewrite Hn0; reflexivity).
    change (0 <? 0) with false. cbv beta iota. rewrite U0. reflexivity. }
  apply (age_final STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ t now T T 0 HJ0).
  + apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ.
  + exact Hwlo.
  + exact Hwhi.
  + exact Hoff.
  + intros a Ha Hw Ht. apply KK; [exact Ha | cbv beta; lia].
  + exact PP.
  + apply age_preserved;
      first [ rewrite Q2; apply ER; [lia | reflexivity] | rewrite Q3; apply ER; [lia | reflexivity]
            | rewrite Q4; apply ER; [lia | reflexivity] | rewrite Q8; apply ER; [lia | reflexivity]
            | rewrite Q9; apply ER; [lia | reflexivity] | rewrite Q18; apply ER; [lia | reflexivity]
            | rewrite Q19; apply ER; [lia | reflexivity] | rewrite Q20; apply ER; [lia | reflexivity]
            | rewrite Q21; apply ER; [lia | reflexivity] | rewrite Q22; apply ER; [lia | reflexivity]
            | rewrite Q23; apply ER; [lia | reflexivity] | rewrite Q24; apply ER; [lia | reflexivity]
            | rewrite Q25; apply ER; [lia | reflexivity] | rewrite Q26; apply ER; [lia | reflexivity]
            | rewrite Q27; apply ER; [lia | reflexivity]
            | match goal with |- ?g => idtac "APFAIL" g end; shelve ].
  + rewrite Q10. reflexivity.
  + apply (garr8_frame SEGS _ _ t _ HG0). intros a Ha. rewrite length_map, LT in Ha.
    apply (mbyte_of_aview SEGS). apply KK; [lia | cbv beta; lia].
  + exact AM.
  + apply reac_disco_table_age.age_model_post; [exact LT | exact TOK | exact AM].
- rewrite branch_ge_S, S_SLit, (S_small E 33 (n_of T) 0 E33) in Hc by lia.
  rewrite (bv_swrap_small 64 0) in Hc by (change (bv_half_modulus 64) with (2 ^ 63); lia).
  assert (Hn0 : 0 < n_of T) by (destruct (Z.ltb_spec 0 (n_of T + 0)); [lia | discriminate]). clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK AGE_span (AF_reac_disco_table_age + 124); [age_awr0 Usp (spZ regs) sp0|].
  age_win0 HFr Usp (spZ regs) K2. pose proof (kept_trans _ W _ _ _ KK K2) as KK2. clear KK K2. rename KK2 into KK.
  age_pp HG PP W memc. clear HF HFr HG.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (12%bv : bv 5) P12. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (HFRL : lp_frame (mrestrict (w_H W) (ms_mem ms0)) (spZ regs) regs).
  { unfold lp_frame.
    split; [replace (spZ regs - 80 + 0) with (spZ regs + (-80)) by lia; exact (frame_chunk _ _ _ _ _ _ _ _ _ _ 24%nat 24%bv regs HS eq_refl Usp ltac:(repeat first [left; reflexivity | right]) (ER 24%nat 24%bv ltac:(lia) eq_refl))|].
    split; [replace (spZ regs - 80 + 8) with (spZ regs + (-72)) by lia; exact (frame_chunk _ _ _ _ _ _ _ _ _ _ 23%nat 23%bv regs HS eq_refl Usp ltac:(repeat first [left; reflexivity | right]) (ER 23%nat 23%bv ltac:(lia) eq_refl))|].
    split; [replace (spZ regs - 80 + 16) with (spZ regs + (-64)) by lia; exact (frame_chunk _ _ _ _ _ _ _ _ _ _ 22%nat 22%bv regs HS eq_refl Usp ltac:(repeat first [left; reflexivity | right]) (ER 22%nat 22%bv ltac:(lia) eq_refl))|].
    split; [replace (spZ regs - 80 + 24) with (spZ regs + (-56)) by lia; exact (frame_chunk _ _ _ _ _ _ _ _ _ _ 21%nat 21%bv regs HS eq_refl Usp ltac:(repeat first [left; reflexivity | right]) (ER 21%nat 21%bv ltac:(lia) eq_refl))|].
    split; [replace (spZ regs - 80 + 32) with (spZ regs + (-48)) by lia; exact (frame_chunk _ _ _ _ _ _ _ _ _ _ 20%nat 20%bv regs HS eq_refl Usp ltac:(repeat first [left; reflexivity | right]) (ER 20%nat 20%bv ltac:(lia) eq_refl))|].
    split; [replace (spZ regs - 80 + 40) with (spZ regs + (-40)) by lia; exact (frame_chunk _ _ _ _ _ _ _ _ _ _ 19%nat 19%bv regs HS eq_refl Usp ltac:(repeat first [left; reflexivity | right]) (ER 19%nat 19%bv ltac:(lia) eq_refl))|].
    split; [replace (spZ regs - 80 + 48) with (spZ regs + (-32)) by lia; exact (frame_chunk _ _ _ _ _ _ _ _ _ _ 18%nat 18%bv regs HS eq_refl Usp ltac:(repeat first [left; reflexivity | right]) (ER 18%nat 18%bv ltac:(lia) eq_refl))|].
    split; [replace (spZ regs - 80 + 56) with (spZ regs + (-24)) by lia; exact (frame_chunk _ _ _ _ _ _ _ _ _ _ 9%nat 9%bv regs HS eq_refl Usp ltac:(repeat first [left; reflexivity | right]) (ER 9%nat 9%bv ltac:(lia) eq_refl))|].
    split; [replace (spZ regs - 80 + 64) with (spZ regs + (-16)) by lia; exact (frame_chunk _ _ _ _ _ _ _ _ _ _ 8%nat 8%bv regs HS eq_refl Usp ltac:(repeat first [left; reflexivity | right]) (ER 8%nat 8%bv ltac:(lia) eq_refl))|].
    replace (spZ regs - 80 + 72) with (spZ regs + (-8)) by lia; exact (frame_chunk _ _ _ _ _ _ _ _ _ _ 1%nat 1%bv regs HS eq_refl Usp ltac:(repeat first [left; reflexivity | right]) (ER 1%nat 1%bv ltac:(lia) eq_refl)). }
  pmkst HS.
  change (VAL A_TEXT + 22944) with (BASE + (AF_reac_disco_table_age + 124)).
  apply (age_loop_walk STALE (Z.to_nat (n_of T)) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _
    t now 0 (n_of T) 0 T T HJ0 HJ Hra Hsp16 Hwlo Hwhi Ht0 Ht8 HAM Hside HWR HRA HHV Hnow LT TOK).
  + lia.
  + exact Hn0.
  + apply reac_disco_table_age.age_inv_init; [exact LT | exact T1].
  + reflexivity.
  + rewrite P2, Usp. unfold w64. f_equal; lia.
  + rewrite P3. apply ER; [lia | reflexivity].
  + rewrite P4. apply ER; [lia | reflexivity].
  + rewrite P25. apply ER; [lia | reflexivity].
  + rewrite P26. apply ER; [lia | reflexivity].
  + rewrite P27. apply ER; [lia | reflexivity].
  + rewrite P8. reflexivity.
  + rewrite P9, E10, unsigned_lit_small by lia. reflexivity.
  + rewrite P18, E10. reflexivity.
  + rewrite P19, (ER 11%nat 11%bv ltac:(lia) eq_refl). exact H11.
  + rewrite P20, E32. reflexivity.
  + rewrite P21, E10, E32, unsigned_lit_small by lia. reflexivity.
  + rewrite P22. reflexivity.
  + rewrite P23. reflexivity.
  + rewrite P24. reflexivity.
  + rewrite P12, E33. reflexivity.
  + exact HFRL.
  + rewrite (reac_disco_table_age.upd_n_self T LT).
    apply (garr8_frame SEGS _ _ t _ HG0). intros a Ha. rewrite length_map, LT in Ha.
    apply (mbyte_of_aview SEGS). apply KK; [lia | cbv beta; lia].
  + intros a Ha Hw Ht. apply KK; [exact Ha | cbv beta; lia].
  + exact PP.
  + exact Hgp.
  + exact Htp.
Qed.
End w.
Theorem pb_reac_disco_table_age_of_stale : (forall fq : YK11.FPState, age_stale_iter_P (fx := fq)) ->
  treac_disco_table_age_spec.
Proof.
intros STALE fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t now T
  HJ0 HRO Hra Hra4 Hgp Htp H10 H11 Hnow Hsp16 Hwlo Hwhi Ht0 Ht8 Ht63 HAM Hside HWR HRA HHV LT TOK HG0.
exact (age_main (fx := fq) (STALE fq) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t now T
  HJ0 Hra Hgp Htp H10 H11 Hnow Hsp16 Hwlo Hwhi Ht0 Ht8 HAM Hside HWR HRA HHV LT TOK HG0).
Qed.
Theorem pb_reac_disco_table_age : treac_disco_table_age_spec.
Proof. exact (pb_reac_disco_table_age_of_stale (fun fq => age_stale_iter (fx := fq))). Qed.
End h.
End f.
End d.
