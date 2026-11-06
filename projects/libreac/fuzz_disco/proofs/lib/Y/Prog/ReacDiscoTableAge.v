(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 2047 of its 2116 lines of code are new or changed and 300 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacDiscoTableAge.v, with its numbers changed; 1756 of its 1948 lines of code are new or changed and 1924 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c reac_disco_table_age_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import AcpySameDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC4b YC1h YC1g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_age.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis AMEMCPYEQ : forall fq : YK11.FPState, acpy_same_realizes (fx := fq) SEGS B (SIGMA AS___asan_memcpy).
Definition REAC_DISCO_TABLE_AGE_STK : Z := 96 + ESTACK.
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
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_disco_table_age) regs memc mdc)
    (treac_disco_table_age_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs t now T).

Import YP0m YP0l YCbn YP0e YP06 YP03 YA0o YA0q YC4b YC1h YC1g.
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Definition TA_SB : Z := 0x7fff8000.
Definition TA_Bx : sv := SOff 32 0.
Definition TA_Bspan : Z * Z := (TA_SB, TA_SB + 2 ^ 44 - 1).
Definition ta_cnt_ro : YP09.region := YP09.mkRegion (Some 10%nat) 384 388 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 33 0))].
Definition ta_regions : smem := [stack_region 96; got_regionP; bcell_regionP 32; ta_cnt_ro].
Definition ta_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 8 (2 ^ 47 - 401) 3);
  (32%nat, mkAF TA_SB TA_SB 0); (33%nat, mkAF 0 8 0)] [] [].
Definition ss_ta : sstate := mkSS AF_both3_reac_disco_table_age sr_atoms ta_regions None ta_facts.
Definition ta_SH : list shent := [mkSHE 10 0 400].
Definition ta_extra (n s : Z) : list word := [Z_to_bv 64 TA_SB; Z_to_bv 64 n; Z_to_bv 64 s].

Definition TA_BxL : sv := SOff 20 0.
Definition TA_NOTT : afact := mkAF (2 ^ 64 - 1 - (2 ^ 47 - 401)) (2 ^ 64 - 9) 0.
Definition ta_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 384) (SLit 3)) (SOff 20 0).
Definition ta_srL : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 18%bv (SOff 8 384)) 21%bv ta_shx) 24%bv (SLit 8)) 25%bv (SLit 5000000000)) 26%bv (SLit 3).
Definition ta_cntL : YP09.region := YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 12 0))].
Definition ta_entL : YP09.region := YP09.mkRegion (Some 32%nat) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 33 0))].
Definition ta_regL : smem := [got_regionP; bcell_regionP 20; ta_cntL; ta_entL].
Definition ta_ali1 : sv := SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 22 0) (SLit 48)).
Definition ta_ali2 : sv := SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SLit 48)) (SLit (-48)).
Definition ta_factsL : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 8 (2 ^ 47 - 401) 3); (12%nat, mkAF 1 8 0); (19%nat, mkAF 0 7 0);
   (20%nat, mkAF TA_SB TA_SB 0); (22%nat, mkAF 0 7 0); (23%nat, TA_NOTT); (32%nat, mkAF 8 (2 ^ 47 - 65) 3);
   (34%nat, mkAF 0 336 0)] []
  [(ta_ali1, SOff 32 0); (ta_ali2, SOff 34 0)].
Definition ss_taL : sstate := mkSS 0x5900 ta_srL ta_regL None ta_factsL.
Definition ta_SHL : list shent := [mkSHE 8 0 400; mkSHE 32 40 48].
Definition ta_extraL (t i L mm : Z) : list word := [Z_to_bv 64 (t + 48 * i); Z_to_bv 64 L; Z_to_bv 64 (48 * mm - 48)].
Definition TA_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 20; 21; 23; 24; 25; 26; 27]%bv.

Lemma ta_ble_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z]. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.
Lemma ta_ble_digit : forall (bs : list byte) j, (j < length bs)%nat ->
  (bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat j)) mod 256 = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b bs IH]; intros j Hj; [cbn in Hj; lia|].
rewrite ta_ble_cons. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
destruct j as [|j].
- cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.div_1_r.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- cbn [nth length] in *. replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia.
  rewrite Z.pow_add_r by lia. rewrite <- Z.div_div by (try apply Z.pow_nonzero; lia).
  change (2 ^ 8) with 256.
  replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs).
  + apply IH. lia.
  + rewrite Z.div_add by lia. rewrite (Z.div_small (bv_unsigned b)) by lia. lia.
Qed.
Lemma ta_vm_byte : forall (bs : list byte) j, (j < length bs)%nat ->
  Z_to_bv 8 (YO0f.le_byte (bytes_le_to_Z bs) (length bs) j) = nth j bs (Z_to_bv 8 0).
Proof.
intros bs j Hj. pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as H1.
unfold YO0f.le_byte. rewrite (Z.mod_small (bytes_le_to_Z bs)) by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite ta_ble_digit by exact Hj.
apply Z_to_bv_bv_unsigned.
Qed.
Lemma ta_vm_of_bytes : forall m a (bs : list byte),
  (forall j, (j < length bs)%nat -> mbyte SEGS m (a + Z.of_nat j) = Some (nth j bs (Z_to_bv 8 0))) ->
  val_mem SEGS m a (length bs) (bytes_le_to_Z bs).
Proof. intros m a bs H j Hj. rewrite H by exact Hj. f_equal. symmetry. apply ta_vm_byte. exact Hj. Qed.
Lemma ta_bytes_of_vm : forall m a (bs : list byte),
  val_mem SEGS m a (length bs) (bytes_le_to_Z bs) ->
  forall j, (j < length bs)%nat -> mbyte SEGS m (a + Z.of_nat j) = Some (nth j bs (Z_to_bv 8 0)).
Proof. intros m a bs H j Hj. rewrite (H j Hj). f_equal. apply ta_vm_byte. exact Hj. Qed.
Lemma ta_ga_nth : forall m base (L : list byte),
  garr8 SEGS m base (map (fun b : byte => bv_unsigned b) L) <->
  forall j, (j < length L)%nat -> mbyte SEGS m (base + Z.of_nat j) = Some (nth j L (Z_to_bv 8 0)).
Proof.
intros m base L. split.
- intros HG j Hj. pose proof (garr8_mbyte SEGS m base _ j HG ltac:(rewrite length_map; exact Hj)) as Hm.
  rewrite Hm. f_equal.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite (map_nth (fun b : byte => bv_unsigned b)). apply Z_to_bv_bv_unsigned.
- intros H j Hj. rewrite length_map in Hj.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite (map_nth (fun b : byte => bv_unsigned b)).
  pose proof (bv_unsigned_in_range 8 (nth j L (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256 in Hr.
  split; [|lia]. intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r, H by exact Hj.
  f_equal. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma ta_nth_e : forall (L : list byte) j, (j < length L)%nat -> nth_error L j = Some (nth j L (Z_to_bv 8 0)).
Proof. intros L j Hj. apply nth_error_nth'. exact Hj. Qed.
Lemma ta_vm_of_ga : forall m base (X : list byte) k n,
  garr8 SEGS m base (map (fun b : byte => bv_unsigned b) X) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length X) ->
  val_mem SEGS m (base + k) n (bytes_le_to_Z (disco_table_c.sub X k n)).
Proof.
intros m base X k n HG Hk Hn.
assert (Ls : length (disco_table_c.sub X k n) = n) by (apply disco_table.length_sub; lia).
rewrite <- Ls at 1. apply ta_vm_of_bytes. intros j Hj. rewrite Ls in Hj.
pose proof (proj1 (ta_ga_nth m base X) HG (Z.to_nat k + j)%nat ltac:(lia)) as Hm.
replace (base + k + Z.of_nat j) with (base + Z.of_nat (Z.to_nat k + j)) by lia. rewrite Hm. f_equal.
pose proof (reac_disco_table_age.nth_sub X k n j Hk Hj) as Hs.
rewrite (ta_nth_e _ j) in Hs by lia. rewrite (ta_nth_e X) in Hs by lia. injection Hs as Hs. symmetry. exact Hs.
Qed.
Lemma ta_ga_upd : forall m m' base (X v : list byte) k,
  garr8 SEGS m base (map (fun b : byte => bv_unsigned b) X) -> 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length X) ->
  (forall j, (j < length X)%nat -> ~ (Z.to_nat k <= j < Z.to_nat k + length v)%nat ->
     mbyte SEGS m' (base + Z.of_nat j) = mbyte SEGS m (base + Z.of_nat j)) ->
  (forall j, (j < length v)%nat -> mbyte SEGS m' (base + k + Z.of_nat j) = Some (nth j v (Z_to_bv 8 0))) ->
  garr8 SEGS m' base (map (fun b : byte => bv_unsigned b) (disco_table_c.upd X k v)).
Proof.
intros m m' base X v k HG Hk Hv Hout Hin.
assert (LU : length (disco_table_c.upd X k v) = length X) by (apply reac_disco_table_age.length_upd; lia).
apply ta_ga_nth. intros j Hj. rewrite LU in Hj.
pose proof (reac_disco_table_age.nth_upd X k v j Hk Hv Hj) as Hu.
rewrite (ta_nth_e _ j) in Hu by (rewrite LU; exact Hj).
destruct ((Z.to_nat k <=? j)%nat && (j <? Z.to_nat k + length v)%nat)%bool eqn:Hc.
- apply andb_prop in Hc as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2.
  rewrite (ta_nth_e v (j - Z.to_nat k)) in Hu by lia. injection Hu as Hu. rewrite Hu.
  replace (base + Z.of_nat j) with (base + k + Z.of_nat (j - Z.to_nat k)) by lia. apply Hin. lia.
- rewrite (ta_nth_e X j) in Hu by exact Hj. injection Hu as Hu. rewrite Hu.
  assert (Hn : ~ (Z.to_nat k <= j < Z.to_nat k + length v)%nat).
  { intros [H1 H2]. apply andb_false_iff in Hc as [Hc|Hc]; [apply Nat.leb_gt in Hc | apply Nat.ltb_ge in Hc]; lia. }
  rewrite (Hout j Hj Hn).
  exact (proj1 (ta_ga_nth m base X) HG j Hj).
Qed.

Lemma ta_ga_cnt : forall m m' t (Y : list byte) w, length Y = 400%nat ->
  garr8 SEGS m t (map (fun b : byte => bv_unsigned b) Y) ->
  (forall a, t <= a < t + 400 -> ~ (t + 384 <= a < t + 388) -> mbyte SEGS m' a = mbyte SEGS m a) ->
  val_mem SEGS m' (t + 384) 4 w -> 0 <= w < 2 ^ 32 ->
  garr8 SEGS m' t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd Y 384 (Mem.le4 (Z_to_bv 64 w)))).
Proof.
intros m m' t Y w LY HG Hout VM Hw.
apply (ta_ga_upd m m' t Y (Mem.le4 (Z_to_bv 64 w)) 384 HG); [lia | rewrite Mem.length_le4, LY; lia | |].
- intros j Hj Hn. rewrite LY in Hj. rewrite Mem.length_le4 in Hn. apply Hout; lia.
- intros j Hj. apply (ta_bytes_of_vm m' (t + 384) (Mem.le4 (Z_to_bv 64 w))); [|exact Hj].
  rewrite Mem.length_le4, Mem.bytes_le_to_Z_le4, unsigned_lit_small, Z.mod_small by lia. exact VM.
Qed.
Lemma ta_ga_cpy : forall m m' t (Y : list byte) i j, length Y = 400%nat -> 0 <= i < 8 -> 0 <= j < 8 ->
  garr8 SEGS m t (map (fun b : byte => bv_unsigned b) Y) ->
  (forall a, t <= a < t + 400 -> ~ (t + 48 * i <= a < t + 48 * i + 48) -> mbyte SEGS m' a = mbyte SEGS m a) ->
  (forall c, 0 <= c < 48 -> mbyte SEGS m' (t + 48 * i + c) = mbyte SEGS m (t + 48 * j + c)) ->
  garr8 SEGS m' t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd Y (48 * i) (disco_table_c.entry_of Y j))).
Proof.
intros m m' t Y i j LY Hi Hj HG Hout Hin.
assert (LE : length (disco_table_c.entry_of Y j) = 48%nat) by (unfold disco_table_c.entry_of; apply disco_table.length_sub; rewrite ?LY; lia).
apply (ta_ga_upd m m' t Y (disco_table_c.entry_of Y j) (48 * i) HG); [lia | rewrite LE, LY; lia | |].
- intros k Hk Hn. rewrite LY in Hk. rewrite LE in Hn. apply Hout; lia.
- intros k Hk. rewrite LE in Hk. rewrite Hin by lia.
  replace (t + 48 * j + Z.of_nat k) with (t + Z.of_nat (Z.to_nat (48 * j) + k)) by lia.
  rewrite (proj1 (ta_ga_nth m t Y) HG (Z.to_nat (48 * j) + k)%nat ltac:(lia)). f_equal.
  unfold disco_table_c.entry_of.
  pose proof (reac_disco_table_age.nth_sub Y (48 * j) 48 k ltac:(lia) ltac:(lia)) as Hs.
  rewrite (ta_nth_e _ k) in Hs by (rewrite disco_table.length_sub by (rewrite ?LY; lia); lia).
  rewrite (ta_nth_e Y) in Hs by lia. injection Hs as Hs. symmetry. exact Hs.
Qed.

Lemma ta_mbyte_of_aview2 : forall H H' (m m' : word -> option byte) a b,
  aview SEGS H' m' a = aview SEGS H m b -> mbyte SEGS (mrestrict H' m') a = mbyte SEGS (mrestrict H m) b.
Proof.
intros H H' m m' a b E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H' m') a) as [b'|], (mbyte SEGS (mrestrict H m) b) as [b0|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma ta_den_off : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
intros E n c x Hn Hx Hxc. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SOff n c))). f_equal. change (U E (SOff n c) = x + c).
rewrite U_SOff, Hn, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma ta_U_diff : forall E now L, ew E 9 = Z_to_bv 64 now -> ew E 33 = Z_to_bv 64 L -> 0 <= now < 2 ^ 64 -> 0 <= L < now ->
  U E (SAlu ALU_ADD (SOff 9 0) (SMd M_MUL (SOff 33 0) (SLit (-1)))) = now - L.
Proof.
intros E now L H9 H33 Hn HL. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom E 9 now H9), (U_atom E 33 L H33), U_SLit by lia.
change (zcanon (-1)) with (2 ^ 64 - 1).
unfold zcanon, M64.
replace (L * (2 ^ 64 - 1)) with (- L + L * 2 ^ 64) by ring. rewrite Z_mod_plus_full.
rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.
Lemma ta_mod16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - 96 - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z.div_mod a 16 ltac:(lia)) as Da. pose proof (Z.div_mod b 16 ltac:(lia)) as Db.
rewrite Ha in Da. rewrite Hb in Db. replace (a - 96 - b) with ((a / 16 - 6 - b / 16) * 16) by lia. apply Z.mod_mul. lia.
Qed.
Lemma ta_hull_sub : forall (rd rd' : Z -> option Z) t d n, shadow_hull_vis rd t 400 -> t <= d -> 0 < n -> d + n <= t + 400 ->
  (forall s, shadow_addr t / 8 * 8 <= s < shadow_addr (t + 400 - 1) / 8 * 8 + 8 -> rd' s = rd s) -> shadow_hull_vis rd' d n.
Proof.
intros rd rd' t d n Hh Hd Hn Hdn Hk s Hs.
pose proof (shadow_mono t d Hd) as M1. pose proof (shadow_mono (d + n - 1) (t + 400 - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2).
rewrite Hk by lia. apply Hh. lia.
Qed.
Lemma ta_hull_zone : forall t, 0 <= t -> t + 400 <= 2 ^ 47 - 1 ->
  forall s, shadow_addr t / 8 * 8 <= s < shadow_addr (t + 400 - 1) / 8 * 8 + 8 -> kLowMemEnd <= s < kHighShadowEnd.
Proof.
intros t Ht Htb s Hs. unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *.
pose proof (Z.div_le_mono 0 t 8 ltac:(lia) ltac:(lia)) as D0. change (0 / 8) with 0 in D0.
pose proof (Z.div_le_mono (t + 400 - 1) (2 ^ 47 - 2) 8 ltac:(lia) ltac:(lia)) as D1. change ((2 ^ 47 - 2) / 8) with (2 ^ 44 - 1) in D1.
pose proof (Z.div_le_mono 2147450880 (2147450880 + t / 8) 8 ltac:(lia) ltac:(lia)) as D2. change (2147450880 / 8) with 268431360 in D2.
pose proof (Z.div_le_mono (2147450880 + (t + 400 - 1) / 8) (2 ^ 44 - 1 + 2147450880) 8 ltac:(lia) ltac:(lia)) as D3.
change ((2 ^ 44 - 1 + 2147450880) / 8) with 2199291686911 in D3.
lia.
Qed.

Lemma ta_swrap_small : forall x, 0 <= x < 2 ^ 32 -> 0 <= bv_swrap 32 x -> bv_swrap 32 x = x.
Proof.
intros x Hx H0. unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 32) with (2 ^ 31) in *. change (bv_modulus 32) with (2 ^ 32) in *.
Z.div_mod_to_equations. lia.
Qed.
Lemma ta_n_val : forall T, length T = 400%nat -> disco_table_c.tbl_T1 T ->
  bytes_le_to_Z (disco_table_c.sub T 384 4) = disco_table_c.n_of T.
Proof.
intros T LT T1. unfold disco_table_c.tbl_T1, disco_table_c.n_of, disco_table_c.s32_at, disco_table_c.u_at in *.
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T 384 4)) as H0. pose proof (bytes_le_to_Z_bound (disco_table_c.sub T 384 4)) as H1.
rewrite disco_table.length_sub in H1 by (rewrite ?LT; lia). change (8 * Z.of_nat 4) with 32 in H1.
symmetry. apply ta_swrap_small; lia.
Qed.
Lemma ta_hull_apart : forall lo hi g, lo < hi -> (forall a, lo <= a < hi -> a < YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a) ->
  YImgTop.IMG_LO <= g -> g + 8 <= YImgTop.IMG_TOP -> hi <= g \/ g + 8 <= lo.
Proof.
intros lo hi g Hlh H Hg1 Hg2. destruct (Z.le_gt_cases hi g) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases (g + 8) lo) as [|H2]; [right; lia|]. exfalso.
destruct (H (Z.max lo g) ltac:(lia)); lia.
Qed.
Section w.
Context {fx : YK11.FPState}.
Let RUN := paj_run (PL := PL_both3_0) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (PL := PL_both3_0) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Lemma ta_off_img : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k t,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> amem_range t 400 ->
  (forall a, t <= a < t + 400 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  forall a, t <= a < t + 400 -> a < YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k t HJ Hamr Hwr a Ha.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hwr a Ha))
  as (_ & [[Hc _] | [(_ & b & n & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]).
- right. unfold YImgTop.IMG_TOP. lia.
- pose proof (blk_off_imgP B _ _ _ _ _ b n HAR Hbin) as Ho. unfold off_img in Ho. lia.
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  pose proof (frm_off_imgP B _ _ _ _ _ cid pos HAR Hin') as Ho. unfold off_img in Ho.
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. lia.
- exfalso. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd in *. lia.
Qed.

Lemma ta_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word) t (T : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_TABLE_AGE_STK -> spZ regs <= sp0 ->
  getr regs 10 = w64 t -> 0 < t -> t mod 8 = 0 -> amem_range t 400 ->
  (spZ regs <= t \/ t + 400 <= spZ regs - REAC_DISCO_TABLE_AGE_STK) ->
  (forall a, t <= a < t + 400 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF t 400 ->
  length T = 400%nat -> disco_table_c.tbl_T1 T ->
  garr8 SEGS (mrestrict (w_H W) memc) t (map (fun b : byte => bv_unsigned b) T) ->
  st_ok_pi SEGS (@pa_val _ lib_both3_0_listing PI) (Eimg (Ereg regs (ta_extra (disco_table_c.n_of T) (disco_table_c.seq_of T)))) ss_ta
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_reac_disco_table_age)) memc (seg_rom SEGS))) /\
  sh_ok SEGS TA_Bx ta_SH (Eimg (Ereg regs (ta_extra (disco_table_c.n_of T) (disco_table_c.seq_of T)))) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t T HJ Hal16 Hslo Hshi H10 Ht0 Ht8 Hamr Htsp Hwr Hrad LT T1.
intros HG.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & Hstk0 & Hceil & Hlo0 & Hhi0 & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_DISCO_TABLE_AGE_STK = 4192) by reflexivity.
assert (Ht8b : 8 <= t) by (pose proof (Z.div_mod t 8 ltac:(lia)) as Dt; rewrite Ht8 in Dt; lia).
assert (Htb : t + 400 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
pose proof (proj1 T1) as Hn. pose proof T1 as Hn'. unfold disco_table_c.tbl_T1 in Hn'.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (ta_off_img STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k t HJ Hamr Hwr) as Hoff.
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR, Hoff.
set (E := Eimg (Ereg regs (ta_extra (disco_table_c.n_of T) (disco_table_c.seq_of T)))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ta_extra (disco_table_c.n_of T) (disco_table_c.seq_of T))) n)
  by (intros n Hn0; subst E; apply Eimg_low; exact Hn0).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 TA_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (disco_table_c.n_of T)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn0 Hv. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv. }
assert (VM : val_mem SEGS (mrestrict (w_H W) memc) (t + 384) 4 (disco_table_c.n_of T)).
{ rewrite <- (ta_n_val T LT T1). apply ta_vm_of_ga; [exact HG | lia | rewrite LT; lia]. }
assert (DG : t + 388 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= t + 384)
  by (apply (ta_hull_apart (t + 384) (t + 388)); [lia | intros a Ha; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; apply Hoff; lia | unfold YImgTop.IMG_LO; lia | unfold YImgTop.IMG_TOP; lia]).
assert (DC : t + 388 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= t + 384)
  by (apply (ta_hull_apart (t + 384) (t + 388)); [lia | intros a Ha; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; apply Hoff; lia | unfold YImgTop.IMG_LO; lia | unfold YImgTop.IMG_TOP; lia]).
split.
- rewrite restrict_mkst_fx. unfold ss_ta. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ta_regions, ta_cnt_ro, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E12) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) TA_SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold TA_SB; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * rewrite (VB 10%nat t E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ t 384 4 (SOff 33 0) (disco_table_c.n_of T));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact VM].
  + apply pairwise_disjoint_of_extents. unfold ta_regions, ta_cnt_ro, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat t E10) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [ta_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold TA_SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold TA_SB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, ta_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) memc E TA_Bx 10 t 400 t 0 400 Hrad).
  + unfold U, TA_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold TA_SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

Lemma ta_loop_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) mem md kj (regs : bvmap 5 word) t i mm r L,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kj ->
  (spZ regs + 96) mod 16 = 0 -> sp0 - STK <= spZ regs + 96 - REAC_DISCO_TABLE_AGE_STK -> spZ regs + 96 <= sp0 ->
  8 <= t -> t mod 8 = 0 -> amem_range t 400 ->
  (forall a, t <= a < t + 400 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
  0 <= i < mm -> mm <= 8 -> 0 <= r <= 7 -> 0 <= L < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (t + 384) 4 mm ->
  val_mem SEGS (mrestrict (w_H W) mem) (t + 48 * i + 40) 8 L ->
  getr regs 8 = w64 t -> getr regs 12 = w64 mm -> getr regs 18 = w64 (t + 384) -> getr regs 19 = w64 r ->
  getr regs 20 = w64 TA_SB -> getr regs 21 = w64 (TA_SB + (t + 384) / 8) -> getr regs 22 = w64 i ->
  getr regs 23 = w64 (2 ^ 64 - 1 - t) -> getr regs 24 = w64 8 -> getr regs 25 = w64 5000000000 -> getr regs 26 = w64 3 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (ta_extraL t i L mm))) ss_taL
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x5900)) mem (seg_rom SEGS))) /\
  sh_ok SEGS TA_BxL ta_SHL (Eimg (Ereg regs (ta_extraL t i L mm))) (mrestrict (w_H W) mem).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kj regs t i mm r L HJ Hal16 Hslo Hshi Ht8b Ht8 Hamr Hwr Hrad
  Hi Hmm Hr HL VMc VMl G8 G12 G18 G19 G20 G21 G22 G23 G24 G25 G26.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & Hstk0 & Hceil & Hlo0 & Hhi0 & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_DISCO_TABLE_AGE_STK = 4192) by reflexivity.
assert (Htb : t + 400 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
destruct (al_const _ _ LAWS lyc Sc W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (ta_off_img STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kj t HJ Hamr Hwr) as Hoff.
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR, Hoff.
set (E := Eimg (Ereg regs (ta_extraL t i L mm))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ta_extraL t i L mm)) n)
  by (intros n Hn0; subst E; apply Eimg_low; exact Hn0).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
  by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (apply (EE 2%nat 2%bv); reflexivity).
assert (E8 : ew E 8 = Z_to_bv 64 t) by (rewrite (EE 8%nat 8%bv) by reflexivity; exact G8).
assert (E12 : ew E 12 = Z_to_bv 64 mm) by (rewrite (EE 12%nat 12%bv) by reflexivity; exact G12).
assert (E19 : ew E 19 = Z_to_bv 64 r) by (rewrite (EE 19%nat 19%bv) by reflexivity; exact G19).
assert (E20 : ew E 20 = Z_to_bv 64 TA_SB) by (rewrite (EE 20%nat 20%bv) by reflexivity; exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 i) by (rewrite (EE 22%nat 22%bv) by reflexivity; exact G22).
assert (E23 : ew E 23 = Z_to_bv 64 (2 ^ 64 - 1 - t)) by (rewrite (EE 23%nat 23%bv) by reflexivity; exact G23).
assert (E32 : ew E 32 = Z_to_bv 64 (t + 48 * i)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 L) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (48 * mm - 48)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hsp16 : spZ regs mod 16 = 0).
{ pose proof (Z.div_mod (spZ regs + 96) 16 ltac:(lia)) as D. rewrite Hal16 in D. replace (spZ regs) with (((spZ regs + 96) / 16 - 6) * 16) by lia. apply Z.mod_mul. lia. }
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn0 Hv. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv. }
assert (DG : forall lo hi, t <= lo -> lo < hi -> hi <= t + 400 -> (hi <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= lo) /\ (hi <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= lo)).
{ intros lo hi H1 H2 H3. split; apply (ta_hull_apart lo hi); unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; try lia; intros a Ha; apply Hoff; lia. }
destruct (DG (t + 384) (t + 388) ltac:(lia) ltac:(lia) ltac:(lia)) as [DGc DCc].
destruct (DG (t + 48 * i + 40) (t + 48 * i + 48) ltac:(lia) ltac:(lia) ltac:(lia)) as [DGe DCe].
split.
- rewrite restrict_mkst_fx. unfold ss_taL. apply pa_entry_st_ok_full.
  + unfold ta_srL.
    apply YI04.regs_ok_pin; [|intros X; discriminate X|cbn [sv_denot]; rewrite G26; reflexivity].
    apply YI04.regs_ok_pin; [|intros X; discriminate X|cbn [sv_denot]; rewrite G25; reflexivity].
    apply YI04.regs_ok_pin; [|intros X; discriminate X|cbn [sv_denot]; rewrite G24; reflexivity].
    apply YI04.regs_ok_pin; [|intros X; discriminate X|].
    2: { rewrite G21. unfold ta_shx. rewrite (denot_shx E 8 20 384 t TA_SB E8 E20) by (unfold TA_SB; lia). try (unfold w64; f_equal; lia). }
    apply YI04.regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. rewrite G18, E8. rewrite unsigned_lit_small by lia. reflexivity.
  + vm_compute. reflexivity.
  + unfold ta_regL, ta_cntL, ta_entL, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 20 0) TA_SB);
      [cbn [sv_denot]; rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold TA_SB; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 8%nat t E8) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (t + o) HJ (Hwr (t + o) ltac:(lia))))|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ t 384 4 (SOff 12 0) mm);
      [cbn [sv_denot]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact VMc].
    * rewrite (VB 32%nat (t + 48 * i) E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (t + 48 * i) 40 8 (SOff 33 0) L);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact HL | lia | exact VMl].
  + apply pairwise_disjoint_of_extents. unfold ta_regL, ta_cntL, ta_entL, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 8%nat t E8) by lia. rewrite (VB 32%nat (t + 48 * i) E32) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia.
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [ta_factsL f_atoms atoms_ok]. unfold afact_ok, TA_NOTT. cbn [af_lo af_hi af_al2].
      rewrite Usp, E8, E12, E19, E20, E22, E23, E32, E34, !unsigned_lit_small by (unfold TA_SB; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      assert (H48 : (t + 48 * i) mod 8 = 0).
      { replace (t + 48 * i) with ((t / 8 + 6 * i) * 8) by (pose proof (Z.div_mod t 8 ltac:(lia)); lia). apply Z.mod_mul. lia. }
      unfold TA_SB. repeat match goal with |- _ /\ _ => split end; first [exact Hsp16 | exact Ht8 | exact H48 | lia].
    * cbn [ta_factsL f_alias alias_ok]. unfold ta_ali1, ta_ali2. split; [|split; [|exact I]].
      -- apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
         rewrite (U_atom _ 8 t E8), (U_atom _ 22 i E22), (U_atom _ 32 _ E32), U_SLit by lia.
         change (zcanon 48) with 48. rewrite (zcanon_id (i * 48)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
      -- apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
         rewrite (U_atom _ 12 mm E12), (U_atom _ 34 _ E34), !U_SLit by lia.
         change (zcanon 48) with 48. rewrite (zcanon_id (mm * 48)) by (unfold M64; lia).
         unfold zcanon, M64. Z.div_mod_to_equations. lia.
- unfold sh_ok, ta_SHL. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E TA_BxL 8 t 400 t 0 400 Hrad).
    * unfold U, TA_BxL. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold TA_SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E TA_BxL 32 t 400 (t + 48 * i) 40 48 Hrad).
    * unfold U, TA_BxL. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold TA_SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

Lemma ta_br_ge : forall E n m x y c d, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y ->
  0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> 0 <= x + c < 128 -> 0 <= y + d < 128 ->
  branch_taken BC_GE (sv_denot E (SOff n c)) (sv_denot E (SOff m d)) = negb (x + c <? y + d).
Proof.
intros E n m x y c d Hn Hm Hx Hy Hxc Hyd. cbn [branch_taken].
assert (D1 : sv_denot E (SOff n c) = Z_to_bv 64 (x + c)).
{ rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SOff n c))). f_equal. change (U E (SOff n c) = x + c).
  rewrite U_SOff, Hn, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (D2 : sv_denot E (SOff m d) = Z_to_bv 64 (y + d)).
{ rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SOff m d))). f_equal. change (U E (SOff m d) = y + d).
  rewrite U_SOff, Hm, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
rewrite D1, D2, bv_lts_small by lia. reflexivity.
Qed.
Lemma ta_cnt_val : forall E (H : word -> bool) m t v e,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 e)]) ->
  ew E 8 = Z_to_bv 64 t -> 0 <= t < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  val_mem SEGS (mrestrict H m) (t + 384) 4 v.
Proof.
intros E H m t v e R E8 Ht He Hv.
exact (field_of_region E (mrestrict H m) 8 t _ 384 388 384 388 384 4 e v R ltac:(rewrite E8; apply unsigned_lit_small; lia)
  ltac:(left; reflexivity) He ltac:(lia) ltac:(lia)).
Qed.

Lemma ta_kw_lemma : forall Ex rs H (m m' : word -> option byte) t,
  frame_of Ex rs (mrestrict H m) (mrestrict H m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi -> t + 384 <= a < t + 388) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros Ex rs H m m' t HFx Hw a Ha Hn. exact (kept_of_frame Ex rs H m m' (fun a => t + 384 <= a < t + 388) HFx Hw a Ha Hn). Qed.
Ltac ta_kw E8 HFx K :=
  lazymatch type of HFx with frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
  lazymatch type of E8 with ew _ 8 = Z_to_bv 64 ?t =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS H m' a = aview SEGS H m a);
  [ apply (ta_kw_lemma Ex rs H m m' t HFx);
    let w := eval vm_compute in (windows rs) in change (windows rs) with w;
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Ha := fresh "Ha" in
    intros b wlo whi a Hin Ha; cbn [In] in Hin;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [base_val] in Ha; first [lia | rewrite E8, unsigned_lit_small in Ha by lia; lia] |]);
    destruct Hin
  | ] end end.
Ltac ta_awr E8 Hwr :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | lazymatch type of E8 with ew _ 8 = Z_to_bv 64 ?t =>
      eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8 t);
      [reflexivity | rewrite E8; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hwr; lia | ] end ].
Ltac ta_reg HS r e H :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
  pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
  change (sr_get (ss_regs ss) r) with e in H; cbn [ms_regs restrict mkst] in H end.

Ltac ta_regS HS r e H :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
  pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
  change (sr_get (ss_regs ss) r) with e in H; cbn [ms_regs restrict mkst] in H end.
Ltac ta_kept HKf R18 R21 R24 R25 R26 E8x E20x G18 G21 G24 G25 G26 :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in intros rr Hrr; cbv [TA_KEPT In] in Hrr;
  repeat (destruct Hrr as [<-|Hrr]; [ first [ apply HKf; cbv; tauto
     | rewrite R18, G18; apply (ta_den_off _ 8 384 _ E8x); lia
     | rewrite R21, G21; unfold ta_shx; rewrite (denot_shx _ 8 20 384 _ TA_SB E8x E20x) by (unfold TA_SB; lia); reflexivity
     | rewrite R24, G24; reflexivity | rewrite R25, G25; reflexivity | rewrite R26, G26; reflexivity ] | ]); destruct Hrr.

Lemma ta_cpy_same_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 d -> getr regsT 11 = w64 d -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
  amem_range d n ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d n ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) d n) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA AS___asan_memcpy)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n o raw
  HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok SEGS B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
  destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
  split; [apply apresent_writable; exact Hp | auto]. }
assert (HSRC : 0 <= d /\ d + n <= 2 ^ 63 /\ src_ok SEGS W regsT memT d n /\ d = d /\ amem_range d n /\
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d n /\ (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) d n)).
{ split; [lia|]. split; [lia|]. split.
  - intros a Ha. destruct (Hdest a Ha) as [Hw Hns]. split.
    + apply (aview_some_of_apresent SEGS). exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw)).
    + rewrite Hsp'. exact Hns.
  - split; [reflexivity|]. split; [exact Hamr|]. split; [exact Hra_d | exact Hhull]. }
eapply SRr_mono.
{ exact (AMEMCPYEQ fx lyc Sc W regsT memT mdc d d n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull HSRC). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
assert (Hall : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a).
{ intros a Ha Hw. destruct (Z_lt_le_dec a d) as [H1|H1]; [apply Hfr; lia|].
  destruct (Z_lt_le_dec a (d + n)) as [H2|H2]; [|apply Hfr; lia].
  replace a with (d + (a - d)) by lia. apply Heff. lia. }
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS Hsegs STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply Hall; assumption.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha. left. left. lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hall | exact Hpres2].
Qed.

Lemma ta_denot_add2 : forall E n m x y, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = Z_to_bv 64 (x + y).
Proof.
intros E n m x y Hn Hm Hx Hy Hxy.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)))). f_equal.
change (U E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = x + y). rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n x Hn), (U_atom E m y Hm) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma ta_loop : forall (kf : nat) (A : list byte) (i mm r : Z) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memB mem md kj
    (regs : bvmap 5 word) spE t now (T : list byte),
  length T = 400%nat -> disco_table_c.table_ok T ->
  Z.of_nat kf = mm - i -> 0 <= i < mm -> reac_disco_table_age.age_inv T now A i mm r ->
  reac_disco_table_age_c.age_loop kf A now i mm r =
    reac_disco_table_age_c.age_loop (Z.to_nat (disco_table_c.n_of T)) T now 0 (disco_table_c.n_of T) 0 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kj ->
  spE mod 16 = 0 -> sp0 - STK <= spE - REAC_DISCO_TABLE_AGE_STK -> spE <= sp0 ->
  8 <= t -> t mod 8 = 0 -> amem_range t 400 -> (spE <= t \/ t + 400 <= spE - REAC_DISCO_TABLE_AGE_STK) ->
  (forall a, t <= a < t + 400 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  range_addressable (aview SEGS (w_H W) memB) SHADOW_OFF t 400 -> shadow_hull_vis (aview SEGS (w_H W) memB) t 400 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spE - REAC_DISCO_TABLE_AGE_STK <= a < spE - 96) -> ~ (t <= a < t + 400) ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H W) memB a) ->
  (forall a, apresent (w_H W) memB a -> apresent (w_H W) mem a) ->
  garr8 SEGS (mrestrict (w_H W) mem) t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd A 384 (Mem.le4 (Z_to_bv 64 mm)))) ->
  0 <= now < 2 ^ 64 ->
  spZ regs = spE - 96 -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = w64 t -> getr regs 9 = w64 now -> getr regs 12 = w64 mm -> getr regs 18 = w64 (t + 384) -> getr regs 19 = w64 r ->
  getr regs 20 = w64 TA_SB -> getr regs 21 = w64 (TA_SB + (t + 384) / 8) -> getr regs 22 = w64 i ->
  getr regs 23 = w64 (2 ^ 64 - 1 - t) -> getr regs 24 = w64 8 -> getr regs 25 = w64 5000000000 -> getr regs 26 = w64 3 ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x5900)) mem (seg_rom SEGS)) md)
    (fun W' c' => W' = W /\ exists regs' mem' md' A' m' r',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x59cc)) mem' (seg_rom SEGS)) md' /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' kj /\
       (forall rr, In rr TA_KEPT -> getr regs' rr = getr regs rr) /\ getr regs' 19 = w64 r' /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spE - REAC_DISCO_TABLE_AGE_STK <= a < spE - 96) -> ~ (t <= a < t + 400) ->
          aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memB a) /\
       (forall a, apresent (w_H W) memB a -> apresent (w_H W) mem' a) /\
       garr8 SEGS (mrestrict (w_H W) mem') t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd A' 384 (Mem.le4 (Z_to_bv 64 m')))) /\
       reac_disco_table_age.age_inv T now A' m' m' r' /\
       reac_disco_table_age_c.age_loop (Z.to_nat (disco_table_c.n_of T)) T now 0 (disco_table_c.n_of T) 0 = (A', m', r')).
Proof.
induction kf as [|kf IH];
intros A i mm r STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memB mem md kj regs spE t now T
  LT TOK Hk Hi HI RES HJ Hal16 Hslo Hshi Ht8b Ht8 Hamr Htsp Hwr HradB HhullB HFB HPB HGA Hnow
  Gsp G3 G4 G8 G9 G12 G18 G19 G20 G21 G22 G23 G24 G25 G26; [lia|].
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_DISCO_TABLE_AGE_STK = 4192) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Htb : t + 400 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
pose proof TOK as (T1 & _). pose proof T1 as T1'. unfold disco_table_c.tbl_T1 in T1'.
pose proof HI as (LA & Hii & Hmm & Hr & _).
set (X := disco_table_c.upd A 384 (Mem.le4 (Z_to_bv 64 mm))) in *.
assert (LX : length X = 400%nat) by (unfold X; rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LA; lia).
set (L := disco_table_c.last_of X i).
pose proof (reac_disco_table_age.last_range X i LX ltac:(lia)) as HL.
assert (VMc : val_mem SEGS (mrestrict (w_H W) mem) (t + 384) 4 mm).
{ pose proof (ta_vm_of_ga _ _ X 384 4 HGA ltac:(lia) ltac:(rewrite LX; lia)) as V.
  replace (disco_table_c.sub X 384 4) with (Mem.le4 (Z_to_bv 64 mm)) in V.
  - rewrite Mem.bytes_le_to_Z_le4, unsigned_lit_small, Z.mod_small in V by lia. exact V.
  - replace (disco_table_c.sub X 384 4) with (disco_table_c.sub X 384 (length (Mem.le4 (Z_to_bv 64 mm)))) by (rewrite Mem.length_le4; reflexivity).
    unfold X. symmetry. apply reac_disco_table_age.sub_upd_in; rewrite ?Mem.length_le4, ?LA; lia. }
assert (VMl : val_mem SEGS (mrestrict (w_H W) mem) (t + 48 * i + 40) 8 L).
{ unfold L, disco_table_c.last_of, disco_table_c.u_at. replace (t + 48 * i + 40) with (t + (48 * i + 40)) by lia.
  apply ta_vm_of_ga; [exact HGA | lia | rewrite LX; lia]. }
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & Hstk0 & Hceil & Hlo0 & Hhi0 & H47 & Hbot & Htop & Htop2).
assert (SHM : forall x, t <= x < t + 400 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\
   ~ (spE - REAC_DISCO_TABLE_AGE_STK <= shadow_of_addr SHADOW_OFF x < spE - 96) /\ ~ (t <= shadow_of_addr SHADOW_OFF x < t + 400)).
{ intros x Hx. unfold shadow_of_addr, SHADOW_OFF, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
  pose proof (Z.div_le_mono 0 x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono x (2 ^ 47 - 1) 8 ltac:(lia) ltac:(lia)).
  change ((2 ^ 47 - 1) / 8) with (2 ^ 44 - 1) in *. change (0 / 8) with 0 in *. lia. }

pose proof (ta_off_img STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kj t HJ Hamr Hwr) as Hoff.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_val_range (A_OBJ 0)) as RV0. pose proof (pa_val_range (A_OBJ 12)) as RV12.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR, Hoff.
assert (DGt : t + 400 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= t)
  by (apply (ta_hull_apart t (t + 400)); unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; try lia; intros a Ha; apply Hoff; lia).
assert (DCt : t + 400 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= t)
  by (apply (ta_hull_apart t (t + 400)); unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; try lia; intros a Ha; apply Hoff; lia).
assert (Hrad : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400).
{ apply (range_addressable_agree (aview SEGS (w_H W) memB)); [|exact HradB].
  intros x Hx. destruct (SHM x Hx) as (S1 & S2 & S3). apply HFB; assumption. }
destruct (ta_loop_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kj regs t i mm r L HJ
  ltac:(rewrite Gsp; replace (spE - 96 + 96) with spE by lia; exact Hal16) ltac:(rewrite Gsp; lia) ltac:(rewrite Gsp; lia)
  Ht8b Ht8 Hamr Hwr Hrad ltac:(lia) ltac:(lia) ltac:(lia) HL VMc VMl G8 G12 G18 G19 G20 G21 G22 G23 G24 G25 G26) as [HS SHOK].
remember (Eimg (Ereg regs (ta_extraL t i L mm))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (ta_extraL t i L mm)) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E8 : ew E 8 = Z_to_bv 64 t) by (rewrite (EE 8%nat 8%bv) by reflexivity; exact G8).
assert (E9 : ew E 9 = Z_to_bv 64 now) by (rewrite (EE 9%nat 9%bv) by reflexivity; exact G9).
assert (E12 : ew E 12 = Z_to_bv 64 mm) by (rewrite (EE 12%nat 12%bv) by reflexivity; exact G12).
assert (E19 : ew E 19 = Z_to_bv 64 r) by (rewrite (EE 19%nat 19%bv) by reflexivity; exact G19).
assert (E20 : ew E 20 = Z_to_bv 64 TA_SB) by (rewrite (EE 20%nat 20%bv) by reflexivity; exact G20).
assert (E22 : ew E 22 = Z_to_bv 64 i) by (rewrite (EE 22%nat 22%bv) by reflexivity; exact G22).
assert (E32 : ew E 32 = Z_to_bv 64 (t + 48 * i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 L) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (48 * mm - 48)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).

assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E2 : ew E 2 = getr regs 2) by (apply (EE 2%nat 2%bv); reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spE - 96) by (rewrite E2; exact Gsp).
clear HE.
paj_run_tok RUN HS HJ SHOK TA_Bspan.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 8 t); [reflexivity | rewrite E8; apply unsigned_lit_small; lia | |].
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply Hwr. lia.
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }

rename HF into HF1, HFr into HFr1, HG into HG1.
ta_kw E8 HFr1 K1.
assert (MG1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a) by (intros a Ha; exact (apresent_grows _ _ _ a HG1 Ha)).
assert (SX : disco_table_c.entry_of X i = disco_table_c.entry_of A i)
  by (unfold X; apply reac_disco_table_age.entry_upd_hi; rewrite ?Mem.length_le4; lia).
assert (SXs : reac_disco_table_age_c.disco_stale X i now = reac_disco_table_age_c.disco_stale A i now)
  by (apply reac_disco_table_age.stale_ent; [exact LX | exact LA | lia | lia | exact SX]).
psrr_branch_tok RUN BR HS SHOK TA_Bspan.
{ rewrite branch_geu_U, (U_atom E 33 L E33), (U_atom E 9 now E9) in Hc by lia.
  assert (NS : reac_disco_table_age_c.disco_stale A i now = false).
  { rewrite <- SXs. unfold reac_disco_table_age_c.disco_stale. change (disco_table_c.last_of X i) with L.
    destruct (Z.ltb_spec L now); [discriminate Hc | reflexivity]. }
  clear Hc.
paj_run_tok RUN HS HJ SHOK TA_Bspan; [ta_awr E8 Hwr|].
rename HF into HFa1, HFr into HFra1, HG into HGa1.
ta_kw E8 HFra1 Ka1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) =>
assert (MKa1 : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS (w_H W) (ms_mem mc) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hn; rewrite Ka1 by assumption; apply K1; assumption);
assert (MGa1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem mc) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGa1 (MG1 a Ha))) end.
psrr_branch_tok RUN BR HS SHOK TA_Bspan.
{ rewrite (ta_br_ge E 22 12 i mm 1 0 E22 E12) in Hc by lia.
  assert (Hx : i + 1 = mm) by (destruct (Z.ltb_spec (i + 1) (mm + 0)); [discriminate Hc | lia]).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TA_Bspan 0x59cc; [ta_awr E8 Hwr|].

rename HF into HFx1, HFr into HFrx1, HG into HGx1.
ta_kw E8 HFrx1 Kx1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msFx1 end.
assert (MKfx1 : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS (w_H W) (ms_mem msFx1) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hn; rewrite Kx1 by assumption; first [reflexivity | apply MKa1; assumption]).
assert (MGfx1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem msFx1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGx1 (MGa1 a Ha))).
assert (VMfx1 : val_mem SEGS (mrestrict (w_H W) (ms_mem msFx1)) (t + 384) 4 (mm)).
{ apply (ta_cnt_val E (w_H W) (ms_mem msFx1) t (mm) (SOff 12 (0))); [ | exact E8 | lia | rewrite (ta_den_off E 12 (0) mm E12) by lia; f_equal; lia | lia].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
  exact (st_ok_pi_region_nth E ssf _ 2 (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 12 (0)))]) HS ltac:(vm_compute; reflexivity)) end. }
assert (GAfx1 : garr8 SEGS (mrestrict (w_H W) (ms_mem msFx1)) t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd A 384 (Mem.le4 (Z_to_bv 64 (mm)))))).
{ assert (LAb : length A = 400%nat) by (rewrite ?reac_disco_table_age.length_upd; unfold disco_table_c.entry_of; rewrite ?disco_table.length_sub; rewrite ?LA; lia).
  pose proof (ta_ga_cnt _ _ t (disco_table_c.upd A 384 (Mem.le4 (Z_to_bv 64 (mm)))) (mm) ltac:(rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LAb; lia) HGA
    ltac:(intros a Ha Hn; apply (mbyte_of_aview SEGS); apply MKfx1; lia) VMfx1 ltac:(lia)) as G.
  rewrite reac_disco_table_age.upd_upd in G by (rewrite ?Mem.length_le4, ?LAb; lia). exact G. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
pose proof (regs_kept_of_st_ok_pi E ssf _ regs (ta_extraL t i L mm) [2; 3; 4; 8; 9; 20; 23; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as HKfx1 end.
cbn [ms_regs restrict] in HKfx1.
ta_reg HS (18%bv : bv 5) (SOff 8 384) R18_x1. ta_reg HS (21%bv : bv 5) ta_shx R21_x1. ta_reg HS (24%bv : bv 5) (SLit 8) R24_x1.
ta_reg HS (25%bv : bv 5) (SLit 5000000000) R25_x1. ta_reg HS (26%bv : bv 5) (SLit 3) R26_x1.
ta_reg HS (19%bv : bv 5) (SOff 19 (0)) R19_x1. ta_reg HS (12%bv : bv 5) (SOff 12 (0)) R12_x1. ta_reg HS (22%bv : bv 5) (SOff 22 (1)) R22_x1.
rewrite (ta_den_off E 19 (0) r E19) in R19_x1 by lia.
rewrite (ta_den_off E 12 (0) mm E12) in R12_x1 by lia.
rewrite (ta_den_off E 22 (1) i E22) in R22_x1 by lia.
assert (KEfx1 : forall rr, In rr TA_KEPT -> getr (ms_regs msFx1) rr = getr regs rr)
  by (ta_kept HKfx1 R18_x1 R21_x1 R24_x1 R25_x1 R26_x1 E8 E20 G18 G21 G24 G25 G26).
assert (FBfx1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spE - REAC_DISCO_TABLE_AGE_STK <= a < spE - 96) -> ~ (t <= a < t + 400) ->
  aview SEGS (w_H W) (ms_mem msFx1) a = aview SEGS (w_H W) memB a)
  by (intros a Ha Hw Ht; rewrite MKfx1 by lia; apply HFB; assumption).
assert (PBfx1 : forall a, apresent (w_H W) memB a -> apresent (w_H W) (ms_mem msFx1) a)
  by (intros a Ha; apply MGfx1; apply HPB; exact Ha).
pmkst HS.
apply SRr_ret. split; [reflexivity|].
exists (ms_regs msFx1), (ms_mem msFx1). eexists. exists (A), (mm), (r).
split; [reflexivity|]. split; [exact HJ|]. split; [exact KEfx1|].
split; [rewrite R19_x1; unfold w64; f_equal; lia|]. split; [exact FBfx1|]. split; [exact PBfx1|].
split; [exact GAfx1|]. split; [pose proof (reac_disco_table_age.age_inv_keep T now A i mm r HI ltac:(lia) NS) as HI2; rewrite Hx in HI2; exact HI2 | rewrite <- RES, reac_disco_table_age.age_loop_keep by (assumption || lia); apply reac_disco_table_age.age_loop_end; lia].
}
{ rewrite (ta_br_ge E 22 12 i mm 1 0 E22 E12) in Hc by lia.
  assert (Hx : i + 1 < mm) by (destruct (Z.ltb_spec (i + 1) (mm + 0)); [lia | discriminate Hc]).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TA_Bspan 0x5900; [ta_awr E8 Hwr|].

rename HF into HFc1, HFr into HFrc1, HG into HGc1.
ta_kw E8 HFrc1 Kc1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msFc1 end.
assert (MKfc1 : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS (w_H W) (ms_mem msFc1) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hn; rewrite Kc1 by assumption; first [reflexivity | apply MKa1; assumption]).
assert (MGfc1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem msFc1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGc1 (MGa1 a Ha))).
assert (VMfc1 : val_mem SEGS (mrestrict (w_H W) (ms_mem msFc1)) (t + 384) 4 (mm)).
{ apply (ta_cnt_val E (w_H W) (ms_mem msFc1) t (mm) (SOff 12 (0))); [ | exact E8 | lia | rewrite (ta_den_off E 12 (0) mm E12) by lia; f_equal; lia | lia].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
  exact (st_ok_pi_region_nth E ssf _ 2 (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 12 (0)))]) HS ltac:(vm_compute; reflexivity)) end. }
assert (GAfc1 : garr8 SEGS (mrestrict (w_H W) (ms_mem msFc1)) t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd A 384 (Mem.le4 (Z_to_bv 64 (mm)))))).
{ assert (LAb : length A = 400%nat) by (rewrite ?reac_disco_table_age.length_upd; unfold disco_table_c.entry_of; rewrite ?disco_table.length_sub; rewrite ?LA; lia).
  pose proof (ta_ga_cnt _ _ t (disco_table_c.upd A 384 (Mem.le4 (Z_to_bv 64 (mm)))) (mm) ltac:(rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LAb; lia) HGA
    ltac:(intros a Ha Hn; apply (mbyte_of_aview SEGS); apply MKfc1; lia) VMfc1 ltac:(lia)) as G.
  rewrite reac_disco_table_age.upd_upd in G by (rewrite ?Mem.length_le4, ?LAb; lia). exact G. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
pose proof (regs_kept_of_st_ok_pi E ssf _ regs (ta_extraL t i L mm) [2; 3; 4; 8; 9; 20; 23; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as HKfc1 end.
cbn [ms_regs restrict] in HKfc1.
ta_reg HS (18%bv : bv 5) (SOff 8 384) R18_c1. ta_reg HS (21%bv : bv 5) ta_shx R21_c1. ta_reg HS (24%bv : bv 5) (SLit 8) R24_c1.
ta_reg HS (25%bv : bv 5) (SLit 5000000000) R25_c1. ta_reg HS (26%bv : bv 5) (SLit 3) R26_c1.
ta_reg HS (19%bv : bv 5) (SOff 19 (0)) R19_c1. ta_reg HS (12%bv : bv 5) (SOff 12 (0)) R12_c1. ta_reg HS (22%bv : bv 5) (SOff 22 (1)) R22_c1.
rewrite (ta_den_off E 19 (0) r E19) in R19_c1 by lia.
rewrite (ta_den_off E 12 (0) mm E12) in R12_c1 by lia.
rewrite (ta_den_off E 22 (1) i E22) in R22_c1 by lia.
assert (KEfc1 : forall rr, In rr TA_KEPT -> getr (ms_regs msFc1) rr = getr regs rr)
  by (ta_kept HKfc1 R18_c1 R21_c1 R24_c1 R25_c1 R26_c1 E8 E20 G18 G21 G24 G25 G26).
assert (FBfc1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spE - REAC_DISCO_TABLE_AGE_STK <= a < spE - 96) -> ~ (t <= a < t + 400) ->
  aview SEGS (w_H W) (ms_mem msFc1) a = aview SEGS (w_H W) memB a)
  by (intros a Ha Hw Ht; rewrite MKfc1 by lia; apply HFB; assumption).
assert (PBfc1 : forall a, apresent (w_H W) memB a -> apresent (w_H W) (ms_mem msFc1) a)
  by (intros a Ha; apply MGfc1; apply HPB; exact Ha).
pmkst HS.
eapply SRr_mono.
{ eapply (IH (A) (i + 1) (mm) (r) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memB (ms_mem msFc1) _ kj (ms_regs msFc1) spE t now T LT TOK);
  [ lia | lia | exact (reac_disco_table_age.age_inv_keep T now A i mm r HI ltac:(lia) NS) | rewrite <- RES; symmetry; apply reac_disco_table_age.age_loop_keep; [lia | exact NS] | exact HJ | exact Hal16 | exact Hslo | exact Hshi | exact Ht8b | exact Ht8 | exact Hamr | exact Htsp | exact Hwr
  | exact HradB | exact HhullB | exact FBfc1 | exact PBfc1 | exact GAfc1 | exact Hnow
  | unfold spZ; rewrite (KEfc1 2%bv ltac:(cbv; tauto)); exact Gsp
  | rewrite (KEfc1 3%bv ltac:(cbv; tauto)); exact G3 | rewrite (KEfc1 4%bv ltac:(cbv; tauto)); exact G4
  | rewrite (KEfc1 8%bv ltac:(cbv; tauto)); exact G8 | rewrite (KEfc1 9%bv ltac:(cbv; tauto)); exact G9
  | rewrite R12_c1; unfold w64; f_equal; lia
  | rewrite (KEfc1 18%bv ltac:(cbv; tauto)); exact G18
  | rewrite R19_c1; unfold w64; f_equal; lia
  | rewrite (KEfc1 20%bv ltac:(cbv; tauto)); exact G20 | rewrite (KEfc1 21%bv ltac:(cbv; tauto)); exact G21
  | rewrite R22_c1; unfold w64; f_equal; lia
  | rewrite (KEfc1 23%bv ltac:(cbv; tauto)); exact G23 | rewrite (KEfc1 24%bv ltac:(cbv; tauto)); exact G24
  | rewrite (KEfc1 25%bv ltac:(cbv; tauto)); exact G25 | rewrite (KEfc1 26%bv ltac:(cbv; tauto)); exact G26 ]. }
cbv beta. intros Wq cq _ (-> & regsq & memq & mdq & Aq & mq & rq & -> & HJq & HKq & H19q & HFq & HPq & HGq & HIq & HRq).
split; [reflexivity|]. exists regsq, memq, mdq, Aq, mq, rq. split; [reflexivity|]. split; [exact HJq|].
split; [intros rr Hrr; rewrite (HKq rr Hrr); exact (KEfc1 rr Hrr)|].
split; [exact H19q|]. split; [exact HFq|]. split; [exact HPq|]. split; [exact HGq|]. split; [exact HIq | exact HRq].
}
}
{ rewrite branch_geu_U, (U_atom E 33 L E33), (U_atom E 9 now E9) in Hc by lia.
  assert (HLn : L < now) by (destruct (Z.ltb_spec L now); [lia | discriminate Hc]).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK TA_Bspan; [ta_awr E8 Hwr|].
  rename HF into HF2, HFr into HFr2, HG into HG2.
  ta_kw E8 HFr2 K2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) =>
  assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS (w_H W) (ms_mem mc) a = aview SEGS (w_H W) mem a)
    by (intros a Ha Hn; rewrite K2 by assumption; apply K1; assumption);
  assert (MG12 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem mc) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG2 (MG1 a Ha))) end.
  psrr_branch_tok RUN BR HS SHOK TA_Bspan.
  { rewrite branch_geu_U, U_lit, (ta_U_diff E now L E9 E33) in Hc by lia.
    assert (NS : reac_disco_table_age_c.disco_stale A i now = false).
    { rewrite <- SXs. unfold reac_disco_table_age_c.disco_stale, reac_disco_table_age_c.REAC_DISCO_STALE_NS.
      change (disco_table_c.last_of X i) with L.
      destruct (Z.ltb_spec 5000000000 (now - L)); [discriminate Hc | apply andb_false_r]. }
    clear Hc.
paj_run_tok RUN HS HJ SHOK TA_Bspan; [ta_awr E8 Hwr|].
rename HF into HFa2, HFr into HFra2, HG into HGa2.
ta_kw E8 HFra2 Ka2.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) =>
assert (MKa2 : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS (w_H W) (ms_mem mc) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hn; rewrite Ka2 by assumption; apply K12; assumption);
assert (MGa2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem mc) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGa2 (MG12 a Ha))) end.
psrr_branch_tok RUN BR HS SHOK TA_Bspan.
{ rewrite (ta_br_ge E 22 12 i mm 1 0 E22 E12) in Hc by lia.
  assert (Hx : i + 1 = mm) by (destruct (Z.ltb_spec (i + 1) (mm + 0)); [discriminate Hc | lia]).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TA_Bspan 0x59cc; [ta_awr E8 Hwr|].

rename HF into HFx2, HFr into HFrx2, HG into HGx2.
ta_kw E8 HFrx2 Kx2.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msFx2 end.
assert (MKfx2 : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS (w_H W) (ms_mem msFx2) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hn; rewrite Kx2 by assumption; first [reflexivity | apply MKa2; assumption]).
assert (MGfx2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem msFx2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGx2 (MGa2 a Ha))).
assert (VMfx2 : val_mem SEGS (mrestrict (w_H W) (ms_mem msFx2)) (t + 384) 4 (mm)).
{ apply (ta_cnt_val E (w_H W) (ms_mem msFx2) t (mm) (SOff 12 (0))); [ | exact E8 | lia | rewrite (ta_den_off E 12 (0) mm E12) by lia; f_equal; lia | lia].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
  exact (st_ok_pi_region_nth E ssf _ 2 (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 12 (0)))]) HS ltac:(vm_compute; reflexivity)) end. }
assert (GAfx2 : garr8 SEGS (mrestrict (w_H W) (ms_mem msFx2)) t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd A 384 (Mem.le4 (Z_to_bv 64 (mm)))))).
{ assert (LAb : length A = 400%nat) by (rewrite ?reac_disco_table_age.length_upd; unfold disco_table_c.entry_of; rewrite ?disco_table.length_sub; rewrite ?LA; lia).
  pose proof (ta_ga_cnt _ _ t (disco_table_c.upd A 384 (Mem.le4 (Z_to_bv 64 (mm)))) (mm) ltac:(rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LAb; lia) HGA
    ltac:(intros a Ha Hn; apply (mbyte_of_aview SEGS); apply MKfx2; lia) VMfx2 ltac:(lia)) as G.
  rewrite reac_disco_table_age.upd_upd in G by (rewrite ?Mem.length_le4, ?LAb; lia). exact G. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
pose proof (regs_kept_of_st_ok_pi E ssf _ regs (ta_extraL t i L mm) [2; 3; 4; 8; 9; 20; 23; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as HKfx2 end.
cbn [ms_regs restrict] in HKfx2.
ta_reg HS (18%bv : bv 5) (SOff 8 384) R18_x2. ta_reg HS (21%bv : bv 5) ta_shx R21_x2. ta_reg HS (24%bv : bv 5) (SLit 8) R24_x2.
ta_reg HS (25%bv : bv 5) (SLit 5000000000) R25_x2. ta_reg HS (26%bv : bv 5) (SLit 3) R26_x2.
ta_reg HS (19%bv : bv 5) (SOff 19 (0)) R19_x2. ta_reg HS (12%bv : bv 5) (SOff 12 (0)) R12_x2. ta_reg HS (22%bv : bv 5) (SOff 22 (1)) R22_x2.
rewrite (ta_den_off E 19 (0) r E19) in R19_x2 by lia.
rewrite (ta_den_off E 12 (0) mm E12) in R12_x2 by lia.
rewrite (ta_den_off E 22 (1) i E22) in R22_x2 by lia.
assert (KEfx2 : forall rr, In rr TA_KEPT -> getr (ms_regs msFx2) rr = getr regs rr)
  by (ta_kept HKfx2 R18_x2 R21_x2 R24_x2 R25_x2 R26_x2 E8 E20 G18 G21 G24 G25 G26).
assert (FBfx2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spE - REAC_DISCO_TABLE_AGE_STK <= a < spE - 96) -> ~ (t <= a < t + 400) ->
  aview SEGS (w_H W) (ms_mem msFx2) a = aview SEGS (w_H W) memB a)
  by (intros a Ha Hw Ht; rewrite MKfx2 by lia; apply HFB; assumption).
assert (PBfx2 : forall a, apresent (w_H W) memB a -> apresent (w_H W) (ms_mem msFx2) a)
  by (intros a Ha; apply MGfx2; apply HPB; exact Ha).
pmkst HS.
apply SRr_ret. split; [reflexivity|].
exists (ms_regs msFx2), (ms_mem msFx2). eexists. exists (A), (mm), (r).
split; [reflexivity|]. split; [exact HJ|]. split; [exact KEfx2|].
split; [rewrite R19_x2; unfold w64; f_equal; lia|]. split; [exact FBfx2|]. split; [exact PBfx2|].
split; [exact GAfx2|]. split; [pose proof (reac_disco_table_age.age_inv_keep T now A i mm r HI ltac:(lia) NS) as HI2; rewrite Hx in HI2; exact HI2 | rewrite <- RES, reac_disco_table_age.age_loop_keep by (assumption || lia); apply reac_disco_table_age.age_loop_end; lia].
}
{ rewrite (ta_br_ge E 22 12 i mm 1 0 E22 E12) in Hc by lia.
  assert (Hx : i + 1 < mm) by (destruct (Z.ltb_spec (i + 1) (mm + 0)); [lia | discriminate Hc]).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TA_Bspan 0x5900; [ta_awr E8 Hwr|].

rename HF into HFc2, HFr into HFrc2, HG into HGc2.
ta_kw E8 HFrc2 Kc2.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msFc2 end.
assert (MKfc2 : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS (w_H W) (ms_mem msFc2) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hn; rewrite Kc2 by assumption; first [reflexivity | apply MKa2; assumption]).
assert (MGfc2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem msFc2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGc2 (MGa2 a Ha))).
assert (VMfc2 : val_mem SEGS (mrestrict (w_H W) (ms_mem msFc2)) (t + 384) 4 (mm)).
{ apply (ta_cnt_val E (w_H W) (ms_mem msFc2) t (mm) (SOff 12 (0))); [ | exact E8 | lia | rewrite (ta_den_off E 12 (0) mm E12) by lia; f_equal; lia | lia].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
  exact (st_ok_pi_region_nth E ssf _ 2 (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 12 (0)))]) HS ltac:(vm_compute; reflexivity)) end. }
assert (GAfc2 : garr8 SEGS (mrestrict (w_H W) (ms_mem msFc2)) t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd A 384 (Mem.le4 (Z_to_bv 64 (mm)))))).
{ assert (LAb : length A = 400%nat) by (rewrite ?reac_disco_table_age.length_upd; unfold disco_table_c.entry_of; rewrite ?disco_table.length_sub; rewrite ?LA; lia).
  pose proof (ta_ga_cnt _ _ t (disco_table_c.upd A 384 (Mem.le4 (Z_to_bv 64 (mm)))) (mm) ltac:(rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LAb; lia) HGA
    ltac:(intros a Ha Hn; apply (mbyte_of_aview SEGS); apply MKfc2; lia) VMfc2 ltac:(lia)) as G.
  rewrite reac_disco_table_age.upd_upd in G by (rewrite ?Mem.length_le4, ?LAb; lia). exact G. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
pose proof (regs_kept_of_st_ok_pi E ssf _ regs (ta_extraL t i L mm) [2; 3; 4; 8; 9; 20; 23; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as HKfc2 end.
cbn [ms_regs restrict] in HKfc2.
ta_reg HS (18%bv : bv 5) (SOff 8 384) R18_c2. ta_reg HS (21%bv : bv 5) ta_shx R21_c2. ta_reg HS (24%bv : bv 5) (SLit 8) R24_c2.
ta_reg HS (25%bv : bv 5) (SLit 5000000000) R25_c2. ta_reg HS (26%bv : bv 5) (SLit 3) R26_c2.
ta_reg HS (19%bv : bv 5) (SOff 19 (0)) R19_c2. ta_reg HS (12%bv : bv 5) (SOff 12 (0)) R12_c2. ta_reg HS (22%bv : bv 5) (SOff 22 (1)) R22_c2.
rewrite (ta_den_off E 19 (0) r E19) in R19_c2 by lia.
rewrite (ta_den_off E 12 (0) mm E12) in R12_c2 by lia.
rewrite (ta_den_off E 22 (1) i E22) in R22_c2 by lia.
assert (KEfc2 : forall rr, In rr TA_KEPT -> getr (ms_regs msFc2) rr = getr regs rr)
  by (ta_kept HKfc2 R18_c2 R21_c2 R24_c2 R25_c2 R26_c2 E8 E20 G18 G21 G24 G25 G26).
assert (FBfc2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spE - REAC_DISCO_TABLE_AGE_STK <= a < spE - 96) -> ~ (t <= a < t + 400) ->
  aview SEGS (w_H W) (ms_mem msFc2) a = aview SEGS (w_H W) memB a)
  by (intros a Ha Hw Ht; rewrite MKfc2 by lia; apply HFB; assumption).
assert (PBfc2 : forall a, apresent (w_H W) memB a -> apresent (w_H W) (ms_mem msFc2) a)
  by (intros a Ha; apply MGfc2; apply HPB; exact Ha).
pmkst HS.
eapply SRr_mono.
{ eapply (IH (A) (i + 1) (mm) (r) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memB (ms_mem msFc2) _ kj (ms_regs msFc2) spE t now T LT TOK);
  [ lia | lia | exact (reac_disco_table_age.age_inv_keep T now A i mm r HI ltac:(lia) NS) | rewrite <- RES; symmetry; apply reac_disco_table_age.age_loop_keep; [lia | exact NS] | exact HJ | exact Hal16 | exact Hslo | exact Hshi | exact Ht8b | exact Ht8 | exact Hamr | exact Htsp | exact Hwr
  | exact HradB | exact HhullB | exact FBfc2 | exact PBfc2 | exact GAfc2 | exact Hnow
  | unfold spZ; rewrite (KEfc2 2%bv ltac:(cbv; tauto)); exact Gsp
  | rewrite (KEfc2 3%bv ltac:(cbv; tauto)); exact G3 | rewrite (KEfc2 4%bv ltac:(cbv; tauto)); exact G4
  | rewrite (KEfc2 8%bv ltac:(cbv; tauto)); exact G8 | rewrite (KEfc2 9%bv ltac:(cbv; tauto)); exact G9
  | rewrite R12_c2; unfold w64; f_equal; lia
  | rewrite (KEfc2 18%bv ltac:(cbv; tauto)); exact G18
  | rewrite R19_c2; unfold w64; f_equal; lia
  | rewrite (KEfc2 20%bv ltac:(cbv; tauto)); exact G20 | rewrite (KEfc2 21%bv ltac:(cbv; tauto)); exact G21
  | rewrite R22_c2; unfold w64; f_equal; lia
  | rewrite (KEfc2 23%bv ltac:(cbv; tauto)); exact G23 | rewrite (KEfc2 24%bv ltac:(cbv; tauto)); exact G24
  | rewrite (KEfc2 25%bv ltac:(cbv; tauto)); exact G25 | rewrite (KEfc2 26%bv ltac:(cbv; tauto)); exact G26 ]. }
cbv beta. intros Wq cq _ (-> & regsq & memq & mdq & Aq & mq & rq & -> & HJq & HKq & H19q & HFq & HPq & HGq & HIq & HRq).
split; [reflexivity|]. exists regsq, memq, mdq, Aq, mq, rq. split; [reflexivity|]. split; [exact HJq|].
split; [intros rr Hrr; rewrite (HKq rr Hrr); exact (KEfc2 rr Hrr)|].
split; [exact H19q|]. split; [exact HFq|]. split; [exact HPq|]. split; [exact HGq|]. split; [exact HIq | exact HRq].
}
}
  { rewrite branch_geu_U, U_lit, (ta_U_diff E now L E9 E33) in Hc by lia.
    assert (SA : reac_disco_table_age_c.disco_stale A i now = true).
    { rewrite <- SXs. unfold reac_disco_table_age_c.disco_stale, reac_disco_table_age_c.REAC_DISCO_STALE_NS.
      change (disco_table_c.last_of X i) with L.
      destruct (Z.ltb_spec L now); [|lia]. destruct (Z.ltb_spec 5000000000 (now - L)); [reflexivity | discriminate Hc]. }
    clear Hc.

    paj_run_tok RUN HS HJ SHOK TA_Bspan; [ta_awr E8 Hwr|].
    rename HF into HF3, HFr into HFr3, HG into HG3.
    ta_kw E8 HFr3 K3.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?mc) => rename mc into msC end.
    assert (MKC : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS (w_H W) (ms_mem msC) a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hn; rewrite K3 by assumption; apply K12; assumption).
    assert (MGC : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem msC) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG3 (MG12 a Ha))).
    assert (VMC : val_mem SEGS (mrestrict (w_H W) (ms_mem msC)) (t + 384) 4 mm).
    { apply (ta_cnt_val E (w_H W) (ms_mem msC) t mm (SOff 12 0)); [ | exact E8 | lia | rewrite (ta_den_off E 12 0 mm E12) by lia; f_equal; lia | lia].
      lazymatch type of HS with st_ok _ _ ?ssf _ =>
      exact (YC4b.st_ok_region_nth E ssf _ 2 (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 12 0))]) HS ltac:(vm_compute; reflexivity)) end. }
    ta_regS HS (10%bv : bv 5) (SOff 32 0) Ra0. ta_regS HS (11%bv : bv 5) (SAlu ALU_ADD (SOff 8 0) (SOff 34 0)) Ra1.
    ta_regS HS (12%bv : bv 5) (SLit 48) Ra2. prreg HS (1%bv : bv 5) Rra.
    ta_regS HS (2%bv : bv 5) (SOff 2 0) Rsp. ta_regS HS (3%bv : bv 5) (SOff 3 0) Rgp. ta_regS HS (4%bv : bv 5) (SOff 4 0) Rtp.
    rewrite (ta_den_off E 32 0 (t + 48 * i) E32) in Ra0 by lia. rewrite Z.add_0_r in Ra0.
    rewrite (ta_denot_add2 E 8 34 t (48 * mm - 48) E8 E34) in Ra1 by lia.
    assert (Qsp : spZ (ms_regs msC) = spE - 96) by (unfold spZ; rewrite Rsp, (ta_den_off E 2 0 (spE - 96)) by (try (rewrite E2; unfold w64; rewrite <- Gsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned); lia); rewrite unsigned_lit_small by lia; lia).
    assert (Qgp : getr (ms_regs msC) 3 = w64 (as_gp B)) by (rewrite Rgp; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat 3%bv) by reflexivity; exact G3).
    assert (Qtp : getr (ms_regs msC) 4 = w64 (as_tp B)) by (rewrite Rtp; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat 4%bv) by reflexivity; exact G4).
    assert (SZC : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview SEGS (w_H W) (ms_mem msC) s = aview SEGS (w_H W) memB s).
    { intros s Hs. unfold kLowMemEnd, kHighShadowEnd in Hs. rewrite MKC by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
      apply HFB; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia. }
    assert (RAD : forall d, t <= d -> d + 48 <= t + 400 -> range_addressable (aview SEGS (w_H W) (ms_mem msC)) SHADOW_OFF d 48).
    { intros d Hd1 Hd2. apply (range_addressable_agree (aview SEGS (w_H W) memB)).
      - intros x Hx. destruct (SHM x ltac:(lia)) as (S1 & S2 & S3). apply SZC.
        unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
        pose proof (Z.div_le_mono 0 x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono x (2 ^ 47 - 1) 8 ltac:(lia) ltac:(lia)).
        change ((2 ^ 47 - 1) / 8) with (2 ^ 44 - 1) in *. change (0 / 8) with 0 in *. lia.
      - eapply range_addressable_sub; [exact HradB | lia | lia]. }
    assert (HUL : forall d, t <= d -> d + 48 <= t + 400 -> shadow_hull_vis (aview SEGS (w_H W) (ms_mem msC)) d 48).
    { intros d Hd1 Hd2. apply (ta_hull_sub (aview SEGS (w_H W) memB) _ t d 48 HhullB); [lia | lia | lia |].
      intros s Hs. apply SZC. exact (ta_hull_zone t ltac:(lia) Htb s Hs). }
    pmkst HS.
    destruct (Z.eq_dec i (mm - 1)) as [Eim | Nim].
    { eapply SRr_bind.
      { eapply (ta_cpy_same_at W (ms_regs msC) (ms_mem msC) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ kj (t + 48 * i) 48 (spE - 96 - sp0) (Z_to_bv 64 (BASE + 22880)) HJ).
        - exact Ra0.
        - rewrite Ra1. unfold w64. f_equal. lia.
        - rewrite Ra2. reflexivity.
        - lia. - lia. - lia.
        - rewrite Qsp. lia.
        - apply ta_mod16; assumption.
        - lia. - rewrite Hes. lia.
        - exact Qgp. - exact Qtp. - exact Rra.
        - apply ret_ok_codeptr_v; [lia | reflexivity].
        - intros a Ha. split; [apply Hwr; lia | rewrite Hes; lia].
        - unfold amem_range in *. lia.
        - apply RAD; lia.
        - intros _. apply HUL; lia. }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfr2 & Hpres2).
      assert (CF : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 48 * i <= a < t + 48 * i + 48) -> ~ (spE - 96 - ESTACK <= a < spE - 96) ->
        aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem msC) a)
        by (intros a Ha _ Hw; apply Hfr2; [exact Ha | lia]).
      assert (CI : forall c, 0 <= c < 48 -> aview SEGS (w_H W) mem2 (t + 48 * i + c) = aview SEGS (w_H W) (ms_mem msC) (t + 48 * (mm - 1) + c))
        by (intros c Hc'; rewrite <- Eim; apply Hfr2; rewrite ?Hes; lia).

jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview E (w_H W) (ms_mem msC) mem2 (A_OBJ 0) (VAL (A_OBJ 0))).
    + rewrite EO0. apply unsigned_lit_small. lia.
    + intros a Ha. apply CF; lia.
    + exact Hpres2.
  - apply (region_kept_aview E (w_H W) (ms_mem msC) mem2 (A_OBJ 12) (VAL (A_OBJ 12))).
    + rewrite EO12. apply unsigned_lit_small. lia.
    + intros a Ha. apply CF; lia.
    + exact Hpres2.
  - apply (region_kept_aview E (w_H W) (ms_mem msC) mem2 8 t).
    + rewrite E8. apply unsigned_lit_small. lia.
    + intros a Ha. apply CF; lia.
    + exact Hpres2. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 40)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE' : env_agree 32 (Ereg regs (ta_extraL t i L mm)) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE'.
assert (F8 : ew E' 8 = Z_to_bv 64 t) by (rewrite OLD by lia; exact E8).
assert (F12 : ew E' 12 = Z_to_bv 64 mm) by (rewrite OLD by lia; exact E12).
assert (F19 : ew E' 19 = Z_to_bv 64 r) by (rewrite OLD by lia; exact E19).
assert (F20 : ew E' 20 = Z_to_bv 64 TA_SB) by (rewrite OLD by lia; exact E20).
assert (F22 : ew E' 22 = Z_to_bv 64 i) by (rewrite OLD by lia; exact E22).
assert (F32 : ew E' 32 = Z_to_bv 64 (t + 48 * i)) by (rewrite OLD by lia; exact E32).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (Hrad2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF t 400).
{ apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Hrad]. intros x Hx. destruct (SHM x Hx) as (S1 & S2 & S3).
  rewrite CF by lia. apply MKC; lia. }
assert (SHOK2 : sh_ok SEGS TA_BxL ta_SHL E' (mrestrict (w_H W) mem2)).
{ unfold sh_ok, ta_SHL. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem2 E' TA_BxL 8 t 400 t 0 400 Hrad2).
    * unfold U, TA_BxL. cbn [sv_denot]. rewrite F20, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold TA_SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite F8, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem2 E' TA_BxL 32 t 400 (t + 48 * i) 40 48 Hrad2).
    * unfold U, TA_BxL. cbn [sv_denot]. rewrite F20, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold TA_SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia. }
clear SHOK. rename SHOK2 into SHOK.
assert (GC : garr8 SEGS (mrestrict (w_H W) mem2) t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd X (48 * i) (disco_table_c.entry_of X (mm - 1))))).
{ assert (GC0 : garr8 SEGS (mrestrict (w_H W) (ms_mem msC)) t (map (fun b : byte => bv_unsigned b) X)).
  { pose proof (ta_ga_cnt _ _ t X mm LX HGA ltac:(intros a Ha Hn; apply (mbyte_of_aview SEGS); apply MKC; lia) VMC ltac:(lia)) as G.
    unfold X in G |- *. rewrite reac_disco_table_age.upd_upd in G by (rewrite ?Mem.length_le4, ?LA; lia). exact G. }
  apply (ta_ga_cpy _ _ t X i (mm - 1) LX ltac:(lia) ltac:(lia) GC0).
  - intros a Ha Hn. apply (mbyte_of_aview SEGS). apply CF; lia.
  - intros c Hc'. apply ta_mbyte_of_aview2. apply CI. exact Hc'. }
paj_run_tok RUN HS HJ2 SHOK TA_Bspan; [ta_awr F8 Hwr|].
rename HF into HF4, HFr into HFr4, HG into HG4.
ta_kw F8 HFr4 K4.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into msD end.
assert (MK4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spE - REAC_DISCO_TABLE_AGE_STK <= a < spE - 96) -> ~ (t <= a < t + 400) ->
  aview SEGS (w_H W) (ms_mem msD) a = aview SEGS (w_H W) memB a)
  by (intros a Ha Hw Ht; rewrite K4 by lia; rewrite CF by lia; rewrite MKC by lia; apply HFB; lia).
assert (MG4 : forall a, apresent (w_H W) memB a -> apresent (w_H W) (ms_mem msD) a)
  by (intros a Ha; apply (apresent_grows _ _ _ a HG4); apply Hpres2; apply MGC; apply HPB; exact Ha).
assert (VM4 : val_mem SEGS (mrestrict (w_H W) (ms_mem msD)) (t + 384) 4 (mm - 1)).
{ apply (ta_cnt_val E' (w_H W) (ms_mem msD) t (mm - 1) (SOff 12 (-1))); [ | exact F8 | lia | rewrite (ta_den_off E' 12 (-1) mm F12) by lia; f_equal; lia | lia].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
  exact (st_ok_pi_region_nth E' ssf _ 2 (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 12 (-1)))]) HS ltac:(vm_compute; reflexivity)) end. }
assert (GA4 : garr8 SEGS (mrestrict (w_H W) (ms_mem msD)) t (map (fun b : byte => bv_unsigned b)
  (disco_table_c.upd (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))))).
{ rewrite <- (reac_disco_table_age.tbl_mem_step A i mm (Mem.le4 (Z_to_bv 64 mm)) (Mem.le4 (Z_to_bv 64 (mm - 1)))) by (rewrite ?Mem.length_le4; lia).
  fold X.
  apply (ta_ga_cnt _ _ t (disco_table_c.upd X (48 * i) (disco_table_c.entry_of X (mm - 1))) (mm - 1) ltac:(rewrite reac_disco_table_age.length_upd; unfold disco_table_c.entry_of; rewrite ?disco_table.length_sub; rewrite ?LX; lia) GC).
  - intros a Ha Hn. apply (mbyte_of_aview SEGS). apply K4; lia.
  - exact VM4.
  - lia. }
pose proof (reac_disco_table_age.age_inv_stale T now A i mm r LT T1 HI ltac:(lia) SA) as HIs.
psrr_branch_tok RUN BR HS SHOK TA_Bspan.
{ rewrite (ta_br_ge E' 22 12 i mm 0 (-1) F22 F12) in Hc by lia.
  assert (Hx : i = mm - 1) by (destruct (Z.ltb_spec (i + 0) (mm + -1)); [discriminate Hc | lia]).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK TA_Bspan 0x59cc; [ta_awr F8 Hwr|].
  clear HJ. rename HJ2 into HJ.

rename HF into HFsxa, HFr into HFrsxa, HG into HGsxa.
ta_kw F8 HFrsxa Ksxa.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msFsxa end.
assert (MKfsxa : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS (w_H W) (ms_mem msFsxa) a = aview SEGS (w_H W) (ms_mem msD) a)
  by (intros a Ha Hn; rewrite Ksxa by assumption; first [reflexivity | apply (fun a _ _ => eq_refl); assumption]).
assert (MGfsxa : forall a, apresent (w_H W) (ms_mem msD) a -> apresent (w_H W) (ms_mem msFsxa) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGsxa ((fun a Ha => Ha) a Ha))).
assert (VMfsxa : val_mem SEGS (mrestrict (w_H W) (ms_mem msFsxa)) (t + 384) 4 (mm - 1)).
{ apply (ta_cnt_val E' (w_H W) (ms_mem msFsxa) t (mm - 1) (SOff 12 (-1))); [ | exact F8 | lia | rewrite (ta_den_off E' 12 (-1) mm F12) by lia; f_equal; lia | lia].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
  exact (st_ok_pi_region_nth E' ssf _ 2 (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 12 (-1)))]) HS ltac:(vm_compute; reflexivity)) end. }
assert (GAfsxa : garr8 SEGS (mrestrict (w_H W) (ms_mem msFsxa)) t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))))).
{ assert (LAb : length (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) = 400%nat) by (rewrite ?reac_disco_table_age.length_upd; unfold disco_table_c.entry_of; rewrite ?disco_table.length_sub; rewrite ?LA; lia).
  pose proof (ta_ga_cnt _ _ t (disco_table_c.upd (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))) (mm - 1) ltac:(rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LAb; lia) GA4
    ltac:(intros a Ha Hn; apply (mbyte_of_aview SEGS); apply MKfsxa; lia) VMfsxa ltac:(lia)) as G.
  rewrite reac_disco_table_age.upd_upd in G by (rewrite ?Mem.length_le4, ?LAb; lia). exact G. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
pose proof (regs_kept_of_st_ok_pi E' ssf _ regs (ta_extraL t i L mm) [2; 3; 4; 8; 9; 20; 23; 27]%bv HS HAE' ltac:(vm_compute; reflexivity)) as HKfsxa end.
cbn [ms_regs restrict] in HKfsxa.
ta_reg HS (18%bv : bv 5) (SOff 8 384) R18_sxa. ta_reg HS (21%bv : bv 5) ta_shx R21_sxa. ta_reg HS (24%bv : bv 5) (SLit 8) R24_sxa.
ta_reg HS (25%bv : bv 5) (SLit 5000000000) R25_sxa. ta_reg HS (26%bv : bv 5) (SLit 3) R26_sxa.
ta_reg HS (19%bv : bv 5) (SOff 19 (1)) R19_sxa. ta_reg HS (12%bv : bv 5) (SOff 12 (-1)) R12_sxa. ta_reg HS (22%bv : bv 5) (SOff 22 (0)) R22_sxa.
rewrite (ta_den_off E' 19 (1) r F19) in R19_sxa by lia.
rewrite (ta_den_off E' 12 (-1) mm F12) in R12_sxa by lia.
rewrite (ta_den_off E' 22 (0) i F22) in R22_sxa by lia.
assert (KEfsxa : forall rr, In rr TA_KEPT -> getr (ms_regs msFsxa) rr = getr regs rr)
  by (ta_kept HKfsxa R18_sxa R21_sxa R24_sxa R25_sxa R26_sxa F8 F20 G18 G21 G24 G25 G26).
assert (FBfsxa : forall a, 0 <= a < 2 ^ 64 -> ~ (spE - REAC_DISCO_TABLE_AGE_STK <= a < spE - 96) -> ~ (t <= a < t + 400) ->
  aview SEGS (w_H W) (ms_mem msFsxa) a = aview SEGS (w_H W) memB a)
  by (intros a Ha Hw Ht; rewrite MKfsxa by lia; apply MK4; lia).
assert (PBfsxa : forall a, apresent (w_H W) memB a -> apresent (w_H W) (ms_mem msFsxa) a)
  by (intros a Ha; apply MGfsxa; apply MG4; exact Ha).
pmkst HS.
apply SRr_ret. split; [reflexivity|].
exists (ms_regs msFsxa), (ms_mem msFsxa). eexists. exists (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))), (mm - 1), (r + 1).
split; [reflexivity|]. split; [exact HJ|]. split; [exact KEfsxa|].
split; [rewrite R19_sxa; unfold w64; f_equal; lia|]. split; [exact FBfsxa|]. split; [exact PBfsxa|].
split; [exact GAfsxa|]. split; [rewrite Hx in HIs; rewrite Hx; exact HIs | rewrite <- RES, reac_disco_table_age.age_loop_stale by (assumption || lia); apply reac_disco_table_age.age_loop_end; lia].
}
{ rewrite (ta_br_ge E' 22 12 i mm 0 (-1) F22 F12) in Hc by lia.
  assert (Hx : i < mm - 1) by (destruct (Z.ltb_spec (i + 0) (mm + -1)); [lia | discriminate Hc]).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK TA_Bspan 0x5900; [ta_awr F8 Hwr|].
  clear HJ. rename HJ2 into HJ.

rename HF into HFsca, HFr into HFrsca, HG into HGsca.
ta_kw F8 HFrsca Ksca.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msFsca end.
assert (MKfsca : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS (w_H W) (ms_mem msFsca) a = aview SEGS (w_H W) (ms_mem msD) a)
  by (intros a Ha Hn; rewrite Ksca by assumption; first [reflexivity | apply (fun a _ _ => eq_refl); assumption]).
assert (MGfsca : forall a, apresent (w_H W) (ms_mem msD) a -> apresent (w_H W) (ms_mem msFsca) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGsca ((fun a Ha => Ha) a Ha))).
assert (VMfsca : val_mem SEGS (mrestrict (w_H W) (ms_mem msFsca)) (t + 384) 4 (mm - 1)).
{ apply (ta_cnt_val E' (w_H W) (ms_mem msFsca) t (mm - 1) (SOff 12 (-1))); [ | exact F8 | lia | rewrite (ta_den_off E' 12 (-1) mm F12) by lia; f_equal; lia | lia].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
  exact (st_ok_pi_region_nth E' ssf _ 2 (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 12 (-1)))]) HS ltac:(vm_compute; reflexivity)) end. }
assert (GAfsca : garr8 SEGS (mrestrict (w_H W) (ms_mem msFsca)) t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))))).
{ assert (LAb : length (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) = 400%nat) by (rewrite ?reac_disco_table_age.length_upd; unfold disco_table_c.entry_of; rewrite ?disco_table.length_sub; rewrite ?LA; lia).
  pose proof (ta_ga_cnt _ _ t (disco_table_c.upd (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))) (mm - 1) ltac:(rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LAb; lia) GA4
    ltac:(intros a Ha Hn; apply (mbyte_of_aview SEGS); apply MKfsca; lia) VMfsca ltac:(lia)) as G.
  rewrite reac_disco_table_age.upd_upd in G by (rewrite ?Mem.length_le4, ?LAb; lia). exact G. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
pose proof (regs_kept_of_st_ok_pi E' ssf _ regs (ta_extraL t i L mm) [2; 3; 4; 8; 9; 20; 23; 27]%bv HS HAE' ltac:(vm_compute; reflexivity)) as HKfsca end.
cbn [ms_regs restrict] in HKfsca.
ta_reg HS (18%bv : bv 5) (SOff 8 384) R18_sca. ta_reg HS (21%bv : bv 5) ta_shx R21_sca. ta_reg HS (24%bv : bv 5) (SLit 8) R24_sca.
ta_reg HS (25%bv : bv 5) (SLit 5000000000) R25_sca. ta_reg HS (26%bv : bv 5) (SLit 3) R26_sca.
ta_reg HS (19%bv : bv 5) (SOff 19 (1)) R19_sca. ta_reg HS (12%bv : bv 5) (SOff 12 (-1)) R12_sca. ta_reg HS (22%bv : bv 5) (SOff 22 (0)) R22_sca.
rewrite (ta_den_off E' 19 (1) r F19) in R19_sca by lia.
rewrite (ta_den_off E' 12 (-1) mm F12) in R12_sca by lia.
rewrite (ta_den_off E' 22 (0) i F22) in R22_sca by lia.
assert (KEfsca : forall rr, In rr TA_KEPT -> getr (ms_regs msFsca) rr = getr regs rr)
  by (ta_kept HKfsca R18_sca R21_sca R24_sca R25_sca R26_sca F8 F20 G18 G21 G24 G25 G26).
assert (FBfsca : forall a, 0 <= a < 2 ^ 64 -> ~ (spE - REAC_DISCO_TABLE_AGE_STK <= a < spE - 96) -> ~ (t <= a < t + 400) ->
  aview SEGS (w_H W) (ms_mem msFsca) a = aview SEGS (w_H W) memB a)
  by (intros a Ha Hw Ht; rewrite MKfsca by lia; apply MK4; lia).
assert (PBfsca : forall a, apresent (w_H W) memB a -> apresent (w_H W) (ms_mem msFsca) a)
  by (intros a Ha; apply MGfsca; apply MG4; exact Ha).
pmkst HS.
eapply SRr_mono.
{ eapply (IH (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) (i) (mm - 1) (r + 1) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memB (ms_mem msFsca) _ kj (ms_regs msFsca) spE t now T LT TOK);
  [ lia | lia | exact HIs | rewrite <- RES; symmetry; apply reac_disco_table_age.age_loop_stale; [lia | exact SA] | exact HJ | exact Hal16 | exact Hslo | exact Hshi | exact Ht8b | exact Ht8 | exact Hamr | exact Htsp | exact Hwr
  | exact HradB | exact HhullB | exact FBfsca | exact PBfsca | exact GAfsca | exact Hnow
  | unfold spZ; rewrite (KEfsca 2%bv ltac:(cbv; tauto)); exact Gsp
  | rewrite (KEfsca 3%bv ltac:(cbv; tauto)); exact G3 | rewrite (KEfsca 4%bv ltac:(cbv; tauto)); exact G4
  | rewrite (KEfsca 8%bv ltac:(cbv; tauto)); exact G8 | rewrite (KEfsca 9%bv ltac:(cbv; tauto)); exact G9
  | rewrite R12_sca; unfold w64; f_equal; lia
  | rewrite (KEfsca 18%bv ltac:(cbv; tauto)); exact G18
  | rewrite R19_sca; unfold w64; f_equal; lia
  | rewrite (KEfsca 20%bv ltac:(cbv; tauto)); exact G20 | rewrite (KEfsca 21%bv ltac:(cbv; tauto)); exact G21
  | rewrite R22_sca; unfold w64; f_equal; lia
  | rewrite (KEfsca 23%bv ltac:(cbv; tauto)); exact G23 | rewrite (KEfsca 24%bv ltac:(cbv; tauto)); exact G24
  | rewrite (KEfsca 25%bv ltac:(cbv; tauto)); exact G25 | rewrite (KEfsca 26%bv ltac:(cbv; tauto)); exact G26 ]. }
cbv beta. intros Wq cq _ (-> & regsq & memq & mdq & Aq & mq & rq & -> & HJq & HKq & H19q & HFq & HPq & HGq & HIq & HRq).
split; [reflexivity|]. exists regsq, memq, mdq, Aq, mq, rq. split; [reflexivity|]. split; [exact HJq|].
split; [intros rr Hrr; rewrite (HKq rr Hrr); exact (KEfsca rr Hrr)|].
split; [exact H19q|]. split; [exact HFq|]. split; [exact HPq|]. split; [exact HGq|]. split; [exact HIq | exact HRq].
}

    }
    { eapply SRr_bind.
      { eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS___asan_memcpy) (AMEMCPY fx) W (ms_regs msC) (ms_mem msC)
          STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ kj (t + 48 * i) (t + 48 * (mm - 1)) 48 (spE - 96 - sp0) (Z_to_bv 64 (BASE + 22880)) HJ).
        - exact Ra0.
        - rewrite Ra1. unfold w64. f_equal. lia.
        - rewrite Ra2. reflexivity.
        - lia. - lia. - lia.
        - rewrite Qsp. lia.
        - apply ta_mod16; assumption.
        - lia. - rewrite Hes. lia.
        - exact Qgp. - exact Qtp. - exact Rra.
        - apply ret_ok_codeptr_v; [lia | reflexivity].
        - intros a Ha. split; [apply Hwr; lia | rewrite Hes; lia].
        - unfold amem_range in *. lia.
        - apply RAD; lia.
        - intros _. apply HUL; lia.
        - split; [lia|]. split; [lia|]. split.
          { intros a Ha. split.
            - apply (aview_some_of_apresent SEGS). exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hwr a ltac:(lia)))).
            - rewrite Qsp, Hes. lia. }
          split; [lia|]. split; [unfold amem_range in *; lia|]. split; [apply RAD; lia | intros _; apply HUL; lia]. }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff2 & Hfr2 & Hpres2).
      assert (CF : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 48 * i <= a < t + 48 * i + 48) -> ~ (spE - 96 - ESTACK <= a < spE - 96) ->
        aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem msC) a)
        by (intros a Ha Hd Hw; apply Hfr2; [exact Ha | exact Hd | lia]).
      assert (CI : forall c, 0 <= c < 48 -> aview SEGS (w_H W) mem2 (t + 48 * i + c) = aview SEGS (w_H W) (ms_mem msC) (t + 48 * (mm - 1) + c))
        by (intros c Hc'; exact (Heff2 c Hc')).

jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview E (w_H W) (ms_mem msC) mem2 (A_OBJ 0) (VAL (A_OBJ 0))).
    + rewrite EO0. apply unsigned_lit_small. lia.
    + intros a Ha. apply CF; lia.
    + exact Hpres2.
  - apply (region_kept_aview E (w_H W) (ms_mem msC) mem2 (A_OBJ 12) (VAL (A_OBJ 12))).
    + rewrite EO12. apply unsigned_lit_small. lia.
    + intros a Ha. apply CF; lia.
    + exact Hpres2.
  - apply (region_kept_aview E (w_H W) (ms_mem msC) mem2 8 t).
    + rewrite E8. apply unsigned_lit_small. lia.
    + intros a Ha. apply CF; lia.
    + exact Hpres2. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 40)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE' : env_agree 32 (Ereg regs (ta_extraL t i L mm)) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE'.
assert (F8 : ew E' 8 = Z_to_bv 64 t) by (rewrite OLD by lia; exact E8).
assert (F12 : ew E' 12 = Z_to_bv 64 mm) by (rewrite OLD by lia; exact E12).
assert (F19 : ew E' 19 = Z_to_bv 64 r) by (rewrite OLD by lia; exact E19).
assert (F20 : ew E' 20 = Z_to_bv 64 TA_SB) by (rewrite OLD by lia; exact E20).
assert (F22 : ew E' 22 = Z_to_bv 64 i) by (rewrite OLD by lia; exact E22).
assert (F32 : ew E' 32 = Z_to_bv 64 (t + 48 * i)) by (rewrite OLD by lia; exact E32).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (Hrad2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF t 400).
{ apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Hrad]. intros x Hx. destruct (SHM x Hx) as (S1 & S2 & S3).
  rewrite CF by lia. apply MKC; lia. }
assert (SHOK2 : sh_ok SEGS TA_BxL ta_SHL E' (mrestrict (w_H W) mem2)).
{ unfold sh_ok, ta_SHL. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem2 E' TA_BxL 8 t 400 t 0 400 Hrad2).
    * unfold U, TA_BxL. cbn [sv_denot]. rewrite F20, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold TA_SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite F8, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem2 E' TA_BxL 32 t 400 (t + 48 * i) 40 48 Hrad2).
    * unfold U, TA_BxL. cbn [sv_denot]. rewrite F20, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold TA_SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia. }
clear SHOK. rename SHOK2 into SHOK.
assert (GC : garr8 SEGS (mrestrict (w_H W) mem2) t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd X (48 * i) (disco_table_c.entry_of X (mm - 1))))).
{ assert (GC0 : garr8 SEGS (mrestrict (w_H W) (ms_mem msC)) t (map (fun b : byte => bv_unsigned b) X)).
  { pose proof (ta_ga_cnt _ _ t X mm LX HGA ltac:(intros a Ha Hn; apply (mbyte_of_aview SEGS); apply MKC; lia) VMC ltac:(lia)) as G.
    unfold X in G |- *. rewrite reac_disco_table_age.upd_upd in G by (rewrite ?Mem.length_le4, ?LA; lia). exact G. }
  apply (ta_ga_cpy _ _ t X i (mm - 1) LX ltac:(lia) ltac:(lia) GC0).
  - intros a Ha Hn. apply (mbyte_of_aview SEGS). apply CF; lia.
  - intros c Hc'. apply ta_mbyte_of_aview2. apply CI. exact Hc'. }
paj_run_tok RUN HS HJ2 SHOK TA_Bspan; [ta_awr F8 Hwr|].
rename HF into HF4, HFr into HFr4, HG into HG4.
ta_kw F8 HFr4 K4.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into msD end.
assert (MK4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spE - REAC_DISCO_TABLE_AGE_STK <= a < spE - 96) -> ~ (t <= a < t + 400) ->
  aview SEGS (w_H W) (ms_mem msD) a = aview SEGS (w_H W) memB a)
  by (intros a Ha Hw Ht; rewrite K4 by lia; rewrite CF by lia; rewrite MKC by lia; apply HFB; lia).
assert (MG4 : forall a, apresent (w_H W) memB a -> apresent (w_H W) (ms_mem msD) a)
  by (intros a Ha; apply (apresent_grows _ _ _ a HG4); apply Hpres2; apply MGC; apply HPB; exact Ha).
assert (VM4 : val_mem SEGS (mrestrict (w_H W) (ms_mem msD)) (t + 384) 4 (mm - 1)).
{ apply (ta_cnt_val E' (w_H W) (ms_mem msD) t (mm - 1) (SOff 12 (-1))); [ | exact F8 | lia | rewrite (ta_den_off E' 12 (-1) mm F12) by lia; f_equal; lia | lia].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
  exact (st_ok_pi_region_nth E' ssf _ 2 (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 12 (-1)))]) HS ltac:(vm_compute; reflexivity)) end. }
assert (GA4 : garr8 SEGS (mrestrict (w_H W) (ms_mem msD)) t (map (fun b : byte => bv_unsigned b)
  (disco_table_c.upd (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))))).
{ rewrite <- (reac_disco_table_age.tbl_mem_step A i mm (Mem.le4 (Z_to_bv 64 mm)) (Mem.le4 (Z_to_bv 64 (mm - 1)))) by (rewrite ?Mem.length_le4; lia).
  fold X.
  apply (ta_ga_cnt _ _ t (disco_table_c.upd X (48 * i) (disco_table_c.entry_of X (mm - 1))) (mm - 1) ltac:(rewrite reac_disco_table_age.length_upd; unfold disco_table_c.entry_of; rewrite ?disco_table.length_sub; rewrite ?LX; lia) GC).
  - intros a Ha Hn. apply (mbyte_of_aview SEGS). apply K4; lia.
  - exact VM4.
  - lia. }
pose proof (reac_disco_table_age.age_inv_stale T now A i mm r LT T1 HI ltac:(lia) SA) as HIs.
psrr_branch_tok RUN BR HS SHOK TA_Bspan.
{ rewrite (ta_br_ge E' 22 12 i mm 0 (-1) F22 F12) in Hc by lia.
  assert (Hx : i = mm - 1) by (destruct (Z.ltb_spec (i + 0) (mm + -1)); [discriminate Hc | lia]).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK TA_Bspan 0x59cc; [ta_awr F8 Hwr|].
  clear HJ. rename HJ2 into HJ.

rename HF into HFsxb, HFr into HFrsxb, HG into HGsxb.
ta_kw F8 HFrsxb Ksxb.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msFsxb end.
assert (MKfsxb : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS (w_H W) (ms_mem msFsxb) a = aview SEGS (w_H W) (ms_mem msD) a)
  by (intros a Ha Hn; rewrite Ksxb by assumption; first [reflexivity | apply (fun a _ _ => eq_refl); assumption]).
assert (MGfsxb : forall a, apresent (w_H W) (ms_mem msD) a -> apresent (w_H W) (ms_mem msFsxb) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGsxb ((fun a Ha => Ha) a Ha))).
assert (VMfsxb : val_mem SEGS (mrestrict (w_H W) (ms_mem msFsxb)) (t + 384) 4 (mm - 1)).
{ apply (ta_cnt_val E' (w_H W) (ms_mem msFsxb) t (mm - 1) (SOff 12 (-1))); [ | exact F8 | lia | rewrite (ta_den_off E' 12 (-1) mm F12) by lia; f_equal; lia | lia].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
  exact (st_ok_pi_region_nth E' ssf _ 2 (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 12 (-1)))]) HS ltac:(vm_compute; reflexivity)) end. }
assert (GAfsxb : garr8 SEGS (mrestrict (w_H W) (ms_mem msFsxb)) t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))))).
{ assert (LAb : length (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) = 400%nat) by (rewrite ?reac_disco_table_age.length_upd; unfold disco_table_c.entry_of; rewrite ?disco_table.length_sub; rewrite ?LA; lia).
  pose proof (ta_ga_cnt _ _ t (disco_table_c.upd (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))) (mm - 1) ltac:(rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LAb; lia) GA4
    ltac:(intros a Ha Hn; apply (mbyte_of_aview SEGS); apply MKfsxb; lia) VMfsxb ltac:(lia)) as G.
  rewrite reac_disco_table_age.upd_upd in G by (rewrite ?Mem.length_le4, ?LAb; lia). exact G. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
pose proof (regs_kept_of_st_ok_pi E' ssf _ regs (ta_extraL t i L mm) [2; 3; 4; 8; 9; 20; 23; 27]%bv HS HAE' ltac:(vm_compute; reflexivity)) as HKfsxb end.
cbn [ms_regs restrict] in HKfsxb.
ta_reg HS (18%bv : bv 5) (SOff 8 384) R18_sxb. ta_reg HS (21%bv : bv 5) ta_shx R21_sxb. ta_reg HS (24%bv : bv 5) (SLit 8) R24_sxb.
ta_reg HS (25%bv : bv 5) (SLit 5000000000) R25_sxb. ta_reg HS (26%bv : bv 5) (SLit 3) R26_sxb.
ta_reg HS (19%bv : bv 5) (SOff 19 (1)) R19_sxb. ta_reg HS (12%bv : bv 5) (SOff 12 (-1)) R12_sxb. ta_reg HS (22%bv : bv 5) (SOff 22 (0)) R22_sxb.
rewrite (ta_den_off E' 19 (1) r F19) in R19_sxb by lia.
rewrite (ta_den_off E' 12 (-1) mm F12) in R12_sxb by lia.
rewrite (ta_den_off E' 22 (0) i F22) in R22_sxb by lia.
assert (KEfsxb : forall rr, In rr TA_KEPT -> getr (ms_regs msFsxb) rr = getr regs rr)
  by (ta_kept HKfsxb R18_sxb R21_sxb R24_sxb R25_sxb R26_sxb F8 F20 G18 G21 G24 G25 G26).
assert (FBfsxb : forall a, 0 <= a < 2 ^ 64 -> ~ (spE - REAC_DISCO_TABLE_AGE_STK <= a < spE - 96) -> ~ (t <= a < t + 400) ->
  aview SEGS (w_H W) (ms_mem msFsxb) a = aview SEGS (w_H W) memB a)
  by (intros a Ha Hw Ht; rewrite MKfsxb by lia; apply MK4; lia).
assert (PBfsxb : forall a, apresent (w_H W) memB a -> apresent (w_H W) (ms_mem msFsxb) a)
  by (intros a Ha; apply MGfsxb; apply MG4; exact Ha).
pmkst HS.
apply SRr_ret. split; [reflexivity|].
exists (ms_regs msFsxb), (ms_mem msFsxb). eexists. exists (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))), (mm - 1), (r + 1).
split; [reflexivity|]. split; [exact HJ|]. split; [exact KEfsxb|].
split; [rewrite R19_sxb; unfold w64; f_equal; lia|]. split; [exact FBfsxb|]. split; [exact PBfsxb|].
split; [exact GAfsxb|]. split; [rewrite Hx in HIs; rewrite Hx; exact HIs | rewrite <- RES, reac_disco_table_age.age_loop_stale by (assumption || lia); apply reac_disco_table_age.age_loop_end; lia].
}
{ rewrite (ta_br_ge E' 22 12 i mm 0 (-1) F22 F12) in Hc by lia.
  assert (Hx : i < mm - 1) by (destruct (Z.ltb_spec (i + 0) (mm + -1)); [lia | discriminate Hc]).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK TA_Bspan 0x5900; [ta_awr F8 Hwr|].
  clear HJ. rename HJ2 into HJ.

rename HF into HFscb, HFr into HFrscb, HG into HGscb.
ta_kw F8 HFrscb Kscb.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msFscb end.
assert (MKfscb : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) -> aview SEGS (w_H W) (ms_mem msFscb) a = aview SEGS (w_H W) (ms_mem msD) a)
  by (intros a Ha Hn; rewrite Kscb by assumption; first [reflexivity | apply (fun a _ _ => eq_refl); assumption]).
assert (MGfscb : forall a, apresent (w_H W) (ms_mem msD) a -> apresent (w_H W) (ms_mem msFscb) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGscb ((fun a Ha => Ha) a Ha))).
assert (VMfscb : val_mem SEGS (mrestrict (w_H W) (ms_mem msFscb)) (t + 384) 4 (mm - 1)).
{ apply (ta_cnt_val E' (w_H W) (ms_mem msFscb) t (mm - 1) (SOff 12 (-1))); [ | exact F8 | lia | rewrite (ta_den_off E' 12 (-1) mm F12) by lia; f_equal; lia | lia].
  lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
  exact (st_ok_pi_region_nth E' ssf _ 2 (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 12 (-1)))]) HS ltac:(vm_compute; reflexivity)) end. }
assert (GAfscb : garr8 SEGS (mrestrict (w_H W) (ms_mem msFscb)) t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))))).
{ assert (LAb : length (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) = 400%nat) by (rewrite ?reac_disco_table_age.length_upd; unfold disco_table_c.entry_of; rewrite ?disco_table.length_sub; rewrite ?LA; lia).
  pose proof (ta_ga_cnt _ _ t (disco_table_c.upd (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) 384 (Mem.le4 (Z_to_bv 64 (mm - 1)))) (mm - 1) ltac:(rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LAb; lia) GA4
    ltac:(intros a Ha Hn; apply (mbyte_of_aview SEGS); apply MKfscb; lia) VMfscb ltac:(lia)) as G.
  rewrite reac_disco_table_age.upd_upd in G by (rewrite ?Mem.length_le4, ?LAb; lia). exact G. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
pose proof (regs_kept_of_st_ok_pi E' ssf _ regs (ta_extraL t i L mm) [2; 3; 4; 8; 9; 20; 23; 27]%bv HS HAE' ltac:(vm_compute; reflexivity)) as HKfscb end.
cbn [ms_regs restrict] in HKfscb.
ta_reg HS (18%bv : bv 5) (SOff 8 384) R18_scb. ta_reg HS (21%bv : bv 5) ta_shx R21_scb. ta_reg HS (24%bv : bv 5) (SLit 8) R24_scb.
ta_reg HS (25%bv : bv 5) (SLit 5000000000) R25_scb. ta_reg HS (26%bv : bv 5) (SLit 3) R26_scb.
ta_reg HS (19%bv : bv 5) (SOff 19 (1)) R19_scb. ta_reg HS (12%bv : bv 5) (SOff 12 (-1)) R12_scb. ta_reg HS (22%bv : bv 5) (SOff 22 (0)) R22_scb.
rewrite (ta_den_off E' 19 (1) r F19) in R19_scb by lia.
rewrite (ta_den_off E' 12 (-1) mm F12) in R12_scb by lia.
rewrite (ta_den_off E' 22 (0) i F22) in R22_scb by lia.
assert (KEfscb : forall rr, In rr TA_KEPT -> getr (ms_regs msFscb) rr = getr regs rr)
  by (ta_kept HKfscb R18_scb R21_scb R24_scb R25_scb R26_scb F8 F20 G18 G21 G24 G25 G26).
assert (FBfscb : forall a, 0 <= a < 2 ^ 64 -> ~ (spE - REAC_DISCO_TABLE_AGE_STK <= a < spE - 96) -> ~ (t <= a < t + 400) ->
  aview SEGS (w_H W) (ms_mem msFscb) a = aview SEGS (w_H W) memB a)
  by (intros a Ha Hw Ht; rewrite MKfscb by lia; apply MK4; lia).
assert (PBfscb : forall a, apresent (w_H W) memB a -> apresent (w_H W) (ms_mem msFscb) a)
  by (intros a Ha; apply MGfscb; apply MG4; exact Ha).
pmkst HS.
eapply SRr_mono.
{ eapply (IH (disco_table_c.upd A (48 * i) (disco_table_c.entry_of A (mm - 1))) (i) (mm - 1) (r + 1) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memB (ms_mem msFscb) _ kj (ms_regs msFscb) spE t now T LT TOK);
  [ lia | lia | exact HIs | rewrite <- RES; symmetry; apply reac_disco_table_age.age_loop_stale; [lia | exact SA] | exact HJ | exact Hal16 | exact Hslo | exact Hshi | exact Ht8b | exact Ht8 | exact Hamr | exact Htsp | exact Hwr
  | exact HradB | exact HhullB | exact FBfscb | exact PBfscb | exact GAfscb | exact Hnow
  | unfold spZ; rewrite (KEfscb 2%bv ltac:(cbv; tauto)); exact Gsp
  | rewrite (KEfscb 3%bv ltac:(cbv; tauto)); exact G3 | rewrite (KEfscb 4%bv ltac:(cbv; tauto)); exact G4
  | rewrite (KEfscb 8%bv ltac:(cbv; tauto)); exact G8 | rewrite (KEfscb 9%bv ltac:(cbv; tauto)); exact G9
  | rewrite R12_scb; unfold w64; f_equal; lia
  | rewrite (KEfscb 18%bv ltac:(cbv; tauto)); exact G18
  | rewrite R19_scb; unfold w64; f_equal; lia
  | rewrite (KEfscb 20%bv ltac:(cbv; tauto)); exact G20 | rewrite (KEfscb 21%bv ltac:(cbv; tauto)); exact G21
  | rewrite R22_scb; unfold w64; f_equal; lia
  | rewrite (KEfscb 23%bv ltac:(cbv; tauto)); exact G23 | rewrite (KEfscb 24%bv ltac:(cbv; tauto)); exact G24
  | rewrite (KEfscb 25%bv ltac:(cbv; tauto)); exact G25 | rewrite (KEfscb 26%bv ltac:(cbv; tauto)); exact G26 ]. }
cbv beta. intros Wq cq _ (-> & regsq & memq & mdq & Aq & mq & rq & -> & HJq & HKq & H19q & HFq & HPq & HGq & HIq & HRq).
split; [reflexivity|]. exists regsq, memq, mdq, Aq, mq, rq. split; [reflexivity|]. split; [exact HJq|].
split; [intros rr Hrr; rewrite (HKq rr Hrr); exact (KEfscb rr Hrr)|].
split; [exact H19q|]. split; [exact HFq|]. split; [exact HPq|]. split; [exact HGq|]. split; [exact HIq | exact HRq].
}

    }

  }
}
Qed.

Lemma ta_post : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word) t now (T : list byte)
    (regs2 : bvmap 5 word) mem2 md2 pc (T' : list byte) removed,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  sp0 - STK <= spZ regs - REAC_DISCO_TABLE_AGE_STK -> spZ regs <= sp0 ->
  amem_range t 400 ->
  (forall a, t <= a < t + 400 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_DISCO_TABLE_AGE_STK <= a < spZ regs) -> ~ (t <= a < t + 400) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  pc = getr regs 1 -> aregs_preserved regs regs2 -> getr regs2 10 = w64 removed ->
  garr8 SEGS (mrestrict (w_H W) mem2) t (map (fun b : byte => bv_unsigned b) T') ->
  reac_disco_table_age_c.age_model T now = (T', removed) -> length T = 400%nat -> disco_table_c.table_ok T ->
  treac_disco_table_age_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs t now T W
    (mkCfg (mkst regs2 pc mem2 (seg_rom SEGS)) md2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t now T regs2 mem2 md2 pc T' removed
  HJc HJ2 Hslo Hshi Hamr Hwr VALL HP Hpc HRP H10 HG AM LT TOK.
pose proof (@pa_segs_low _ _ PI) as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_DISCO_TABLE_AGE_STK = 4192) by reflexivity.
pose proof HJc as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & Hstk0 & Hceil & Hlo0 & Hhi0 & H47 & Hbot & Htop & Htop2).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp2 & _).
unfold treac_disco_table_age_post. exists lyc, Sc, regs2, mem2, md2, T', removed.
split; [rewrite Hpc; reflexivity|].
split; [exact HJ2|]. split; [exact HRP|]. split; [exact H10|]. split; [reflexivity|]. split; [apply Permutation_refl|].
split.
{ unfold treac_disco_table_age_kept.
  split; [intros a Ha Hs Hga; apply VALL; lia|].
  split.
  { intros b m i Hin Hi Hgi.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & Hb4096 & Hbceil & _).
    apply VALL; lia. }
  split.
  { intros a Himg Hns Hne. pose proof (Hsegs a Himg) as Hlow. apply VALL; [lia | lia |].
    intros Hga.
    destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc (Hwr a Hga))
      as (_ & [[Hc _] | [(_ & b & n & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl _] _]])]]).
    - lia.
    - exact (blk_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Himg).
    - assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
      unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. exact (frm_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr Himg).
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
  split.
  { intros cid pos a Hin Hr Hga.
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs0.
    pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb1.
    pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs0) as Hse.
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
    apply VALL; [lia | lia | exact Hga]. }
  split; [intros a _ _ Hp; exact (HP a Hp)|].
  intros a Ha. apply HJp2. lia. }
split; [reflexivity|].
split.
{ intros a Ht Hs. pose proof (bv_unsigned_in_range 64 a) as Ha. change (bv_modulus 64) with (2 ^ 64) in Ha. apply VALL; [lia | exact Hs | exact Ht]. }
split; [exact HG|]. split; [exact AM|]. exact (reac_disco_table_age.age_model_post T now T' removed LT TOK AM).
Qed.

Lemma ta_vm_low4 : forall E m base off (e : sv),
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 4 e)) ->
  val_mem SEGS m (base + off) 4 (bv_unsigned (sv_denot E e) mod 2 ^ 32).
Proof.
intros E m base off e H k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in H.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1.
unfold byte_of_word in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by lia.
set (v := bv_unsigned (sv_denot E e)).
rewrite !Z.shiftr_div_pow2 by lia.
apply Z.bits_inj'. intros mb Hm.
destruct (Z_lt_le_dec mb 8) as [Hm8|Hm8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.div_pow2_bits by lia.
  assert (Hlt : mb + 8 * Z.of_nat k < 32) by lia.
  rewrite !(Z.mod_pow2_bits_low _ _ _ Hlt). reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma ta_ga_w4 : forall m m' t (Y : list byte) k w, length Y = 400%nat -> 0 <= k -> k + 4 <= 400 ->
  garr8 SEGS m t (map (fun b : byte => bv_unsigned b) Y) ->
  (forall a, t <= a < t + 400 -> ~ (t + k <= a < t + k + 4) -> mbyte SEGS m' a = mbyte SEGS m a) ->
  val_mem SEGS m' (t + k) 4 w -> 0 <= w < 2 ^ 32 ->
  garr8 SEGS m' t (map (fun b : byte => bv_unsigned b) (disco_table_c.upd Y k (Mem.le4 (Z_to_bv 64 w)))).
Proof.
intros m m' t Y k w LY Hk0 Hk HG Hout VM Hw.
apply (ta_ga_upd m m' t Y (Mem.le4 (Z_to_bv 64 w)) k HG); [lia | rewrite Mem.length_le4, LY; lia | |].
- intros j Hj Hn. rewrite LY in Hj. rewrite Mem.length_le4 in Hn. apply Hout; lia.
- intros j Hj. apply (ta_bytes_of_vm m' (t + k) (Mem.le4 (Z_to_bv 64 w))); [|exact Hj].
  rewrite Mem.length_le4, Mem.bytes_le_to_Z_le4, unsigned_lit_small, Z.mod_small by lia. exact VM.
Qed.
Definition TA_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 22; 28; 29; 30; 31]%bv.
Lemma ta_clob_cases : forall r : bv 5, reg_in r TA_CLOB = false -> r = 0%bv \/ In r TA_KEPT.
Proof.
intros r Hr. pose proof (YP01.all_regs_in r) as Hin. cbv [YP01.all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv [TA_KEPT In]; tauto] |]).
destruct Hin.
Qed.
Lemma ta_seq_val : forall E Q, ew E 34 = Z_to_bv 64 Q -> 0 <= Q < 2 ^ 32 ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1))) mod 2 ^ 32 = (Q + 1) mod 2 ^ 32.
Proof.
intros E Q H34 HQ. change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1)))) with (U E (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1))).
rewrite U_SAlu, U_SExt, (U_atom E 34 Q H34), U_SLit by lia. cbn [zalu_raw].
unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). change (Z.of_N 32) with 32.
Z.div_mod_to_equations. lia.
Qed.
Lemma ta_kwG_lemma : forall Ex rs H (m m' : word -> option byte) sp t,
  frame_of Ex rs (mrestrict H m) (mrestrict H m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi -> (sp - 96 <= a < sp) \/ (t <= a < t + 400)) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 96 <= a < sp) -> ~ (t <= a < t + 400) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros Ex rs H m m' sp t HFx Hw a Ha H1 H2.
apply (kept_of_frame Ex rs H m m' (fun a => (sp - 96 <= a < sp) \/ (t <= a < t + 400)) HFx Hw a Ha). intros [X|X]; [exact (H1 X) | exact (H2 X)].
Qed.
Ltac ta_kwG Usp E10x HFx K :=
  lazymatch type of HFx with frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
  lazymatch type of Usp with bv_unsigned (ew _ 2) = ?sp =>
  lazymatch type of E10x with ew _ 10 = Z_to_bv 64 ?t =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 96 <= a < sp) -> ~ (t <= a < t + 400) -> aview SEGS H m' a = aview SEGS H m a);
  [ apply (ta_kwG_lemma Ex rs H m m' sp t HFx);
    let w := eval vm_compute in (windows rs) in change (windows rs) with w;
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Ha := fresh "Ha" in
    intros b wlo whi a Hin Ha; cbn [In] in Hin;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [base_val] in Ha;
      first [lia | rewrite Usp in Ha; left; lia | rewrite E10x, unsigned_lit_small in Ha by lia; right; lia] |]);
    destruct Hin
  | ] end end end.
Ltac ta_awrE Usp spz sp0 t E10x Hwr :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spz - sp0));
      [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | ]
    | eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10 t);
      [reflexivity | rewrite E10x; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hwr; lia | ] ].

Lemma ta_kwS_lemma : forall Ex rs H (m m' : word -> option byte) sp,
  frame_of Ex rs (mrestrict H m) (mrestrict H m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi -> sp - 96 <= a < sp) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 96 <= a < sp) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros Ex rs H m m' sp HFx Hw a Ha H1.
exact (kept_of_frame Ex rs H m m' (fun a => sp - 96 <= a < sp) HFx Hw a Ha H1).
Qed.
Ltac ta_kwS Usp HFx K :=
  lazymatch type of HFx with frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
  lazymatch type of Usp with bv_unsigned (ew _ 2) = ?sp =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 96 <= a < sp) -> aview SEGS H m' a = aview SEGS H m a);
  [ apply (ta_kwS_lemma Ex rs H m m' sp HFx);
    let w := eval vm_compute in (windows rs) in change (windows rs) with w;
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Ha := fresh "Ha" in
    intros b wlo whi a Hin Ha; cbn [In] in Hin;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [base_val] in Ha;
      first [lia | rewrite Usp in Ha; lia] |]);
    destruct Hin
  | ] end end.

Lemma ta_kwQ_lemma : forall Ex rs H (m m' : word -> option byte) sp t,
  frame_of Ex rs (mrestrict H m) (mrestrict H m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi -> (sp - 96 <= a < sp) \/ (t + 392 <= a < t + 396)) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 96 <= a < sp) -> ~ (t + 392 <= a < t + 396) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros Ex rs H m m' sp t HFx Hw a Ha H1 H2.
apply (kept_of_frame Ex rs H m m' (fun a => (sp - 96 <= a < sp) \/ (t + 392 <= a < t + 396)) HFx Hw a Ha). intros [X|X]; [exact (H1 X) | exact (H2 X)].
Qed.
Ltac ta_kwQ Usp E10x HFx K :=
  lazymatch type of HFx with frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
  lazymatch type of Usp with bv_unsigned (ew _ 2) = ?sp =>
  lazymatch type of E10x with ew _ 10 = Z_to_bv 64 ?t =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 96 <= a < sp) -> ~ (t + 392 <= a < t + 396) -> aview SEGS H m' a = aview SEGS H m a);
  [ apply (ta_kwQ_lemma Ex rs H m m' sp t HFx);
    let w := eval vm_compute in (windows rs) in change (windows rs) with w;
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Ha := fresh "Ha" in
    intros b wlo whi a Hin Ha; cbn [In] in Hin;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [base_val] in Ha;
      first [lia | rewrite Usp in Ha; left; lia | rewrite E10x, unsigned_lit_small in Ha by lia; right; lia] |]);
    destruct Hin
  | ] end end end.

Lemma ta_walk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word) (t now : Z) (T : list byte),
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
  SRr SEGS W (cfg_at SEGS (BASE + AF_both3_reac_disco_table_age) regs memc mdc)
    (treac_disco_table_age_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs t now T).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t now T HJ HROD Hra Hra4 Hgp Htp H10 H11 Hnow Hal16 Hslo Hshi
  Ht0 Ht8 Ht63 Hamr Htsp Hwr2 Hrad Hhull LT TOK HGT.
assert (Hwr : forall a, t <= a < t + 400 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a)
  by (intros a Ha; exact (proj1 (Hwr2 a Ha))).
pose proof (@pa_segs_low _ _ PI) as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_DISCO_TABLE_AGE_STK = 4192) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Ht8b : 8 <= t) by (pose proof (Z.div_mod t 8 ltac:(lia)) as Dt; rewrite Ht8 in Dt; lia).
assert (Htb : t + 400 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
pose proof TOK as (T1 & _). pose proof T1 as T1'. unfold disco_table_c.tbl_T1 in T1'.
pose proof (reac_disco_table_age.seq_range T) as HSQ.
pose proof HJ as HJc.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & Hstk0 & Hceil & Hlo0 & Hhi0 & H47 & Hbot & Htop & Htop2).
pose proof (ta_off_img STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k t HJ Hamr Hwr) as Hoff.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_val_range (A_OBJ 0)) as RV0. pose proof (pa_val_range (A_OBJ 12)) as RV12.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR, Hoff.
assert (DGt : t + 400 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= t)
  by (apply (ta_hull_apart t (t + 400)); unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; try lia; intros a Ha; apply Hoff; lia).
assert (DCt : t + 400 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= t)
  by (apply (ta_hull_apart t (t + 400)); unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; try lia; intros a Ha; apply Hoff; lia).
assert (SHZ : forall x, t <= x < t + 400 -> kLowMemEnd <= shadow_of_addr SHADOW_OFF x < kHighShadowEnd).
{ intros x Hx. unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd.
  pose proof (Z.div_le_mono 0 x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono x (2 ^ 47 - 1) 8 ltac:(lia) ltac:(lia)).
  change ((2 ^ 47 - 1) / 8) with (2 ^ 44 - 1) in *. change (0 / 8) with 0 in *. lia. }
assert (ZNS : forall s, kLowMemEnd <= s < kHighShadowEnd -> 0 <= s < 2 ^ 64 /\ ~ (spZ regs - REAC_DISCO_TABLE_AGE_STK <= s < spZ regs) /\ ~ (t <= s < t + 400)).
{ intros s Hs. unfold kLowMemEnd, kHighShadowEnd, amem_range, kHighMemBeg, kHighMemEnd, kLowMemEnd in *. lia. }
destruct (ta_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t T HJ Hal16 Hslo Hshi H10 Ht0 Ht8 Hamr Htsp Hwr Hrad LT T1 HGT) as [HS SHOK].
remember (Eimg (Ereg regs (ta_extra (disco_table_c.n_of T) (disco_table_c.seq_of T)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (ta_extra (disco_table_c.n_of T) (disco_table_c.seq_of T))) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (apply (EE 1%nat 1%bv); reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply (EE 2%nat 2%bv); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (EE 10%nat 10%bv) by reflexivity; exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 now) by (rewrite (EE 11%nat 11%bv) by reflexivity; exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 TA_SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (disco_table_c.n_of T)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (disco_table_c.seq_of T)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_disco_table_age)) with (Z_to_bv 64 (BASE + AF_both3_reac_disco_table_age)).
paj_run_tok RUN HS HJ SHOK TA_Bspan; [ta_awrE Usp (spZ regs) sp0 t E10 Hwr|].
rename HF into HP1, HFr into HPr1, HG into HPg1.
ta_kwS Usp HPr1 PK1.
assert (PG1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a) by (intros a Ha; exact (apresent_grows _ _ _ a HPg1 Ha)).
psrr_branch_tok RUN BR HS SHOK TA_Bspan.
{ cbn [branch_taken] in Hc. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (ta_den_off E 33 0 (disco_table_c.n_of T) E33), Z.add_0_r, bv_lts_small in Hc by lia.
  assert (Hn0 : disco_table_c.n_of T = 0) by (destruct (Z.ltb_spec 0 (disco_table_c.n_of T)); [discriminate Hc | lia]).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK TA_Bspan; [ta_awrE Usp (spZ regs) sp0 t E10 Hwr|].
  rename HF into HP2, HFr into HPr2, HG into HPg2.
  ta_kwS Usp HPr2 PK2.
  lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
  prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat';
  apply (ta_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t now T (ms_regs msc) (ms_mem msc) _ _ T 0 HJc
    ltac:(apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ) Hslo Hshi Hamr Hwr);
  [ intros a Ha Hs Ht; rewrite PK2 by lia; apply PK1; lia
  | intros a Ha; apply (apresent_grows _ _ _ a HPg2); apply PG1; exact Ha
  | cbn [ms_regs]; rewrite R1, E1; exact Hra
  | eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]
  | cbn [ms_regs]; rewrite R10; reflexivity
  | apply (garr8_frame SEGS (mrestrict (w_H W) memc)); [exact HGT|];
    intros a Ha; rewrite length_map, LT in Ha; apply (mbyte_of_aview SEGS); rewrite PK2 by lia; apply PK1; lia
  | pose proof (reac_disco_table_age.upd_n_self T LT) as U0;
    rewrite (reac_disco_table_age.age_model_of T now T (disco_table_c.n_of T) 0) by (rewrite Hn0; reflexivity);
    replace (0 <? 0) with false by reflexivity; rewrite U0; reflexivity
  | exact LT | exact TOK ]
  end. }

{ cbn [branch_taken] in Hc. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (ta_den_off E 33 0 (disco_table_c.n_of T) E33), Z.add_0_r, bv_lts_small in Hc by lia.
  assert (Hn0 : 0 < disco_table_c.n_of T) by (destruct (Z.ltb_spec 0 (disco_table_c.n_of T)); [lia | discriminate Hc]).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TA_Bspan 0x5900; [ta_awrE Usp (spZ regs) sp0 t E10 Hwr|].
  rename HF into HP2, HFr into HPr2, HG into HPg2.
  ta_kwS Usp HPr2 PK2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms59 end.
  assert (PKB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 96 <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem ms59) a = aview SEGS (w_H W) memc a)
    by (intros a Ha Hs; rewrite PK2 by lia; apply PK1; lia).
  assert (PGB : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms59) a)
    by (intros a Ha; apply (apresent_grows _ _ _ a HPg2); apply PG1; exact Ha).
  ta_reg HS (2%bv : bv 5) (SOff 2 (-96)) Q2. ta_reg HS (8%bv : bv 5) (SOff 10 0) Q8. ta_reg HS (9%bv : bv 5) (SOff 11 0) Q9.
  ta_reg HS (12%bv : bv 5) (SOff 33 0) Q12. ta_reg HS (18%bv : bv 5) (SOff 10 384) Q18. ta_reg HS (19%bv : bv 5) (SLit 0) Q19.
  ta_reg HS (20%bv : bv 5) (SOff 32 0) Q20.
  ta_reg HS (21%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 384) (SLit 3)) (SOff 32 0)) Q21.
  ta_reg HS (22%bv : bv 5) (SLit 0) Q22. ta_reg HS (23%bv : bv 5) (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) Q23.
  ta_reg HS (24%bv : bv 5) (SLit 8) Q24. ta_reg HS (25%bv : bv 5) (SLit 5000000000) Q25. ta_reg HS (26%bv : bv 5) (SLit 3) Q26.
  ta_reg HS (3%bv : bv 5) (SOff 3 0) Q3. ta_reg HS (4%bv : bv 5) (SOff 4 0) Q4.
  assert (HradB : range_addressable (aview SEGS (w_H W) (ms_mem ms59)) SHADOW_OFF t 400).
  { apply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact Hrad]. intros x Hx.
    destruct (ZNS _ (SHZ x Hx)) as (Z1 & Z2 & Z3). apply PKB; lia. }
  assert (HhullB : shadow_hull_vis (aview SEGS (w_H W) (ms_mem ms59)) t 400).
  { apply (ta_hull_sub (aview SEGS (w_H W) memc) _ t t 400 Hhull); [lia | lia | lia |].
    intros s Hs. destruct (ZNS s (ta_hull_zone t ltac:(lia) Htb s Hs)) as (Z1 & Z2 & Z3). apply PKB; lia. }
  assert (HGB : garr8 SEGS (mrestrict (w_H W) (ms_mem ms59)) t
     (map (fun b : byte => bv_unsigned b) (disco_table_c.upd T 384 (Mem.le4 (Z_to_bv 64 (disco_table_c.n_of T)))))).
  { rewrite (reac_disco_table_age.upd_n_self T LT). apply (garr8_frame SEGS (mrestrict (w_H W) memc)); [exact HGT|].
    intros a Ha. rewrite length_map, LT in Ha. apply (mbyte_of_aview SEGS). apply PKB; lia. }
  pmkst HS.
  eapply SRr_bind.
  { eapply (ta_loop (Z.to_nat (disco_table_c.n_of T)) T 0 (disco_table_c.n_of T) 0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
      (ms_mem ms59) (ms_mem ms59) _ k (ms_regs ms59) (spZ regs) t now T LT TOK);
    [ lia | lia | exact (reac_disco_table_age.age_inv_init T now LT T1) | reflexivity | exact HJ | exact Hal16 | exact Hslo | exact Hshi
    | exact Ht8b | exact Ht8 | exact Hamr | exact Htsp | exact Hwr | exact HradB | exact HhullB | intros; reflexivity | intros a Ha; exact Ha
    | exact HGB | exact Hnow
    | unfold spZ at 1; rewrite Q2, (ta_den_off E 2 (-96) (spZ regs)) by (try (rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned); lia); rewrite unsigned_lit_small by lia; lia
    | rewrite Q3; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat 3%bv) by reflexivity; exact Hgp
    | rewrite Q4; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat 4%bv) by reflexivity; exact Htp
    | rewrite Q8, (ta_den_off E 10 0 t E10) by lia; f_equal; lia
    | rewrite Q9, (ta_den_off E 11 0 now E11) by lia; f_equal; lia
    | rewrite Q12, (ta_den_off E 33 0 (disco_table_c.n_of T) E33) by lia; f_equal; lia
    | rewrite Q18, (ta_den_off E 10 384 t E10) by lia; reflexivity
    | rewrite Q19; reflexivity
    | rewrite Q20, (ta_den_off E 32 0 TA_SB E32) by (unfold TA_SB; lia); f_equal; lia
    | rewrite Q21, (denot_shx E 10 32 384 t TA_SB E10 E32) by (unfold TA_SB; lia); reflexivity
    | rewrite Q22; reflexivity
    | rewrite Q23; rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_XOR (SOff 10 0) (SLit (-1)))));
      change (bv_unsigned (sv_denot E (SAlu ALU_XOR (SOff 10 0) (SLit (-1))))) with (U E (SAlu ALU_XOR (SOff 10 0) (SLit (-1))));
      rewrite (U_not E 10 t E10) by lia; reflexivity
    | rewrite Q24; reflexivity | rewrite Q25; reflexivity | rewrite Q26; reflexivity ]. }
  cbv beta. intros W' c' _ (-> & regsL & memL & mdL & A' & m' & r' & -> & HJL & HKL & HL19 & HFL & HPL & HGL & HIL & HRL).

  pose proof HIL as (LA' & Hii' & Hmm' & Hr' & _).
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let rs := eval vm_compute in (firstn 3 (ss_mem ss)) in
    pose proof (st_ok_pi_submem E ss _ rs HS ltac:(lazymatch goal with |- submem ?a ?b => let b' := eval vm_compute in b in change (submem a b') end; submem_tac) ltac:(vm_compute; reflexivity)) as HS1 end.
  cbn [ss_pc ss_regs ss_resv ss_facts] in HS1.
  jafter_stretch_pi HS1 40%nat regsL (mrestrict (w_H W) memL) TA_CLOB 22988 HS2.
  match type of HS2 with ?A1 -> _ => assert (HRR : A1); [|specialize (HS2 HRR); clear HRR] end.
  { intros rr Hrr. cbn [ms_regs restrict]. destruct (ta_clob_cases rr Hrr) as [-> | Hk]; [rewrite !getr_zero; reflexivity | exact (HKL rr Hk)]. }
  match type of HS2 with ?A1 -> _ => assert (HRK : A1); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (region_kept_aview E (w_H W) (ms_mem ms59) memL 2 (spZ regs)); [exact Usp | | exact HPL].
      intros a Ha. apply HFL; lia.
    - apply (region_kept_aview E (w_H W) (ms_mem ms59) memL (A_OBJ 0) (VAL (A_OBJ 0))); [rewrite EO0; apply unsigned_lit_small; lia | | exact HPL].
      intros a Ha. apply HFL; lia.
    - apply (region_kept_aview E (w_H W) (ms_mem ms59) memL (A_OBJ 12) (VAL (A_OBJ 12))); [rewrite EO12; apply unsigned_lit_small; lia | | exact HPL].
      intros a Ha. apply HFL; lia. }
  rewrite <- restrict_mkst_fx in HS2.
  remember (havoc E 40 (map (getr regsL) TA_CLOB)) as Ev2 eqn:HE2 in HS2.
  assert (HEI2 : img_env VAL A_LIM Ev2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD2 : forall n, (n < 40)%nat -> ew Ev2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
  assert (HAE2 : env_agree 32 (Ereg regs (ta_extra (disco_table_c.n_of T) (disco_table_c.seq_of T))) Ev2) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE]).
  assert (E2_52 : ew Ev2 52 = Z_to_bv 64 r').
  { rewrite HE2. replace 52%nat with (40 + 12)%nat by reflexivity.
    rewrite (ew_havoc_new E 40 (map (getr regsL) TA_CLOB) 12 (Z_to_bv 64 0)) by (cbn; lia). cbn [nth map TA_CLOB]. exact HL19. }
  assert (F1 : ew Ev2 1 = getr regs 1) by (rewrite OLD2 by lia; exact E1).
  assert (F10 : ew Ev2 10 = Z_to_bv 64 t) by (rewrite OLD2 by lia; exact E10).
  assert (F32 : ew Ev2 32 = Z_to_bv 64 TA_SB) by (rewrite OLD2 by lia; exact E32).
  assert (F34 : ew Ev2 34 = Z_to_bv 64 (disco_table_c.seq_of T)) by (rewrite OLD2 by lia; exact E34).
  assert (Usp2 : bv_unsigned (ew Ev2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
  assert (FO0 : ew Ev2 (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (rewrite HE2, ew_havoc_above by (cbn; unfold A_OBJ, A_TEXT; lia); exact EO0).
  assert (FO12 : ew Ev2 (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (rewrite HE2, ew_havoc_above by (cbn; unfold A_OBJ, A_TEXT; lia); exact EO12).
  clear HE2.
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 ?ms2 =>
    pose proof (st_ok_pi_add_fact Ev2 ss2 ms2 52 (mkAF 0 8 0) HS2
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E2_52, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS3 end.
  clear HS2.
  assert (VMS : val_mem SEGS (mrestrict (w_H W) memL) (t + 392) 4 (disco_table_c.seq_of T)).
  { pose proof (ta_vm_of_ga _ t (disco_table_c.upd A' 384 (Mem.le4 (Z_to_bv 64 m'))) 392 4 HGL ltac:(lia)
      ltac:(rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LA'; lia)) as V.
    replace (bytes_le_to_Z (disco_table_c.sub (disco_table_c.upd A' 384 (Mem.le4 (Z_to_bv 64 m'))) 392 4)) with (disco_table_c.seq_of T) in V; [exact V|].
    rewrite reac_disco_table_age.sub_upd_out by (rewrite ?Mem.length_le4, ?LA'; lia).
    unfold disco_table_c.seq_of, disco_table_c.u_at. f_equal.
    symmetry. apply reac_disco_table_age.sub_frame; [lia | rewrite LT; lia | rewrite LA', LT; reflexivity |].
    intros kk Hkk. destruct HIL as (_ & _ & _ & _ & _ & _ & _ & Hfr). apply Hfr. lia. }
  lazymatch type of HS3 with st_ok_pi _ _ _ ?ss3 ?ms3 =>
  pose proof (st_ok_pi_add_region Ev2 ss3 ms3 (YP09.mkRegion (Some 10%nat) 392 396 392 396 [YP09.mkChunk 392 (CVal 4 (SOff 34 0))]) HS3 eq_refl) as HS4 end.
  match type of HS4 with ?A1 -> _ => assert (HRO : A1); [|specialize (HS4 HRO); clear HRO] end.
  { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
    rewrite F10, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (t + o) HJL (Hwr (t + o) ltac:(lia))))|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS Ev2 _ t 392 4 (SOff 34 0) (disco_table_c.seq_of T));
    [cbn [sv_denot]; rewrite F34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact VMS]. }
  match type of HS4 with ?A1 -> _ => assert (HRD : A1); [|specialize (HS4 HRD); clear HRD] end.
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    assert (FO0' : ew Ev2 241 = Z_to_bv 64 (VAL (A_OBJ 0))) by exact FO0. assert (FO12' : ew Ev2 253 = Z_to_bv 64 (VAL (A_OBJ 12))) by exact FO12.
    rewrite F10, FO0', FO12', Usp2, !unsigned_lit_small by lia.
    repeat split; lia. }
  clear HS3.
  assert (HradL : range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF t 400).
  { apply (range_addressable_agree (aview SEGS (w_H W) (ms_mem ms59))); [|exact HradB]. intros x Hx.
    destruct (ZNS _ (SHZ x Hx)) as (Z1 & Z2 & Z3). apply HFL; lia. }
  assert (SHOKL : sh_ok SEGS TA_Bx ta_SH Ev2 (mrestrict (w_H W) memL)).
  { unfold sh_ok, ta_SH. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W) memL Ev2 TA_Bx 10 t 400 t 0 400 HradL).
    + unfold U, TA_Bx. cbn [sv_denot]. rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold TA_SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite F10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    + lia. + lia.
    + intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia. }
  clear HS SHOK.
  paj_run_tok RUN HS4 HJL SHOKL TA_Bspan; [ta_awrE Usp2 (spZ regs) sp0 t F10 Hwr|].
  rename HF into HQ1, HFr into HQr1, HG into HQg1.
  ta_kwQ Usp2 F10 HQr1 QK1.
  lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into msE end.
  assert (FRL : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_DISCO_TABLE_AGE_STK <= a < spZ regs) -> ~ (t <= a < t + 400) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) memc a)
    by (intros a Ha Hs Ht; rewrite HFL by lia; apply PKB; lia).
  assert (PRL : forall a, apresent (w_H W) memc a -> apresent (w_H W) memL a) by (intros a Ha; apply HPL; apply PGB; exact Ha).
  psrr_branch_tok RUN BR HS4 SHOKL TA_Bspan.
  { rewrite branch_eq_U, (U_atom Ev2 52 r' E2_52), U_lit in Hc by lia.
    assert (Hr0 : r' = 0) by (destruct (Z.eqb_spec r' 0); [lia | discriminate Hc]).
    clear Hc.
    paj_run_tok RUN HS4 HJL SHOKL TA_Bspan; [ta_awrE Usp2 (spZ regs) sp0 t F10 Hwr|].
    rename HF into HQ2, HFr into HQr2, HG into HQg2.
    ta_kwQ Usp2 F10 HQr2 QK2.
    lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
    assert (VMF : val_mem SEGS (mrestrict (w_H W) (ms_mem msc)) (t + 392) 4 (disco_table_c.seq_of T))
      by (pose proof (st_ok_pi_region_nth Ev2 ssx _ 0 (YP09.mkRegion (Some 10%nat) 392 396 392 396 [YP09.mkChunk 392 (CVal 4 (SOff 34 0))]) HS ltac:(vm_compute; reflexivity)) as RR;
          cbn [ms_mem restrict] in RR;
          exact (field_of_region Ev2 _ 10 t _ 392 396 392 396 392 4 _ _ RR ltac:(rewrite F10; apply unsigned_lit_small; lia) ltac:(left; reflexivity)
            ltac:(cbn [sv_denot]; rewrite F34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia) ltac:(lia)));
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    apply (ta_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t now T (ms_regs msc) (ms_mem msc) _ _
      (disco_table_c.upd A' 384 (Mem.le4 (Z_to_bv 64 m'))) r' HJc
      ltac:(apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJL) Hslo Hshi Hamr Hwr);
    [ intros a Ha Hs Ht; rewrite QK2 by lia; rewrite QK1 by lia; apply FRL; lia
    | intros a Ha; apply (apresent_grows _ _ _ a HQg2); apply (apresent_grows _ _ _ a HQg1); apply PRL; exact Ha
    | cbn [ms_regs]; rewrite R1, F1; exact Hra
    | eapply (aregs_preserved_of_st_ok SEGS _ Ev2 _ _ regs _ HS); [exact HAE2 | vm_compute; reflexivity]
    | cbn [ms_regs]; rewrite R10, E2_52; reflexivity
    | apply (garr8_frame SEGS (mrestrict (w_H W) memL)); [exact HGL|];
      intros a Ha; rewrite length_map, reac_disco_table_age.length_upd in Ha by (rewrite ?Mem.length_le4, ?LA'; lia); rewrite LA' in Ha;
      destruct (Z_lt_le_dec a (t + 392)) as [Ha1|Ha1]; [apply (mbyte_of_aview SEGS); rewrite QK2 by lia; apply QK1; lia|];
      destruct (Z_lt_le_dec a (t + 396)) as [Ha2|Ha2]; [|apply (mbyte_of_aview SEGS); rewrite QK2 by lia; apply QK1; lia];
      replace a with (t + 392 + (a - (t + 392))) by lia;
      exact (val_mem_agree SEGS _ _ (t + 392) 4 _ VMS VMF (a - (t + 392)) ltac:(lia))
    | rewrite (reac_disco_table_age.age_model_of T now A' m' r') by exact HRL;
      replace (0 <? r') with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
    | exact LT | exact TOK ]
    end. }
  { rewrite branch_eq_U, (U_atom Ev2 52 r' E2_52), U_lit in Hc by lia.
    assert (Hr0 : r' <> 0) by (destruct (Z.eqb_spec r' 0); [discriminate Hc | lia]).
    clear Hc.
    paj_run_tok RUN HS4 HJL SHOKL TA_Bspan; [ta_awrE Usp2 (spZ regs) sp0 t F10 Hwr|].
    rename HF into HQ2, HFr into HQr2, HG into HQg2.
    ta_kwQ Usp2 F10 HQr2 QK2.
    lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
    assert (VMF : val_mem SEGS (mrestrict (w_H W) (ms_mem msc)) (t + 392) 4 ((disco_table_c.seq_of T + 1) mod 2 ^ 32))
      by (pose proof (st_ok_pi_region_nth Ev2 ssx _ 0 (YP09.mkRegion (Some 10%nat) 392 396 392 396 [YP09.mkChunk 392 (CVal 4 (SAlu ALU_ADD (SExt true 32 (SOff 34 0)) (SLit 1)))]) HS ltac:(vm_compute; reflexivity)) as RR;
          cbn [ms_mem restrict] in RR; destruct RR as (_ & _ & _ & Hcs); pose proof (Forall_inv Hcs) as Hc0;
          cbn [YP09.r_base base_val] in Hc0; rewrite F10, unsigned_lit_small in Hc0 by lia;
          pose proof (ta_vm_low4 Ev2 _ t 392 _ Hc0) as V; rewrite (ta_seq_val Ev2 (disco_table_c.seq_of T) F34 HSQ) in V; exact V);
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    apply (ta_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs t now T (ms_regs msc) (ms_mem msc) _ _
      (disco_table_c.upd (disco_table_c.upd A' 384 (Mem.le4 (Z_to_bv 64 m'))) 392 (Mem.le4 (Z_to_bv 64 (disco_table_c.seq_of T + 1)))) r' HJc
      ltac:(apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJL) Hslo Hshi Hamr Hwr);
    [ intros a Ha Hs Ht; rewrite QK2 by lia; rewrite QK1 by lia; apply FRL; lia
    | intros a Ha; apply (apresent_grows _ _ _ a HQg2); apply (apresent_grows _ _ _ a HQg1); apply PRL; exact Ha
    | cbn [ms_regs]; rewrite R1, F1; exact Hra
    | eapply (aregs_preserved_of_st_ok SEGS _ Ev2 _ _ regs _ HS); [exact HAE2 | vm_compute; reflexivity]
    | cbn [ms_regs]; rewrite R10, E2_52; reflexivity
    | rewrite <- (reac_disco_table_age.le4_eq_mod (Z_to_bv 64 ((disco_table_c.seq_of T + 1) mod 2 ^ 32)) (Z_to_bv 64 (disco_table_c.seq_of T + 1)))
        by (pose proof (Z.mod_pos_bound (disco_table_c.seq_of T + 1) (2 ^ 32) ltac:(lia)); rewrite !unsigned_lit_small by lia; rewrite Z.mod_mod by lia; reflexivity);
      apply (ta_ga_w4 _ _ t (disco_table_c.upd A' 384 (Mem.le4 (Z_to_bv 64 m'))) 392 ((disco_table_c.seq_of T + 1) mod 2 ^ 32)
        ltac:(rewrite reac_disco_table_age.length_upd; rewrite ?Mem.length_le4, ?LA'; lia) ltac:(lia) ltac:(lia) HGL);
      [ intros a Ha Hn; apply (mbyte_of_aview SEGS); rewrite QK2 by lia; apply QK1; lia
      | exact VMF
      | apply Z.mod_pos_bound; lia ]
    | rewrite (reac_disco_table_age.age_model_of T now A' m' r') by exact HRL;
      replace (0 <? r') with true by (symmetry; apply Z.ltb_lt; lia); reflexivity
    | exact LT | exact TOK ]
    end. }
}
Qed.

End w.
Theorem pb_reac_disco_table_age : treac_disco_table_age_spec.
Proof. intros fq. exact (ta_walk (fx := fq)). Qed.
End h.
End f.
End d.
