(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_of.v, with its module paths and module names changed; 4197 of its 4280 lines of code are new or changed and 764 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacRivalKindOf.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s YImgTop YA0o YCbm YA0q YI67.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC81 YC4b YC45 YC44 YC85 YC88 YCjr YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_arbitrate_c reac_arbitrate.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require FpStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma arb_ble_cons : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
assert (HT : forall i, 8 <= i -> Z.testbit (bv_unsigned b) i = false).
{ intros i Hi. destruct (Z.eq_dec (bv_unsigned b) 0) as [E0|E0]; [rewrite E0; apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  assert (Z.log2 (bv_unsigned b) < 8) by (apply (proj1 (Z.log2_lt_pow2 (bv_unsigned b) 8 ltac:(lia))); change (2 ^ 8) with 256; lia). lia. }
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (HT i Hi8). reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (HT i Hi8). reflexivity.
Qed.

Lemma le_byte_ble : forall (bs : list byte) j, (j < length bs)%nat ->
  YO0f.le_byte (bytes_le_to_Z bs) (length bs) j = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b bs IH]; intros j Hj; cbn [length] in Hj; [lia|].
pose proof (bytes_le_to_Z_nonneg bs) as N0. pose proof (bytes_le_to_Z_bound bs) as N1.
pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
rewrite arb_ble_cons. unfold YO0f.le_byte. cbn [length].
assert (HX : 0 <= bv_unsigned b + bytes_le_to_Z bs * 256 < 2 ^ (8 * Z.of_nat (S (length bs)))).
{ replace (8 * Z.of_nat (S (length bs))) with (8 * Z.of_nat (length bs) + 8) by lia. rewrite Z.pow_add_r by lia.
  change (2 ^ 8) with 256. set (X := 2 ^ (8 * Z.of_nat (length bs))) in *. nia. }
rewrite (Z.mod_small _ _ HX).
destruct j as [|j].
- cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- cbn [nth]. rewrite <- (IH j ltac:(lia)). unfold YO0f.le_byte. rewrite (Z.mod_small (bytes_le_to_Z bs)) by lia.
  replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia. rewrite <- Z.shiftr_shiftr by lia.
  replace (Z.shiftr (bv_unsigned b + bytes_le_to_Z bs * 256) 8) with (bytes_le_to_Z bs). reflexivity.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma val_mem_garr8_sub : forall (m : word -> option byte) a (T : list byte) k (n : nat),
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) T) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length T) ->
  val_mem SEGS m (a + k) n (bytes_le_to_Z (disco_table_c.sub T k n)).
Proof.
intros m a T k n HG Hk Hkn j Hj.
assert (Hl : length (disco_table_c.sub T k n) = n).
{ unfold disco_table_c.sub. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
rewrite <- Hl at 2. rewrite le_byte_ble by lia.
assert (Hj2 : (Z.to_nat k + j < length (map (fun b : byte => bv_unsigned b) T))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte SEGS m a _ _ HG Hj2) as Hb.
replace (a + k + Z.of_nat j) with (a + Z.of_nat (Z.to_nat k + j)) by lia. rewrite Hb. f_equal.
unfold disco_table_c.sub. rewrite nth_firstn. replace ((j <? n)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite map_nth. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis TRIVAL : treac_rival_kind_of_spec B.
Definition REAC_ARBITRATE_STK : Z := 144 + 2 * ESTACK.
Definition treac_arbitrate_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (t our fsm pace now out : Z) (T P : list byte) : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B REAC_ARBITRATE_STK [(out, out + 32)] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       getr regs' 1 = getr regs 1 /\
       Permutation (ablocks B ly' S') (ablocks B ly S) /\
       garr8 SEGS (mrestrict (w_H W') mem') out
         (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.arb_model t our T P fsm pace now)) /\
       (t <> 0 -> garr8 SEGS (mrestrict (w_H W') mem') t (map (fun b : byte => bv_unsigned b) T)) /\
       (our <> 0 -> garr8 SEGS (mrestrict (w_H W') mem') our (map (fun b : byte => bv_unsigned b) P)) /\
       W' = W /\
       (forall a : word, ~ (out <= bv_unsigned a < out + 32) ->
          ~ (spZ regs - REAC_ARBITRATE_STK <= bv_unsigned a < spZ regs) ->
          aview SEGS (w_H W) mem' (bv_unsigned a) = aview SEGS (w_H W) mem (bv_unsigned a))).
Definition treac_arbitrate_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte),
  afn_pre SEGS B REAC_ARBITRATE_STK ly S W regs mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 our -> getr regs 12 = w64 fsm ->
  getr regs 13 = w64 pace -> getr regs 14 = w64 now -> getr regs 15 = w64 out ->
  0 <= t < 2 ^ 64 -> 0 <= our < 2 ^ 64 -> - 2 ^ 31 <= fsm < 2 ^ 31 -> - 2 ^ 31 <= pace < 2 ^ 31 ->
  0 <= now < 2 ^ 64 -> 0 < out < 2 ^ 64 ->
  In (bo, No) (ablocks B ly S) -> bo <= out -> out + 32 <= bo + req_size No -> out mod 4 = 0 ->
  (t <> 0 ->
     In (bt, Nt) (ablocks B ly S) /\ bt <= t /\ t + 400 <= bt + req_size Nt /\ t mod 8 = 0 /\
     length T = 400%nat /\ garr8 SEGS (mrestrict (w_H W) mem) t (map (fun b : byte => bv_unsigned b) T) /\
     disco_table_c.table_ok T /\ (out + 32 <= t \/ t + 400 <= out)) ->
  (our <> 0 ->
     In (bp, Np) (ablocks B ly S) /\ bp <= our /\ our + 6 <= bp + req_size Np /\
     length P = 6%nat /\ garr8 SEGS (mrestrict (w_H W) mem) our (map (fun b : byte => bv_unsigned b) P) /\
     (out + 32 <= our \/ our + 6 <= out)) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_arbitrate) regs mem md)
    (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

Definition ARB_BX : sv := SOff 32 0.
Definition ARB_SPAN : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition arbA_regions : smem :=
  [ stack_region 144; got_regionP; bcell_regionP 32;
    YP09.mkRegion (Some 15%nat) 0 32 0 32 [];
    YP09.mkRegion (Some 10%nat) 0 400 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 33 0))] ].
Definition arbA_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 3);
            (15%nat, mkAF 4096 140737479966720 2); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 8 0) ] [] [].
Definition ss_arbA : sstate := mkSS AF_both3_reac_arbitrate sr_atoms arbA_regions None arbA_facts.
Definition arbA_SH : list shent := [ mkSHE 15 0 32; mkSHE 10 0 400 ].
Definition arbA_extra (n : Z) : list word := map (Z_to_bv 64) [SB; n].
Definition EA (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs (arbA_extra n)).

Lemma arb_val_mem_zero : forall H (m : word -> option byte) a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a n 0.
Proof.
intros H m a n Hz j Hj. destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
assert (L0 : YO0f.le_byte 0 n j = 0).
{ unfold YO0f.le_byte. rewrite (Z.mod_0_l (2 ^ (8 * Z.of_nat n))) by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. apply Z.mod_0_l. lia. }
rewrite L0. unfold bv_wrap. rewrite Z.mod_0_l by (unfold bv_modulus; apply Z.pow_nonzero; lia). lia.
Qed.

Lemma arb_U_BX : forall E, ew E 32 = Z_to_bv 64 SB -> U E ARB_BX = SHADOW_OFF.
Proof.
intros E H. unfold U, ARB_BX. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
Qed.

Lemma arb_U_atom : forall E (m : nat) p, ew E m = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> U E (SOff m 0) = p.
Proof.
intros E m p H Hp. unfold U. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma arb_shent : forall ly S W mem md E (m : nat) b n p lo hi,
  AR SEGS B ly S W mem md -> In (b, n) (ablocks B ly S) ->
  U E ARB_BX = SHADOW_OFF -> U E (SOff m 0) = p -> b <= p + lo -> p + hi <= b + req_size n -> 0 <= lo <= hi ->
  shent_ok SEGS ARB_BX E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
intros ly S W mem md E m b n p lo hi HAR Hin HU Hp H1 H2 H3.
destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hin) as (_ & _ & _ & Hia & _).
apply (shent_ok_of_range SEGS (w_H W) mem E ARB_BX m (p + lo) (hi - lo) p lo hi).
- apply (range_addressable_of_block SEGS B LAWS ly S W mem md b n (p + lo) (hi - lo) HAR Hin); lia.
- exact HU.
- exact Hp.
- lia.
- lia.
- intros x Hx. revert Hia H1 H2 H3 Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.

Lemma arb_garr8_val_mem : forall (m : word -> option byte) a (bs : list byte) v,
  val_mem SEGS m a (length bs) v -> v mod 2 ^ (8 * Z.of_nat (length bs)) = bytes_le_to_Z bs ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) bs).
Proof.
intros m a bs v HV Hv j Hj. rewrite length_map in Hj.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia). rewrite map_nth.
pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
split; [|lia].
intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r.
rewrite (HV j Hj). f_equal. f_equal.
transitivity (bv_unsigned (nth j bs (Z_to_bv 8 0))).
- rewrite <- (le_byte_ble bs j Hj), <- Hv. unfold YO0f.le_byte. rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
- unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite (Z.mod_small (bv_unsigned (nth j bs (Z_to_bv 8 0))) 256) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma arb_denot_shx : forall E (m : nat) x off,
  ew E 32 = Z_to_bv 64 SB -> ew E m = Z_to_bv 64 x -> 0 <= x < 2 ^ 47 -> 0 <= x + off < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff m off) (SLit 3))) = Z_to_bv 64 (SB + (x + off) / 8) /\
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m off) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SB + (x + off) / 8).
Proof.
intros E m x off H32 Hm Hx Hxo.
assert (UX : U E (SAlu ALU_SRL (SOff m off) (SLit 3)) = (x + off) / 8).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E m x off Hm) by lia.
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (U32 : U E (SOff 32 0) = SB) by (apply U_atom; [exact H32 | unfold SB; lia]).
assert (Hq : 0 <= (x + off) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
split; rewrite denot_lit_U; f_equal; rewrite U_SAlu; cbn [zalu_raw]; rewrite UX, U32; rewrite zcanon_id by (unfold M64, SB; lia); lia.
Qed.

Lemma arbA_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t out bt Nt bo No : Z) (T : list byte),
  afn_pre SEGS B REAC_ARBITRATE_STK ly S W regs mem md ch ->
  getr regs 10 = w64 t -> getr regs 15 = w64 out -> 0 <= t < 2 ^ 64 -> 0 < out < 2 ^ 64 ->
  In (bo, No) (ablocks B ly S) -> bo <= out -> out + 32 <= bo + req_size No -> out mod 4 = 0 ->
  t <> 0 -> In (bt, Nt) (ablocks B ly S) -> bt <= t -> t + 400 <= bt + req_size Nt -> t mod 8 = 0 ->
  length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map (fun b : byte => bv_unsigned b) T) ->
  0 <= disco_table_c.n_of T <= 8 -> (out + 32 <= t \/ t + 400 <= out) ->
  st_ok_pi (fx := fq) SEGS VAL (EA regs (disco_table_c.n_of T)) ss_arbA
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_reac_arbitrate)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS ARB_BX arbA_SH (EA regs (disco_table_c.n_of T)) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch t out bt Nt bo No T HPRE H10 H15 Rt Rout Hbo Hbo1 Hbo2 Ho4 Ht0 Hbt Hbt1 Hbt2 Ht8 LT GT RN Hdis.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ bo No HAR Hbo) as Hoimg.
destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (Ht16 & Ht4096 & Htceil & Htia & Htpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ bt Nt HAR Hbt) as Htimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold off_img, IMG_LO, IMG_TOP in HcellR, HgotR, Hoimg, Htimg.
assert (Hu384 : disco_table_c.u_at T 384 4 = disco_table_c.n_of T).
{ unfold disco_table_c.n_of, disco_table_c.s32_at in *. unfold disco_table_c.u_at in *.
  assert (Hl : length (disco_table_c.sub T 384 4) = 4%nat).
  { unfold disco_table_c.sub. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
  pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T 384 4)) as U0.
  pose proof (bytes_le_to_Z_bound (disco_table_c.sub T 384 4)) as U1. rewrite Hl in U1.
  change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in U1.
  set (u := bytes_le_to_Z (disco_table_c.sub T 384 4)) in *.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 32) with 4294967296 in *.
  change (4294967296 / 2) with 2147483648 in *.
  destruct (Z_lt_le_dec u 2147483648) as [Hs|Hs].
  - rewrite Z.mod_small by lia. lia.
  - exfalso. replace (u + 2147483648) with ((u - 2147483648) + 1 * 4294967296) in RN by lia.
    rewrite Z_mod_plus_full, Z.mod_small in RN by lia. lia. }
assert (VN : val_mem SEGS (mrestrict (w_H W) mem) (t + 384) 4 (disco_table_c.n_of T)).
{ rewrite <- Hu384. unfold disco_table_c.u_at. apply val_mem_garr8_sub; [exact GT | lia | rewrite LT; lia]. }
rewrite restrict_mkst_fx.
set (E := EA regs (disco_table_c.n_of T)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbA_extra (disco_table_c.n_of T))) n)
  by (intros n Hn; subst E; unfold EA; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (disco_table_c.n_of T)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Eo66 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold EA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_arbA. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold arbA_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo1) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Eo66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo66) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 ARB_BX SB);
      [cbn [sv_denot ARB_BX]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. unfold SB. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 15%nat out E15) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hopres (out + o) ltac:(lia))).
    * rewrite (VB 10%nat t E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ t 384 4 (SOff 33 0) (disco_table_c.n_of T));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VN].
  + apply pairwise_disjoint_of_extents. unfold arbA_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat t E10), (VB 15%nat out E15) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo1) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo66) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Hoceil Hoia Hoimg Ho4096 Htceil Htia Htimg Ht4096 Hbo1 Hbo2 Hbt1 Hbt2 Hdis C1 C3 WS Hstk0 HcellR HgcD HgotR.
    clear. unfold off_img, in_app. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [arbA_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E15, E32, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hoceil Ho4096 Htceil Ht4096 Hbo1 Hbo2 Hbt1 Hbt2 Hal16 Ho4 Ht8 RN C1 C3 WS Hstk0.
    clear. unfold SB. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, arbA_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E ARB_BX 15 out 32 out 0 32).
    * apply (range_addressable_of_block SEGS B LAWS ly S W mem md bo No out 32 HAR Hbo); lia.
    * unfold U, ARB_BX. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E15, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. revert Hoia Hbo1 Hbo2 Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E ARB_BX 10 t 400 t 0 400).
    * apply (range_addressable_of_block SEGS B LAWS ly S W mem md bt Nt t 400 HAR Hbt); lia.
    * unfold U, ARB_BX. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. revert Htia Hbt1 Hbt2 Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.


Definition AF_ARB_L : Z := AF_both3_reac_arbitrate + 260.
Definition AF_ARB_E : Z := AF_both3_reac_arbitrate + 664.
Definition AF_ARB_N : Z := AF_both3_reac_arbitrate + 808.
Definition AF_ARB_B : Z := AF_both3_reac_arbitrate + 464.
Definition ARB_STALE : Z := 5000000000.
Definition ARB_SAVES : list (Z * Z) :=
  [(136, 1); (128, 8); (120, 9); (112, 18); (104, 19); (96, 20); (88, 21); (80, 22); (72, 23); (64, 24); (56, 25); (48, 26); (40, 27)].
Definition arb_out0 (pace : Z) : list Z :=
  map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.arb_bytes 0 reac_arbitrate_c.MAC0 0 pace 0 0 0).


Definition arb_frame (m : word -> option byte) (regs : bvmap 5 word) : Prop :=
  forall p, In p ARB_SAVES -> val_mem SEGS m (spZ regs - 144 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p)))).

Definition arb_slots (m : word -> option byte) (regs : bvmap 5 word) (fsm out : Z) : Prop :=
  val_mem SEGS m (spZ regs - 144) 8 (SB + (out + 16) / 8) /\
  val_mem SEGS m (spZ regs - 144 + 8) 8 (out + 16) /\
  val_mem SEGS m (spZ regs - 144 + 16) 8 (fsm mod 2 ^ 64) /\
  val_mem SEGS m (spZ regs - 144 + 24) 8 out.

Definition arb_est (fsm : Z) : bool := (fsm =? 2) || (fsm =? 3).

Definition arb_pre ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) : Prop :=
  afn_pre SEGS B REAC_ARBITRATE_STK ly S W regs mem md ch /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
  getr regs 10 = w64 t /\ getr regs 11 = w64 our /\ getr regs 12 = w64 fsm /\
  getr regs 13 = w64 pace /\ getr regs 14 = w64 now /\ getr regs 15 = w64 out /\
  0 <= t < 2 ^ 64 /\ 0 <= our < 2 ^ 64 /\ - 2 ^ 31 <= fsm < 2 ^ 31 /\ - 2 ^ 31 <= pace < 2 ^ 31 /\
  0 <= now < 2 ^ 64 /\ 0 < out < 2 ^ 64 /\
  In (bo, No) (ablocks B ly S) /\ bo <= out /\ out + 32 <= bo + req_size No /\ out mod 4 = 0 /\
  (t <> 0 ->
     In (bt, Nt) (ablocks B ly S) /\ bt <= t /\ t + 400 <= bt + req_size Nt /\ t mod 8 = 0 /\
     length T = 400%nat /\ garr8 SEGS (mrestrict (w_H W) mem) t (map (fun b : byte => bv_unsigned b) T) /\
     disco_table_c.table_ok T /\ (out + 32 <= t \/ t + 400 <= out)) /\
  (our <> 0 ->
     In (bp, Np) (ablocks B ly S) /\ bp <= our /\ our + 6 <= bp + req_size Np /\
     length P = 6%nat /\ garr8 SEGS (mrestrict (w_H W) mem) our (map (fun b : byte => bv_unsigned b) P) /\
     (out + 32 <= our \/ our + 6 <= out)).

Definition arb_cmn ly S W (regs : bvmap 5 word) mem md (our pace out : Z)
    (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S W mem3 md3 0 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a) /\
  arb_frame (mrestrict (w_H W) mem3) regs /\
  garr8 SEGS (mrestrict (w_H W) mem3) out (arb_out0 pace) /\
  getr regs3 2 = Z_to_bv 64 (spZ regs - 144) /\ getr regs3 3 = getr regs 3 /\ getr regs3 4 = getr regs 4 /\
  getr regs3 9 = Z_to_bv 64 our /\ getr regs3 24 = Z_to_bv 64 SB.

Definition arb_invE ly S W (regs : bvmap 5 word) mem md (t our fsm pace now out : Z) (T P : list byte) (b : option Z)
    (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
  arb_cmn ly S W regs mem md our pace out regs3 mem3 md3 /\
  getr regs3 18 = Z_to_bv 64 out /\ getr regs3 19 = Z_to_bv 64 (reac_arbitrate.baddr t b) /\
  getr regs3 8 = Z_to_bv 64 t /\
  b = reac_arbitrate_c.best t T P our now /\ arb_est fsm = true.

Definition arb_invN ly S W (regs : bvmap 5 word) mem md (t our fsm pace now out : Z) (T P : list byte)
    (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
  arb_cmn ly S W regs mem md our pace out regs3 mem3 md3 /\
  getr regs3 18 = Z_to_bv 64 out /\ getr regs3 20 = Z_to_bv 64 fsm /\
  reac_arbitrate_c.best t T P our now = None /\ arb_est fsm = false.

Definition arb_invB ly S W (regs : bvmap 5 word) mem md (t our fsm pace now out : Z) (T P : list byte) (j : Z)
    (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
  arb_cmn ly S W regs mem md our pace out regs3 mem3 md3 /\
  arb_slots (mrestrict (w_H W) mem3) regs fsm out /\
  getr regs3 18 = Z_to_bv 64 out /\ getr regs3 19 = Z_to_bv 64 (t + 48 * j) /\
  getr regs3 8 = Z_to_bv 64 t /\
  reac_arbitrate_c.best t T P our now = Some j /\ arb_est fsm = false.

Definition arb_invL ly S W (regs : bvmap 5 word) mem md (t our fsm pace now out : Z) (T P : list byte) (i : Z) (b : option Z)
    (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
  arb_cmn ly S W regs mem md our pace out regs3 mem3 md3 /\
  arb_slots (mrestrict (w_H W) mem3) regs fsm out /\
  val_mem SEGS (mrestrict (w_H W) mem3) (spZ regs - 144 + 32) 8 ARB_STALE /\
  getr regs3 8 = Z_to_bv 64 t /\ getr regs3 18 = Z_to_bv 64 2 /\
  getr regs3 19 = Z_to_bv 64 (reac_arbitrate.baddr t b) /\
  getr regs3 20 = Z_to_bv 64 (48 * disco_table_c.n_of T) /\ getr regs3 21 = Z_to_bv 64 now /\
  getr regs3 25 = Z_to_bv 64 432 /\ getr regs3 26 = Z_to_bv 64 (48 * i) /\
  getr regs3 27 = Z_to_bv 64 (2 ^ 64 - 1 - t) /\
  b = reac_arbitrate.scanz T P our now i /\ t <> 0 /\ 0 <= i < disco_table_c.n_of T.

Definition ARB_STKA : list YP09.chunk :=
  [ YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
    YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
    YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 27 0)) ].

Definition ARB_STKS : list YP09.chunk :=
  [ YP09.mkChunk (-144) (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 15 16) (SLit 3)) (SOff 32 0)));
    YP09.mkChunk (-136) (CVal 8 (SOff 15 16)); YP09.mkChunk (-128) (CVal 8 (SOff 12 0));
    YP09.mkChunk (-120) (CVal 8 (SOff 15 0)) ].

Lemma arb_frameA : forall E m (regs : bvmap 5 word) cs wlo whi,
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (-144) 0 wlo whi cs) ->
  bv_unsigned (ew E 2) = spZ regs ->
  (forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n))) ->
  incl ARB_STKA cs -> arb_frame m regs.
Proof.
intros E m regs cs wlo whi HR Hsp AG Hin.
assert (SL : forall od e v, In (YP09.mkChunk od (CVal 8 e)) ARB_STKA -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (spZ regs + od) 8 v).
{ intros od e v Hc He Hv. exact (slot_of_region E m (spZ regs) cs (-144) 0 wlo whi od e v HR Hsp (Hin _ Hc) He Hv). }
assert (RG : forall (n : nat) (r : Z), (n < 32)%nat -> r = Z.of_nat n ->
  sv_denot E (SOff n 0) = Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros n r Hn ->. cbn [sv_denot]. rewrite (AG n Hn), Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity. }
intros p Hp. pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (snd p)))) as Rg. unfold bv_modulus in Rg.
change (2 ^ Z.of_N 64) with (2 ^ 64) in Rg.
cbn [ARB_SAVES In] in Hp.
repeat (destruct Hp as [<-|Hp];
  [ cbn [fst snd] in Rg |- *;
    match goal with |- val_mem _ _ (spZ regs - 144 + ?o) _ _ =>
      let o' := eval vm_compute in (o - 144) in replace (spZ regs - 144 + o) with (spZ regs + o') by lia end;
    eapply SL; [cbn [ARB_STKA In]; repeat (first [left; reflexivity | right]) | apply RG; [lia | reflexivity] | lia] |]).
destruct Hp.
Qed.
Definition ARB_OUTA : list YP09.chunk :=
  [ YP09.mkChunk 16 (CVal 4 (SOff 13 0)); YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0));
    YP09.mkChunk 20 (CVal 4 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SLit 0)) ].

Lemma arb_out0_split : forall pace, arb_out0 pace =
  map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) 8) ++ map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) 8) ++
  map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 pace) ++ map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) 4) ++
  map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) 8).
Proof. intros pace. unfold arb_out0, reac_arbitrate_c.arb_bytes. rewrite !map_app. reflexivity. Qed.

Lemma arb_outA : forall E m out pace cs,
  region_ok SEGS E m (YP09.mkRegion (Some 15%nat) 0 32 0 32 cs) -> bv_unsigned (ew E 15) = out ->
  ew E 13 = Z_to_bv 64 pace -> incl ARB_OUTA cs -> garr8 SEGS m out (arb_out0 pace).
Proof.
intros E m out pace cs HR Hout H13 Hin.
destruct HR as (_ & _ & _ & Hcs). cbn [YP09.r_chunks YP09.r_base base_val] in Hcs. rewrite Hout in Hcs.
assert (CK : forall c, In c ARB_OUTA -> YP09.chunk_ok SEGS E m out c) by (intros c Hc; exact (proj1 (Forall_forall _ _) Hcs c (Hin c Hc))).
assert (Z8 : forall o, In (YP09.mkChunk o (CVal 8 (SLit 0))) ARB_OUTA ->
  garr8 SEGS m (out + o) (map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) 8))).
{ intros o Ho. apply (arb_garr8_val_mem m (out + o) (repeat (Z_to_bv 8 0) 8) 0); [|reflexivity].
  pose proof (val_mem_low_of_chunk SEGS E m out o 8 (SLit 0) (CK _ Ho) ltac:(lia)) as V. exact V. }
assert (Z4 : garr8 SEGS m (out + 20) (map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) 4))).
{ apply (arb_garr8_val_mem m (out + 20) (repeat (Z_to_bv 8 0) 4) 0); [|reflexivity].
  pose proof (val_mem_low_of_chunk SEGS E m out 20 4 (SLit 0) (CK (YP09.mkChunk 20 (CVal 4 (SLit 0))) ltac:(cbn; tauto)) ltac:(lia)) as V. exact V. }
assert (LZ : length (reac_arbitrate_c.z4 pace) = 4%nat) by reflexivity.
assert (ZP : garr8 SEGS m (out + 16) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 pace))).
{ apply (arb_garr8_val_mem m _ _ (bv_unsigned (sv_denot E (SOff 13 0)) mod 2 ^ (8 * Z.of_N 4))).
  - pose proof (val_mem_low_of_chunk SEGS E m out 16 4 (SOff 13 0) (CK (YP09.mkChunk 16 (CVal 4 (SOff 13 0))) ltac:(cbn; tauto)) ltac:(lia)) as V.
    rewrite LZ. exact V.
  - rewrite LZ. change (reac_arbitrate_c.z4 pace) with (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 pace))).
    rewrite bytes_le_Z_to_le by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 pace)); lia).
    cbn [sv_denot]. rewrite H13, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity. }
rewrite arb_out0_split.
apply garr8_app. split; [replace out with (out + 0) at 1 by lia; apply Z8; cbn; tauto|].
rewrite length_map, repeat_length.
apply garr8_app. split; [apply Z8; cbn; tauto|].
rewrite length_map, repeat_length.
apply garr8_app. split; [replace (out + Z.of_nat 8 + Z.of_nat 8) with (out + 16) by lia; exact ZP|].
rewrite length_map, LZ.
apply garr8_app. split; [replace (out + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 4) with (out + 20) by lia; exact Z4|].
rewrite length_map, repeat_length.
replace (out + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4) with (out + 24) by lia. apply Z8. cbn; tauto.
Qed.


Lemma arb_meq_step : forall E rs H (m0 m1 m2 : word -> option byte) (Zs : Z -> Prop),
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m1 a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros E rs H m0 m1 m2 Zs HF Hw HM a Ha Hn.
rewrite (kept_of_frame (segs := SEGS) E rs H m1 m2 Zs HF Hw a Ha Hn). exact (HM a Ha Hn).
Qed.

Lemma arb_slotsA : forall E m (regs : bvmap 5 word) fsm out cs wlo whi,
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (-144) 0 wlo whi cs) ->
  bv_unsigned (ew E 2) = spZ regs ->
  ew E 32 = Z_to_bv 64 SB -> ew E 15 = Z_to_bv 64 out -> ew E 12 = Z_to_bv 64 fsm ->
  0 <= out < 2 ^ 47 - 16 ->
  incl ARB_STKS cs -> arb_slots m regs fsm out.
Proof.
intros E m regs fsm out cs wlo whi HR Hsp H32 H15 H12 Rout Hin.
assert (SL : forall od e v, In (YP09.mkChunk od (CVal 8 e)) ARB_STKS -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (spZ regs + od) 8 v).
{ intros od e v Hc He Hv. exact (slot_of_region E m (spZ regs) cs (-144) 0 wlo whi od e v HR Hsp (Hin _ Hc) He Hv). }
split; [|split; [|split]].
- replace (spZ regs - 144) with (spZ regs + -144) by lia. eapply SL.
  + cbn [ARB_STKS In]. left; reflexivity.
  + exact (proj2 (arb_denot_shx E 15 out 16 H32 H15 ltac:(lia) ltac:(lia))).
  + assert (0 <= (out + 16) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). unfold SB. lia.
- replace (spZ regs - 144 + 8) with (spZ regs + -136) by lia. eapply SL.
  + cbn [ARB_STKS In]. right; left; reflexivity.
  + cbn [sv_denot]. rewrite H15. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
- replace (spZ regs - 144 + 16) with (spZ regs + -128) by lia. eapply SL.
  + cbn [ARB_STKS In]. right; right; left; reflexivity.
  + cbn [sv_denot]. rewrite H12, Z.add_0_r. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
  + apply Z.mod_pos_bound. lia.
- replace (spZ regs - 144 + 24) with (spZ regs + -120) by lia. eapply SL.
  + cbn [ARB_STKS In]. right; right; right; left; reflexivity.
  + cbn [sv_denot]. rewrite H15, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + lia.
Qed.

Lemma arb_est_br : forall E (k : nat) fsm, ew E k = Z_to_bv 64 fsm -> - 2 ^ 31 <= fsm < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SOff k 0) (SLit (-2)))) (sv_denot E (SLit 2)) = arb_est fsm.
Proof.
intros E k fsm H Hf. unfold arb_est. rewrite <- (reac_arbitrate.est_eq fsm Hf).
cbn [branch_taken sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. f_equal.
rewrite <- (Z_to_bv_bv_unsigned 64 (Z_to_bv 64 fsm)) at 1. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw].
rewrite Z_to_bv64_canon. rewrite (zcanon_small (bv_unsigned (Z_to_bv 64 fsm))) by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 fsm)); unfold bv_modulus in *; lia).
reflexivity.
Qed.

Lemma arb_s4_val : forall E n, ew E 33 = Z_to_bv 64 n -> 0 < n <= 8 ->
  sv_denot E (SAlu ALU_SUB
    (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) (SLit 6))
    (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) (SLit 4)))
  = Z_to_bv 64 (48 * n).
Proof.
intros E n H Hn. cbn [sv_denot]. rewrite H.
assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8) as Hc by lia.
destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ]; vm_compute; reflexivity.
Qed.

Lemma arb_xor_val : forall E t, ew E 10 = Z_to_bv 64 t -> 0 <= t < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) = Z_to_bv 64 (2 ^ 64 - 1 - t).
Proof.
intros E t H Ht. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw]. rewrite Z_to_bv64_canon.
rewrite (zcanon_small t) by lia. change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_allones by lia. reflexivity.
Qed.

Lemma arb_best_n0 : forall t (T P : list byte) our now, t <> 0 -> disco_table_c.n_of T <= 0 ->
  reac_arbitrate_c.best t T P our now = None.
Proof.
intros t T P our now Ht Hn. unfold reac_arbitrate_c.best. replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ht).
unfold reac_arbitrate_c.cands. replace (Z.to_nat (disco_table_c.n_of T)) with 0%nat by lia. reflexivity.
Qed.
Ltac arb_awr Usp Eout Hbo :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [azlit_tac|]
  | eapply awr_ok_cons_stack; [reflexivity | exact Usp | azlit_tac | azlit_tac |]
  | eapply awr_ok_cons_gen with (n := 15%nat);
    [ reflexivity | rewrite Eout; apply unsigned_lit_small; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; left; split;
      [ eexists; split; [left; reflexivity | cbn; lia] | do 2 eexists; split; [exact Hbo | lia] ]
    | ] ].

Ltac arb_win Usp Eout :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?Eout in Hrr;
      rewrite ?unsigned_lit_small in Hrr by lia; cbv beta; lia | ]);
  destruct Hin.

Ltac arb_rreg HS r H :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
  pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
  cbn [ms_regs restrict mkst] in H end.

Ltac arb_region HS i HR :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  let r := eval vm_compute in (nth_error (ss_mem ss) i) in
  lazymatch r with Some ?rr => pose proof (st_ok_pi_region_nth _ _ _ i rr HS ltac:(vm_compute; reflexivity)) as HR end end;
  cbn [ms_mem restrict] in HR.

Ltac arb_incl := let c := fresh "c" in let Hc := fresh "Hc" in
  intros c Hc; cbn [In ARB_STKA ARB_OUTA ARB_STKS] in Hc;
  repeat (destruct Hc as [<-|Hc]; [cbn [In]; repeat (first [left; reflexivity | right]) |]); destruct Hc.

Lemma arb_bge0 : forall E (m : nat) v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff m 0)) = negb (0 <? v).
Proof.
intros E m v H Hv. cbn [branch_taken sv_denot]. rewrite H, unsigned_lit_small, Z.add_0_r by lia.
unfold bv_lts. rewrite !YK11.bv_signed_small by (rewrite unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia. reflexivity.
Qed.


Ltac arb_meq Usp Eout Zs :=
  lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), MEQ : forall a, _ -> _ -> aview _ _ ?m1 a = aview _ _ ?m0 a |- _ =>
  let M := fresh "MEQ" in
  pose proof (arb_meq_step Ef rs H m0 m1 m2 Zs HFr ltac:(arb_win Usp Eout) MEQ) as M; clear MEQ; rename M into MEQ end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Ltac arb_cmn_tac HS HJ Usp AG E15 E32 H11 H13 :=
  split; [exact HJ|];
  split; [let a := fresh "a" in let Ha := fresh "Ha" in let N1 := fresh "N1" in let N2 := fresh "N2" in
    intros a Ha N1 N2; lazymatch goal with MEQ : forall a, _ -> _ -> aview _ _ _ a = aview _ _ _ a |- _ => apply MEQ; [exact Ha | cbv beta; tauto] end|];
  split; [let HRs := fresh "HRs" in arb_region HS 1%nat HRs; apply (arb_frameA _ _ _ _ _ _ HRs Usp AG); arb_incl|];
  split; [let HRo := fresh "HRo" in arb_region HS 0%nat HRo; apply (arb_outA _ _ _ _ _ HRo ltac:(rewrite E15; apply unsigned_lit_small; lia)
        ltac:(rewrite (AG 13%nat) by lia; exact H13)); arb_incl|];
  split; [let R := fresh "R" in arb_rreg HS (2%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite Usp; reflexivity|];
  split; [let R := fresh "R" in arb_rreg HS (3%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite (AG 3%nat) by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [let R := fresh "R" in arb_rreg HS (4%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite (AG 4%nat) by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
  split; [let R := fresh "R" in arb_rreg HS (9%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite (AG 11%nat) by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact H11|];
  (let R := fresh "R" in arb_rreg HS (24%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
Lemma arb_segA_t : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (Q : world SEGS -> config -> Prop),
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P -> t <> 0 ->
  (forall regs3 mem3 md3,
     arb_invL ly S W regs mem md t our fsm pace now out T P 0 None regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_L)) mem3 (seg_rom SEGS)) md3) Q) ->
  (forall regs3 mem3 md3,
     arb_invE ly S W regs mem md t our fsm pace now out T P None regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_E)) mem3 (seg_rom SEGS)) md3) Q) ->
  (forall regs3 mem3 md3,
     arb_invN ly S W regs mem md t our fsm pace now out T P regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_N)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_arbitrate) regs mem md) Q.
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P Q HA Ht0 HL HE HN.
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HPP).
destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis).
pose proof TOK as (TOK1 & _). unfold disco_table_c.tbl_T1 in TOK1.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
destruct (arbA_entry fq ly S W regs mem md ch t out bt Nt bo No T HPRE H10 H15 Rt Rout Hbo Hbo1 Hbo2 Ho4 Ht0 Hbt Hbt1 Hbt2 Ht8 LT GT TOK1 Hdis) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_ARBITRATE_STK [(out, out + 32)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (Ht16 & Ht4096 & Htceil & Htia & Htpres & _).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (blk_off_imgP _ _ _ _ _ _ bo No HAR Hbo) as Hoimg. pose proof (blk_off_imgP _ _ _ _ _ _ bt Nt HAR Hbt) as Htimg.
unfold off_img, IMG_LO, IMG_TOP in HcellR, HgotR, Hoimg, Htimg. cbv [A_OBJ Nat.add] in HcellR, HgotR.
remember (EA regs (disco_table_c.n_of T)) as E eqn:HEq.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EA; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbA_extra (disco_table_c.n_of T))) n)
  by (intros n Hn; subst E; unfold EA; apply Eimg_low; exact Hn).
assert (AG : forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n))).
{ intros n Hn. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; reflexivity).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite (AG 15%nat) by lia; exact H15).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat) by lia; exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (disco_table_c.n_of T)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
clear HEq EL.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_arbitrate)) with (Z_to_bv 64 (BASE + AF_both3_reac_arbitrate)).
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [ awr_ok_tac; try exact Usp | ].
{ eapply awr_ok_cons_gen with (n := 15%nat) (b := out); [reflexivity | rewrite E15; apply unsigned_lit_small; lia | | ].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. left. split.
    + exists (out, out + 32). split; [left; reflexivity | cbn; lia].
    + exists bo, No. split; [exact Hbo | lia].
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) HFr ltac:(arb_win Usp E15)) as K1. clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIGMA AS___asan_memset) (AMEMSET fq) W (ms_regs msX) (ms_mem msX)
     REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S _ 0 out 0 32 (-144) _ HJ) end.
  - rewrite Ra0, E15. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite Qsp, Usp. apply unsigned_lit_small. lia.
  - reflexivity.
  - lia.
  - rewrite WS. unfold ESTACK. lia.
  - rewrite Qgp, (AG 3%nat) by lia. exact Hgp.
  - rewrite Qtp, (AG 4%nat) by lia. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [right; left; split; [exists (out, out + 32); split; [left; reflexivity | cbn; lia] | exists bo, No; split; [exact Hbo | lia]] | unfold ESTACK; lia].
  - apply (amem_range_of_block SEGS B LAWS ly S W _ _ bo No out 32 (proj1 HJ) Hbo); lia.
  - apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bo No out 32 (proj1 HJ) Hbo); lia.
  - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bo No out 32 (proj1 HJ) Hbo); lia.
  - exact I. }
cbv beta. clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2 & HSM).
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) a ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha N. cbv beta in N. rewrite (Hfr a Ha) by (unfold ESTACK; lia). apply K1; [exact Ha | cbv beta; exact N]. }
clear K1.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 4]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [ | | | | apply Forall_nil].
  - eapply region_kept_aview; [exact Usp | | exact Hpres2].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
    [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot1)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell1)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | lia].
  - eapply region_kept_aview; [rewrite E10; apply unsigned_lit_small; lia | | exact Hpres2].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bo No (proj1 HJ2) Hbo) as (_ & _ & _ & _ & Hopres2 & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ea := Ev) in HS end.
assert (HEI2 : img_env VAL A_LIM Ea) by (subst Ea; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 512)%nat -> ew Ea n = ew E n) by (intros n Hn; subst Ea; rewrite YN3v.ew_havoc_old by lia; reflexivity).
clearbody Ea.
assert (AG2 : forall n, (n < 32)%nat -> ew Ea n = getr regs (Z_to_bv 5 (Z.of_nat n))) by (intros n Hn; rewrite OLD2 by lia; apply AG; exact Hn).
assert (E15b : ew Ea 15 = Z_to_bv 64 out) by (rewrite OLD2 by lia; exact E15).
assert (E10b : ew Ea 10 = Z_to_bv 64 t) by (rewrite OLD2 by lia; exact E10).
assert (E32b : ew Ea 32 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E32).
assert (E33b : ew Ea 33 = Z_to_bv 64 (disco_table_c.n_of T)) by (rewrite OLD2 by lia; exact E33).
assert (Uspb : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
 pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 15%nat) 0 32 0 32
   [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 4 (SLit 0));
    YP09.mkChunk 20 (CVal 4 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SLit 0))]) HS eq_refl) as HS3 end.
match type of HS3 with ?A -> ?Bq -> _ => assert (HRO : A); [|assert (HDJ : Bq); [|specialize (HS3 HRO HDJ); clear HRO HDJ]] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite E15b, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hopres2 (out + o) ltac:(lia))).
  + repeat apply Forall_cons; try apply Forall_nil;
    (eapply chunk_ok_val; [reflexivity | zside | zside | apply arb_val_mem_zero; intros i Hi; cbn in Hi;
     rewrite <- Z.add_assoc, Heff by lia; reflexivity]). }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
  cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E15b, E10b, Uspb, (HEI2 241%nat ltac:(unfold A_TEXT, A_LIM; lia)), (HEI2 253%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  rewrite !unsigned_lit_small by lia. repeat split; lia. }
clear HS SHOK. rename HS3 into HS.
assert (SHOK : sh_ok SEGS ARB_BX arbA_SH Ea (mrestrict (w_H W) mem2)).
{ constructor; [|constructor; [|constructor]].
  - apply (arb_shent ly S W mem2 md2 Ea 15 bo No out 0 32 (proj1 HJ2) Hbo); [apply arb_U_BX; exact E32b | apply arb_U_atom; [exact E15b | lia] | lia | lia | lia].
  - apply (arb_shent ly S W mem2 md2 Ea 10 bt Nt t 0 400 (proj1 HJ2) Hbt); [apply arb_U_BX; exact E32b | apply arb_U_atom; [exact E10b | lia] | lia | lia | lia]. }
paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arb_awr Uspb E15b Hbo |].
arb_meq Uspb E15b (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
- rewrite (arb_bge0 Ea 33 (disco_table_c.n_of T) E33b ltac:(lia)) in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arb_awr Uspb E15b Hbo |].
  arb_meq Uspb E15b (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
  assert (E12b : ew Ea 12 = Z_to_bv 64 fsm) by (rewrite (AG2 12%nat) by lia; exact H12).
  psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
  + rewrite (arb_est_br Ea 12 fsm E12b Rfsm) in Hc0.
    paj_run_to_tok RUNTO HS HJ2 SHOK ARB_SPAN 32804; [arb_awr Uspb E15b Hbo |].
    arb_meq Uspb E15b (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
    pmkst HS. change (BASE + 32804) with (BASE + AF_ARB_E). apply HE.
    split; [arb_cmn_tac HS HJ2 Uspb AG2 E15b E32b H11 H13|].
    split; [arb_rreg HS (18%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite E15b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [arb_rreg HS (19%bv : bv 5) R; rewrite R; reflexivity|].
    split; [arb_rreg HS (8%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite E10b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [symmetry; apply arb_best_n0; lia | exact Hc0].
  + rewrite (arb_est_br Ea 12 fsm E12b Rfsm) in Hc0.
    paj_run_to_tok RUNTO HS HJ2 SHOK ARB_SPAN 32948; [arb_awr Uspb E15b Hbo |].
    arb_meq Uspb E15b (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
    pmkst HS. change (BASE + 32948) with (BASE + AF_ARB_N). apply HN.
    split; [arb_cmn_tac HS HJ2 Uspb AG2 E15b E32b H11 H13|].
    split; [arb_rreg HS (18%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite E15b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [arb_rreg HS (20%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite E12b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [apply arb_best_n0; lia | exact Hc0].
- rewrite (arb_bge0 Ea 33 (disco_table_c.n_of T) E33b ltac:(lia)) in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK ARB_SPAN 32400; [arb_awr Uspb E15b Hbo |].
  arb_meq Uspb E15b (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
  assert (E12b : ew Ea 12 = Z_to_bv 64 fsm) by (rewrite (AG2 12%nat) by lia; exact H12).
  pmkst HS. change (BASE + 32400) with (BASE + AF_ARB_L). apply HL.
  split; [arb_cmn_tac HS HJ2 Uspb AG2 E15b E32b H11 H13|].
  split; [arb_region HS 1%nat HRs; apply (arb_slotsA Ea _ regs fsm out _ _ _ HRs Uspb E32b E15b E12b ltac:(lia)); arb_incl|].
  split; [arb_region HS 1%nat HRs; replace (spZ regs - 144 + 32) with (spZ regs + -112) by lia;
    apply (slot_of_region Ea _ (spZ regs) _ (-144) 0 _ _ (-112) (SLit ARB_STALE) ARB_STALE HRs Uspb);
    [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | unfold ARB_STALE; lia]|].
  split; [arb_rreg HS (8%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite E10b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
  split; [arb_rreg HS (18%bv : bv 5) R; rewrite R; reflexivity|].
  split; [arb_rreg HS (19%bv : bv 5) R; rewrite R; reflexivity|].
  split; [arb_rreg HS (20%bv : bv 5) R; rewrite R; apply (arb_s4_val Ea _ E33b); lia|].
  split; [arb_rreg HS (21%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite (AG2 14%nat) by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact H14|].
  split; [arb_rreg HS (25%bv : bv 5) R; rewrite R; reflexivity|].
  split; [arb_rreg HS (26%bv : bv 5) R; rewrite R; reflexivity|].
  split; [arb_rreg HS (27%bv : bv 5) R; rewrite R; exact (arb_xor_val Ea t E10b Rt)|].
  split; [reflexivity|]. split; [exact Ht0|]. lia.
Qed.
Definition arbA0_regions : smem :=
  [ stack_region 144; got_regionP; bcell_regionP 32; YP09.mkRegion (Some 15%nat) 0 32 0 32 [] ].
Definition arbA0_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0 0 0);
            (15%nat, mkAF 4096 140737479966720 2); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_arbA0 : sstate := mkSS AF_both3_reac_arbitrate sr_atoms arbA0_regions None arbA0_facts.
Definition arbA0_SH : list shent := [ mkSHE 15 0 32 ].
Definition EA0 (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SB]).

Lemma arbA0_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (out bo No : Z),
  afn_pre SEGS B REAC_ARBITRATE_STK ly S W regs mem md ch ->
  getr regs 10 = w64 0 -> getr regs 15 = w64 out -> 0 < out < 2 ^ 64 ->
  In (bo, No) (ablocks B ly S) -> bo <= out -> out + 32 <= bo + req_size No -> out mod 4 = 0 ->
  st_ok_pi (fx := fq) SEGS VAL (EA0 regs) ss_arbA0
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_reac_arbitrate)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS ARB_BX arbA0_SH (EA0 regs) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch out bo No HPRE H10 H15 Rout Hbo Hbo1 Hbo2 Ho4.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ bo No HAR Hbo) as Hoimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold off_img, IMG_LO, IMG_TOP in HcellR, HgotR, Hoimg.
rewrite restrict_mkst_fx.
set (E := EA0 regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n)
  by (intros n Hn; subst E; unfold EA0; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Eo66 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EA0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold EA0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_arbA0. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold arbA0_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo1) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Eo66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo66) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 ARB_BX SB);
      [cbn [sv_denot ARB_BX]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. unfold SB. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 15%nat out E15) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hopres (out + o) ltac:(lia))).
  + apply pairwise_disjoint_of_extents. unfold arbA0_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 15%nat out E15) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo1) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo66) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Hoceil Hoia Hoimg Ho4096 Hbo1 Hbo2 C1 C3 WS Hstk0 HcellR HgcD HgotR.
    clear. unfold in_app. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [arbA0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E15, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hoceil Ho4096 Hbo1 Hbo2 Hal16 Ho4 C1 C3 WS Hstk0.
    clear. unfold SB. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, arbA0_SH. constructor; [|constructor].
  apply (arb_shent ly S W mem md E 15 bo No out 0 32 HAR Hbo); [apply arb_U_BX; exact E32 | apply arb_U_atom; [exact E15 | lia] | lia | lia | lia].
Qed.

Lemma arb_segA_0 : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (Q : world SEGS -> config -> Prop),
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P -> t = 0 ->
  (forall regs3 mem3 md3,
     arb_invL ly S W regs mem md t our fsm pace now out T P 0 None regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_L)) mem3 (seg_rom SEGS)) md3) Q) ->
  (forall regs3 mem3 md3,
     arb_invE ly S W regs mem md t our fsm pace now out T P None regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_E)) mem3 (seg_rom SEGS)) md3) Q) ->
  (forall regs3 mem3 md3,
     arb_invN ly S W regs mem md t our fsm pace now out T P regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_N)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_arbitrate) regs mem md) Q.
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P Q HA Ht0 HL HE HN.
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HPP).
subst t.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
destruct (arbA0_entry fq ly S W regs mem md ch out bo No HPRE H10 H15 Rout Hbo Hbo1 Hbo2 Ho4) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_ARBITRATE_STK [(out, out + 32)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (blk_off_imgP _ _ _ _ _ _ bo No HAR Hbo) as Hoimg.
unfold off_img, IMG_LO, IMG_TOP in HcellR, HgotR, Hoimg. cbv [A_OBJ Nat.add] in HcellR, HgotR.
remember (EA0 regs) as E eqn:HEq.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EA0; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n)
  by (intros n Hn; subst E; unfold EA0; apply Eimg_low; exact Hn).
assert (AG : forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n))).
{ intros n Hn. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; reflexivity).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite (AG 15%nat) by lia; exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (rewrite (AG 10%nat) by lia; exact H10).
clear HEq EL.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_arbitrate)) with (Z_to_bv 64 (BASE + AF_both3_reac_arbitrate)).
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [ awr_ok_tac; try exact Usp | ].
{ eapply awr_ok_cons_gen with (n := 15%nat) (b := out); [reflexivity | rewrite E15; apply unsigned_lit_small; lia | | ].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. left. split.
    + exists (out, out + 32). split; [left; reflexivity | cbn; lia].
    + exists bo, No. split; [exact Hbo | lia].
  - apply awr_ok_nil. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) HFr ltac:(arb_win Usp E15)) as K1. clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIGMA AS___asan_memset) (AMEMSET fq) W (ms_regs msX) (ms_mem msX)
     REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S _ 0 out 0 32 (-144) _ HJ) end.
  - rewrite Ra0, E15. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite Qsp, Usp. apply unsigned_lit_small. lia.
  - reflexivity.
  - lia.
  - rewrite WS. unfold ESTACK. lia.
  - rewrite Qgp, (AG 3%nat) by lia. exact Hgp.
  - rewrite Qtp, (AG 4%nat) by lia. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [right; left; split; [exists (out, out + 32); split; [left; reflexivity | cbn; lia] | exists bo, No; split; [exact Hbo | lia]] | unfold ESTACK; lia].
  - apply (amem_range_of_block SEGS B LAWS ly S W _ _ bo No out 32 (proj1 HJ) Hbo); lia.
  - apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bo No out 32 (proj1 HJ) Hbo); lia.
  - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bo No out 32 (proj1 HJ) Hbo); lia.
  - exact I. }
cbv beta. clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2 & HSM).
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) a ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha N. cbv beta in N. rewrite (Hfr a Ha) by (unfold ESTACK; lia). apply K1; [exact Ha | cbv beta; exact N]. }
clear K1.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [ | | | apply Forall_nil].
  - eapply region_kept_aview; [exact Usp | | exact Hpres2].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
    [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot1)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell1)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bo No (proj1 HJ2) Hbo) as (_ & _ & _ & _ & Hopres2 & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ea := Ev) in HS end.
assert (HEI2 : img_env VAL A_LIM Ea) by (subst Ea; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 512)%nat -> ew Ea n = ew E n) by (intros n Hn; subst Ea; rewrite YN3v.ew_havoc_old by lia; reflexivity).
clearbody Ea.
assert (AG2 : forall n, (n < 32)%nat -> ew Ea n = getr regs (Z_to_bv 5 (Z.of_nat n))) by (intros n Hn; rewrite OLD2 by lia; apply AG; exact Hn).
assert (E15b : ew Ea 15 = Z_to_bv 64 out) by (rewrite OLD2 by lia; exact E15).
assert (E32b : ew Ea 32 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E32).
assert (E10b : ew Ea 10 = Z_to_bv 64 0) by (rewrite OLD2 by lia; exact E10).
assert (Uspb : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
 pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 15%nat) 0 32 0 32
   [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 4 (SLit 0));
    YP09.mkChunk 20 (CVal 4 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SLit 0))]) HS eq_refl) as HS3 end.
match type of HS3 with ?A -> ?Bq -> _ => assert (HRO : A); [|assert (HDJ : Bq); [|specialize (HS3 HRO HDJ); clear HRO HDJ]] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite E15b, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hopres2 (out + o) ltac:(lia))).
  + repeat apply Forall_cons; try apply Forall_nil;
    (eapply chunk_ok_val; [reflexivity | zside | zside | apply arb_val_mem_zero; intros i Hi; cbn in Hi;
     rewrite <- Z.add_assoc, Heff by lia; reflexivity]). }
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
  cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E15b, Uspb, (HEI2 241%nat ltac:(unfold A_TEXT, A_LIM; lia)), (HEI2 253%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  rewrite !unsigned_lit_small by lia. repeat split; lia. }
clear HS SHOK. rename HS3 into HS.
assert (SHOK : sh_ok SEGS ARB_BX arbA0_SH Ea (mrestrict (w_H W) mem2)).
{ constructor; [|constructor].
  apply (arb_shent ly S W mem2 md2 Ea 15 bo No out 0 32 (proj1 HJ2) Hbo); [apply arb_U_BX; exact E32b | apply arb_U_atom; [exact E15b | lia] | lia | lia | lia]. }
paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arb_awr Uspb E15b Hbo |].
arb_meq Uspb E15b (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
2: { exfalso. rewrite branch_eq_U, (U_atom Ea 10 0 E10b ltac:(lia)), U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arb_awr Uspb E15b Hbo |].
arb_meq Uspb E15b (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
assert (E12b : ew Ea 12 = Z_to_bv 64 fsm) by (rewrite (AG2 12%nat) by lia; exact H12).
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
- change BC_NE with (neg_bc BC_EQ) in Hc0. rewrite branch_taken_neg, (arb_est_br Ea 12 fsm E12b Rfsm) in Hc0. apply negb_true_iff in Hc0.
  paj_run_to_tok RUNTO HS HJ2 SHOK ARB_SPAN 32948; [arb_awr Uspb E15b Hbo |].
  arb_meq Uspb E15b (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
  pmkst HS. change (BASE + 32948) with (BASE + AF_ARB_N). apply HN.
  split; [arb_cmn_tac HS HJ2 Uspb AG2 E15b E32b H11 H13|].
  split; [arb_rreg HS (18%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite E15b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
  split; [arb_rreg HS (20%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite E12b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
  split; [reflexivity | exact Hc0].
- change BC_NE with (neg_bc BC_EQ) in Hc0. rewrite branch_taken_neg, (arb_est_br Ea 12 fsm E12b Rfsm) in Hc0. apply negb_false_iff in Hc0.
  paj_run_to_tok RUNTO HS HJ2 SHOK ARB_SPAN 32804; [arb_awr Uspb E15b Hbo |].
  arb_meq Uspb E15b (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
  pmkst HS. change (BASE + 32804) with (BASE + AF_ARB_E). apply HE.
  split; [arb_cmn_tac HS HJ2 Uspb AG2 E15b E32b H11 H13|].
  split; [arb_rreg HS (18%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite E15b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
  split; [arb_rreg HS (19%bv : bv 5) R; rewrite R; reflexivity|].
  split; [arb_rreg HS (8%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite E10b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
  split; [reflexivity | exact Hc0].
Qed.

Definition ARB_SEGA : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (Q : world SEGS -> config -> Prop),
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  (forall regs3 mem3 md3,
     arb_invL ly S W regs mem md t our fsm pace now out T P 0 None regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_L)) mem3 (seg_rom SEGS)) md3) Q) ->
  (forall regs3 mem3 md3,
     arb_invE ly S W regs mem md t our fsm pace now out T P None regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_E)) mem3 (seg_rom SEGS)) md3) Q) ->
  (forall regs3 mem3 md3,
     arb_invN ly S W regs mem md t our fsm pace now out T P regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_N)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_arbitrate) regs mem md) Q.

Lemma arb_segA : ARB_SEGA.
Proof.
unfold ARB_SEGA.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P Q HA HL HE HN.
destruct (Z.eq_dec t 0) as [Ht0|Ht0].
- exact (arb_segA_0 fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P Q HA Ht0 HL HE HN).
- exact (arb_segA_t fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P Q HA Ht0 HL HE HN).
Qed.

Lemma arb_val_mem_keep : forall H (m m' : word -> option byte) a (n : nat) v,
  (forall k, 0 <= k < Z.of_nat n -> aview SEGS H m' (a + k) = aview SEGS H m (a + k)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v HK HV j Hj. rewrite <- (HV j Hj).
pose proof (HK (Z.of_nat j) ltac:(lia)) as Hq. unfold aview in Hq.
destruct (mbyte SEGS (mrestrict H m') (a + Z.of_nat j)) as [b1|] eqn:E1;
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat j)) as [b2|] eqn:E2; cbn in Hq; try discriminate; [|reflexivity].
injection Hq as Hq. f_equal. apply bv_eq. exact Hq.
Qed.

Lemma arb_garr8_keep : forall H (m m' : word -> option byte) a (l : list Z),
  (forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS H m' (a + k) = aview SEGS H m (a + k)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
intros H m m' a l HK HG j Hj. destruct (HG j Hj) as [HV HR]. split; [|exact HR].
apply (arb_val_mem_keep H m m' (a + Z.of_nat j) 1 _); [|exact HV].
intros k Hk. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply HK. lia.
Qed.

Definition ARB_LBX : sv := SOff 24 0.
Definition arbL_regions : smem :=
  [ YP09.mkRegion (Some 2%nat) 0 144 0 0
      [YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 32 (CVal 8 (SLit 5000000000))];
    YP09.mkRegion (Some 32%nat) 0 48 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 (SOff 34 0))] ].
Definition arbL_atoms : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 4096 140737479966720 3); (18%nat, mkAF 2 2 0);
    (20%nat, mkAF 48 384 4); (24%nat, mkAF SB SB 0); (25%nat, mkAF 432 432 0);
    (26%nat, mkAF 0 336 4); (27%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0); (32%nat, mkAF 4096 140737479966720 3);
    (33%nat, mkAF 0 (2 ^ 32 - 1) 0) ].
Definition arbL_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 8 0) (SOff 26 0), SOff 32 0) ].
Definition ss_arbL0 : sstate := mkSS AF_ARB_L sr_atoms arbL_regions None (mkFacts ((19%nat, mkAF 0 0 0) :: arbL_atoms) [] arbL_alias).
Definition arbL_SH0 : list shent := [ mkSHE 32 0 48 ].
Definition arbL_best : YP09.region := YP09.mkRegion (Some 19%nat) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 37 0))].
Definition ss_arbL1 : sstate :=
  mkSS AF_ARB_L sr_atoms (arbL_regions ++ [arbL_best]) None (mkFacts ((19%nat, mkAF 4096 140737479966720 3) :: arbL_atoms) [] arbL_alias).
Definition arbL_SH1 : list shent := [ mkSHE 32 0 48; mkSHE 19 40 48 ].
Definition arbL_extra (e role last fsm out lastb : Z) : list word := map (Z_to_bv 64) [e; role; last; fsm; out; lastb].
Definition arb_lastb (T : list byte) (b : option Z) : Z := match b with Some j => disco_table_c.last_of T j | None => 0 end.
Definition EL (regs3 : bvmap 5 word) (t i out fsm : Z) (T : list byte) (b : option Z) : env :=
  Eimg (Ereg regs3 (arbL_extra (t + 48 * i) (disco_table_c.role_of_e T i mod 2 ^ 32) (disco_table_c.last_of T i)
    (fsm mod 2 ^ 64) out (arb_lastb T b))).

Lemma arb_role_range : forall (T : list byte) i, - 2 ^ 31 <= disco_table_c.role_of_e T i < 2 ^ 31.
Proof.
intros T i. unfold disco_table_c.role_of_e, disco_table_c.s32_at, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
pose proof (Z.mod_pos_bound (disco_table_c.u_at T (48 * i + 8) 4 + 2147483648) 4294967296 ltac:(lia)). lia.
Qed.

Lemma arbL_U_sub : forall E a c, ew E 21 = Z_to_bv 64 a -> ew E 34 = Z_to_bv 64 c -> 0 <= a < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> c < a ->
  U E (SAlu ALU_ADD (SOff 21 0) (SMd M_MUL (SOff 34 0) (SLit (-1)))) = a - c.
Proof.
intros E a c Ha Hc Ra Rc Hac. unfold U. cbn [sv_denot]. rewrite Ha, Hc, !Z.add_0_r, !Z_to_bv_bv_unsigned.
rewrite zmd64_sound, zalu64_sound, unsigned_lit. unfold zalu64, zmd64. cbn [zalu_raw zmd_raw].
rewrite !(zcanon_small a), !(zcanon_small c) by lia. change (zcanon (-1)) with (2 ^ 64 - 1).
unfold zcanon, M64. Z.div_mod_to_equations. nia.
Qed.

Lemma arb_sub_nth : forall (T : list byte) (j w k : nat), (k < w)%nat ->
  nth_error (disco_table_c.sub T (Z.of_nat j) w) k = nth_error T (j + k).
Proof. intros T j w k Hk. unfold disco_table_c.sub. rewrite Nat2Z.id, nth_error_firstn. destruct (Nat.ltb_spec k w); [|lia]. apply nth_error_skipn. Qed.

Lemma arb_garr8_nth : forall (m : word -> option byte) base (L : list byte) j b,
  garr8 SEGS m base (map (fun b0 : byte => bv_unsigned b0) L) -> nth_error L j = Some b ->
  mbyte SEGS m (base + Z.of_nat j) = Some b.
Proof.
intros m base L j b G Hj.
assert (Hl : (j < length L)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite (garr8_mbyte SEGS m base _ j G) by (rewrite length_map; exact Hl).
f_equal. rewrite (nth_error_nth (map (fun b0 : byte => bv_unsigned b0) L) j 0 (map_nth_error _ j L Hj)). apply Z_to_bv_bv_unsigned.
Qed.

Lemma arb_aview_nth : forall H (m : word -> option byte) base (L : list byte) j b,
  garr8 SEGS (mrestrict H m) base (map (fun b0 : byte => bv_unsigned b0) L) -> nth_error L j = Some b ->
  aview SEGS H m (base + Z.of_nat j) = Some (bv_unsigned b).
Proof. intros H m base L j b G Hj. unfold aview. rewrite (arb_garr8_nth _ base L j b G Hj). reflexivity. Qed.

Lemma arb_aview_some : forall H (m : word -> option byte) base (L : list byte) a,
  garr8 SEGS (mrestrict H m) base (map (fun b0 : byte => bv_unsigned b0) L) -> base <= a < base + Z.of_nat (length L) ->
  aview SEGS H m a <> None.
Proof.
intros H m base L a G Ha.
destruct (nth_error L (Z.to_nat (a - base))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
replace a with (base + Z.of_nat (Z.to_nat (a - base))) by lia. rewrite (arb_aview_nth H m base L _ b G Hb). discriminate.
Qed.

Lemma arb_mac : forall H (m : word -> option byte) t p (T P : list byte) i,
  length T = 400%nat -> length P = 6%nat -> 0 <= i <= 7 ->
  garr8 SEGS (mrestrict H m) t (map (fun b0 : byte => bv_unsigned b0) T) -> garr8 SEGS (mrestrict H m) p (map (fun b0 : byte => bv_unsigned b0) P) ->
  ((forall i0, 0 <= i0 < 6 -> aview SEGS H m (t + 48 * i + i0) = aview SEGS H m (p + i0)) <-> disco_table_c.mac_of T i = P).
Proof.
intros H m t p T P i LT LP Ri GT GP. unfold disco_table_c.mac_of.
assert (NT : forall k, (k < 6)%nat -> nth_error (disco_table_c.sub T (48 * i) 6) k = nth_error T (Z.to_nat (48 * i) + k)).
{ intros k Hk. replace (48 * i) with (Z.of_nat (Z.to_nat (48 * i))) at 1 by lia. apply arb_sub_nth. exact Hk. }
assert (VT : forall k b, nth_error T (Z.to_nat (48 * i) + k) = Some b -> aview SEGS H m (t + 48 * i + Z.of_nat k) = Some (bv_unsigned b)).
{ intros k b Hb. replace (t + 48 * i + Z.of_nat k) with (t + Z.of_nat (Z.to_nat (48 * i) + k)) by lia. exact (arb_aview_nth H m t T _ b GT Hb). }
assert (VP : forall k b, nth_error P k = Some b -> aview SEGS H m (p + Z.of_nat k) = Some (bv_unsigned b)).
{ intros k b Hb. exact (arb_aview_nth H m p P k b GP Hb). }
split.
- intros HE. apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k 6) as [Hk|Hk].
  + rewrite (NT k Hk).
    destruct (nth_error T (Z.to_nat (48 * i) + k)) as [b1|] eqn:E1; [|apply nth_error_None in E1; lia].
    destruct (nth_error P k) as [b2|] eqn:E2; [|apply nth_error_None in E2; lia].
    pose proof (HE (Z.of_nat k) ltac:(lia)) as Hq. rewrite (VT k b1 E1), (VP k b2 E2) in Hq.
    injection Hq as Hq. f_equal. apply bv_eq. exact Hq.
  + assert (LS : length (disco_table_c.sub T (48 * i) 6) = 6%nat) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn, LT; lia).
    rewrite (proj2 (nth_error_None (disco_table_c.sub T (48 * i) 6) k) ltac:(lia)), (proj2 (nth_error_None P k) ltac:(lia)). reflexivity.
- intros HE i0 Hi0. pose proof (NT (Z.to_nat i0) ltac:(lia)) as Hn. rewrite HE in Hn.
  destruct (nth_error P (Z.to_nat i0)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  replace i0 with (Z.of_nat (Z.to_nat i0)) by lia. rewrite (VP _ b Eb). symmetry in Hn. rewrite (VT _ b Hn). reflexivity.
Qed.

Lemma arbL_mac_bool : forall (v : word) (T P : list byte) i,
  (v = w64 0 <-> disco_table_c.mac_of T i = P) -> (bv_unsigned v =? 0) = reac_arbitrate_c.bytes_eqb (disco_table_c.mac_of T i) P.
Proof.
intros v T P i HX. apply Bool.eq_iff_eq_true. rewrite Z.eqb_eq, reac_arbitrate.bytes_eqb_true, <- HX.
unfold w64. split; intros H.
- apply bv_eq. rewrite H. reflexivity.
- rewrite H. reflexivity.
Qed.

Lemma arbL_shent : forall ly S W mem md E (m : nat) b n p lo hi,
  AR SEGS B ly S W mem md -> In (b, n) (ablocks B ly S) ->
  ew E 24 = Z_to_bv 64 SB -> ew E m = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> b <= p + lo -> p + hi <= b + req_size n -> 0 <= lo <= hi ->
  shent_ok SEGS ARB_LBX E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
intros ly S W mem md E m b n p lo hi HAR Hin H24 Hm Hp H1 H2 H3.
destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hin) as (_ & _ & _ & Hia & _).
apply (shent_ok_of_range SEGS (w_H W) mem E ARB_LBX m (p + lo) (hi - lo) p lo hi).
- apply (range_addressable_of_block SEGS B LAWS ly S W mem md b n (p + lo) (hi - lo) HAR Hin); lia.
- unfold U, ARB_LBX. cbn [sv_denot]. rewrite H24, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- intros x Hx. revert Hia H1 H2 H3 Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.

Lemma arb_frame_keep : forall H (m m' : word -> option byte) (regs : bvmap 5 word),
  (forall a, spZ regs - 144 <= a < spZ regs -> aview SEGS H m' a = aview SEGS H m a) ->
  arb_frame (mrestrict H m) regs -> arb_frame (mrestrict H m') regs.
Proof.
intros H m m' regs HK HF p Hp. apply (arb_val_mem_keep H m m' _ 8 _); [|exact (HF p Hp)].
intros k Hk. apply HK. cbn [ARB_SAVES In] in Hp.
repeat (destruct Hp as [<-|Hp]; [cbn [fst]; lia|]). destruct Hp.
Qed.

Lemma arb_slots_keep : forall H (m m' : word -> option byte) (regs : bvmap 5 word) fsm out,
  (forall a, spZ regs - 144 <= a < spZ regs -> aview SEGS H m' a = aview SEGS H m a) ->
  arb_slots (mrestrict H m) regs fsm out -> arb_slots (mrestrict H m') regs fsm out.
Proof.
intros H m m' regs fsm out HK (S0 & S8 & S16 & S24).
split; [|split; [|split]]; (eapply (arb_val_mem_keep H m m'); [intros k Hk; apply HK; lia | eassumption]).
Qed.

Lemma arbL_cmn_step : forall ly S W (regs : bvmap 5 word) mem md our pace out regs3 mem3 md3 (regs4 : bvmap 5 word) mem4 md4,
  arb_cmn ly S W regs mem md our pace out regs3 mem3 md3 ->
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S W mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (fun a => spZ regs - REAC_ARBITRATE_STK <= a < spZ regs - 144) a ->
     aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a) ->
  0 <= out -> out + 32 <= spZ regs - REAC_ARBITRATE_STK -> spZ regs < 2 ^ 64 ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 9 = getr regs3 9 -> getr regs4 24 = getr regs3 24 ->
  arb_cmn ly S W regs mem md our pace out regs4 mem4 md4.
Proof.
intros ly S W regs mem md our pace out regs3 mem3 md3 regs4 mem4 md4
  (HJ & HK & HFR & HOUT & R2 & R3 & R4 & R9 & R24) HJ4 HV Ho0 Hos Hsp Q2 Q3 Q4 Q9 Q24.
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
split; [exact HJ4|].
split; [intros a Ha Hno Hns; rewrite (HV a Ha) by (cbv beta; lia); exact (HK a Ha Hno Hns)|].
split; [apply (arb_frame_keep (w_H W) mem3 mem4 regs); [intros a Ha; apply HV; [lia | cbv beta; lia] | exact HFR]|].
split; [apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact HOUT];
  assert (Hl : length (arb_out0 pace) = 32%nat) by (unfold arb_out0; rewrite length_map; reflexivity);
  rewrite Hl; intros a Ha; apply HV; [lia | cbv beta; lia]|].
rewrite Q2, Q3, Q4, Q9, Q24. tauto.
Qed.

Lemma arb_swrap_mod : forall u, 0 <= u < 2 ^ 32 -> bv_swrap 32 u mod 2 ^ 32 = u.
Proof.
intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
change (4294967296 / 2) with 2147483648. change (2 ^ 32) with 4294967296.
Z.div_mod_to_equations. lia.
Qed.

Lemma arb_u_range : forall (T : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length T) ->
  0 <= disco_table_c.u_at T k n < 2 ^ (8 * Z.of_nat n).
Proof.
intros T k n Hk Hkn. unfold disco_table_c.u_at.
assert (Hl : length (disco_table_c.sub T k n) = n).
{ unfold disco_table_c.sub. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k n)). pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k n)). rewrite Hl in *. lia.
Qed.

Lemma arb_role_mod : forall (T : list byte) i, length T = 400%nat -> 0 <= i < 8 ->
  disco_table_c.role_of_e T i mod 2 ^ 32 = disco_table_c.u_at T (48 * i + 8) 4.
Proof.
intros T i LT Hi. unfold disco_table_c.role_of_e, disco_table_c.s32_at. apply arb_swrap_mod.
pose proof (arb_u_range T (48 * i + 8) 4 ltac:(lia) ltac:(rewrite LT; lia)) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R. exact R.
Qed.

Lemma arb_scanz_range : forall T P our now i j, reac_arbitrate.scanz T P our now i = Some j -> 0 <= j < i.
Proof. exact reac_arbitrate.scanz_range. Qed.

Lemma arbL_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (i : Z) (b : option Z) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invL ly S W regs mem md t our fsm pace now out T P i b regs3 mem3 md3 ->
  (b = None ->
   st_ok_pi (fx := fq) SEGS VAL (EL regs3 t i out fsm T b) ss_arbL0
     (restrict (w_H W) (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_L)) mem3 (seg_rom SEGS)))
   /\ sh_ok SEGS ARB_LBX arbL_SH0 (EL regs3 t i out fsm T b) (mrestrict (w_H W) mem3)) /\
  (forall j, b = Some j ->
   st_ok_pi (fx := fq) SEGS VAL (EL regs3 t i out fsm T b) ss_arbL1
     (restrict (w_H W) (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_L)) mem3 (seg_rom SEGS)))
   /\ sh_ok SEGS ARB_LBX arbL_SH1 (EL regs3 t i out fsm T b) (mrestrict (w_H W) mem3)).
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b regs3 mem3 md3 HA HI.
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HPP).
pose proof HI as (HC & HSL & H32s & G8 & G18 & G19 & G20 & G21 & G25 & G26 & G27 & Hb & Ht0 & Hi).
pose proof HC as (HJ & MEQ & HFR & HOUT & G2 & G3 & G4 & G9 & G24).
pose proof HSL as (S0 & S8 & S16 & S24).
destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis).
pose proof TOK as (TOK1 & _). unfold disco_table_c.tbl_T1 in TOK1.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
pose proof (proj1 HJ) as HAR3.
destruct (al_blocks _ _ LAWS ly S W mem3 md3 bt Nt HAR3 Hbt) as (Ht16 & Ht4096 & Htceil & Htia & Htpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ bt Nt HAR3 Hbt) as Htimg.
unfold off_img, IMG_LO, IMG_TOP in Htimg.
assert (GT3 : garr8 SEGS (mrestrict (w_H W) mem3) t (map (fun b0 : byte => bv_unsigned b0) T)).
{ apply (arb_garr8_keep (w_H W) mem mem3 t _); [|exact GT]. rewrite length_map, LT. intros k Hk.
  apply MEQ; revert Hk Hdis Htia Htceil Ht4096 Hbt1 Hbt2 Hslo Hceil Hstk0 Hshi H47 WS C1 C3 Rt Rout; clear; unfold in_app; intros; lia. }
assert (Hbr : 0 <= reac_arbitrate.baddr t b < 140737479966720 /\ reac_arbitrate.baddr t b mod 8 = 0 /\
  (forall j, b = Some j -> 0 <= j < i /\ reac_arbitrate.baddr t b = t + 48 * j) /\ (b = None -> reac_arbitrate.baddr t b = 0)).
{ destruct b as [j|].
  - pose proof (arb_scanz_range T P our now i j (eq_sym Hb)) as Rj. cbn [reac_arbitrate.baddr].
    split; [revert Rj Hi TOK1 Htceil Ht4096 Hbt1 Hbt2 C1; clear; intros; lia|].
    split; [rewrite Z.add_mod, Ht8 by lia; replace (48 * j) with (8 * (6 * j)) by lia; rewrite Z.mul_comm, Z_mod_mult; reflexivity|].
    split; [intros j' Hj'; injection Hj' as <-; split; [lia | reflexivity] | discriminate].
  - cbn [reac_arbitrate.baddr]. split; [lia|]. split; [reflexivity|]. split; [discriminate | reflexivity]. }
destruct Hbr as (Rb & Rb8 & HbS & HbN).
rewrite restrict_mkst_fx.
set (E := EL regs3 t i out fsm T b).
assert (EL0 : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs3 (arbL_extra (t + 48 * i) (disco_table_c.role_of_e T i mod 2 ^ 32) (disco_table_c.last_of T i)
    (fsm mod 2 ^ 64) out (arb_lastb T b))) n) by (intros n Hn; subst E; unfold EL; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 144).
{ rewrite EL0 by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), G2. apply unsigned_lit_small. lia. }
assert (E8 : ew E 8 = Z_to_bv 64 t) by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl); exact G8).
assert (E18 : ew E 18 = Z_to_bv 64 2) by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 18 18%bv eq_refl); exact G18).
assert (E19 : ew E 19 = Z_to_bv 64 (reac_arbitrate.baddr t b)) by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 19 19%bv eq_refl); exact G19).
assert (E20 : ew E 20 = Z_to_bv 64 (48 * disco_table_c.n_of T)) by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 20 20%bv eq_refl); exact G20).
assert (E24 : ew E 24 = Z_to_bv 64 SB) by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 24 24%bv eq_refl); exact G24).
assert (E25 : ew E 25 = Z_to_bv 64 432) by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 25 25%bv eq_refl); exact G25).
assert (E26 : ew E 26 = Z_to_bv 64 (48 * i)) by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 26 26%bv eq_refl); exact G26).
assert (E27 : ew E 27 = Z_to_bv 64 (2 ^ 64 - 1 - t)) by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 27 27%bv eq_refl); exact G27).
assert (E32 : ew E 32 = Z_to_bv 64 (t + 48 * i)) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (disco_table_c.role_of_e T i mod 2 ^ 32)) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (disco_table_c.last_of T i)) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (fsm mod 2 ^ 64)) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 out) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (arb_lastb T b)) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 5)).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hrole : disco_table_c.role_of_e T i mod 2 ^ 32 = disco_table_c.u_at T (48 * i + 8) 4) by (apply arb_role_mod; [exact LT | lia]).
assert (Rrole : 0 <= disco_table_c.role_of_e T i mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
assert (Rlast : 0 <= disco_table_c.last_of T i < 2 ^ 64).
{ pose proof (arb_u_range T (48 * i + 40) 8 ltac:(lia) ltac:(rewrite LT; lia)) as R. unfold disco_table_c.last_of. exact R. }
split.
{ intros HbN0. split.
- unfold ss_arbL0. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold arbL_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 144) 16 8 (SOff 35 0) (fsm mod 2 ^ 64));
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (Z.mod_pos_bound fsm (2 ^ 64) ltac:(lia)); zside | zside | exact S16].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 144) 24 8 (SOff 36 0) out);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact S24].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 144) 32 8 (SLit 5000000000) ARB_STALE);
         [reflexivity | unfold ARB_STALE; zside | zside | exact H32s].
    * rewrite (VB 32%nat (t + 48 * i) E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ (t + 48 * i) 8 4 (SOff 33 0) (disco_table_c.role_of_e T i mod 2 ^ 32));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | zside |].
         rewrite Hrole. replace (t + 48 * i + 8) with (t + (48 * i + 8)) by lia. unfold disco_table_c.u_at.
         apply val_mem_garr8_sub; [exact GT3 | lia | rewrite LT; lia].
      -- apply (chunk_ok_val SEGS E _ (t + 48 * i) 40 8 (SOff 34 0) (disco_table_c.last_of T i));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside |].
         replace (t + 48 * i + 40) with (t + (48 * i + 40)) by lia. unfold disco_table_c.last_of, disco_table_c.u_at.
         apply val_mem_garr8_sub; [exact GT3 | lia | rewrite LT; lia].
  + apply pairwise_disjoint_of_extents. unfold arbL_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 32%nat (t + 48 * i) E32) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Htceil Htia Htimg Ht4096 Hbt1 Hbt2 C1 C3 WS Hstk0 Hi TOK1. clear. unfold in_app. intros. repeat split; lia.
  + split; [|split; [exact I | split; [|exact I]]].
    * cbn [f_atoms arbL_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E8, E18, E19, E20, E24, E25, E26, E27, E32, E33.
      rewrite !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      assert (Hsp16 : (spZ regs - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
      assert (H48n : (48 * disco_table_c.n_of T) mod 16 = 0) by (replace (48 * disco_table_c.n_of T) with (16 * (3 * disco_table_c.n_of T)) by lia; rewrite Z.mul_comm, Z_mod_mult; reflexivity).
      assert (H48i : (48 * i) mod 16 = 0) by (replace (48 * i) with (16 * (3 * i)) by lia; rewrite Z.mul_comm, Z_mod_mult; reflexivity).
      assert (He8 : (t + 48 * i) mod 8 = 0) by (rewrite Z.add_mod, Ht8 by lia; replace (48 * i) with (8 * (6 * i)) by lia; rewrite Z.mul_comm, Z_mod_mult; reflexivity).
      rewrite (HbN HbN0) in *.
      revert Hslo Hshi H47 Hceil Htceil Htia Ht4096 Hbt1 Hbt2 C1 C3 WS Hstk0 Hi TOK1 Rt Ht8 Hsp16 H48n H48i He8 Rrole.
      clear. unfold SB, in_app. intros. repeat match goal with |- _ /\ _ => split end; lia.
    * cbn [f_alias arbL_alias]. cbn [sv_denot]. rewrite E8, E26, E32, !Z.add_0_r, !Z_to_bv_bv_unsigned.
      rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw]. rewrite Z_to_bv64_canon.
      rewrite (zcanon_small t), (zcanon_small (48 * i)) by lia. reflexivity.
- unfold sh_ok, arbL_SH0. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem3 E ARB_LBX 32 t 400 (t + 48 * i) 0 48).
  + apply (range_addressable_of_block SEGS B LAWS ly S W mem3 md3 bt Nt t 400 HAR3 Hbt); lia.
  + unfold U, ARB_LBX. cbn [sv_denot]. rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. revert Htia Hbt1 Hbt2 Hx Hi TOK1. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
}
{ intros j HbS0. pose proof (HbS j HbS0) as (Rj & Hbj). split.
- unfold ss_arbL1. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold arbL_regions, arbL_best. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 144) 16 8 (SOff 35 0) (fsm mod 2 ^ 64));
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (Z.mod_pos_bound fsm (2 ^ 64) ltac:(lia)); zside | zside | exact S16].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 144) 24 8 (SOff 36 0) out);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact S24].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 144) 32 8 (SLit 5000000000) ARB_STALE);
         [reflexivity | unfold ARB_STALE; zside | zside | exact H32s].
    * rewrite (VB 32%nat (t + 48 * i) E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ (t + 48 * i) 8 4 (SOff 33 0) (disco_table_c.role_of_e T i mod 2 ^ 32));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | zside |].
         rewrite Hrole. replace (t + 48 * i + 8) with (t + (48 * i + 8)) by lia. unfold disco_table_c.u_at.
         apply val_mem_garr8_sub; [exact GT3 | lia | rewrite LT; lia].
      -- apply (chunk_ok_val SEGS E _ (t + 48 * i) 40 8 (SOff 34 0) (disco_table_c.last_of T i));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside |].
         replace (t + 48 * i + 40) with (t + (48 * i + 40)) by lia. unfold disco_table_c.last_of, disco_table_c.u_at.
         apply val_mem_garr8_sub; [exact GT3 | lia | rewrite LT; lia].
    * rewrite (VB 19%nat (t + 48 * j)) by first [rewrite E19, Hbj; reflexivity | lia]. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (t + 48 * j) 40 8 (SOff 37 0) (disco_table_c.last_of T j));
      [cbn [sv_denot]; rewrite E37, HbS0, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | zside |].
      { pose proof (arb_u_range T (48 * j + 40) 8 ltac:(lia) ltac:(rewrite LT; lia)) as R. unfold disco_table_c.last_of. exact R. }
      replace (t + 48 * j + 40) with (t + (48 * j + 40)) by lia. unfold disco_table_c.last_of, disco_table_c.u_at.
      apply val_mem_garr8_sub; [exact GT3 | lia | rewrite LT; lia].
  + apply pairwise_disjoint_of_extents. unfold arbL_regions, arbL_best, extent_of_region. cbn [app].
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 32%nat (t + 48 * i) E32) by lia.
    rewrite (VB 19%nat (t + 48 * j)) by first [rewrite E19, Hbj; reflexivity | lia].
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Htceil Htia Htimg Ht4096 Hbt1 Hbt2 C1 C3 WS Hstk0 Hi TOK1 Rj. clear. unfold in_app. intros. repeat split; lia.
  + split; [|split; [exact I | split; [|exact I]]].
    * cbn [f_atoms arbL_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E8, E18, E19, E20, E24, E25, E26, E27, E32, E33.
      rewrite !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      assert (Hsp16 : (spZ regs - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
      assert (H48n : (48 * disco_table_c.n_of T) mod 16 = 0) by (replace (48 * disco_table_c.n_of T) with (16 * (3 * disco_table_c.n_of T)) by lia; rewrite Z.mul_comm, Z_mod_mult; reflexivity).
      assert (H48i : (48 * i) mod 16 = 0) by (replace (48 * i) with (16 * (3 * i)) by lia; rewrite Z.mul_comm, Z_mod_mult; reflexivity).
      assert (He8 : (t + 48 * i) mod 8 = 0) by (rewrite Z.add_mod, Ht8 by lia; replace (48 * i) with (8 * (6 * i)) by lia; rewrite Z.mul_comm, Z_mod_mult; reflexivity).
      rewrite Hbj in *.
      assert (Hj8 : (t + 48 * j) mod 8 = 0) by (rewrite Z.add_mod, Ht8 by lia; replace (48 * j) with (8 * (6 * j)) by lia; rewrite Z.mul_comm, Z_mod_mult; reflexivity).
      revert Hslo Hshi H47 Hceil Htceil Htia Ht4096 Hbt1 Hbt2 C1 C3 WS Hstk0 Hi TOK1 Rt Ht8 Hsp16 H48n H48i He8 Rrole Rj Hj8.
      clear. unfold SB, in_app. intros. repeat match goal with |- _ /\ _ => split end; lia.
    * cbn [f_alias arbL_alias]. cbn [sv_denot]. rewrite E8, E26, E32, !Z.add_0_r, !Z_to_bv_bv_unsigned.
      rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw]. rewrite Z_to_bv64_canon.
      rewrite (zcanon_small t), (zcanon_small (48 * i)) by lia. reflexivity.
- unfold sh_ok, arbL_SH1. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem3 E ARB_LBX 32 t 400 (t + 48 * i) 0 48).
    * apply (range_addressable_of_block SEGS B LAWS ly S W mem3 md3 bt Nt t 400 HAR3 Hbt); lia.
    * unfold U, ARB_LBX. cbn [sv_denot]. rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. revert Htia Hbt1 Hbt2 Hx Hi TOK1. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem3 E ARB_LBX 19 t 400 (t + 48 * j) 40 48).
    * apply (range_addressable_of_block SEGS B LAWS ly S W mem3 md3 bt Nt t 400 HAR3 Hbt); lia.
    * unfold U, ARB_LBX. cbn [sv_denot]. rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E19, Hbj, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. revert Htia Hbt1 Hbt2 Hx Hi TOK1 Rj. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia. }
Qed.

Definition arb_post_cfg (fq : YK11.FPState) (pc : Z) (regs3 : bvmap 5 word) mem3 md3 : config :=
  mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + pc)) mem3 (seg_rom SEGS)) md3.

Definition ARB_SEGL : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (i : Z) (b : option Z) (regs3 : bvmap 5 word) mem3 md3
    (Q : world SEGS -> config -> Prop),
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invL ly S W regs mem md t our fsm pace now out T P i b regs3 mem3 md3 ->
  (forall regs4 mem4 md4,
     arb_invL ly S W regs mem md t our fsm pace now out T P (i + 1) (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 ->
     SRr SEGS W (arb_post_cfg fq AF_ARB_L regs4 mem4 md4) Q) ->
  (forall regs4 mem4 md4,
     arb_invE ly S W regs mem md t our fsm pace now out T P (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 ->
     SRr SEGS W (arb_post_cfg fq AF_ARB_E regs4 mem4 md4) Q) ->
  (forall regs4 mem4 md4,
     arb_invN ly S W regs mem md t our fsm pace now out T P regs4 mem4 md4 ->
     SRr SEGS W (arb_post_cfg fq AF_ARB_N regs4 mem4 md4) Q) ->
  (forall j regs4 mem4 md4,
     arb_invB ly S W regs mem md t our fsm pace now out T P j regs4 mem4 md4 ->
     SRr SEGS W (arb_post_cfg fq AF_ARB_B regs4 mem4 md4) Q) ->
  SRr SEGS W (arb_post_cfg fq AF_ARB_L regs3 mem3 md3) Q.

Definition ARB_SEGE : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (b : option Z) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invE ly S W regs mem md t our fsm pace now out T P b regs3 mem3 md3 ->
  SRr SEGS W (arb_post_cfg fq AF_ARB_E regs3 mem3 md3) (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).

Definition ARB_SEGN : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invN ly S W regs mem md t our fsm pace now out T P regs3 mem3 md3 ->
  SRr SEGS W (arb_post_cfg fq AF_ARB_N regs3 mem3 md3) (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).

Definition ARB_SEGB : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (j : Z) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invB ly S W regs mem md t our fsm pace now out T P j regs3 mem3 md3 ->
  SRr SEGS W (arb_post_cfg fq AF_ARB_B regs3 mem3 md3) (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).


Lemma arb_segL : ARB_SEGL.
Proof.
unfold ARB_SEGL.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b regs3 mem3 md3 Q HA HI HL HE HN HB.
destruct (arbL_entry fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b regs3 mem3 md3 HA HI) as [HE0 HE1].
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HPP).
pose proof HI as (HC & HSL & H32s & G8 & G18 & G19 & G20 & G21 & G25 & G26 & G27 & Hb & Ht0 & Hi).
pose proof HC as (HJ & MEQ0 & HFR & HOUT & G2 & G3 & G4 & G9 & G24).
destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis).
pose proof TOK as (TOK1 & _). unfold disco_table_c.tbl_T1 in TOK1.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (Ht16 & Ht4096 & Htceil & Htia & Htpres & _).
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
assert (KT : 4096 <= t /\ t + 400 <= alloc_ceiling) by lia.
assert (KO : 4096 <= out /\ out + 32 <= alloc_ceiling) by lia.
assert (KS : alloc_ceiling + 8336 <= spZ regs /\ spZ regs <= 2 ^ 47 /\ spZ regs mod 16 = 0) by (rewrite WS in Hstk0; lia).
assert (KC : alloc_ceiling <= 140737479966720) by lia.
assert (KP : our <> 0 -> exists Np', In (bp, Np') (ablocks B ly S) /\ 4096 <= our /\ our + 6 <= alloc_ceiling /\ length P = 6%nat /\
   garr8 SEGS (mrestrict (w_H W) mem) our (map (fun b0 : byte => bv_unsigned b0) P) /\ bp <= our /\ our + 6 <= bp + req_size Np').
{ intros Hour. destruct (HPP Hour) as (Hbp & Hbp1 & Hbp2 & LP & GP & Hpd).
  destruct (al_blocks _ _ LAWS ly S W mem md bp Np HAR Hbp) as (_ & Hp4096 & Hpceil & _). exists Np.
  split; [exact Hbp|]. split; [lia|]. split; [lia|]. split; [exact LP|]. split; [exact GP|]. split; lia. }
assert (MEQ3 : forall a, 0 <= a < 2 ^ 64 -> ~ (fun a => spZ regs - REAC_ARBITRATE_STK <= a < spZ regs - 144) a ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by (intros; reflexivity).
assert (Rrole : - 2 ^ 31 <= disco_table_c.role_of_e T i < 2 ^ 31) by apply arb_role_range.
assert (Rlast : 0 <= disco_table_c.last_of T i < 2 ^ 64).
{ pose proof (arb_u_range T (48 * i + 40) 8 ltac:(lia) ltac:(rewrite LT; lia)) as R. unfold disco_table_c.last_of. exact R. }
assert (EL0 : forall bb n, (n < A_TEXT)%nat -> ew (EL regs3 t i out fsm T bb) n =
  ew (Ereg regs3 (arbL_extra (t + 48 * i) (disco_table_c.role_of_e T i mod 2 ^ 32) (disco_table_c.last_of T i) (fsm mod 2 ^ 64) out (arb_lastb T bb))) n)
  by (intros bb n Hn; unfold EL; apply Eimg_low; exact Hn).
assert (EE2 : forall bb, bv_unsigned (ew (EL regs3 t i out fsm T bb) 2) = spZ regs - 144).
{ intros bb. rewrite EL0 by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), G2. apply unsigned_lit_small. lia. }
assert (EE3 : forall bb, ew (EL regs3 t i out fsm T bb) 3 = getr regs 3) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 3 3%bv eq_refl); exact G3).
assert (EE4 : forall bb, ew (EL regs3 t i out fsm T bb) 4 = getr regs 4) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 4 4%bv eq_refl); exact G4).
assert (EE8 : forall bb, ew (EL regs3 t i out fsm T bb) 8 = Z_to_bv 64 t) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl); exact G8).
assert (EE9 : forall bb, ew (EL regs3 t i out fsm T bb) 9 = Z_to_bv 64 our) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl); exact G9).
assert (EE18 : forall bb, ew (EL regs3 t i out fsm T bb) 18 = Z_to_bv 64 2) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 18 18%bv eq_refl); exact G18).
assert (EE19 : ew (EL regs3 t i out fsm T b) 19 = Z_to_bv 64 (reac_arbitrate.baddr t b)) by (rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 19 19%bv eq_refl); exact G19).
assert (EE20 : forall bb, ew (EL regs3 t i out fsm T bb) 20 = Z_to_bv 64 (48 * disco_table_c.n_of T)) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 20 20%bv eq_refl); exact G20).
assert (EE21 : forall bb, ew (EL regs3 t i out fsm T bb) 21 = Z_to_bv 64 now) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 21 21%bv eq_refl); exact G21).
assert (EE24 : forall bb, ew (EL regs3 t i out fsm T bb) 24 = Z_to_bv 64 SB) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 24 24%bv eq_refl); exact G24).
assert (EE25 : forall bb, ew (EL regs3 t i out fsm T bb) 25 = Z_to_bv 64 432) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 25 25%bv eq_refl); exact G25).
assert (EE26 : forall bb, ew (EL regs3 t i out fsm T bb) 26 = Z_to_bv 64 (48 * i)) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 26 26%bv eq_refl); exact G26).
assert (EE27 : forall bb, ew (EL regs3 t i out fsm T bb) 27 = Z_to_bv 64 (2 ^ 64 - 1 - t)) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 27 27%bv eq_refl); exact G27).
assert (EE32 : forall bb, ew (EL regs3 t i out fsm T bb) 32 = Z_to_bv 64 (t + 48 * i)) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (EE33 : forall bb, ew (EL regs3 t i out fsm T bb) 33 = Z_to_bv 64 (disco_table_c.role_of_e T i mod 2 ^ 32)) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (EE34 : forall bb, ew (EL regs3 t i out fsm T bb) 34 = Z_to_bv 64 (disco_table_c.last_of T i)) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
assert (EE35 : forall bb, ew (EL regs3 t i out fsm T bb) 35 = Z_to_bv 64 fsm).
{ intros bb; rewrite EL0 by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs3 _ 3). apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. }
assert (EE36 : forall bb, ew (EL regs3 t i out fsm T bb) 36 = Z_to_bv 64 out) by (intros bb; rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 4)).
assert (EE37 : ew (EL regs3 t i out fsm T b) 37 = Z_to_bv 64 (arb_lastb T b)) by (rewrite EL0 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 5)).
assert (EEr : forall bb n, (n < 32)%nat -> ew (EL regs3 t i out fsm T bb) n = getr regs3 (Z_to_bv 5 (Z.of_nat n))).
{ intros bb n Hn. rewrite EL0 by (unfold A_TEXT; lia). apply ew_Ereg_nat. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
clear EL0.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold arb_post_cfg. unfold arb_post_cfg in HL, HE, HN, HB.
assert (HEIb : forall bb, img_env VAL A_LIM (EL regs3 t i out fsm T bb)) by (intros bb; unfold EL; apply Eimg_env).
let rec go := idtac;
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 32552; [awr_ok_tac |];
  arb_meq Usp Usp (fun a => spZ regs - REAC_ARBITRATE_STK <= a < spZ regs - 144);
  lazymatch goal with
  | HS' : st_ok _ _ (setpc ?ssx _) (restrict _ _) |- _ => call; go
  | HS' : st_ok_pi _ _ ?Ec ?ss _, SHOK' : sh_ok _ ?Bx ?SH _ _ |- _ =>
      let pc := eval vm_compute in (ss_pc ss) in
      lazymatch pc with
      | 32552 => next
      | _ => psrr_branch_tok RUN BR HS' SHOK' ARB_SPAN; [conv; go | conv; go]
      end
  end end
with conv := idtac;
  lazymatch goal with
  | Hc : branch_taken BC_NE (sv_denot ?Ex (SExt true 32 (SOff 33 0))) (sv_denot ?Ex (SOff 18 0)) = _ |- _ =>
    let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew Ex n = ew _ n |- _ => H end in
    rewrite branch_ne_U, (U_atom Ex 18 2 (eq_trans (AG 18%nat ltac:(lia)) (EE18 _)) ltac:(lia)),
      (U_sx32_eqk_s Ex 33 _ 2 (eq_trans (AG 33%nat ltac:(lia)) (EE33 _)) Rrole ltac:(lia)) in Hc;
    apply (f_equal negb) in Hc; rewrite negb_involutive in Hc; cbn [negb] in Hc;
    let F := fresh "Frole" in rename Hc into F
  | Hc : branch_taken BC_EQ (sv_denot ?Ex (SOff 9 0)) (sv_denot ?Ex (SLit 0)) = _ |- _ =>
    let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew Ex n = ew _ n |- _ => H end in
    rewrite branch_eq_U, (U_atom Ex 9 our (eq_trans (AG 9%nat ltac:(lia)) (EE9 _)) Rour), YI04.U_lit in Hc by lia;
    let F := fresh "Four" in rename Hc into F
  | Hc : branch_taken BC_GEU (sv_denot ?Ex (SOff 34 0)) (sv_denot ?Ex (SOff 21 0)) = _ |- _ =>
    let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew Ex n = ew _ n |- _ => H end in
    rewrite branch_geu_U, (U_atom Ex 34 _ (eq_trans (AG 34%nat ltac:(lia)) (EE34 _)) Rlast),
      (U_atom Ex 21 now (eq_trans (AG 21%nat ltac:(lia)) (EE21 _)) Rnow) in Hc;
    apply (f_equal negb) in Hc; rewrite negb_involutive in Hc; cbn [negb] in Hc;
    let F := fresh "Fnow" in rename Hc into F
  | Hc : branch_taken BC_LTU (sv_denot ?Ex (SLit 5000000000)) (sv_denot ?Ex (SAlu ALU_ADD (SOff 21 0) (SMd M_MUL (SOff 34 0) (SLit (-1))))) = _,
    Fn : (disco_table_c.last_of T i <? now) = true |- _ =>
    let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew Ex n = ew _ n |- _ => H end in
    rewrite branch_ltu_U, YI04.U_lit, (arbL_U_sub Ex now _ (eq_trans (AG 21%nat ltac:(lia)) (EE21 _)) (eq_trans (AG 34%nat ltac:(lia)) (EE34 _)) Rnow Rlast (proj1 (Z.ltb_lt _ _) Fn)) in Hc by lia;
    change 5000000000 with reac_arbitrate_c.REAC_DISCO_STALE_NS in Hc;
    let F := fresh "Fst" in rename Hc into F
  | Hc : branch_taken BC_EQ (sv_denot ?Ex (SOff 19 0)) (sv_denot ?Ex (SLit 0)) = _ |- _ =>
    let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew Ex n = ew _ n |- _ => H end in
    rewrite branch_eq_U, (U_atom Ex 19 0 (eq_trans (AG 19%nat ltac:(lia)) EE19) ltac:(lia)), YI04.U_lit in Hc by lia;
    first [ exfalso; discriminate Hc | let F := fresh "Fs3" in rename Hc into F ]
  | Hc : branch_taken BC_GEU (sv_denot ?Ex (SOff 37 0)) (sv_denot ?Ex (SOff 34 0)) = _ |- _ =>
    let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew Ex n = ew _ n |- _ => H end in
    rewrite branch_geu_U, (U_atom Ex 37 _ (eq_trans (AG 37%nat ltac:(lia)) EE37) Rlastb),
      (U_atom Ex 34 _ (eq_trans (AG 34%nat ltac:(lia)) (EE34 _)) Rlast) in Hc;
    cbn [arb_lastb] in Hc;
    apply (f_equal negb) in Hc; rewrite negb_involutive in Hc; cbn [negb] in Hc;
    let F := fresh "Fcmp" in rename Hc into F
  | Hc : branch_taken BC_EQ (sv_denot ?Ex (SOff ?k 0)) (sv_denot ?Ex (SLit 0)) = _, EV : ew ?Ex ?k = ?v, XC : ?v = w64 0 <-> _ |- _ =>
    rewrite branch_eq_U, YI04.U_lit, U_SOff, EV, Z.add_0_r, zcanon_unsigned in Hc by lia;
    rewrite (arbL_mac_bool v T P i XC) in Hc;
    let F := fresh "Fmac" in rename Hc into F
  end
with call := idtac;
  lazymatch goal with HS : st_ok _ ?Ec ?ssc (restrict (w_H W) ?msX), HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOKc : sh_ok _ _ ?SHc _ _, Fo : (our =? 0) = false |- _ =>
  let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew Ec n = ew _ n |- _ => H end in
  let E0 := lazymatch type of AG with forall n, _ -> ew Ec n = ew ?e n => e end in
  let HEIc := lazymatch goal with H : img_env _ _ Ec |- _ => H end in
  let MEQc := lazymatch goal with H : forall a, _ -> _ -> aview _ _ (ms_mem msX) a = aview _ _ mem3 a |- _ => H end in
  let K := run_K_hi HS in
  let K4 := eval vm_compute in (K + 4)%nat in
  let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
  let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
  prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
  prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
  rewrite (eq_trans (AG 32%nat ltac:(lia)) (EE32 _)) in Ra0;
  rewrite (eq_trans (AG 9%nat ltac:(lia)) (EE9 _)) in Ra1;
  rewrite (eq_trans (AG 3%nat ltac:(lia)) (EE3 _)) in Qgp;
  rewrite (eq_trans (AG 4%nat ltac:(lia)) (EE4 _)) in Qtp;
  let HspU := fresh "HspU" in
  assert (HspU : spZ (ms_regs msX) = spZ regs + -144) by (unfold spZ at 1; rewrite Qsp; try rewrite (AG 2%nat ltac:(lia)); rewrite (EE2 _); lia);
  let Hour := fresh "Hour" in assert (Hour : our <> 0) by (apply Z.eqb_neq; exact Fo);
  let Np' := fresh "Np'" in let Hbp' := fresh "Hbp'" in let Kp1 := fresh "Kp1" in let Kp2 := fresh "Kp2" in
  let LP := fresh "LP" in let GP := fresh "GP" in let Hbp1' := fresh "Hbp1'" in let Hbp2' := fresh "Hbp2'" in
  destruct (KP Hour) as (Np' & Hbp' & Kp1 & Kp2 & LP & GP & Hbp1' & Hbp2');
  let HtP := fresh "HtP" in let HpP := fresh "HpP" in
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bt Nt (proj1 HJc) Hbt) as (_ & _ & _ & _ & HtP & _);
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bp Np' (proj1 HJc) Hbp') as (_ & _ & _ & _ & HpP & _);
  pmkst HS;
  eapply SRr_bind;
  [ eapply (aj_bcmp_at (fx := fq) SEGS B LAWS pa_segs_low (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fq) W (ms_regs msX) (ms_mem msX)
      REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S _ 0 (t + 48 * i) our 6 (-144) _ HJc);
    [ rewrite Ra0; reflexivity | rewrite Ra1; reflexivity | rewrite Ra2; reflexivity | lia | lia | lia | lia | lia
    | rewrite HspU; lia | reflexivity | lia | rewrite WS; unfold ESTACK; lia
    | rewrite Qgp; exact Hgp | rewrite Qtp; exact Htp | exact Rra | apply ret_ok_codeptr_v; [lia | reflexivity]
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HtP a ltac:(lia))) | rewrite HspU; unfold ESTACK; lia]
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HpP a ltac:(lia))) | rewrite HspU; unfold ESTACK; lia]
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold ESTACK; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold ESTACK; lia
    | apply (amem_range_of_block SEGS B LAWS ly S W _ _ bt Nt (t + 48 * i) 6 (proj1 HJc) Hbt); lia
    | apply (amem_range_of_block SEGS B LAWS ly S W _ _ bp Np' our 6 (proj1 HJc) Hbp'); lia
    | apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bt Nt (t + 48 * i) 6 (proj1 HJc) Hbt); lia
    | intros _; apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bt Nt (t + 48 * i) 6 (proj1 HJc) Hbt); lia
    | apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bp Np' our 6 (proj1 HJc) Hbp'); lia
    | intros _; apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bp Np' our 6 (proj1 HJc) Hbp'); lia ]
  | cbv beta; clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp;
    let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
    let v := fresh "v" in let HJ2 := fresh "HJ2" in let HP2 := fresh "HP2" in let Hv := fresh "Hv" in let Hcmp := fresh "Hcmp" in
    let Hfr2 := fresh "Hfr2" in let Hpres2 := fresh "Hpres2" in let HPost := fresh "HPost" in
    intros W2 c2 _ HPost; destruct HPost as (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2);
    let XC := fresh "XC" in
    assert (XC : v = w64 0 <-> disco_table_c.mac_of T i = P);
    [ rewrite Hcmp; apply (arb_mac (w_H W) (ms_mem msX) t our T P i LT LP ltac:(lia));
      [ apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem); [|exact GT]; rewrite length_map, LT;
        let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; rewrite MEQc by (cbv beta; lia); apply MEQ0; lia
      | apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem); [|exact GP]; rewrite length_map, LP;
        let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; rewrite MEQc by (cbv beta; lia); apply MEQ0; lia ]
    | ];
    let MEQ2 := fresh "MEQ" in
    assert (MEQ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (fun a => spZ regs - REAC_ARBITRATE_STK <= a < spZ regs - 144) a ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let N := fresh "N" in
      intros a Ha N; cbv beta in N; rewrite (Hfr2 a Ha) by (unfold ESTACK; lia); apply MEQc; [exact Ha | cbv beta; exact N]
    | ];
    let idxs := lazymatch SHc with arbL_SH1 => constr:([0; 1; 2]%nat) | arbL_SH0 => constr:([0; 1]%nat) end in
    let HS2 := fresh "HS" in
    jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 idxs HS2;
    match type of HS2 with ?tt -> _ => let HRK := fresh in assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end;
    [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
      (eapply region_kept_aview;
       [ first [ try rewrite (AG 2%nat ltac:(lia)); apply EE2
               | rewrite (eq_trans (AG 32%nat ltac:(lia)) (EE32 _)); apply unsigned_lit_small; lia
               | rewrite (eq_trans (AG 19%nat ltac:(lia)) EE19); cbn [reac_arbitrate.baddr]; apply unsigned_lit_small; lia ]
       | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr2; [lia | unfold ESTACK; lia]
       | exact Hpres2 ])
    | clear HS; rewrite <- restrict_mkst_fx in HS2;
      lazymatch type of HS2 with st_ok_pi _ _ ?En _ _ =>
      let Ea := fresh "Ea" in
      set (Ea := En) in HS2;
      let HEIa := fresh "HEI" in let AGa := fresh "AG" in let EV := fresh "EV" in let SHOK2 := fresh "SHOK" in
      assert (HEIa : img_env VAL A_LIM Ea) by (subst Ea; apply img_env_havoc_hi; [exact HEIc | cbv; lia]);
      assert (AGa : forall n, (n < 512)%nat -> ew Ea n = ew E0 n) by (intros nn Hnn; subst Ea; rewrite ew_havoc_old by lia; apply AG; exact Hnn);
      assert (EV : ew Ea K4 = v) by (subst Ea; change K4 with (K + 4)%nat; rewrite (ew_havoc_new Ec K _ 4 (Z_to_bv 64 0)) by (cbn; lia); exact Hv);
      clearbody Ea;
      assert (SHOK2 : sh_ok SEGS ARB_LBX SHc Ea (mrestrict (w_H W) mem2));
      [ unfold arbL_SH0, arbL_SH1; repeat apply Forall_cons; try apply Forall_nil;
        first [ apply (arbL_shent ly S W mem2 md2 Ea 32 bt Nt (t + 48 * i) 0 48 (proj1 HJ2) Hbt);
                [rewrite AGa by lia; apply EE24 | rewrite AGa by lia; apply EE32 | lia | lia | lia | lia]
              | apply (arbL_shent ly S W mem2 md2 Ea 19 bt Nt (t + 48 * j) 40 48 (proj1 HJ2) Hbt);
                [rewrite AGa by lia; apply EE24 | rewrite AGa by lia; exact EE19 | lia | lia | lia | lia] ]
      | clear HJc SHOKc MEQc HEIc Hcmp Hfr2 Hpres2 HP2 Hv ]
      end ] ]
  end
with next := idtac;
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss _, Hb0 : ?b0 = reac_arbitrate.scanz T P our now i |- _ =>
  let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew Ec n = ew _ n |- _ => H end in
  let s3 := eval vm_compute in (sr_get (ss_regs ss) 19%bv) in
  let HB' := fresh "HB'" in
  lazymatch s3 with
  | SOff 32 0 => assert (HB' : reac_arbitrate.scanz T P our now (i + 1) = Some i)
  | SOff 19 0 => assert (HB' : reac_arbitrate.scanz T P our now (i + 1) = b0)
  end;
  [ rewrite reac_arbitrate.scanz_succ by lia; rewrite <- Hb0; unfold reac_arbitrate.stp, reac_arbitrate_c.cand, reac_arbitrate_c.stale;
    cbv beta iota;
    repeat match goal with
    | F : (?x =? ?y) = _ |- context [?x =? ?y] => rewrite F
    | F : (?x <? ?y) = _ |- context [?x <? ?y] => rewrite F
    | F : reac_arbitrate_c.bytes_eqb ?x ?y = _ |- context [reac_arbitrate_c.bytes_eqb ?x ?y] => rewrite F
    end;
    cbn [andb orb negb]; reflexivity
  | lazymatch goal with HS0 : st_ok_pi _ _ _ _ _, HJ0 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK0 : sh_ok _ _ _ _ _ |- _ =>
      paj_run_tok RUN HS0 HJ0 SHOK0 ARB_SPAN; [awr_ok_tac |] end;
    arb_meq Usp Usp (fun a => spZ regs - REAC_ARBITRATE_STK <= a < spZ regs - 144);
    lazymatch goal with HS1 : st_ok_pi _ _ _ _ _, SHOK1 : sh_ok _ _ _ _ _ |- _ => psrr_branch_tok RUN BR HS1 SHOK1 ARB_SPAN end;
    [ backT | backF ] ]
  end
with backconv := idtac;
  lazymatch goal with Hc : branch_taken BC_NE (sv_denot ?Ex (SOff 20 0)) (sv_denot ?Ex (SOff 26 48)) = _ |- _ =>
    let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew Ex n = ew _ n |- _ => H end in
    rewrite branch_ne_U, (U_atom Ex 20 _ (eq_trans (AG 20%nat ltac:(lia)) (EE20 _)) ltac:(lia)),
      (U_atom_off Ex 26 (48 * i) 48 (eq_trans (AG 26%nat ltac:(lia)) (EE26 _)) ltac:(lia) ltac:(lia)) in Hc
  end
with backT := idtac;
  backconv;
  lazymatch goal with Hc : negb (48 * disco_table_c.n_of T =? 48 * i + 48) = true |- _ =>
    apply negb_true_iff, Z.eqb_neq in Hc; let Hn1 := fresh "Hn1" in assert (Hn1 : i + 1 < disco_table_c.n_of T) by lia; clear Hc end;
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 32400; [awr_ok_tac |] end;
  arb_meq Usp Usp (fun a => spZ regs - REAC_ARBITRATE_STK <= a < spZ regs - 144);
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => pmkst HS end;
  change (BASE + 32400) with (BASE + AF_ARB_L); apply HL; leafL
with backF := idtac;
  backconv;
  lazymatch goal with Hc : negb (48 * disco_table_c.n_of T =? 48 * i + 48) = false |- _ =>
    apply negb_false_iff, Z.eqb_eq in Hc; let Hn1 := fresh "Hn1" in assert (Hn1 : i + 1 = disco_table_c.n_of T) by lia; clear Hc end;
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_tok RUN HS HJ SHOK ARB_SPAN; [awr_ok_tac |] end;
  arb_meq Usp Usp (fun a => spZ regs - REAC_ARBITRATE_STK <= a < spZ regs - 144);
  lazymatch goal with HS1 : st_ok_pi _ _ _ _ _, SHOK1 : sh_ok _ _ _ _ _ |- _ => psrr_branch_tok RUN BR HS1 SHOK1 ARB_SPAN end;
  [ estconv;
    lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
      paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 32804; [awr_ok_tac |] end;
    arb_meq Usp Usp (fun a => spZ regs - REAC_ARBITRATE_STK <= a < spZ regs - 144);
    lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => pmkst HS end;
    change (BASE + 32804) with (BASE + AF_ARB_E); apply HE; leafE
  | estconv;
    lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
      paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 32604; [awr_ok_tac |] end;
    arb_meq Usp Usp (fun a => spZ regs - REAC_ARBITRATE_STK <= a < spZ regs - 144);
    lazymatch goal with HS : st_ok_pi _ _ _ ?ssx _, SHOK : sh_ok _ _ _ _ _ |- _ =>
      let pc := eval vm_compute in (ss_pc ssx) in
      lazymatch pc with
      | 32604 => pmkst HS; change (BASE + 32604) with (BASE + AF_ARB_B);
                 lazymatch goal with HB'' : reac_arbitrate.scanz T P our now (i + 1) = Some ?jx |- _ => apply (HB jx); leafB end
      | _ => psrr_branch_tok RUN BR HS SHOK ARB_SPAN;
             [ conv;
               lazymatch goal with HS2 : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK2 : sh_ok _ _ _ _ _ |- _ =>
                 paj_run_to_tok RUNTO HS2 HJ SHOK2 ARB_SPAN 32948; [awr_ok_tac |] end;
               arb_meq Usp Usp (fun a => spZ regs - REAC_ARBITRATE_STK <= a < spZ regs - 144);
               lazymatch goal with HS2 : st_ok_pi _ _ _ _ _ |- _ => pmkst HS2 end;
               change (BASE + 32948) with (BASE + AF_ARB_N); apply HN; leafN
             | conv ]
      end
    end ]
with estconv := idtac;
  lazymatch goal with Hc : branch_taken BC_EQ (sv_denot ?Ex (SAlu ALU_AND (SOff 35 0) (SLit (-2)))) (sv_denot ?Ex (SLit 2)) = _ |- _ =>
    let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew Ex n = ew _ n |- _ => H end in
    rewrite (arb_est_br Ex 35 fsm (eq_trans (AG 35%nat ltac:(lia)) (EE35 _)) Rfsm) in Hc;
    let F := fresh "Fest" in rename Hc into F
  end
with rget r := idtac;
  lazymatch goal with HS : st_ok_pi _ _ ?Ec _ _ |- _ =>
    let R := fresh "R" in prreg HS r R; rewrite R; clear R end
with evv n EE := idtac;
  lazymatch goal with HS : st_ok_pi _ _ ?Ec _ _ |- _ =>
    let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew Ec n = ew _ n |- _ => H end in
    first [rewrite (eq_trans (AG n ltac:(lia)) (EE _)) | rewrite (eq_trans (AG n ltac:(lia)) EE)] end
with rsame r n := idtac;
  rget r;
  lazymatch goal with HS : st_ok_pi _ _ ?Ec _ _ |- _ =>
    let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew Ec n = ew _ n |- _ => H end in
    rewrite (eq_trans (AG n ltac:(lia)) (EEr _ n ltac:(lia))) end;
  reflexivity
with cmnL := idtac;
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m4 _ _, MEQ : forall a, _ -> _ -> aview _ _ ?m4 a = aview _ _ mem3 a |- _ =>
    eapply (arbL_cmn_step ly S W regs mem md our pace out regs3 mem3 md3 _ _ _ HC HJ MEQ);
    [ lia | lia | lia | rsame (2%bv : bv 5) 2%nat | rsame (3%bv : bv 5) 3%nat | rsame (4%bv : bv 5) 4%nat
    | rsame (9%bv : bv 5) 9%nat | rsame (24%bv : bv 5) 24%nat ] end
with s3get := idtac;
  rget (19%bv : bv 5);
  first [ evv 19%nat EE19 | evv 32%nat EE32 ]; reflexivity
with leafL := idtac;
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m4 _ _, MEQ : forall a, _ -> _ -> aview _ _ ?m4 a = aview _ _ mem3 a,
    HB' : reac_arbitrate.scanz T P our now (i + 1) = _ |- _ =>
  split; [cmnL|];
  split; [apply (arb_slots_keep (w_H W) mem3 m4 regs fsm out); [let a := fresh "a" in intros a ?; apply MEQ; [lia | cbv beta; lia] | exact HSL]|];
  split; [apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 m4); [let a := fresh "a" in intros a ?; apply MEQ; [lia | cbv beta; lia] | exact H32s]|];
  split; [rget (8%bv : bv 5); evv 8%nat EE8; reflexivity|];
  split; [rget (18%bv : bv 5); evv 18%nat EE18; reflexivity|];
  split; [rewrite HB'; s3get|];
  split; [rget (20%bv : bv 5); evv 20%nat EE20; reflexivity|];
  split; [rget (21%bv : bv 5); evv 21%nat EE21; reflexivity|];
  split; [rget (25%bv : bv 5); evv 25%nat EE25; reflexivity|];
  split; [rget (26%bv : bv 5); evv 26%nat EE26; rewrite unsigned_lit_small by lia; f_equal; lia|];
  split; [rget (27%bv : bv 5); evv 27%nat EE27; reflexivity|];
  split; [reflexivity|]; split; [exact Ht0 | lia]
  end
with leafE := idtac;
  lazymatch goal with Fe : arb_est fsm = true, HB' : reac_arbitrate.scanz T P our now (i + 1) = _ |- _ =>
  split; [cmnL|];
  split; [rget (18%bv : bv 5); evv 36%nat EE36; reflexivity|];
  split; [rewrite HB'; s3get|];
  split; [rget (8%bv : bv 5); evv 8%nat EE8; reflexivity|];
  split; [rewrite (reac_arbitrate.best_scanz t T P our now Ht0); rewrite <- Hn1; reflexivity | exact Fe]
  end
with leafN := idtac;
  lazymatch goal with Fe : arb_est fsm = false, HB' : reac_arbitrate.scanz T P our now (i + 1) = _ |- _ =>
  split; [cmnL|];
  split; [rget (18%bv : bv 5); evv 36%nat EE36; reflexivity|];
  split; [rget (20%bv : bv 5); evv 35%nat EE35; reflexivity|];
  split; [rewrite (reac_arbitrate.best_scanz t T P our now Ht0); rewrite <- Hn1, HB'; reflexivity | exact Fe]
  end
with leafB := idtac;
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m4 _ _, MEQ : forall a, _ -> _ -> aview _ _ ?m4 a = aview _ _ mem3 a,
    Fe : arb_est fsm = false, HB' : reac_arbitrate.scanz T P our now (i + 1) = _ |- _ =>
  split; [cmnL|];
  split; [apply (arb_slots_keep (w_H W) mem3 m4 regs fsm out); [let a := fresh "a" in intros a ?; apply MEQ; [lia | cbv beta; lia] | exact HSL]|];
  split; [rget (18%bv : bv 5); evv 36%nat EE36; reflexivity|];
  split; [s3get|];
  split; [rget (8%bv : bv 5); evv 8%nat EE8; reflexivity|];
  split; [rewrite (reac_arbitrate.best_scanz t T P our now Ht0); rewrite <- Hn1; exact HB' | exact Fe]
  end
in
destruct b as [j|]; [destruct (HE1 j eq_refl) as [HS SHOK]; pose proof (HEIb (Some j)) as HEI;
  pose proof (arb_scanz_range T P our now i j (eq_sym Hb)) as Rj;
  assert (Rlastb : 0 <= disco_table_c.last_of T j < 2 ^ 64) by (unfold disco_table_c.last_of; apply (arb_u_range T (48 * j + 40) 8); [lia | rewrite LT; lia])
 | destruct (HE0 eq_refl) as [HS SHOK]; pose proof (HEIb None) as HEI];
(lazymatch type of HS with st_ok_pi _ _ ?E0 _ _ =>
  assert (AG0 : forall n, (n < 512)%nat -> ew E0 n = ew E0 n) by reflexivity;
  assert (Usp : bv_unsigned (ew E0 2) = spZ regs - 144) by apply EE2 end);
go.
Qed.
Lemma arbE_post_intro : forall (fq fq' : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) ly' S' (regs' : bvmap 5 word) mem' md',
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fq') k = Sem.reg_get (@YK11.fp_regs fq) k) ->
  (@YK11.fp_csr fq' = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fq')) 5) 7 = 0) ->
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly' S' W mem' md' 0 ->
  aregs_preserved regs regs' -> getr regs' 1 = getr regs 1 ->
  Permutation (ablocks B ly' S') (ablocks B ly S) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  garr8 SEGS (mrestrict (w_H W) mem') out
    (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.arb_model t our T P fsm pace now)) ->
  treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P W
    (mkCfg (mkst (fx := fq') regs' (getr regs 1) mem' (seg_rom SEGS)) md').
Proof.
intros fq fq' ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ly' S' regs' mem' md'
  HFX HCX HA HJ HPR Hra HPerm HK Hout.
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HPP).
pose proof HPRE as (HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
unfold treac_arbitrate_post, apost_base.
exists fq', ly', S', regs', mem', md'.
split; [reflexivity|]. split; [exact HFX|]. split; [exact HCX|]. split; [exact HJ|]. split; [exact HPR|].
split; [exact Hra|]. split; [exact HPerm|]. split; [exact Hout|].
split; [|split; [|split; [reflexivity|]]].
- intros Ht0. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis).
  destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & Ht4096 & Htceil & _).
  apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem' t _); [|exact GT].
  intros a Ha. rewrite length_map, LT in Ha. apply HK; lia.
- intros Hu0. destruct (HPP Hu0) as (Hbp & Hbp1 & Hbp2 & LP & GP & Hdis).
  destruct (al_blocks _ _ LAWS ly S W mem md bp Np HAR Hbp) as (_ & Hp4096 & Hpceil & _).
  apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem' our _); [|exact GP].
  intros a Ha. rewrite length_map, LP in Ha. apply HK; lia.
- intros a N1 N2. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra. apply HK; [lia | exact N1 | exact N2].
Qed.

Lemma arbE_rival_at : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md (out : Z) ly3 S3
    (regsT : bvmap 5 word) memT md3 (e r d s c : Z) (raw : word),
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly3 S3 W memT md3 0 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regsT 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 ->
  (e <> 0 ->
     e + 24 <= 2 ^ 63 /\ in_app (e + 8) 16 /\ off_img (e + 8) 16 /\
     range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF (e + 8) 16 /\
     (forall a, e + 8 <= a < e + 24 -> apresent (w_H W) memT a) /\
     -2 ^ 31 <= r < 2 ^ 31 /\ 0 <= d < 2 ^ 8 /\ 0 <= s < 2 ^ 8 /\ 0 <= c < 2 ^ 32 /\
     val_mem SEGS (mrestrict (w_H W) memT) (e + 8) 4 r /\
     val_mem SEGS (mrestrict (w_H W) memT) (e + 12) 1 d /\
     val_mem SEGS (mrestrict (w_H W) memT) (e + 16) 1 s /\
     val_mem SEGS (mrestrict (w_H W) memT) (e + 20) 4 c) ->
  spZ regsT = spZ regs - 144 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> s0Z regsT < alloc_ceiling ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regsT (Z_to_bv 64 (SIGMA AS_reac_rival_kind_of)) memT (seg_rom SEGS)) md3)
    (fun W2 c2 => W2 = W /\ exists (fq2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
       c2 = mkCfg (mkst (fx := fq2) regs2 raw mem2 (seg_rom SEGS)) md2 /\
       (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fq2) k = Sem.reg_get (@YK11.fp_regs fq) k) /\
       (@YK11.fp_csr fq2 = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fq2)) 5) 7 = 0) /\
       ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly2 S2 W mem2 md2 0 /\
       aregs_preserved regsT regs2 /\
       getr regs2 10 = w64 (if e =? 0 then 0 else reac_rival_kind_of_c.reac_rival_kind_model d r s c) /\
       Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\
       (forall a : word, ~ (spZ regs - 144 - REAC_RIVAL_KIND_OF_STK <= bv_unsigned a < spZ regs - 144) -> mem2 a = memT a)).
Proof.
intros fq ly S W regs mem md out ly3 S3 regsT memT md3 e r d s c raw HJ HROD H10 Re He8 HE Hsp Hgp Htp Hra Hraw Hraw4 Hs0.
pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & HQT).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity. assert (WR : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
rewrite pa_sigma_reac_rival_kind_of.
eapply SRr_mono.
{ apply (TRIVAL fq ly3 S3 W regsT memT md3 [] e r d s c).
  - apply (afn_pre_at SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly3 S3 W memT md3 0 regsT
      REAC_RIVAL_KIND_OF_STK (-144) [] HJ).
    + rewrite Hsp. lia.
    + reflexivity.
    + lia.
    + rewrite WR. unfold ESTACK. lia.
    + rewrite WR, WS. unfold ESTACK. lia.
    + rewrite Hra. exact Hraw.
    + unfold raZ. rewrite Hra. exact Hraw4.
    + exact Hgp.
    + exact Htp.
    + apply achain_low. exact Hs0.
  - exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD).
  - exact H10.
  - exact Re.
  - exact He8.
  - exact HE. }
cbv beta. intros W2 c2 HW2 HPOST.
unfold treac_rival_kind_of_post, apost_base in HPOST.
destruct HPOST as (fq2 & ly2 & S2 & regs2 & mem2 & md2 & Hc & Hfr2 & Hcsr2 & HJ1 & HP & Ha0 & HPerm & -> & Hkeep).
split; [reflexivity|]. exists fq2, ly2, S2, regs2, mem2, md2.
split; [rewrite Hc, Hra; reflexivity|]. split; [exact Hfr2|]. split; [exact Hcsr2|].
split.
{ change (@nil (Z * Z)) with (@nil (Z * Z) ++ @nil (Z * Z)). replace 0 with (0 + 0) by lia.
  eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | rewrite Hsp, WR, WS; unfold ESTACK; lia | rewrite Hsp; lia |].
  intros a Ha. exfalso. exact (inFP_nil a Ha). }
split; [exact HP|]. split; [exact Ha0|]. split; [exact HPerm|].
intros a Ha. apply Hkeep. rewrite Hsp. exact Ha.
Qed.

Lemma arbE_z4_garr8 : forall (m : word -> option byte) a v V,
  val_mem SEGS m a 4 V -> V mod 2 ^ 32 = bv_unsigned (Z_to_bv 64 v) mod 2 ^ 32 ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)).
Proof.
intros m a v V HV HE.
assert (LZ : length (reac_arbitrate_c.z4 v) = 4%nat) by reflexivity.
apply (arb_garr8_val_mem m a _ V); [rewrite LZ; exact HV|].
rewrite LZ. change (reac_arbitrate_c.z4 v) with (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v))).
rewrite bytes_le_Z_to_le by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 v)); lia). exact HE.
Qed.

Lemma arbE_bytes_garr8 : forall (m : word -> option byte) out st (mac : list byte) hv pc cf rv ch,
  garr8 SEGS m out (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 st)) ->
  length mac = 6%nat -> garr8 SEGS m (out + 4) (map (fun b : byte => bv_unsigned b) mac) ->
  garr8 SEGS m (out + 10) [0; 0] ->
  garr8 SEGS m (out + 12) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 hv)) ->
  garr8 SEGS m (out + 16) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 pc)) ->
  garr8 SEGS m (out + 20) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 cf)) ->
  garr8 SEGS m (out + 24) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 rv)) ->
  garr8 SEGS m (out + 28) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 ch)) ->
  garr8 SEGS m out (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.arb_bytes st mac hv pc cf rv ch)).
Proof.
intros m out st mac hv pc cf rv ch G0 Lm G4 G10 G12 G16 G20 G24 G28.
assert (LZ : forall v, length (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)) = 4%nat)
  by (intros v; rewrite length_map; reflexivity).
unfold reac_arbitrate_c.arb_bytes. rewrite !map_app.
apply garr8_app. split; [exact G0|]. rewrite LZ.
apply garr8_app. split; [replace (out + Z.of_nat 4) with (out + 4) by lia; exact G4|]. rewrite length_map, Lm.
apply garr8_app. split; [replace (out + Z.of_nat 4 + Z.of_nat 6) with (out + 10) by lia; exact G10|].
cbn [map length].
apply garr8_app. split; [replace (out + Z.of_nat 4 + Z.of_nat 6 + Z.of_nat 2) with (out + 12) by lia; exact G12|]. rewrite LZ.
apply garr8_app. split; [replace (out + Z.of_nat 4 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 4) with (out + 16) by lia; exact G16|]. rewrite LZ.
apply garr8_app. split; [replace (out + Z.of_nat 4 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 4 + Z.of_nat 4) with (out + 20) by lia; exact G20|]. rewrite LZ.
apply garr8_app. split; [replace (out + Z.of_nat 4 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) with (out + 24) by lia; exact G24|]. rewrite LZ.
replace (out + Z.of_nat 4 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) with (out + 28) by lia. exact G28.
Qed.

Lemma arbE_nth_regs : forall r : bv 5, nth (Z.to_nat (bv_unsigned r)) all_regs 0%bv = r.
Proof.
apply (reg_cases_lit (fun r => nth (Z.to_nat (bv_unsigned r)) all_regs 0%bv = r)).
intros r Hr. cbv [all_regs In] in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]). destruct Hr.
Qed.

Lemma arbE_z4_ble : forall x, bytes_le_to_Z (reac_arbitrate_c.z4 x) = x mod 2 ^ 32.
Proof.
intros x. change (reac_arbitrate_c.z4 x) with (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 x))).
rewrite bytes_le_Z_to_le by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 x)); lia).
change (8 * Z.of_nat 4) with 32. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 32 * 2 ^ 32).
rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.

Lemma arbE_u64_mod32 : forall v, bv_unsigned (Z_to_bv 64 v) mod 2 ^ 32 = v mod 2 ^ 32.
Proof.
intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 32 * 2 ^ 32).
rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.

Definition arbE_X (regs3 : bvmap 5 word) (pace t : Z) (T : list byte) (b : option Z) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 (pace mod 2 ^ 32); Z_to_bv 64 (reac_arbitrate.baddr t b);
   Z_to_bv 64 (match b with Some j => reac_arbitrate_c.ch_of T j | None => 0 end)] ++ map (getr regs3) all_regs.
Definition arbE_EQ (regs regs3 : bvmap 5 word) (pace t : Z) (T : list byte) (b : option Z) : env :=
  Eimg (Ereg regs (arbE_X regs3 pace t T b)).
Definition arbE_sr (s3v : sv) : list sv :=
  [SLit 0; SOff 37 0; SOff 2 (-144); SOff 3 0; SOff 4 0; SOff 41 0; SOff 42 0; SOff 43 0;
   SOff 10 0; SOff 11 0; SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0; SOff 51 0;
   SOff 52 0; SOff 53 0; SOff 15 0; s3v; SOff 56 0; SOff 57 0; SOff 58 0; SOff 59 0;
   SOff 32 0; SOff 61 0; SOff 62 0; SOff 63 0; SOff 64 0; SOff 65 0; SOff 66 0; SOff 67 0].
Definition arbE_s3 (b : option Z) : sv := match b with None => SLit 0 | Some _ => SOff 34 0 end.
Definition arbE_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-144) 0 0 0 ARB_STKA.
Definition arbE_o0 : YP09.region := YP09.mkRegion (Some 15%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SLit 0))].
Definition arbE_o12 : YP09.region := YP09.mkRegion (Some 15%nat) 12 32 12 32
  [YP09.mkChunk 12 (CVal 4 (SLit 0)); YP09.mkChunk 16 (CVal 4 (SOff 33 0)); YP09.mkChunk 20 (CVal 4 (SLit 0));
   YP09.mkChunk 24 (CVal 4 (SLit 0)); YP09.mkChunk 28 (CVal 4 (SLit 0))].
Definition arbE_bst : YP09.region := YP09.mkRegion (Some 34%nat) 0 48 0 0 [YP09.mkChunk 20 (CVal 4 (SOff 35 0))].
Definition arbE_regions (b : option Z) : smem :=
  match b with None => [arbE_stk; arbE_o0; arbE_o12] | Some _ => [arbE_stk; arbE_o0; arbE_o12; arbE_bst] end.
Definition arbE_facts (b : option Z) : facts :=
  match b with
  | None => mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (15%nat, mkAF 4096 140737479966720 2); (32%nat, mkAF SB SB 0)] [] []
  | Some _ => mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (15%nat, mkAF 4096 140737479966720 2); (32%nat, mkAF SB SB 0);
                       (34%nat, mkAF 4096 140737479966720 3)] [] []
  end.
Definition ss_arbE (b : option Z) : sstate := mkSS AF_ARB_E (arbE_sr (arbE_s3 b)) (arbE_regions b) None (arbE_facts b).
Definition arbE_SH (b : option Z) : list shent :=
  match b with None => [mkSHE 15 0 32] | Some _ => [mkSHE 15 0 32; mkSHE 34 0 48] end.

Lemma arbE_ew_ext : forall regs regs3 pace t T b (r : bv 5),
  ew (arbE_EQ regs regs3 pace t T b) (36 + Z.to_nat (bv_unsigned r)) = getr regs3 r.
Proof.
intros regs regs3 pace t T b r. pose proof (u5_range r) as Hr. unfold arbE_EQ. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (36 + Z.to_nat (bv_unsigned r))%nat with (32 + (4 + Z.to_nat (bv_unsigned r)))%nat by lia.
rewrite ew_Ereg_extra. unfold arbE_X. rewrite app_nth2 by (cbn [length]; lia). cbn [length].
replace (4 + Z.to_nat (bv_unsigned r) - 4)%nat with (Z.to_nat (bv_unsigned r)) by lia.
rewrite (nth_indep _ _ (getr regs3 0%bv)) by (rewrite length_map; cbn [length all_regs]; lia).
rewrite map_nth, arbE_nth_regs. reflexivity.
Qed.

Lemma arbE_regs_ok : forall (regs regs3 : bvmap 5 word) pace t T b out our,
  getr regs 15 = w64 out -> getr regs 11 = w64 our -> getr regs 10 = w64 t ->
  getr regs3 2 = Z_to_bv 64 (spZ regs - 144) -> getr regs3 3 = getr regs 3 -> getr regs3 4 = getr regs 4 ->
  getr regs3 8 = Z_to_bv 64 t -> getr regs3 9 = Z_to_bv 64 our -> getr regs3 18 = Z_to_bv 64 out ->
  getr regs3 19 = Z_to_bv 64 (reac_arbitrate.baddr t b) -> getr regs3 24 = Z_to_bv 64 SB ->
  regs_ok (arbE_EQ regs regs3 pace t T b) (arbE_sr (arbE_s3 b)) regs3.
Proof.
intros regs regs3 pace t T b out our H15 H11 H10 R2 R3 R4 R8 R9 R18 R19 R24.
set (E := arbE_EQ regs regs3 pace t T b).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbE_X regs3 pace t T b)) n)
  by (intros n Hn; subst E; unfold arbE_EQ; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E11 : ew E 11 = Z_to_bv 64 our) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (reac_arbitrate.baddr t b)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EX : forall r : bv 5, ew E (36 + Z.to_nat (bv_unsigned r)) = getr regs3 r) by (intros r; exact (arbE_ew_ext regs regs3 pace t T b r)).
clearbody E. clear EL.
apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
destruct b as [j|];
(repeat (destruct Hz as [<-|Hz];
  [ match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
    cbn [sv_denot];
    first
    [ rewrite getr_zero; reflexivity
    | rewrite R19; reflexivity
    | lazymatch goal with |- getr _ ?zz = Z_to_bv 64 (bv_unsigned (ew E ?k) + _) =>
        replace k with (36 + Z.to_nat (bv_unsigned zz))%nat by reflexivity;
        rewrite (EX zz), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end
    | rewrite R2, E2; unfold spZ; f_equal; lia
    | first [ rewrite R3, E3 | rewrite R4, E4 | rewrite R8, E10 | rewrite R9, E11 | rewrite R18, E15 | rewrite R24, E32
            | rewrite R19, E34 ];
      rewrite Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity ]
  | ]); try (exfalso; exact Hz)).
Qed.

Lemma arbE_stk_chunks : forall E m (regs : bvmap 5 word),
  (forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n))) ->
  arb_frame m regs -> Forall (YP09.chunk_ok SEGS E m (spZ regs)) ARB_STKA.
Proof.
intros E m regs AG HS.
apply Forall_forall. intros c Hc. cbn [ARB_STKA In] in Hc.
repeat (destruct Hc as [<-|Hc];
  [ lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?od (CVal 8 (SOff ?n 0))) =>
      let p := eval vm_compute in (od + 144, Z.of_nat n) in
      let Hp := fresh "Hp" in
      pose proof (HS p ltac:(cbn [ARB_SAVES In]; repeat (first [left; reflexivity | right]))) as Hp;
      cbn [fst snd] in Hp;
      pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat n)))) as Rg; unfold bv_modulus in Rg;
      apply (chunk_ok_val SEGS E m (spZ regs) od 8 (SOff n 0) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat n)))));
      [ cbn [sv_denot]; rewrite AG by lia; rewrite Z.add_0_r; reflexivity
      | change (8 * Z.of_N 8) with 64; change (Z.of_N 64) with 64 in Rg; revert Rg;
        generalize (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat n)))); intros; lia
      | cbn; lia
      | change (N.to_nat 8) with 8%nat; replace (spZ regs + od) with (spZ regs - 144 + (od + 144)) by lia; exact Hp ]
    end
  | ]).
destruct Hc.
Qed.

Definition arbE_kept (W : world SEGS) (m0 m : word -> option byte) (Zx : Z -> Prop) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ Zx a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m0 a.

Lemma arbE_kept_refl : forall W m Zx, arbE_kept W m m Zx.
Proof. intros W m Zx a _ _. reflexivity. Qed.

Lemma arbE_kept_step : forall W m0 m m' (Zx Zy Zz : Z -> Prop),
  arbE_kept W m0 m Zx -> (forall a, 0 <= a < 2 ^ 64 -> ~ Zy a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, Zx a -> Zz a) -> (forall a, Zy a -> Zz a) -> arbE_kept W m0 m' Zz.
Proof.
intros W m0 m m' Zx Zy Zz K St Hx Hy a Ha Hz.
rewrite St by (try exact Ha; intro Q; apply Hz; apply Hy; exact Q).
apply K; [exact Ha | intro Q; apply Hz; apply Hx; exact Q].
Qed.

Lemma arbE_kept_frame : forall W m0 m m' (Zx : Z -> Prop) E rs,
  arbE_kept W m0 m Zx -> frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zx a) ->
  arbE_kept W m0 m' Zx.
Proof.
intros W m0 m m' Zx E rs K HF Hw a Ha Hz.
rewrite (kept_of_frame (segs := SEGS) E rs (w_H W) m m' Zx HF Hw a Ha Hz). exact (K a Ha Hz).
Qed.

Lemma arbE_garr8_copy : forall H m0 m s d l,
  garr8 SEGS (mrestrict H m0) s l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS H m (d + i) = aview SEGS H m0 (s + i)) ->
  garr8 SEGS (mrestrict H m) d l.
Proof.
intros H m0 m s d l G K j Hj. destruct (G j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r.
specialize (Hv 0%nat Hk). rewrite Z.add_0_r in Hv.
assert (A0 : aview SEGS H m0 (s + Z.of_nat j) = Some (bv_unsigned (Z_to_bv 8 (YO0f.le_byte (nth j l 0) 1 0))))
  by (unfold aview; rewrite Hv; reflexivity).
rewrite <- (K (Z.of_nat j) ltac:(lia)) in A0.
destruct (aview_byte SEGS H m (d + Z.of_nat j) _ A0) as (b & Hb & Hbv & _). rewrite Hb. f_equal.
apply bv_eq. symmetry. exact Hbv.
Qed.

Lemma arbE_chunk_val : forall (fq : YK11.FPState) E ss ms i r off (w : N) e,
  st_ok_pi (fx := fq) SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) -> (Z.of_N w <= 8) ->
  val_mem SEGS (ms_mem ms) (base_val E (YP09.r_base r) + off) (N.to_nat w) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros fq E ss ms i r off w e HS Hi Hc Hw.
pose proof (st_ok_region_nth (fx := fq) E (abs_ss VAL ss) ms i r HS Hi) as (_ & _ & _ & Hcs).
apply (val_mem_low_of_chunk SEGS E (ms_mem ms) _ off w e); [| exact Hw].
exact (proj1 (Forall_forall _ _) Hcs _ Hc).
Qed.

Lemma arbE_out0_rest : forall m out pace, garr8 SEGS m out (arb_out0 pace) ->
  garr8 SEGS m (out + 4) (map (fun b : byte => bv_unsigned b) reac_arbitrate_c.MAC0) /\ garr8 SEGS m (out + 10) [0; 0].
Proof.
intros m out pace HO.
assert (L : length (arb_out0 pace) = 32%nat) by (unfold arb_out0, reac_arbitrate_c.arb_bytes; rewrite length_map, !length_app; reflexivity).
split.
- pose proof (garr8_sub_x SEGS m out (arb_out0 pace) 4 6 HO ltac:(rewrite L; lia)) as G. exact G.
- pose proof (garr8_sub_x SEGS m out (arb_out0 pace) 10 2 HO ltac:(rewrite L; lia)) as G. exact G.
Qed.

Lemma arbE_z4_chunk : forall m a V v, val_mem SEGS m a 4 (V mod 2 ^ 32) -> V mod 2 ^ 32 = v mod 2 ^ 32 ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)).
Proof.
intros m a V v H Hv. apply (arbE_z4_garr8 m a v (V mod 2 ^ 32) H). rewrite Z.mod_mod by lia. rewrite Hv. symmetry. apply arbE_u64_mod32.
Qed.

Lemma arbE_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (b : option Z) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invE ly S W regs mem md t our fsm pace now out T P b regs3 mem3 md3 ->
  st_ok_pi (fx := fq) SEGS VAL (arbE_EQ regs regs3 pace t T b) (ss_arbE b)
    (restrict (w_H W) (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_E)) mem3 (seg_rom SEGS)))
  /\ sh_ok SEGS ARB_BX (arbE_SH b) (arbE_EQ regs regs3 pace t T b) (mrestrict (w_H W) mem3).
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P b regs3 mem3 md3 HPRE HINV.
destruct HPRE as (HAF & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
destruct HINV as ((HJ & HK & HFR & HO & R2 & R3 & R4 & R9 & R24) & R18 & R19 & R8 & Hb & Hest).
pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
pose proof (proj1 HJ) as HAR3.
destruct (al_blocks _ _ LAWS ly S W mem3 md3 bo No HAR3 Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
assert (BJ : forall j, b = Some j -> t <> 0 /\ 0 <= j < disco_table_c.n_of T).
{ intros j ->. assert (Ht0 : t <> 0) by (intro E0; unfold reac_arbitrate_c.best in Hb; rewrite (proj2 (Z.eqb_eq t 0) E0) in Hb; discriminate).
  split; [exact Ht0|]. symmetry in Hb. rewrite reac_arbitrate.best_scanz in Hb by exact Ht0. exact (reac_arbitrate.scanz_range _ _ _ _ _ _ Hb). }
assert (GT3 : t <> 0 -> garr8 SEGS (mrestrict (w_H W) mem3) t (map (fun b0 : byte => bv_unsigned b0) T)).
{ intros Ht0. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis).
  destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & Ht4096 & Htceil & _).
  eapply garr8_frame; [exact GT|]. intros a Ha. rewrite length_map, LT in Ha. apply (mbyte_of_aview SEGS). apply HK; lia. }
rewrite arb_out0_split in HO.
apply garr8_app in HO as [O0 HO]. rewrite length_map, repeat_length in HO.
apply garr8_app in HO as [O8 HO]. rewrite length_map, repeat_length in HO.
apply garr8_app in HO as [O16 HO]. change (length (map (fun b0 : byte => bv_unsigned b0) (reac_arbitrate_c.z4 pace))) with 4%nat in HO.
apply garr8_app in HO as [O20 O24]. rewrite length_map, repeat_length in O24.
replace (out + Z.of_nat 8) with (out + 8) in O8 by lia.
replace (out + Z.of_nat 8 + Z.of_nat 8) with (out + 16) in O16 by lia.
replace (out + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 4) with (out + 20) in O20 by lia.
replace (out + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4) with (out + 24) in O24 by lia.
assert (V0 : val_mem SEGS (mrestrict (w_H W) mem3) (out + 0) 4 0).
{ pose proof (val_mem_garr8_sub _ out _ 0 4 O0 ltac:(lia) ltac:(rewrite repeat_length; lia)) as V. exact V. }
assert (V12 : val_mem SEGS (mrestrict (w_H W) mem3) (out + 12) 4 0).
{ pose proof (val_mem_garr8_sub _ (out + 8) _ 4 4 O8 ltac:(lia) ltac:(rewrite repeat_length; lia)) as V.
  replace (out + 8 + 4) with (out + 12) in V by lia. exact V. }
assert (V16 : val_mem SEGS (mrestrict (w_H W) mem3) (out + 16) 4 (pace mod 2 ^ 32)).
{ pose proof (val_mem_garr8_sub _ (out + 16) _ 0 4 O16 ltac:(lia) ltac:(cbn; lia)) as V.
  replace (out + 16 + 0) with (out + 16) in V by lia. change (disco_table_c.sub (reac_arbitrate_c.z4 pace) 0 4) with (reac_arbitrate_c.z4 pace) in V.
  rewrite arbE_z4_ble in V. exact V. }
assert (V20 : val_mem SEGS (mrestrict (w_H W) mem3) (out + 20) 4 0).
{ pose proof (val_mem_garr8_sub _ (out + 20) _ 0 4 O20 ltac:(lia) ltac:(rewrite repeat_length; lia)) as V.
  replace (out + 20 + 0) with (out + 20) in V by lia. exact V. }
assert (V24 : val_mem SEGS (mrestrict (w_H W) mem3) (out + 24) 4 0).
{ pose proof (val_mem_garr8_sub _ (out + 24) _ 0 4 O24 ltac:(lia) ltac:(rewrite repeat_length; lia)) as V.
  replace (out + 24 + 0) with (out + 24) in V by lia. exact V. }
assert (V28 : val_mem SEGS (mrestrict (w_H W) mem3) (out + 28) 4 0).
{ pose proof (val_mem_garr8_sub _ (out + 24) _ 4 4 O24 ltac:(lia) ltac:(rewrite repeat_length; lia)) as V.
  replace (out + 24 + 4) with (out + 28) in V by lia. exact V. }
clear O0 O8 O16 O20 O24.
remember (arbE_EQ regs regs3 pace t T b) as E eqn:HE.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbE_X regs3 pace t T b)) n)
  by (intros n Hn; subst E; unfold arbE_EQ; apply Eimg_low; exact Hn).
assert (AG : forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n)))
  by (intros n Hn; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_lt; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pace mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (reac_arbitrate.baddr t b)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (match b with Some j => reac_arbitrate_c.ch_of T j | None => 0 end))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (HRS : regs_ok E (arbE_sr (arbE_s3 b)) regs3)
  by (subst E; exact (arbE_regs_ok regs regs3 pace t T b out our H15 H11 H10 R2 R3 R4 R8 R9 R18 R19 R24)).
assert (RK0 : region_ok SEGS E (mrestrict (w_H W) mem3) arbE_stk).
{ unfold region_ok, arbE_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  exact (arbE_stk_chunks E _ regs AG HFR). }
assert (RK1 : region_ok SEGS E (mrestrict (w_H W) mem3) arbE_o0).
{ unfold region_ok, arbE_o0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E15, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hopres (out + o) ltac:(lia)))|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ out 0 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V0]. }
assert (RK2 : region_ok SEGS E (mrestrict (w_H W) mem3) arbE_o12).
{ unfold region_ok, arbE_o12. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E15, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hopres (out + o) ltac:(lia)))|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ out 12 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V12].
  - apply (chunk_ok_val SEGS E _ out 16 4 (SOff 33 0) (pace mod 2 ^ 32));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (Z.mod_pos_bound pace (2 ^ 32) ltac:(lia)); cbn; lia | cbn; lia | exact V16].
  - apply (chunk_ok_val SEGS E _ out 20 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V20].
  - apply (chunk_ok_val SEGS E _ out 24 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V24].
  - apply (chunk_ok_val SEGS E _ out 28 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V28]. }
split.
- rewrite restrict_mkst_fx. unfold ss_arbE. apply pa_entry_st_ok_full.
  + exact HRS.
  + destruct b; vm_compute; reflexivity.
  + destruct b as [j|]; cbn [arbE_regions]; repeat apply Forall_cons; try apply Forall_nil; try assumption.
    destruct (BJ j eq_refl) as [Ht0 Rj]. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & (T1 & _) & Hdis).
    unfold disco_table_c.tbl_T1 in T1.
    destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & Ht4096 & Htceil & _).
    unfold region_ok, arbE_bst. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E34. cbn [reac_arbitrate.baddr]. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    pose proof (reac_arbitrate.u_range T (48 * j + 20) 4 ltac:(lia) ltac:(rewrite LT; lia)) as Rc.
    apply (chunk_ok_val SEGS E _ (t + 48 * j) 20 4 (SOff 35 0) (reac_arbitrate_c.ch_of T j)).
    * cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * unfold reac_arbitrate_c.ch_of. cbn in Rc |- *. lia.
    * cbn; lia.
    * change (N.to_nat 4) with 4%nat. replace (t + 48 * j + 20) with (t + (48 * j + 20)) by lia.
      unfold reac_arbitrate_c.ch_of, disco_table_c.u_at. apply val_mem_garr8_sub; [exact (GT3 Ht0) | lia | rewrite LT; lia].
  + apply pairwise_disjoint_of_extents.
    destruct b as [j|]; cbn [arbE_regions]; unfold arbE_stk, arbE_o0, arbE_o12, arbE_bst, extent_of_region;
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Usp, E15, unsigned_lit_small by lia;
    cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
    * destruct (BJ j eq_refl) as [Ht0 Rj]. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & (T1 & _) & Hdis).
      unfold disco_table_c.tbl_T1 in T1.
      destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & Ht4096 & Htceil & _).
      rewrite E34. cbn [reac_arbitrate.baddr]. rewrite unsigned_lit_small by lia.
      repeat split; lia.
    * repeat split; lia.
  + destruct b as [j|]; (split; [|split; [exact I | exact I]]); cbn [arbE_facts f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
    rewrite Usp, E15, E32, !unsigned_lit_small by (unfold SB; lia);
    change (2 ^ 4) with 16; change (2 ^ 3) with 8; change (2 ^ 2) with 4; rewrite !Z.pow_0_r, !Z.mod_1_r.
    * destruct (BJ j eq_refl) as [Ht0 Rj]. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & (T1 & _) & Hdis).
      unfold disco_table_c.tbl_T1 in T1.
      destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & Ht4096 & Htceil & _).
      rewrite E34. cbn [reac_arbitrate.baddr]. rewrite unsigned_lit_small by lia.
      unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
      all: rewrite Z.add_mod by lia; rewrite Ht8; replace (48 * j) with ((6 * j) * 8) by lia; rewrite Z.mod_mul by lia; reflexivity.
    * unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- destruct b as [j|]; unfold sh_ok, arbE_SH; constructor;
  [apply (arb_shent ly S W mem3 md3 E 15 bo No out 0 32 HAR3 Hbo); [apply arb_U_BX; exact E32 | apply arb_U_atom; [exact E15 | lia] | lia | lia | lia] | |
   apply (arb_shent ly S W mem3 md3 E 15 bo No out 0 32 HAR3 Hbo); [apply arb_U_BX; exact E32 | apply arb_U_atom; [exact E15 | lia] | lia | lia | lia] | constructor].
  destruct (BJ j eq_refl) as [Ht0 Rj]. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & (T1 & _) & Hdis).
  unfold disco_table_c.tbl_T1 in T1.
  destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & Ht4096 & Htceil & _).
  constructor; [|constructor].
  apply (arb_shent ly S W mem3 md3 E 34 bt Nt (t + 48 * j) 0 48 HAR3 Hbt);
  [apply arb_U_BX; exact E32 | apply arb_U_atom; [rewrite E34; reflexivity | lia] | lia | lia | lia].
Qed.

Lemma arbE_ret : forall (fq fq' : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (b : option Z) (regs3 : bvmap 5 word)
    Ec ss ms md' ly' S',
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fq') k = Sem.reg_get (@YK11.fp_regs fq) k) ->
  (@YK11.fp_csr fq' = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fq')) 5) 7 = 0) ->
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  (forall n, (n < 240)%nat -> ew Ec n = ew (arbE_EQ regs regs3 pace t T b) n) -> ed Ec = ed (arbE_EQ regs regs3 pace t T b) ->
  st_ok_pi (fx := fq') SEGS VAL Ec ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  plookup pl_tpi (ss_pc ss) = Some (PW RET_WORD_r) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  sr_get (ss_regs ss) 1 = SOff 1 0 ->
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly' S' W (ms_mem ms) md' 0 ->
  Permutation (ablocks B ly' S') (ablocks B ly S) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a) ->
  garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) out
    (map (fun b0 : byte => bv_unsigned b0) (reac_arbitrate_c.arb_model t our T P fsm pace now)) ->
  SRr SEGS W (mkCfg ms md') (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).
Proof.
intros fq fq' ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P b regs3 Ec ss ms md' ly' S'
  HFX HCX HPRE HA HD HS Hrv Hpl Hcs Hr1 HJ HPerm HK Hout.
pose proof HPRE as ((HAR & Hra & _) & _).
assert (EL : forall n, (n < 32)%nat -> ew Ec n = ew (Ereg regs (arbE_X regs3 pace t T b)) n)
  by (intros n Hn; rewrite HA by lia; unfold arbE_EQ; apply Eimg_low; unfold A_TEXT; lia).
assert (R1 : getr (ms_regs ms) 1 = getr regs 1).
{ rewrite (st_ok_pi_restrict_reg (fx := fq') (w_H W) Ec ss ms 1 HS), Hr1. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EL by lia. exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
eapply (paj_ret_at (fx := fq') (PI := PI) W Ec ss ms md' _ HS Hrv Hpl).
intros mat'. rewrite R1, Hra.
apply (arbE_post_intro fq fq' ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ly' S' (ms_regs ms) (ms_mem ms) _ HFX HCX HPRE).
- apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
- apply (aregs_preserved_of_st_ok SEGS (w_H W) Ec (abs_ss VAL ss) ms regs (arbE_X regs3 pace t T b) HS); [|exact Hcs].
  split; [intros n Hn; apply EL; exact Hn | rewrite HD; reflexivity].
- exact R1.
- exact HPerm.
- exact HK.
- exact Hout.
Qed.

Ltac arbE_awr HA Eout Hbo out :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [azlit_tac|]
  | eapply awr_ok_cons_gen with (n := 15%nat) (b := out);
    [ reflexivity | try (rewrite (HA 15%nat) by lia); rewrite Eout; apply unsigned_lit_small; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; left; split;
      [ eexists; split; [left; reflexivity | cbn; lia] | do 2 eexists; split; [exact Hbo | lia] ]
    | ] ].

Ltac arbE_envt E0 HA HD :=
  let Ev := lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ => Ev | HS : st_ok _ ?Ev _ _ |- _ => Ev end in
  let E1 := fresh "Ec" in
  lazymatch goal with HS : st_ok_pi _ _ Ev _ _ , SHOK : sh_ok _ _ _ Ev _ |- _ => set (E1 := Ev) in HS, SHOK
                    | HS : st_ok _ Ev _ _ , SHOK : sh_ok _ _ _ Ev _ |- _ => set (E1 := Ev) in HS, SHOK end;
  let HEIn := fresh "HEI" in
  assert (HEIn : img_env pa_val A_LIM E1) by (subst E1; assumption);
  let HA' := fresh "HA" in
  assert (HA' : forall n, (n < 240)%nat -> ew E1 n = ew E0 n)
    by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; subst E1;
        rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply HA; exact Hn);
  let HD' := fresh "HD" in
  assert (HD' : ed E1 = ed E0) by (subst E1; exact HD);
  clearbody E1; clear HA HD; rename HA' into HA; rename HD' into HD.

Ltac arbE_envr E0 HA HD HR :=
  let Ev := lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ => Ev | HS : st_ok _ ?Ev _ _ |- _ => Ev end in
  let HR' := fresh "HR" in
  lazymatch type of HR with ew _ ?k = ?v =>
    assert (HR' : ew Ev k = v) by (rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact HR) end;
  clear HR; rename HR' into HR;
  let E1 := fresh "Ec" in
  lazymatch goal with HS : st_ok_pi _ _ Ev _ _ , SHOK : sh_ok _ _ _ Ev _ |- _ => set (E1 := Ev) in HS, SHOK, HR
                    | HS : st_ok _ Ev _ _ , SHOK : sh_ok _ _ _ Ev _ |- _ => set (E1 := Ev) in HS, SHOK, HR end;
  let HEIn := fresh "HEI" in
  assert (HEIn : img_env pa_val A_LIM E1) by (subst E1; assumption);
  let HA' := fresh "HA" in
  assert (HA' : forall n, (n < 240)%nat -> ew E1 n = ew E0 n)
    by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; subst E1;
        rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply HA; exact Hn);
  let HD' := fresh "HD" in
  assert (HD' : ed E1 = ed E0) by (subst E1; exact HD);
  clearbody E1; clear HA HD; rename HA' into HA; rename HD' into HD.

Ltac arbE_win HA E15 :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta;
      first [ lia
            | try (rewrite (HA 15%nat) in Hrr by lia); rewrite E15 in Hrr; rewrite unsigned_lit_small in Hrr by lia; lia ]
    | ]);
  destruct Hin.

Ltac arbE_kstep K HA E15 :=
  lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m) (mrestrict _ ?m') |- _ =>
    lazymatch type of K with arbE_kept ?W ?m0 _ ?Zx =>
      let K' := fresh "K" in
      assert (K' : arbE_kept W m0 m' Zx);
      [ apply (arbE_kept_frame W m0 m m' Zx Ef rs K HFr); arbE_win HA E15 | clear K HFr; rename K' into K ] end end.

Ltac arbE_zc HS HA E15 out i off v G tac :=
  lazymatch type of HS with st_ok_pi ?sg _ ?Ex ?ss (restrict ?H ?msX) =>
  let r := eval vm_compute in (nth_error (ss_mem ss) i) in
  lazymatch r with Some ?rr =>
  let cs := eval vm_compute in (YP09.r_chunks rr) in
  let e := lazymatch cs with context [YP09.mkChunk off (CVal 4 ?e)] => e end in
  let V := fresh "V" in
  pose proof (arbE_chunk_val _ Ex ss (restrict H msX) i rr off 4 e HS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
  cbn [YP09.r_base base_val ms_mem restrict] in V;
  rewrite (HA 15%nat) in V by lia; rewrite E15 in V; rewrite unsigned_lit_small in V by lia;
  change (N.to_nat 4) with 4%nat in V; change (8 * Z.of_N 4) with 32 in V;
  assert (G : garr8 sg (mrestrict H (ms_mem msX)) (out + off) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)));
  [ apply (arbE_z4_chunk _ _ _ v V); tac | clear V ]
  end end.

Lemma arbE_swrap : forall x, -2 ^ 31 <= bv_swrap 32 x < 2 ^ 31 /\ bv_swrap 32 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
intros x. unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with 2147483648 by reflexivity. replace (bv_modulus 32) with 4294967296 by reflexivity.
change (2 ^ 31) with 2147483648. change (2 ^ 32) with 4294967296.
pose proof (Z.mod_pos_bound (x + 2147483648) 4294967296 ltac:(lia)) as M.
split; [set (y := (x + 2147483648) mod 4294967296) in *; lia|].
rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma arbE_sext_mod : forall E e, bv_unsigned (sv_denot E (SExt true 32 e)) mod 2 ^ 32 = bv_unsigned (sv_denot E e) mod 2 ^ 32.
Proof.
intros E e. cbn [sv_denot]. rewrite sext32_unsigned, bv_extract_unsigned.
generalize (bv_unsigned (sv_denot E e)). intros x.
unfold bv_swrap. replace (bv_half_modulus 32) with 2147483648 by reflexivity.
unfold bv_wrap. replace (bv_modulus 64) with 18446744073709551616 by reflexivity.
replace (bv_modulus 32) with 4294967296 by reflexivity.
change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 32) with 4294967296.
Z.div_mod_to_equations. lia.
Qed.

Lemma arbE_vmeqv : forall (m : word -> option byte) a (n : nat) v v',
  val_mem SEGS m a n v -> v mod 2 ^ (8 * Z.of_nat n) = v' mod 2 ^ (8 * Z.of_nat n) -> val_mem SEGS m a n v'.
Proof.
intros m a n v v' H Hv k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite Hv. reflexivity.
Qed.

Lemma arbE_pres_call : forall H (memT mem2 : word -> option byte) lo hi,
  (forall w : word, ~ (lo <= bv_unsigned w < hi) -> mem2 w = memT w) ->
  (forall a, lo <= a < hi -> apresent H mem2 a) ->
  forall a, apresent H memT a -> apresent H mem2 a.
Proof.
intros H memT mem2 lo hi Hk Hp a [Hh [bb Hb]]. split; [exact Hh|].
destruct (Z_le_dec lo (bv_unsigned (Z_to_bv 64 a))) as [L1|L1];
[destruct (Z_lt_dec (bv_unsigned (Z_to_bv 64 a)) hi) as [L2|L2]|].
- destruct (Hp (bv_unsigned (Z_to_bv 64 a)) (conj L1 L2)) as [_ Hx]. rewrite Z_to_bv_bv_unsigned in Hx. exact Hx.
- exists bb. rewrite (Hk (Z_to_bv 64 a)) by lia. exact Hb.
- exists bb. rewrite (Hk (Z_to_bv 64 a)) by lia. exact Hb.
Qed.

Lemma arbE_aview_call : forall H (memT mem2 : word -> option byte) lo hi a,
  (forall w : word, ~ (lo <= bv_unsigned w < hi) -> mem2 w = memT w) -> 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  aview SEGS H mem2 a = aview SEGS H memT a.
Proof.
intros H memT mem2 lo hi a Hk Ha Hn. apply aview_eq_of. unfold mrestrict.
rewrite (Hk (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; exact Hn). reflexivity.
Qed.

Ltac arbE_lit HA E33 :=
  first [ cbn [sv_denot]; apply arbE_u64_mod32
        | cbn [sv_denot]; rewrite (HA 33%nat) by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned, arbE_u64_mod32; apply Z.mod_mod; lia
        | vm_compute; reflexivity ].

Lemma arbE_some : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (j : Z) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invE ly S W regs mem md t our fsm pace now out T P (Some j) regs3 mem3 md3 ->
  SRr SEGS W (arb_post_cfg fq AF_ARB_E regs3 mem3 md3) (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P j regs3 mem3 md3 HPRE HINV.
unfold arb_post_cfg.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
destruct (arbE_entry fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P (Some j) regs3 mem3 md3 HPRE HINV) as [HS SHOK].
pose proof HINV as ((HJ & HK & HFR & HO & R2 & R3 & R4 & R9 & R24) & R18 & R19 & R8 & Hb & EST).
unfold arb_est in EST.
pose proof HPRE as (HAF & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
assert (Ht0 : t <> 0) by (intro E0; unfold reac_arbitrate_c.best in Hb; rewrite (proj2 (Z.eqb_eq t 0) E0) in Hb; discriminate).
assert (Rj : 0 <= j < disco_table_c.n_of T).
{ symmetry in Hb. rewrite reac_arbitrate.best_scanz in Hb by exact Ht0. exact (reac_arbitrate.scanz_range _ _ _ _ _ _ Hb). }
destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis).
pose proof TOK as (T1 & _). unfold disco_table_c.tbl_T1 in T1.
destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (Ht16 & Ht4096 & Htceil & Htia & Htpres & _).
remember (arbE_EQ regs regs3 pace t T (Some j)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold arbE_EQ; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbE_X regs3 pace t T (Some j))) n)
  by (intros n Hn; subst E; unfold arbE_EQ; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E11 : ew E 11 = Z_to_bv 64 our) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pace mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (t + 48 * j)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (reac_arbitrate_c.ch_of T j)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (HA : forall n, (n < 240)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (HD : ed E = ed E) by reflexivity.
pose proof (arbE_kept_refl W mem3 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as K.
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbE_awr HA E15 Hbo out |].
arbE_kstep K HA E15. clear HF HG.
arbE_envt E HA HD.
assert (WR : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
pose proof (blk_off_imgP _ _ _ _ _ _ bt Nt HAR Hbt) as Htimg. unfold off_img, IMG_LO, IMG_TOP in Htimg.
pose proof pa_B_ok as (HB0 & HB1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt Nt (proj1 HJ) Hbt) as (_ & _ & _ & _ & HtpT & _).
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (8%bv : bv 5) Qs0.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
rewrite (HA 34%nat) in Ra0 by lia. rewrite E34 in Ra0.
rewrite (HA 10%nat) in Qs0 by lia. rewrite E10 in Qs0.
rewrite (HA 2%nat) in Qsp by lia. rewrite Usp in Qsp.
rewrite (HA 3%nat) in Qgp by lia. rewrite E3 in Qgp.
rewrite (HA 4%nat) in Qtp by lia. rewrite E4 in Qtp.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) => rename msX into msT end.
assert (GTT : garr8 SEGS (mrestrict (w_H W) (ms_mem msT)) t (map (fun b0 : byte => bv_unsigned b0) T)).
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem (ms_mem msT) t _); [|exact GT].
  intros a Ha. rewrite length_map, LT in Ha. rewrite (K a) by (cbv beta; lia). apply HK; lia. }
assert (VR : val_mem SEGS (mrestrict (w_H W) (ms_mem msT)) (t + 48 * j + 8) 4 (disco_table_c.role_of_e T j)).
{ pose proof (val_mem_garr8_sub _ t T (48 * j + 8) 4 GTT ltac:(lia) ltac:(rewrite LT; lia)) as V.
  replace (t + (48 * j + 8)) with (t + 48 * j + 8) in V by lia.
  apply (arbE_vmeqv _ _ 4 _ _ V). unfold disco_table_c.role_of_e, disco_table_c.s32_at, disco_table_c.u_at.
  change (8 * Z.of_nat 4) with 32. symmetry. apply arbE_swrap. }
assert (VD : val_mem SEGS (mrestrict (w_H W) (ms_mem msT)) (t + 48 * j + 12) 1 (disco_table_c.hd_of T j)).
{ pose proof (val_mem_garr8_sub _ t T (48 * j + 12) 1 GTT ltac:(lia) ltac:(rewrite LT; lia)) as V.
  replace (t + (48 * j + 12)) with (t + 48 * j + 12) in V by lia. exact V. }
assert (VS : val_mem SEGS (mrestrict (w_H W) (ms_mem msT)) (t + 48 * j + 16) 1 (reac_arbitrate_c.slots_of T j)).
{ pose proof (val_mem_garr8_sub _ t T (48 * j + 16) 1 GTT ltac:(lia) ltac:(rewrite LT; lia)) as V.
  replace (t + (48 * j + 16)) with (t + 48 * j + 16) in V by lia. exact V. }
assert (VC : val_mem SEGS (mrestrict (w_H W) (ms_mem msT)) (t + 48 * j + 20) 4 (reac_arbitrate_c.ch_of T j)).
{ pose proof (val_mem_garr8_sub _ t T (48 * j + 20) 4 GTT ltac:(lia) ltac:(rewrite LT; lia)) as V.
  replace (t + (48 * j + 20)) with (t + 48 * j + 20) in V by lia. exact V. }
pose proof (reac_arbitrate.u_range T (48 * j + 12) 1 ltac:(lia) ltac:(rewrite LT; lia)) as RD.
pose proof (reac_arbitrate.u_range T (48 * j + 16) 1 ltac:(lia) ltac:(rewrite LT; lia)) as RS.
pose proof (reac_arbitrate.u_range T (48 * j + 20) 4 ltac:(lia) ltac:(rewrite LT; lia)) as RC.
change (8 * Z.of_nat 1) with 8 in RD, RS. change (8 * Z.of_nat 4) with 32 in RC.
destruct (arbE_swrap (disco_table_c.u_at T (48 * j + 8) 4)) as [RR _].
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msX) _) ?mdX) _ =>
  eapply (arbE_rival_at fq ly S W regs mem md out ly S (ms_regs msX) (ms_mem msX) mdX (t + 48 * j)
    (disco_table_c.role_of_e T j) (disco_table_c.hd_of T j) (reac_arbitrate_c.slots_of T j) (reac_arbitrate_c.ch_of T j) _ HJ HROD) end.
  - rewrite Ra0. reflexivity.
  - lia.
  - rewrite Z.add_mod by lia. rewrite Ht8. replace (48 * j) with ((6 * j) * 8) by lia. rewrite Z.mod_mul by lia. reflexivity.
  - intros _. split; [lia|]. split; [apply (in_app_sub _ _ _ _ Htia); lia|]. split; [unfold off_img, IMG_LO, IMG_TOP; lia|].
    split; [apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bt Nt (t + 48 * j + 8) 16 (proj1 HJ) Hbt); lia|].
    split; [intros a Ha; exact (proj1 (HtpT a ltac:(lia)))|].
    split; [unfold disco_table_c.role_of_e, disco_table_c.s32_at; lia|].
    split; [exact RD|]. split; [exact RS|]. split; [exact RC|].
    split; [exact VR|]. split; [exact VD|]. split; [exact VS|]. exact VC.
  - unfold spZ at 1. rewrite Qsp. rewrite unsigned_lit_small by lia. lia.
  - rewrite Qgp. exact Hgp.
  - rewrite Qtp. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite Qs0. rewrite unsigned_lit_small by lia. lia. }
cbv beta. clear Ra0 Rra Qs0 Qsp Qgp Qtp.
intros W2 c2 _ (-> & fq2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfr2 & Hcsr2 & HJ2 & HP2 & Ha02 & HPerm2 & Hkp2).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HsP2 & _).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 144 - REAC_RIVAL_KIND_OF_STK <= a < spZ regs - 144) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem msX) a)
    by (intros a Ha Hn; exact (arbE_aview_call (w_H W) (ms_mem msX) mem2 _ _ a Hkp2 Ha Hn));
  assert (PC : forall a, apresent (w_H W) (ms_mem msX) a -> apresent (w_H W) mem2 a)
    by (apply (arbE_pres_call (w_H W) (ms_mem msX) mem2 _ _ Hkp2); intros a Ha; apply HsP2; rewrite WS; rewrite WR in Ha; lia) end.
lazymatch type of K with arbE_kept _ _ ?mq ?Zx =>
  pose proof (arbE_kept_step W mem3 mq mem2 Zx (fun a => spZ regs - 144 - REAC_RIVAL_KIND_OF_STK <= a < spZ regs - 144) Zx K KC
    ltac:(intros a Hq; exact Hq) ltac:(intros a Hq; cbv beta in Hq |- *; rewrite WR in Hq; rewrite WS; lia)) as K2 end.
clear K. rename K2 into K.
assert (HboX : In (bo, No) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); exact Hbo).
assert (HbtX : In (bt, Nt) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); exact Hbt).
pose proof (YA0o.st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms. rewrite Hms in HS. clear Hms.
rewrite restrict_mkst_fx in HS.
pose proof (FpStep.fp_st_ok_fx SEGS fq fq2 _ _ _ _ _ _ HS) as HSq. clear HS. rename HSq into HS.
clear RUN RUNTO BR.
pose proof (paj_run (fx := fq2) B LAWS) as RUN. pose proof (paj_run_to (fx := fq2) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq2) (PI := PI)) as BR.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; [ | | | | apply Forall_nil].
  - eapply region_kept_aview; [rewrite (HA 2%nat) by lia; exact Usp | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia.
  - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia.
  - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia.
  - eapply region_kept_aview; [rewrite (HA 34%nat) by lia; rewrite E34; apply unsigned_lit_small; lia | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
  assert (SHOK2 : sh_ok SEGS ARB_BX (arbE_SH (Some j)) Ea (mrestrict (w_H W) mem2)) end.
{ constructor; [|constructor; [|constructor]].
  - apply (arb_shent ly2 S2 W mem2 md2 _ 15 bo No out 0 32 (proj1 HJ2) HboX);
    [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
    | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 15%nat) by lia; exact E15 | lia] | lia | lia | lia].
  - apply (arb_shent ly2 S2 W mem2 md2 _ 34 bt Nt (t + 48 * j) 0 48 (proj1 HJ2) HbtX);
    [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
    | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 34%nat) by lia; exact E34 | lia] | lia | lia | lia]. }
clear SHOK. rename SHOK2 into SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
  assert (HEIa : img_env VAL A_LIM Ea) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
  assert (HR : ew Ea 516 = getr regs2 10) by reflexivity end.
rewrite (proj2 (Z.eqb_neq (t + 48 * j) 0) ltac:(lia)) in Ha02.
change (reac_rival_kind_of_c.reac_rival_kind_model (disco_table_c.hd_of T j) (disco_table_c.role_of_e T j)
  (reac_arbitrate_c.slots_of T j) (reac_arbitrate_c.ch_of T j)) with (reac_arbitrate_c.rival_of T j) in Ha02.
arbE_envr E HA HD HR.
paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbE_awr HA E15 HboX out |].
arbE_kstep K HA E15. clear HF HG.
arbE_envr E HA HD HR.
destruct (arbE_out0_rest _ out pace HO) as [GM0 G10].
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
- assert (U0 : our = 0).
  { rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite (HA 11%nat) in Hc by lia.
    rewrite E11, Z.add_0_r, unsigned_lit_small in Hc by lia.
    unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia. change (0 mod 2 ^ 64) with 0 in Hc. apply Z.eqb_eq. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbE_awr HA E15 HboX out |].
  arbE_kstep K HA E15. clear HF HG.
  arbE_envr E HA HD HR.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno Hns. rewrite (K a Ha) by (cbv beta; lia). apply HK; assumption. }
  arbE_zc HS HA E15 out 1%nat 0 1 G0 ltac:(arbE_lit HA E33). rewrite Z.add_0_r in G0.
  arbE_zc HS HA E15 out 2%nat 12 0 G12 ltac:(arbE_lit HA E33).
  arbE_zc HS HA E15 out 2%nat 16 pace G16 ltac:(arbE_lit HA E33).
  arbE_zc HS HA E15 out 2%nat 20 1 G20 ltac:(arbE_lit HA E33).
  arbE_zc HS HA E15 out 2%nat 24 (reac_arbitrate_c.rival_of T j) G24
    ltac:(cbn [sv_denot]; rewrite HR, Z.add_0_r, Z_to_bv_bv_unsigned, Ha02; apply arbE_u64_mod32).
  arbE_zc HS HA E15 out 2%nat 28 (reac_arbitrate_c.ch_of T j) G28
    ltac:(rewrite arbE_sext_mod; cbn [sv_denot]; rewrite (HA 35%nat) by lia; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; apply arbE_u64_mod32).
  assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) reac_arbitrate_c.MAC0)).
  { apply (arbE_garr8_copy _ mem3 _ (out + 4) (out + 4) _ GM0). intros i Hi. cbn in Hi. apply K; [lia | cbv beta; lia]. }
  assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
  { apply (arbE_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi. apply K; [lia | cbv beta; lia]. }
  eapply (arbE_ret fq fq2 ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P (Some j) regs3 _ _ _ _ ly2 S2 Hfr2 Hcsr2 HPRE
    ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ2 HPerm2 KF).
  unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite <- Hb, EST, (proj2 (Z.eqb_eq our 0) U0). cbv iota.
  exact (arbE_bytes_garr8 _ out 1 reac_arbitrate_c.MAC0 0 pace 1 (reac_arbitrate_c.rival_of T j) (reac_arbitrate_c.ch_of T j)
    G0 eq_refl GM2 G102 G12 G16 G20 G24 G28).
- assert (U0 : our <> 0).
  { rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite (HA 11%nat) in Hc by lia.
    rewrite E11, Z.add_0_r, unsigned_lit_small in Hc by lia.
    unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia. change (0 mod 2 ^ 64) with 0 in Hc. apply Z.eqb_neq. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbE_awr HA E15 HboX out |].
  arbE_kstep K HA E15. clear HF HG.
  arbE_envr E HA HD HR.
  destruct (HP U0) as (Hbp & Hbp1 & Hbp2 & LP & GP & Hdp).
  destruct (al_blocks _ _ LAWS ly S W mem md bp Np HAR Hbp) as (_ & Hp4096 & Hpceil & _).
  assert (HbpX : In (bp, Np) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); exact Hbp).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bp Np (proj1 HJ2) HbpX) as (_ & _ & _ & _ & Hppres & _).
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
  prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
  rewrite (HA 15%nat) in Ra0 by lia. rewrite E15, unsigned_lit_small in Ra0 by lia.
  rewrite (HA 11%nat) in Ra1 by lia. rewrite E11 in Ra1.
  rewrite (HA 2%nat) in Qsp by lia. rewrite Usp in Qsp.
  rewrite (HA 3%nat) in Qgp by lia. rewrite E3 in Qgp.
  rewrite (HA 4%nat) in Qtp by lia. rewrite E4 in Qtp.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) => rename msX into msU end.
  pmkst HS.
  eapply SRr_bind.
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA AS___asan_memcpy) (AMEMCPY fq2) W (ms_regs msU) (ms_mem msU)
       REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly2 S2 _ 0 (out + 4) our 6 (-144) _ HJ2).
    - rewrite Ra0. reflexivity.
    - rewrite Ra1. reflexivity.
    - rewrite Ra2. reflexivity.
    - lia.
    - lia.
    - lia.
    - unfold spZ at 1. rewrite Qsp. apply unsigned_lit_small. lia.
    - reflexivity.
    - lia.
    - rewrite WS. unfold ESTACK. lia.
    - rewrite Qgp. exact Hgp.
    - rewrite Qtp. exact Htp.
    - exact Rra.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split; [right; left; split; [exists (out, out + 32); split; [left; reflexivity | cbn; lia]
        | exists bo, No; split; [first [exact HboX | exact Hbo] | lia]] | unfold ESTACK; lia].
    - apply (amem_range_of_block SEGS B LAWS ly2 S2 W _ _ bo No (out + 4) 6 (proj1 HJ2) HboX); lia.
    - apply (range_addressable_of_block SEGS B LAWS ly2 S2 W _ _ bo No (out + 4) 6 (proj1 HJ2) HboX); lia.
    - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W _ _ bo No (out + 4) 6 (proj1 HJ2) HboX); lia.
    - split; [lia|]. split; [lia|]. split.
      + intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (Hppres a ltac:(lia))) |].
        unfold spZ. rewrite Qsp. rewrite unsigned_lit_small by lia. unfold ESTACK. lia.
      + split; [lia|]. split; [apply (amem_range_of_block SEGS B LAWS ly2 S2 W _ _ bp Np our 6 (proj1 HJ2) HbpX); lia|].
        split; [apply (range_addressable_of_block SEGS B LAWS ly2 S2 W _ _ bp Np our 6 (proj1 HJ2) HbpX); lia|].
        intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W _ _ bp Np our 6 (proj1 HJ2) HbpX); lia. }
  cbv beta. clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp.
  intros W2 c2 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr & Hpres4 & HSM).
  assert (HfrZ : forall a, 0 <= a < 2 ^ 64 -> ~ ((out + 4 <= a < out + 10) \/ (spZ regs - 144 - ESTACK <= a < spZ regs - 144)) ->
    aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) (ms_mem msU) a).
  { intros a Ha Hz. apply Hfr; [exact Ha | intro; apply Hz; left; lia | intro; apply Hz; right; lia]. }
  assert (GM : garr8 SEGS (mrestrict (w_H W) mem4) (out + 4) (map (fun b0 : byte => bv_unsigned b0) P)).
  { apply (arbE_garr8_copy _ mem _ our (out + 4) _ GP). intros i Hi. rewrite length_map, LP in Hi.
    rewrite Heff by lia. rewrite (K (our + i)); [| lia | cbv beta; lia]. apply HK; lia. }
  assert (G104 : garr8 SEGS (mrestrict (w_H W) mem4) (out + 10) [0; 0]).
  { apply (arbE_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi.
    rewrite HfrZ by (unfold ESTACK; lia). apply K; [lia | cbv beta; lia]. }
  pose proof (arbE_kept_step _ _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) K HfrZ
    ltac:(intros a Hq; cbv beta in Hq |- *; lia) ltac:(intros a Hq; cbv beta in Hq |- *; rewrite WS; unfold ESTACK in Hq; lia)) as K2.
  clear K.
  jafter_call_keep_hi HS 1024%nat regs4 (mrestrict (w_H W) mem4) HP4 [0; 1; 2; 3]%nat HS2.
  match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [ | | | | apply Forall_nil].
    - eapply region_kept_aview; [rewrite (HA 2%nat) by lia; exact Usp | | exact Hpres4].
      intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
    - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact Hpres4].
      intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
    - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact Hpres4].
      intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
    - eapply region_kept_aview; [rewrite (HA 34%nat) by lia; rewrite E34; apply unsigned_lit_small; lia | | exact Hpres4].
      intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
    assert (SHOK2 : sh_ok SEGS ARB_BX (arbE_SH (Some j)) Ea (mrestrict (w_H W) mem4)) end.
  { constructor; [|constructor; [|constructor]].
    - apply (arb_shent ly2 S2 W mem4 md4 _ 15 bo No out 0 32 (proj1 HJ4) HboX);
      [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
      | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 15%nat) by lia; exact E15 | lia] | lia | lia | lia].
    - apply (arb_shent ly2 S2 W mem4 md4 _ 34 bt Nt (t + 48 * j) 0 48 (proj1 HJ4) HbtX);
      [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
      | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 34%nat) by lia; exact E34 | lia] | lia | lia | lia]. }
  clear SHOK. rename SHOK2 into SHOK.
  lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
    assert (HEIb : img_env VAL A_LIM Ea) by (apply img_env_havoc_hi; [assumption | cbv; lia]) end.
  arbE_envr E HA HD HR.
  pose proof (arbE_kept_refl W mem4 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as KM.
  paj_run_tok RUN HS HJ4 SHOK ARB_SPAN; [arbE_awr HA E15 HboX out |].
  lazymatch goal with HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => pose proof HFr' as HFr2 end.
  arbE_kstep K2 HA E15. arbE_kstep KM HA E15. clear HF HG.
  arbE_envr E HA HD HR.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno Hns. rewrite (K2 a Ha) by (cbv beta; lia). apply HK; assumption. }
  arbE_zc HS HA E15 out 1%nat 0 1 G0 ltac:(arbE_lit HA E33). rewrite Z.add_0_r in G0.
  arbE_zc HS HA E15 out 2%nat 12 1 G12 ltac:(arbE_lit HA E33).
  arbE_zc HS HA E15 out 2%nat 16 pace G16 ltac:(arbE_lit HA E33).
  arbE_zc HS HA E15 out 2%nat 20 1 G20 ltac:(arbE_lit HA E33).
  arbE_zc HS HA E15 out 2%nat 24 (reac_arbitrate_c.rival_of T j) G24
    ltac:(cbn [sv_denot]; rewrite HR, Z.add_0_r, Z_to_bv_bv_unsigned, Ha02; apply arbE_u64_mod32).
  arbE_zc HS HA E15 out 2%nat 28 (reac_arbitrate_c.ch_of T j) G28
    ltac:(rewrite arbE_sext_mod; cbn [sv_denot]; rewrite (HA 35%nat) by lia; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; apply arbE_u64_mod32).
  assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) P)).
  { apply (arbE_garr8_copy _ mem4 _ (out + 4) (out + 4) _ GM). intros i Hi. rewrite length_map, LP in Hi.
    apply KM; [lia | cbv beta; lia]. }
  assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
  { apply (arbE_garr8_copy _ mem4 _ (out + 10) (out + 10) _ G104). intros i Hi. cbn in Hi. apply KM; [lia | cbv beta; lia]. }
  eapply (arbE_ret fq fq2 ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P (Some j) regs3 _ _ _ _ ly2 S2 Hfr2 Hcsr2 HPRE
    ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ4 HPerm2 KF).
  unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite <- Hb, EST, (proj2 (Z.eqb_neq our 0) U0). cbv iota.
  exact (arbE_bytes_garr8 _ out 1 P 1 pace 1 (reac_arbitrate_c.rival_of T j) (reac_arbitrate_c.ch_of T j)
    G0 LP GM2 G102 G12 G16 G20 G24 G28).
Qed.

Lemma arbE_none : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invE ly S W regs mem md t our fsm pace now out T P None regs3 mem3 md3 ->
  SRr SEGS W (arb_post_cfg fq AF_ARB_E regs3 mem3 md3) (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs3 mem3 md3 HPRE HINV.
unfold arb_post_cfg.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
destruct (arbE_entry fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P None regs3 mem3 md3 HPRE HINV) as [HS SHOK].
pose proof HINV as ((HJ & HK & HFR & HO & R2 & R3 & R4 & R9 & R24) & R18 & R19 & R8 & Hb & EST).
unfold arb_est in EST.
pose proof HPRE as (HAF & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
assert (Htc : 0 <= t < alloc_ceiling).
{ destruct (Z.eq_dec t 0) as [->|Ht0]; [lia|]. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & _).
  destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & _ & Htceil & _). lia. }
remember (arbE_EQ regs regs3 pace t T None) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold arbE_EQ; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbE_X regs3 pace t T None)) n)
  by (intros n Hn; subst E; unfold arbE_EQ; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E11 : ew E 11 = Z_to_bv 64 our) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pace mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HA : forall n, (n < 240)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (HD : ed E = ed E) by reflexivity.
pose proof (arbE_kept_refl W mem3 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as K.
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbE_awr HA E15 Hbo out |].
arbE_kstep K HA E15. clear HF HG.
arbE_envt E HA HD.
assert (WR : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
pose proof pa_B_ok as (HB0 & HB1 & _).
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (8%bv : bv 5) Qs0.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
rewrite (HA 10%nat) in Qs0 by lia. rewrite E10 in Qs0.
rewrite (HA 2%nat) in Qsp by lia. rewrite Usp in Qsp.
rewrite (HA 3%nat) in Qgp by lia. rewrite E3 in Qgp.
rewrite (HA 4%nat) in Qtp by lia. rewrite E4 in Qtp.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msX) _) ?mdX) _ =>
  eapply (arbE_rival_at fq ly S W regs mem md out ly S (ms_regs msX) (ms_mem msX) mdX 0 0 0 0 0 _ HJ HROD) end.
  - rewrite Ra0. reflexivity.
  - lia.
  - reflexivity.
  - intros Hne. exfalso. apply Hne. reflexivity.
  - unfold spZ at 1. rewrite Qsp. rewrite unsigned_lit_small by lia. lia.
  - rewrite Qgp. exact Hgp.
  - rewrite Qtp. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite Qs0. rewrite unsigned_lit_small by lia. lia. }
cbv beta. clear Ra0 Rra Qs0 Qsp Qgp Qtp.
intros W2 c2 _ (-> & fq2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfr2 & Hcsr2 & HJ2 & HP2 & Ha02 & HPerm2 & Hkp2).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HsP2 & _).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 144 - REAC_RIVAL_KIND_OF_STK <= a < spZ regs - 144) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem msX) a)
    by (intros a Ha Hn; exact (arbE_aview_call (w_H W) (ms_mem msX) mem2 _ _ a Hkp2 Ha Hn));
  assert (PC : forall a, apresent (w_H W) (ms_mem msX) a -> apresent (w_H W) mem2 a)
    by (apply (arbE_pres_call (w_H W) (ms_mem msX) mem2 _ _ Hkp2); intros a Ha; apply HsP2; rewrite WS; rewrite WR in Ha; lia) end.
lazymatch type of K with arbE_kept _ _ ?mq ?Zx =>
  pose proof (arbE_kept_step W mem3 mq mem2 Zx (fun a => spZ regs - 144 - REAC_RIVAL_KIND_OF_STK <= a < spZ regs - 144) Zx K KC
    ltac:(intros a Hq; exact Hq) ltac:(intros a Hq; cbv beta in Hq |- *; rewrite WR in Hq; rewrite WS; lia)) as K2 end.
clear K. rename K2 into K.
assert (HboX : In (bo, No) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); exact Hbo).
pose proof (YA0o.st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms. rewrite Hms in HS. clear Hms.
rewrite restrict_mkst_fx in HS.
pose proof (FpStep.fp_st_ok_fx SEGS fq fq2 _ _ _ _ _ _ HS) as HSq. clear HS. rename HSq into HS.
clear RUN RUNTO BR.
pose proof (paj_run (fx := fq2) B LAWS) as RUN. pose proof (paj_run_to (fx := fq2) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq2) (PI := PI)) as BR.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; [ | | | apply Forall_nil].
  - eapply region_kept_aview; [rewrite (HA 2%nat) by lia; exact Usp | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia.
  - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia.
  - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
  assert (SHOK2 : sh_ok SEGS ARB_BX (arbE_SH None) Ea (mrestrict (w_H W) mem2)) end.
{ constructor; [|constructor].
  apply (arb_shent ly2 S2 W mem2 md2 _ 15 bo No out 0 32 (proj1 HJ2) HboX);
  [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
  | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 15%nat) by lia; exact E15 | lia] | lia | lia | lia]. }
clear SHOK. rename SHOK2 into SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
  assert (HEIa : img_env VAL A_LIM Ea) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
  assert (HR : ew Ea 516 = getr regs2 10) by reflexivity end.
rewrite Z.eqb_refl in Ha02.
arbE_envr E HA HD HR.
paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbE_awr HA E15 HboX out |].
arbE_kstep K HA E15. clear HF HG.
arbE_envr E HA HD HR.
destruct (arbE_out0_rest _ out pace HO) as [GM0 G10].
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
- assert (U0 : our = 0).
  { rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite (HA 11%nat) in Hc by lia.
    rewrite E11, Z.add_0_r, unsigned_lit_small in Hc by lia.
    unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia. change (0 mod 2 ^ 64) with 0 in Hc. apply Z.eqb_eq. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbE_awr HA E15 HboX out |].
  arbE_kstep K HA E15. clear HF HG.
  arbE_envr E HA HD HR.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno Hns. rewrite (K a Ha) by (cbv beta; lia). apply HK; assumption. }
  arbE_zc HS HA E15 out 1%nat 0 1 G0 ltac:(arbE_lit HA E33). rewrite Z.add_0_r in G0.
  arbE_zc HS HA E15 out 2%nat 12 0 G12 ltac:(arbE_lit HA E33).
  arbE_zc HS HA E15 out 2%nat 16 pace G16 ltac:(arbE_lit HA E33).
  arbE_zc HS HA E15 out 2%nat 20 0 G20 ltac:(arbE_lit HA E33).
  arbE_zc HS HA E15 out 2%nat 24 0 G24
    ltac:(cbn [sv_denot]; rewrite HR, Z.add_0_r, Z_to_bv_bv_unsigned, Ha02; apply arbE_u64_mod32).
  arbE_zc HS HA E15 out 2%nat 28 0 G28 ltac:(arbE_lit HA E33).
  assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) reac_arbitrate_c.MAC0)).
  { apply (arbE_garr8_copy _ mem3 _ (out + 4) (out + 4) _ GM0). intros i Hi. cbn in Hi. apply K; [lia | cbv beta; lia]. }
  assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
  { apply (arbE_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi. apply K; [lia | cbv beta; lia]. }
  eapply (arbE_ret fq fq2 ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P None regs3 _ _ _ _ ly2 S2 Hfr2 Hcsr2 HPRE
    ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ2 HPerm2 KF).
  unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite <- Hb, EST, (proj2 (Z.eqb_eq our 0) U0). cbv iota.
  exact (arbE_bytes_garr8 _ out 1 reac_arbitrate_c.MAC0 0 pace 0 0 0 G0 eq_refl GM2 G102 G12 G16 G20 G24 G28).
- assert (U0 : our <> 0).
  { rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite (HA 11%nat) in Hc by lia.
    rewrite E11, Z.add_0_r, unsigned_lit_small in Hc by lia.
    unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia. change (0 mod 2 ^ 64) with 0 in Hc. apply Z.eqb_neq. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbE_awr HA E15 HboX out |].
  arbE_kstep K HA E15. clear HF HG.
  arbE_envr E HA HD HR.
  destruct (HP U0) as (Hbp & Hbp1 & Hbp2 & LP & GP & Hdp).
  destruct (al_blocks _ _ LAWS ly S W mem md bp Np HAR Hbp) as (_ & Hp4096 & Hpceil & _).
  assert (HbpX : In (bp, Np) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); exact Hbp).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bp Np (proj1 HJ2) HbpX) as (_ & _ & _ & _ & Hppres & _).
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
  prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
  rewrite (HA 15%nat) in Ra0 by lia. rewrite E15, unsigned_lit_small in Ra0 by lia.
  rewrite (HA 11%nat) in Ra1 by lia. rewrite E11 in Ra1.
  rewrite (HA 2%nat) in Qsp by lia. rewrite Usp in Qsp.
  rewrite (HA 3%nat) in Qgp by lia. rewrite E3 in Qgp.
  rewrite (HA 4%nat) in Qtp by lia. rewrite E4 in Qtp.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) => rename msX into msU end.
  pmkst HS.
  eapply SRr_bind.
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA AS___asan_memcpy) (AMEMCPY fq2) W (ms_regs msU) (ms_mem msU)
       REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly2 S2 _ 0 (out + 4) our 6 (-144) _ HJ2).
    - rewrite Ra0. reflexivity.
    - rewrite Ra1. reflexivity.
    - rewrite Ra2. reflexivity.
    - lia.
    - lia.
    - lia.
    - unfold spZ at 1. rewrite Qsp. apply unsigned_lit_small. lia.
    - reflexivity.
    - lia.
    - rewrite WS. unfold ESTACK. lia.
    - rewrite Qgp. exact Hgp.
    - rewrite Qtp. exact Htp.
    - exact Rra.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split; [right; left; split; [exists (out, out + 32); split; [left; reflexivity | cbn; lia]
        | exists bo, No; split; [first [exact HboX | exact Hbo] | lia]] | unfold ESTACK; lia].
    - apply (amem_range_of_block SEGS B LAWS ly2 S2 W _ _ bo No (out + 4) 6 (proj1 HJ2) HboX); lia.
    - apply (range_addressable_of_block SEGS B LAWS ly2 S2 W _ _ bo No (out + 4) 6 (proj1 HJ2) HboX); lia.
    - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W _ _ bo No (out + 4) 6 (proj1 HJ2) HboX); lia.
    - split; [lia|]. split; [lia|]. split.
      + intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (Hppres a ltac:(lia))) |].
        unfold spZ. rewrite Qsp. rewrite unsigned_lit_small by lia. unfold ESTACK. lia.
      + split; [lia|]. split; [apply (amem_range_of_block SEGS B LAWS ly2 S2 W _ _ bp Np our 6 (proj1 HJ2) HbpX); lia|].
        split; [apply (range_addressable_of_block SEGS B LAWS ly2 S2 W _ _ bp Np our 6 (proj1 HJ2) HbpX); lia|].
        intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W _ _ bp Np our 6 (proj1 HJ2) HbpX); lia. }
  cbv beta. clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp.
  intros W2 c2 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr & Hpres4 & HSM).
  assert (HfrZ : forall a, 0 <= a < 2 ^ 64 -> ~ ((out + 4 <= a < out + 10) \/ (spZ regs - 144 - ESTACK <= a < spZ regs - 144)) ->
    aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) (ms_mem msU) a).
  { intros a Ha Hz. apply Hfr; [exact Ha | intro; apply Hz; left; lia | intro; apply Hz; right; lia]. }
  assert (GM : garr8 SEGS (mrestrict (w_H W) mem4) (out + 4) (map (fun b0 : byte => bv_unsigned b0) P)).
  { apply (arbE_garr8_copy _ mem _ our (out + 4) _ GP). intros i Hi. rewrite length_map, LP in Hi.
    rewrite Heff by lia. rewrite (K (our + i)); [| lia | cbv beta; lia]. apply HK; lia. }
  assert (G104 : garr8 SEGS (mrestrict (w_H W) mem4) (out + 10) [0; 0]).
  { apply (arbE_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi.
    rewrite HfrZ by (unfold ESTACK; lia). apply K; [lia | cbv beta; lia]. }
  pose proof (arbE_kept_step _ _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) K HfrZ
    ltac:(intros a Hq; cbv beta in Hq |- *; lia) ltac:(intros a Hq; cbv beta in Hq |- *; rewrite WS; unfold ESTACK in Hq; lia)) as K2.
  clear K.
  jafter_call_keep_hi HS 1024%nat regs4 (mrestrict (w_H W) mem4) HP4 [0; 1; 2]%nat HS2.
  match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [ | | | apply Forall_nil].
    - eapply region_kept_aview; [rewrite (HA 2%nat) by lia; exact Usp | | exact Hpres4].
      intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
    - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact Hpres4].
      intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
    - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact Hpres4].
      intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
    assert (SHOK2 : sh_ok SEGS ARB_BX (arbE_SH None) Ea (mrestrict (w_H W) mem4)) end.
  { constructor; [|constructor].
    apply (arb_shent ly2 S2 W mem4 md4 _ 15 bo No out 0 32 (proj1 HJ4) HboX);
    [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
    | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 15%nat) by lia; exact E15 | lia] | lia | lia | lia]. }
  clear SHOK. rename SHOK2 into SHOK.
  lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
    assert (HEIb : img_env VAL A_LIM Ea) by (apply img_env_havoc_hi; [assumption | cbv; lia]) end.
  arbE_envr E HA HD HR.
  pose proof (arbE_kept_refl W mem4 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as KM.
  paj_run_tok RUN HS HJ4 SHOK ARB_SPAN; [arbE_awr HA E15 HboX out |].
  lazymatch goal with HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => pose proof HFr' as HFr2 end.
  arbE_kstep K2 HA E15. arbE_kstep KM HA E15. clear HF HG.
  arbE_envr E HA HD HR.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno Hns. rewrite (K2 a Ha) by (cbv beta; lia). apply HK; assumption. }
  arbE_zc HS HA E15 out 1%nat 0 1 G0 ltac:(arbE_lit HA E33). rewrite Z.add_0_r in G0.
  arbE_zc HS HA E15 out 2%nat 12 1 G12 ltac:(arbE_lit HA E33).
  arbE_zc HS HA E15 out 2%nat 16 pace G16 ltac:(arbE_lit HA E33).
  arbE_zc HS HA E15 out 2%nat 20 0 G20 ltac:(arbE_lit HA E33).
  arbE_zc HS HA E15 out 2%nat 24 0 G24
    ltac:(cbn [sv_denot]; rewrite HR, Z.add_0_r, Z_to_bv_bv_unsigned, Ha02; apply arbE_u64_mod32).
  arbE_zc HS HA E15 out 2%nat 28 0 G28 ltac:(arbE_lit HA E33).
  assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) P)).
  { apply (arbE_garr8_copy _ mem4 _ (out + 4) (out + 4) _ GM). intros i Hi. rewrite length_map, LP in Hi.
    apply KM; [lia | cbv beta; lia]. }
  assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
  { apply (arbE_garr8_copy _ mem4 _ (out + 10) (out + 10) _ G104). intros i Hi. cbn in Hi. apply KM; [lia | cbv beta; lia]. }
  eapply (arbE_ret fq fq2 ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P None regs3 _ _ _ _ ly2 S2 Hfr2 Hcsr2 HPRE
    ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ4 HPerm2 KF).
  unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite <- Hb, EST, (proj2 (Z.eqb_neq our 0) U0). cbv iota.
  exact (arbE_bytes_garr8 _ out 1 P 1 pace 0 0 0 G0 LP GM2 G102 G12 G16 G20 G24 G28).
Qed.

Lemma arb_segE : ARB_SEGE.
Proof.
unfold ARB_SEGE.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P b regs3 mem3 md3 HPRE HINV.
destruct b as [j|].
- exact (arbE_some fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P j regs3 mem3 md3 HPRE HINV).
- exact (arbE_none fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs3 mem3 md3 HPRE HINV).
Qed.
Definition arbN_srf (i : nat) : sv :=
  match i with
  | 0%nat => SLit 0 | 2%nat => SOff 2 (-144) | 3%nat => SOff 3 0 | 4%nat => SOff 4 0
  | 9%nat => SOff 11 0 | 18%nat => SOff 15 0 | 20%nat => SOff 12 0 | 24%nat => SOff 32 0
  | _ => SOff (33 + i) 0
  end.
Definition arbN_sr : list sv := map arbN_srf (seq 0 32).
Definition arbN_extra (regs3 : bvmap 5 word) : list word := Z_to_bv 64 SB :: map (getr regs3) all_regs.
Definition arbN_E (regs regs3 : bvmap 5 word) : env := Eimg (Ereg regs (arbN_extra regs3)).
Definition arbN_regions : smem :=
  [ YP09.mkRegion (Some 2%nat) (-144) 0 0 0 ARB_STKA;
    YP09.mkRegion (Some 15%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SLit 0))];
    YP09.mkRegion (Some 15%nat) 4 10 4 4 [YP09.mkChunk 4 (CVal 4 (SLit 0)); YP09.mkChunk 8 (CVal 2 (SLit 0))];
    YP09.mkRegion (Some 15%nat) 10 16 12 16 [YP09.mkChunk 10 (CVal 2 (SLit 0)); YP09.mkChunk 12 (CVal 4 (SLit 0))] ].
Definition arbN_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (15%nat, mkAF 4096 140737479966720 2); (32%nat, mkAF SB SB 0) ] [] [].
Definition arbN_ss : sstate := mkSS AF_ARB_N arbN_sr arbN_regions None arbN_facts.
Definition arbN_SH : list shent := [ mkSHE 15 0 32 ].

Lemma arbN_vm0 : forall m a (L : list Z) (o : Z) (n : nat),
  garr8 SEGS m a L -> 0 <= o -> o + Z.of_nat n <= Z.of_nat (length L) ->
  (forall k, (k < n)%nat -> nth (Z.to_nat o + k) L 0 = 0) -> val_mem SEGS m (a + o) n 0.
Proof.
intros m a L o n HG Ho Hn HZ k Hk.
replace (a + o + Z.of_nat k) with (a + Z.of_nat (Z.to_nat o + k)) by lia.
rewrite (garr8_mbyte SEGS m a L (Z.to_nat o + k) HG ltac:(lia)). rewrite (HZ k Hk). f_equal.
unfold YO0f.le_byte. rewrite (Z.mod_0_l (2 ^ (8 * Z.of_nat n))) by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma arbN_stk_ok : forall E m (regs : bvmap 5 word),
  arb_frame m regs -> (forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n))) ->
  Forall (YP09.chunk_ok SEGS E m (spZ regs)) ARB_STKA.
Proof.
intros E m regs HF AG.
assert (K : forall (od : Z) (n : nat) (r : Z), In (144 + od, r) ARB_SAVES -> (n < 32)%nat -> r = Z.of_nat n ->
  YP09.chunk_ok SEGS E m (spZ regs) (YP09.mkChunk od (CVal 8 (SOff n 0)))).
{ intros od n r Hin Hn ->. pose proof (HF _ Hin) as V. cbn [fst snd] in V.
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat n)))) as Rg. unfold bv_modulus in Rg.
  apply (chunk_ok_val SEGS E m (spZ regs) od 8 (SOff n 0) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat n))))).
  - cbn [sv_denot]. rewrite (AG n Hn), Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ Z.of_N 64) with (2 ^ 64) in Rg. lia.
  - lia.
  - replace (spZ regs + od) with (spZ regs - 144 + (144 + od)) by lia. exact V. }
unfold ARB_STKA. repeat apply Forall_cons; try apply Forall_nil;
(eapply K; [cbn [ARB_SAVES In]; repeat (first [left; reflexivity | right]) | lia | reflexivity]).
Qed.

Lemma arbN_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invN ly S W regs mem md t our fsm pace now out T P regs3 mem3 md3 ->
  st_ok_pi (fx := fq) SEGS VAL (arbN_E regs regs3) arbN_ss
    (restrict (w_H W) (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_N)) mem3 (seg_rom SEGS)))
  /\ sh_ok SEGS ARB_BX arbN_SH (arbN_E regs regs3) (mrestrict (w_H W) mem3).
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs3 mem3 md3 HA HI.
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HPP).
destruct HI as ((HJ & MEQ & HFR & HOUT & R2 & R3 & R4 & R9 & R24) & R18 & R20 & Hbest & Hest).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS ly S W mem3 md3 bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ bo No HAR Hbo) as Hoimg.
unfold off_img, IMG_LO, IMG_TOP in Hoimg.
rewrite restrict_mkst_fx.
set (E := arbN_E regs regs3).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbN_extra regs3)) n)
  by (intros n Hn; subst E; unfold arbN_E; apply Eimg_low; exact Hn).
assert (AG : forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n)))
  by (intros n Hn; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_lt; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 our) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 fsm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (LO : Z.of_nat (length (arb_out0 pace)) = 32) by reflexivity.
split.
- unfold arbN_ss. apply pa_entry_st_ok_full.
  + apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [ lazymatch goal with |- _ = sv_denot ?Ex (sr_get ?sr ?rr) =>
          let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end;
        cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
        first
        [ solve [rewrite getr_zero; reflexivity]
        | solve [rewrite R2, Usp; f_equal; lia]
        | solve [rewrite R3, E3; reflexivity]
        | solve [rewrite R4, E4; reflexivity]
        | solve [rewrite R9, E11; reflexivity]
        | solve [rewrite R18, E15; reflexivity]
        | solve [rewrite R20, E12; reflexivity]
        | solve [rewrite R24, E32; reflexivity]
        | solve [rewrite EL by (unfold A_TEXT; lia); reflexivity] ]
      | ]).
    destruct Hr.
  + vm_compute. reflexivity.
  + unfold arbN_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply (arbN_stk_ok E _ regs HFR AG).
    * rewrite (VB 15%nat out E15) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hopres (out + o) ltac:(lia)))|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ out 0 4 (SLit 0) 0); [reflexivity | zside | zside |].
      apply (arbN_vm0 _ out (arb_out0 pace) 0 4 HOUT); [lia | rewrite LO; lia |].
      intros k Hk. destruct k as [|[|[|[|k]]]]; [reflexivity..|lia].
    * rewrite (VB 15%nat out E15) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ out 4 4 (SLit 0) 0); [reflexivity | zside | zside |].
         apply (arbN_vm0 _ out (arb_out0 pace) 4 4 HOUT); [lia | rewrite LO; lia |].
         intros k Hk. destruct k as [|[|[|[|k]]]]; [reflexivity..|lia].
      -- apply (chunk_ok_val SEGS E _ out 8 2 (SLit 0) 0); [reflexivity | zside | zside |].
         apply (arbN_vm0 _ out (arb_out0 pace) 8 2 HOUT); [lia | rewrite LO; lia |].
         intros k Hk. destruct k as [|[|k]]; [reflexivity..|lia].
    * rewrite (VB 15%nat out E15) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hopres (out + o) ltac:(lia)))|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ out 10 2 (SLit 0) 0); [reflexivity | zside | zside |].
         apply (arbN_vm0 _ out (arb_out0 pace) 10 2 HOUT); [lia | rewrite LO; lia |].
         intros k Hk. destruct k as [|[|k]]; [reflexivity..|lia].
      -- apply (chunk_ok_val SEGS E _ out 12 4 (SLit 0) 0); [reflexivity | zside | zside |].
         apply (arbN_vm0 _ out (arb_out0 pace) 12 4 HOUT); [lia | rewrite LO; lia |].
         intros k Hk. destruct k as [|[|[|[|k]]]]; [reflexivity..|lia].
  + apply pairwise_disjoint_of_extents. unfold arbN_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 15%nat out E15) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Hoceil Hoia Hoimg Ho4096 Hbo1 Hbo2 C1 C3 WS Hstk0.
    clear. unfold in_app. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [arbN_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E15, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hoceil Ho4096 Hbo1 Hbo2 Hal16 Ho4 C1 C3 WS Hstk0.
    clear. unfold SB. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, arbN_SH. constructor; [|constructor].
  apply (arb_shent ly S W mem3 md3 E 15 bo No out 0 32 HAR Hbo); [apply arb_U_BX; exact E32 | apply arb_U_atom; [exact E15 | lia] | lia | lia | lia].
Qed.

Lemma arbN_fsm_br : forall E fsm, ew E 12 = Z_to_bv 64 fsm -> - 2 ^ 31 <= fsm < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SOff 12 0)) (sv_denot E (SLit 1)) = negb (fsm =? 1).
Proof.
intros E fsm H Hf. change BC_NE with (neg_bc BC_EQ). rewrite branch_taken_neg. f_equal.
cbn [branch_taken sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. apply reac_arbitrate.prob_eq. exact Hf.
Qed.

Lemma arbN_model : forall t our (T P : list byte) fsm pace now,
  reac_arbitrate_c.best t T P our now = None -> arb_est fsm = false ->
  reac_arbitrate_c.arb_model t our T P fsm pace now =
  if fsm =? 1 then reac_arbitrate_c.arb_bytes 1 (if our =? 0 then reac_arbitrate_c.MAC0 else P) (if our =? 0 then 0 else 1) pace 0 0 0
  else reac_arbitrate_c.arb_bytes 0 reac_arbitrate_c.MAC0 0 pace 0 0 0.
Proof.
intros t our T P fsm pace now Hb He. unfold reac_arbitrate_c.arb_model. rewrite Hb. unfold arb_est in He. rewrite He. reflexivity.
Qed.

Lemma arbN_z4 : forall m a v, 0 <= v < 2 ^ 32 -> val_mem SEGS m a 4 v ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)).
Proof.
intros m a v Hv HV. assert (LZ : length (reac_arbitrate_c.z4 v) = 4%nat) by reflexivity.
apply (arb_garr8_val_mem m a _ v); rewrite LZ; [exact HV|].
change (reac_arbitrate_c.z4 v) with (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v))).
rewrite bytes_le_Z_to_le by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 v)); lia).
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma arbN_mac0 : forall m a, val_mem SEGS m a 4 0 -> val_mem SEGS m (a + 4) 2 0 ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) reac_arbitrate_c.MAC0).
Proof.
intros m a V0 V4.
change (map (fun b : byte => bv_unsigned b) reac_arbitrate_c.MAC0) with
  (map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) 4) ++ map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) 2)).
apply garr8_app. split.
- apply (arb_garr8_val_mem m a _ 0); [exact V0 | reflexivity].
- rewrite length_map, repeat_length. apply (arb_garr8_val_mem m _ _ 0); [exact V4 | reflexivity].
Qed.

Lemma arbN_out_asm : forall m out pace (st hv : Z) (mac : list byte),
  length mac = 6%nat -> 0 <= st < 2 ^ 32 -> 0 <= hv < 2 ^ 32 ->
  val_mem SEGS m out 4 st -> garr8 SEGS m (out + 4) (map (fun b : byte => bv_unsigned b) mac) ->
  val_mem SEGS m (out + 10) 2 0 -> val_mem SEGS m (out + 12) 4 hv ->
  garr8 SEGS m (out + 16) (skipn 16 (arb_out0 pace)) ->
  garr8 SEGS m out (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.arb_bytes st mac hv pace 0 0 0)).
Proof.
intros m out pace st hv mac Lm Hst Hhv V0 G4 V10 V12 G16.
assert (HS16 : skipn 16 (arb_out0 pace) =
  map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 pace) ++ map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 0) ++
  map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 0) ++ map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 0)) by reflexivity.
assert (L4 : forall v, length (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)) = 4%nat) by reflexivity.
unfold reac_arbitrate_c.arb_bytes. rewrite !map_app.
apply garr8_app. split; [exact (arbN_z4 m out st Hst V0)|]. rewrite L4.
apply garr8_app. split; [replace (out + Z.of_nat 4) with (out + 4) by lia; exact G4|]. rewrite length_map, Lm.
apply garr8_app. split.
{ apply (arb_garr8_val_mem m _ [Z_to_bv 8 0; Z_to_bv 8 0] 0); [|reflexivity].
  replace (out + Z.of_nat 4 + Z.of_nat 6) with (out + 10) by lia. exact V10. }
change (length (map (fun b : byte => bv_unsigned b) [Z_to_bv 8 0; Z_to_bv 8 0])) with 2%nat.
apply garr8_app. split; [replace (out + Z.of_nat 4 + Z.of_nat 6 + Z.of_nat 2) with (out + 12) by lia; exact (arbN_z4 m _ hv Hhv V12)|].
rewrite L4. replace (out + Z.of_nat 4 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 4) with (out + 16) by lia.
rewrite HS16 in G16. exact G16.
Qed.

Lemma arbN_hi16 : forall H (m3 m : word -> option byte) out pace,
  garr8 SEGS (mrestrict H m3) out (arb_out0 pace) ->
  (forall a, out + 16 <= a < out + 32 -> aview SEGS H m a = aview SEGS H m3 a) ->
  garr8 SEGS (mrestrict H m) (out + 16) (skipn 16 (arb_out0 pace)).
Proof.
intros H m3 m out pace HG HK.
assert (LO : length (arb_out0 pace) = 32%nat) by reflexivity.
pose proof (garr8_sub_x SEGS _ out (arb_out0 pace) 16 16 HG ltac:(rewrite LO; lia)) as G.
assert (EQ : firstn 16 (skipn 16 (arb_out0 pace)) = skipn 16 (arb_out0 pace)) by (apply firstn_all2; rewrite length_skipn, LO; lia).
rewrite EQ in G. replace (out + Z.of_nat 16) with (out + 16) in G by lia.
apply (garr8_aview_kept SEGS H H m3 m (out + 16)); [|exact G].
intros a Ha. rewrite length_skipn, LO in Ha. apply HK. lia.
Qed.

Lemma arbN_fld : forall E m (out : Z) lo hi wlo whi cs od (w : N) (v : Z),
  region_ok SEGS E m (YP09.mkRegion (Some 15%nat) lo hi wlo whi cs) -> ew E 15 = Z_to_bv 64 out -> 0 <= out < 2 ^ 64 ->
  In (YP09.mkChunk od (CVal w (SLit v))) cs -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS m (out + od) (N.to_nat w) v.
Proof.
intros E m out lo hi wlo whi cs od w v HR H15 Ho Hin Hv Hw.
eapply field_of_region; [exact HR | rewrite H15; apply unsigned_lit_small; exact Ho | exact Hin | reflexivity | exact Hv | exact Hw].
Qed.

Lemma arbN_leaf : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (regs3 : bvmap 5 word) mem3 md3
    E ss ms mdf extra,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invN ly S W regs mem md t our fsm pace now out T P regs3 mem3 md3 ->
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S W (ms_mem ms) mdf 0 ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  plookup (@pl_tpi _ PL_both3_0) (ss_pc ss) = Some (PW RET_WORD_r) ->
  env_agree 32 (Ereg regs extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (1%bv :: CALLEE_SAVED) = true ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((out <= a < out + 16) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) out
    (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.arb_model t our T P fsm pace now)) ->
  SRr SEGS W (mkCfg ms mdf) (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs3 mem3 md3 E ss ms mdf extra
  HA HI HJf HS Hrv Hpc HAE Hcs MEQf GOUT.
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HPP).
pose proof HI as ((HJ3 & MEQ3 & _) & _).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR0 Hbo) as (_ & _ & Hoceil & _).
cbn [forallb] in Hcs. apply andb_prop in Hcs as [Hc1 Hcs].
pose proof (regs_kept_of_st_ok_pi E ss _ regs extra [1%bv] HS HAE ltac:(cbn [forallb]; rewrite Hc1; reflexivity) 1%bv (or_introl eq_refl)) as R1.
cbn [ms_regs restrict] in R1.
assert (MF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha N1 N2. rewrite (MEQf a Ha ltac:(intros [X|X]; [apply N1; lia | exact (N2 X)])). exact (MEQ3 a Ha N1 N2). }
apply (paj_ret_at (fx := fq) (PL := PL_both3_0) (PI := PI) W E ss ms mdf _ HS Hrv Hpc).
intros mat.
unfold treac_arbitrate_post. apply apost_base_same_fx.
exists ly, S, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdf) mat mdf).
split; [rewrite R1, Hra; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJf|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs extra HS HAE); exact Hcs|].
split; [exact R1|].
split; [apply Permutation_refl|].
split; [exact GOUT|].
split.
{ intros Ht0. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis).
  destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR0 Hbt) as (_ & _ & Htceil & _).
  apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem (ms_mem ms) t); [|exact GT].
  intros a Ha. rewrite length_map, LT in Ha. apply MF; lia. }
split.
{ intros Hp0. destruct (HPP Hp0) as (Hbp & Hbp1 & Hbp2 & LP & GP & Hdisp).
  destruct (al_blocks _ _ LAWS ly S W mem md bp Np HAR0 Hbp) as (_ & _ & Hpceil & _).
  apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem (ms_mem ms) our); [|exact GP].
  intros a Ha. rewrite length_map, LP in Ha. apply MF; lia. }
split; [reflexivity|].
intros a N1 N2. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra.
exact (MF (bv_unsigned a) Ra N1 N2).
Qed.

Lemma arb_segN : ARB_SEGN.
Proof.
unfold ARB_SEGN.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs3 mem3 md3 HA HI.
destruct (arbN_entry fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs3 mem3 md3 HA HI) as [HS SHOK].
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HPP).
pose proof HI as ((HJ & MEQ0 & HFR & HOUT & R2 & R3 & R4 & R9 & R24) & R18 & R20 & Hbest & Hest).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem3 md3 bo No (proj1 HJ) Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
remember (arbN_E regs regs3) as E eqn:HEq.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold arbN_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbN_extra regs3)) n)
  by (intros n Hn; subst E; unfold arbN_E; apply Eimg_low; exact Hn).
assert (HAE : env_agree 32 (Ereg regs (arbN_extra regs3)) E)
  by (split; [intros k Hk; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
assert (AG : forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n)))
  by (intros n Hn; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_lt; exact Hn).
assert (E11 : ew E 11 = Z_to_bv 64 our) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 fsm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; reflexivity).
clear HEq EL.
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (fun a => (out <= a < out + 16) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) a ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by (intros; reflexivity).
unfold arb_post_cfg.
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arb_awr Usp E15 Hbo |].
arb_meq Usp E15 (fun a => (out <= a < out + 16) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
- rewrite (arbN_fsm_br E fsm E12 Rfsm) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arb_awr Usp E15 Hbo |].
  arb_meq Usp E15 (fun a => (out <= a < out + 16) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
  arb_region HS 1%nat HRa. arb_region HS 2%nat HRb. arb_region HS 3%nat HRc.
  eapply (arbN_leaf fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs3 mem3 md3 E _ _ _ _
    HA HI HJ HS eq_refl ltac:(vm_compute; reflexivity) HAE ltac:(vm_compute; reflexivity) MEQ).
  rewrite (arbN_model t our T P fsm pace now Hbest Hest), (proj2 (Z.eqb_neq fsm 1) Hc).
  apply arbN_out_asm; [reflexivity | lia | lia | | | | | ].
  + pose proof (arbN_fld E _ out _ _ _ _ _ 0 4 0 HRa E15 ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
    rewrite Z.add_0_r in V. exact V.
  + apply arbN_mac0.
    * exact (arbN_fld E _ out _ _ _ _ _ 4 4 0 HRb E15 ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)).
    * replace (out + 4 + 4) with (out + 8) by lia.
      exact (arbN_fld E _ out _ _ _ _ _ 8 2 0 HRb E15 ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)).
  + exact (arbN_fld E _ out _ _ _ _ _ 10 2 0 HRc E15 ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)).
  + exact (arbN_fld E _ out _ _ _ _ _ 12 4 0 HRc E15 ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)).
  + apply (arbN_hi16 _ mem3 _ out pace HOUT). intros a Ha. apply MEQ; [lia | cbv beta; lia].
- rewrite (arbN_fsm_br E fsm E12 Rfsm) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arb_awr Usp E15 Hbo |].
  arb_meq Usp E15 (fun a => (out <= a < out + 16) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
  psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
  + rewrite branch_eq_U, (U_atom E 11 our E11 ltac:(lia)), U_SLit in Hc0. change (zcanon 0) with 0 in Hc0. apply Z.eqb_eq in Hc0.
    paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arb_awr Usp E15 Hbo |].
    arb_meq Usp E15 (fun a => (out <= a < out + 16) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
    arb_region HS 1%nat HRa. arb_region HS 2%nat HRb. arb_region HS 3%nat HRc.
    eapply (arbN_leaf fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs3 mem3 md3 E _ _ _ _
      HA HI HJ HS eq_refl ltac:(vm_compute; reflexivity) HAE ltac:(vm_compute; reflexivity) MEQ).
    rewrite (arbN_model t our T P fsm pace now Hbest Hest), (proj2 (Z.eqb_eq fsm 1) Hc), (proj2 (Z.eqb_eq our 0) Hc0).
    apply arbN_out_asm; [reflexivity | lia | lia | | | | | ].
    * pose proof (arbN_fld E _ out _ _ _ _ _ 0 4 1 HRa E15 ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
      rewrite Z.add_0_r in V. exact V.
    * apply arbN_mac0.
      -- exact (arbN_fld E _ out _ _ _ _ _ 4 4 0 HRb E15 ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)).
      -- replace (out + 4 + 4) with (out + 8) by lia.
         exact (arbN_fld E _ out _ _ _ _ _ 8 2 0 HRb E15 ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)).
    * exact (arbN_fld E _ out _ _ _ _ _ 10 2 0 HRc E15 ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)).
    * exact (arbN_fld E _ out _ _ _ _ _ 12 4 0 HRc E15 ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)).
    * apply (arbN_hi16 _ mem3 _ out pace HOUT). intros a Ha. apply MEQ; [lia | cbv beta; lia].
  + rewrite branch_eq_U, (U_atom E 11 our E11 ltac:(lia)), U_SLit in Hc0. change (zcanon 0) with 0 in Hc0. apply Z.eqb_neq in Hc0.
    paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arb_awr Usp E15 Hbo |].
    arb_meq Usp E15 (fun a => (out <= a < out + 16) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
    destruct (HPP Hc0) as (Hbp & Hbp1 & Hbp2 & LP & GP & Hdisp).
    destruct (al_blocks _ _ LAWS ly S W mem md bp Np HAR0 Hbp) as (Hp16 & Hp4096 & Hpceil & Hpia & _).
    prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
    prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
    pmkst HS.
    eapply SRr_bind.
    { lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
      eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA AS___asan_memcpy) (AMEMCPY fq) W (ms_regs msX) (ms_mem msX)
         REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S _ 0 (out + 4) our 6 (-144) _ HJ) end.
      - rewrite Ra0, E15, unsigned_lit_small by lia. reflexivity.
      - rewrite Ra1, E11. reflexivity.
      - rewrite Ra2. reflexivity.
      - lia.
      - lia.
      - lia.
      - unfold spZ at 1. rewrite Qsp, Usp. apply unsigned_lit_small. lia.
      - reflexivity.
      - lia.
      - rewrite WS. unfold ESTACK. lia.
      - rewrite Qgp, (AG 3%nat) by lia. exact Hgp.
      - rewrite Qtp, (AG 4%nat) by lia. exact Htp.
      - exact Rra.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. split; [right; left; split; [exists (out, out + 32); split; [left; reflexivity | cbn; lia] | exists bo, No; split; [exact Hbo | lia]] | unfold ESTACK; lia].
      - apply (amem_range_of_block SEGS B LAWS ly S W _ _ bo No (out + 4) 6 (proj1 HJ) Hbo); lia.
      - apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bo No (out + 4) 6 (proj1 HJ) Hbo); lia.
      - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bo No (out + 4) 6 (proj1 HJ) Hbo); lia.
      - destruct (al_blocks _ _ LAWS _ _ _ _ _ bp Np (proj1 HJ) Hbp) as (_ & _ & _ & _ & Hppres & _).
        split; [lia|]. split; [lia|]. split.
        { intros a Ha. split; [apply aview_some_of_apresent; apply (proj1 (Hppres a ltac:(lia)))|].
          unfold spZ at 1. rewrite Qsp, Usp, unsigned_lit_small by lia. unfold ESTACK. lia. }
        split; [lia|].
        split; [apply (amem_range_of_block SEGS B LAWS ly S W _ _ bp Np our 6 (proj1 HJ) Hbp); lia|].
        split; [apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bp Np our 6 (proj1 HJ) Hbp); lia|].
        intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bp Np our 6 (proj1 HJ) Hbp); lia. }
    cbv beta. clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp.
    intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2 & HSM).
    pose proof MEQ as MEQT.
    assert (MEQb : forall a, 0 <= a < 2 ^ 64 -> ~ (fun a => (out <= a < out + 16) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) a ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
    { intros a Ha N. cbv beta in N. rewrite (Hfr a Ha) by (unfold ESTACK; lia). apply MEQ; [exact Ha | cbv beta; exact N]. }
    clear MEQ. rename MEQb into MEQ.
    assert (MEQ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (fun a => a < out + 4 \/ out + 10 <= a) a ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a) by (intros; reflexivity).
    jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 3]%nat HS2.
    match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. repeat apply Forall_cons; [ | | | apply Forall_nil].
      - eapply region_kept_aview; [exact Usp | | exact Hpres2].
        intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
      - eapply region_kept_aview; [rewrite E15; apply unsigned_lit_small; lia | | exact Hpres2].
        intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
      - eapply region_kept_aview; [rewrite E15; apply unsigned_lit_small; lia | | exact Hpres2].
        intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ea := Ev) in HS end.
    assert (HEIa : img_env VAL A_LIM Ea) by (subst Ea; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
    assert (OLDa : forall n, (n < 512)%nat -> ew Ea n = ew E n) by (intros n Hn; subst Ea; rewrite YN3v.ew_havoc_old by lia; reflexivity).
    assert (HAEa : env_agree 32 (Ereg regs (arbN_extra regs3)) Ea) by (subst Ea; apply env_agree_havoc_ge; [lia | exact HAE]).
    clearbody Ea.
    assert (E15b : ew Ea 15 = Z_to_bv 64 out) by (rewrite OLDa by lia; exact E15).
    assert (E32b : ew Ea 32 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E32).
    assert (Uspb : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
    clear SHOK.
    assert (SHOK : sh_ok SEGS ARB_BX arbN_SH Ea (mrestrict (w_H W) mem2)).
    { constructor; [|constructor].
      apply (arb_shent ly S W mem2 md2 Ea 15 bo No out 0 32 (proj1 HJ2) Hbo); [apply arb_U_BX; exact E32b | apply arb_U_atom; [exact E15b | lia] | lia | lia | lia]. }
    paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arb_awr Uspb E15b Hbo |].
    lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (arb_meq_step Ef rs H mem2 m1 m2 (fun a => a < out + 4 \/ out + 10 <= a) HFr ltac:(arb_win Uspb E15b) MEQ2) as M2 end.
    clear MEQ2. rename M2 into MEQ2.
    arb_meq Uspb E15b (fun a => (out <= a < out + 16) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)).
    arb_region HS 1%nat HRa. arb_region HS 2%nat HRc.
    eapply (arbN_leaf fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs3 mem3 md3 Ea _ _ _ _
      HA HI HJ2 HS eq_refl ltac:(vm_compute; reflexivity) HAEa ltac:(vm_compute; reflexivity) MEQ).
    rewrite (arbN_model t our T P fsm pace now Hbest Hest), (proj2 (Z.eqb_eq fsm 1) Hc), (proj2 (Z.eqb_neq our 0) Hc0).
    apply arbN_out_asm; [exact LP | lia | lia | | | | | ].
    * pose proof (arbN_fld Ea _ out _ _ _ _ _ 0 4 1 HRa E15b ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
      rewrite Z.add_0_r in V. exact V.
    * apply (garr8_aview SEGS (w_H W) (w_H W) mem _ our (out + 4)); [|exact GP].
      intros i Hi. rewrite length_map, LP in Hi.
      rewrite (MEQ2 (out + 4 + i) ltac:(lia) ltac:(cbv beta; lia)), (Heff i ltac:(lia)).
      rewrite (MEQT (our + i) ltac:(lia) ltac:(cbv beta; lia)).
      apply MEQ0; lia.
    * exact (arbN_fld Ea _ out _ _ _ _ _ 10 2 0 HRc E15b ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)).
    * exact (arbN_fld Ea _ out _ _ _ _ _ 12 4 1 HRc E15b ltac:(lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia) ltac:(cbn; lia)).
    * apply (arbN_hi16 _ mem3 _ out pace HOUT). intros a Ha. apply MEQ; [lia | cbv beta; lia].
Qed.
Definition arbB_kept (W : world SEGS) (m0 m : word -> option byte) (Zx : Z -> Prop) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ Zx a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m0 a.

Lemma arbB_kept_refl : forall W m Zx, arbB_kept W m m Zx.
Proof. intros W m Zx a _ _. reflexivity. Qed.

Lemma arbB_kept_step : forall W m0 m m' (Zx Zy Zz : Z -> Prop),
  arbB_kept W m0 m Zx -> (forall a, 0 <= a < 2 ^ 64 -> ~ Zy a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, Zx a -> Zz a) -> (forall a, Zy a -> Zz a) -> arbB_kept W m0 m' Zz.
Proof.
intros W m0 m m' Zx Zy Zz K St Hx Hy a Ha Hz.
rewrite St by (try exact Ha; intro Q; apply Hz; apply Hy; exact Q).
apply K; [exact Ha | intro Q; apply Hz; apply Hx; exact Q].
Qed.

Lemma arbB_kept_frame : forall W m0 m m' (Zx : Z -> Prop) E rs,
  arbB_kept W m0 m Zx -> frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zx a) ->
  arbB_kept W m0 m' Zx.
Proof.
intros W m0 m m' Zx E rs K HF Hw a Ha Hz.
rewrite (kept_of_frame (segs := SEGS) E rs (w_H W) m m' Zx HF Hw a Ha Hz). exact (K a Ha Hz).
Qed.

Lemma arbB_garr8_copy : forall H m0 m s d l,
  garr8 SEGS (mrestrict H m0) s l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS H m (d + i) = aview SEGS H m0 (s + i)) ->
  garr8 SEGS (mrestrict H m) d l.
Proof.
intros H m0 m s d l G K j Hj. destruct (G j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r.
specialize (Hv 0%nat Hk). rewrite Z.add_0_r in Hv.
assert (A0 : aview SEGS H m0 (s + Z.of_nat j) = Some (bv_unsigned (Z_to_bv 8 (YO0f.le_byte (nth j l 0) 1 0))))
  by (unfold aview; rewrite Hv; reflexivity).
rewrite <- (K (Z.of_nat j) ltac:(lia)) in A0.
destruct (aview_byte SEGS H m (d + Z.of_nat j) _ A0) as (b & Hb & Hbv & _). rewrite Hb. f_equal.
apply bv_eq. symmetry. exact Hbv.
Qed.

Lemma arbB_chunk_val : forall (fq : YK11.FPState) E ss ms i r off (w : N) e,
  st_ok_pi (fx := fq) SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) -> (Z.of_N w <= 8) ->
  val_mem SEGS (ms_mem ms) (base_val E (YP09.r_base r) + off) (N.to_nat w) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros fq E ss ms i r off w e HS Hi Hc Hw.
pose proof (st_ok_region_nth (fx := fq) E (abs_ss VAL ss) ms i r HS Hi) as (_ & _ & _ & Hcs).
apply (val_mem_low_of_chunk SEGS E (ms_mem ms) _ off w e); [| exact Hw].
exact (proj1 (Forall_forall _ _) Hcs _ Hc).
Qed.

Lemma arbB_out0_rest : forall m out pace, garr8 SEGS m out (arb_out0 pace) ->
  garr8 SEGS m (out + 4) (map (fun b : byte => bv_unsigned b) reac_arbitrate_c.MAC0) /\ garr8 SEGS m (out + 10) [0; 0].
Proof.
intros m out pace HO.
assert (L : length (arb_out0 pace) = 32%nat) by (unfold arb_out0, reac_arbitrate_c.arb_bytes; rewrite length_map, !length_app; reflexivity).
split.
- pose proof (garr8_sub_x SEGS m out (arb_out0 pace) 4 6 HO ltac:(rewrite L; lia)) as G. exact G.
- pose proof (garr8_sub_x SEGS m out (arb_out0 pace) 10 2 HO ltac:(rewrite L; lia)) as G. exact G.
Qed.

Lemma arbB_u64_mod32 : forall v, bv_unsigned (Z_to_bv 64 v) mod 2 ^ 32 = v mod 2 ^ 32.
Proof.
intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 32 * 2 ^ 32).
rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.

Lemma arbB_z4_garr8 : forall (m : word -> option byte) a v V,
  val_mem SEGS m a 4 V -> V mod 2 ^ 32 = bv_unsigned (Z_to_bv 64 v) mod 2 ^ 32 ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)).
Proof.
intros m a v V HV HE.
assert (LZ : length (reac_arbitrate_c.z4 v) = 4%nat) by reflexivity.
apply (arb_garr8_val_mem m a _ V); [rewrite LZ; exact HV|].
rewrite LZ. change (reac_arbitrate_c.z4 v) with (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v))).
rewrite bytes_le_Z_to_le by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 v)); lia). exact HE.
Qed.

Lemma arbB_z4_chunk : forall m a V v, val_mem SEGS m a 4 (V mod 2 ^ 32) -> V mod 2 ^ 32 = v mod 2 ^ 32 ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)).
Proof.
intros m a V v H Hv. apply (arbB_z4_garr8 m a v (V mod 2 ^ 32) H). rewrite Z.mod_mod by lia. rewrite Hv. symmetry. apply arbB_u64_mod32.
Qed.

Lemma arbB_z4_ble : forall x, bytes_le_to_Z (reac_arbitrate_c.z4 x) = x mod 2 ^ 32.
Proof.
intros x. change (reac_arbitrate_c.z4 x) with (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 x))).
rewrite bytes_le_Z_to_le by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 x)); lia).
change (8 * Z.of_nat 4) with 32. apply arbB_u64_mod32.
Qed.

Lemma arbB_bytes_garr8 : forall (m : word -> option byte) out st (mac : list byte) hv pc cf rv c,
  garr8 SEGS m out (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 st)) ->
  length mac = 6%nat -> garr8 SEGS m (out + 4) (map (fun b : byte => bv_unsigned b) mac) ->
  garr8 SEGS m (out + 10) [0; 0] ->
  garr8 SEGS m (out + 12) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 hv)) ->
  garr8 SEGS m (out + 16) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 pc)) ->
  garr8 SEGS m (out + 20) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 cf)) ->
  garr8 SEGS m (out + 24) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 rv)) ->
  garr8 SEGS m (out + 28) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 c)) ->
  garr8 SEGS m out (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.arb_bytes st mac hv pc cf rv c)).
Proof.
intros m out st mac hv pc cf rv c G0 Lm G4 G10 G12 G16 G20 G24 G28.
assert (LZ : forall v, length (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)) = 4%nat)
  by (intros v; rewrite length_map; reflexivity).
unfold reac_arbitrate_c.arb_bytes. rewrite !map_app.
apply garr8_app. split; [exact G0|]. rewrite LZ.
apply garr8_app. split; [replace (out + Z.of_nat 4) with (out + 4) by lia; exact G4|]. rewrite length_map, Lm.
apply garr8_app. split; [replace (out + Z.of_nat 4 + Z.of_nat 6) with (out + 10) by lia; exact G10|].
cbn [map length].
apply garr8_app. split; [replace (out + Z.of_nat 4 + Z.of_nat 6 + Z.of_nat 2) with (out + 12) by lia; exact G12|]. rewrite LZ.
apply garr8_app. split; [replace (out + Z.of_nat 4 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 4) with (out + 16) by lia; exact G16|]. rewrite LZ.
apply garr8_app. split; [replace (out + Z.of_nat 4 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 4 + Z.of_nat 4) with (out + 20) by lia; exact G20|]. rewrite LZ.
apply garr8_app. split; [replace (out + Z.of_nat 4 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) with (out + 24) by lia; exact G24|]. rewrite LZ.
replace (out + Z.of_nat 4 + Z.of_nat 6 + Z.of_nat 2 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) with (out + 28) by lia. exact G28.
Qed.

Lemma arbB_nth_regs : forall r : bv 5, nth (Z.to_nat (bv_unsigned r)) all_regs 0%bv = r.
Proof.
apply (reg_cases_lit (fun r => nth (Z.to_nat (bv_unsigned r)) all_regs 0%bv = r)).
intros r Hr. cbv [all_regs In] in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]). destruct Hr.
Qed.

Definition arbB_X (regs3 : bvmap 5 word) (pace t : Z) (T : list byte) (j : Z) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 (pace mod 2 ^ 32); Z_to_bv 64 (t + 48 * j); Z_to_bv 64 (reac_arbitrate_c.ch_of T j)]
  ++ map (getr regs3) all_regs.
Definition arbB_E (regs regs3 : bvmap 5 word) (pace t : Z) (T : list byte) (j : Z) : env :=
  Eimg (Ereg regs (arbB_X regs3 pace t T j)).
Definition arbB_sr : list sv :=
  [SLit 0; SOff 37 0; SOff 2 (-144); SOff 3 0; SOff 4 0; SOff 41 0; SOff 42 0; SOff 43 0;
   SOff 10 0; SOff 11 0; SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0; SOff 51 0;
   SOff 52 0; SOff 53 0; SOff 15 0; SOff 34 0; SOff 56 0; SOff 57 0; SOff 58 0; SOff 59 0;
   SOff 32 0; SOff 61 0; SOff 62 0; SOff 63 0; SOff 64 0; SOff 65 0; SOff 66 0; SOff 67 0].
Definition ARBB_STK : list YP09.chunk :=
  YP09.mkChunk (-144) (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 15 16) (SLit 3)) (SOff 32 0))) ::
  YP09.mkChunk (-136) (CVal 8 (SOff 15 16)) :: ARB_STKA.
Definition arbB_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-144) 0 0 0 ARBB_STK.
Definition arbB_o0 : YP09.region := YP09.mkRegion (Some 15%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SLit 0))].
Definition arbB_o12 : YP09.region := YP09.mkRegion (Some 15%nat) 12 32 12 32
  [YP09.mkChunk 12 (CVal 4 (SLit 0)); YP09.mkChunk 16 (CVal 4 (SOff 33 0)); YP09.mkChunk 20 (CVal 4 (SLit 0));
   YP09.mkChunk 24 (CVal 4 (SLit 0)); YP09.mkChunk 28 (CVal 4 (SLit 0))].
Definition arbB_bst : YP09.region := YP09.mkRegion (Some 34%nat) 0 48 0 0 [YP09.mkChunk 20 (CVal 4 (SOff 35 0))].
Definition arbB_regions : smem := [arbB_stk; arbB_o0; arbB_o12; arbB_bst].
Definition arbB_facts : facts :=
  mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (15%nat, mkAF 4096 140737479966720 2); (32%nat, mkAF SB SB 0);
           (34%nat, mkAF 4096 140737479966720 3)] [] [].
Definition ss_arbB : sstate := mkSS AF_ARB_B arbB_sr arbB_regions None arbB_facts.
Definition arbB_SH : list shent := [mkSHE 15 0 32; mkSHE 34 0 48].

Lemma arbB_ew_ext : forall regs regs3 pace t T j (r : bv 5),
  ew (arbB_E regs regs3 pace t T j) (36 + Z.to_nat (bv_unsigned r)) = getr regs3 r.
Proof.
intros regs regs3 pace t T j r. pose proof (u5_range r) as Hr. unfold arbB_E. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (36 + Z.to_nat (bv_unsigned r))%nat with (32 + (4 + Z.to_nat (bv_unsigned r)))%nat by lia.
rewrite ew_Ereg_extra. unfold arbB_X. rewrite app_nth2 by (cbn [length]; lia). cbn [length].
replace (4 + Z.to_nat (bv_unsigned r) - 4)%nat with (Z.to_nat (bv_unsigned r)) by lia.
rewrite (nth_indep _ _ (getr regs3 0%bv)) by (rewrite length_map; cbn [length all_regs]; lia).
rewrite map_nth, arbB_nth_regs. reflexivity.
Qed.

Lemma arbB_regs_ok : forall (regs regs3 : bvmap 5 word) pace t T j out our,
  getr regs 10 = w64 t -> getr regs 11 = w64 our -> getr regs 15 = w64 out ->
  getr regs3 2 = Z_to_bv 64 (spZ regs - 144) -> getr regs3 3 = getr regs 3 -> getr regs3 4 = getr regs 4 ->
  getr regs3 8 = Z_to_bv 64 t -> getr regs3 9 = Z_to_bv 64 our -> getr regs3 18 = Z_to_bv 64 out ->
  getr regs3 19 = Z_to_bv 64 (t + 48 * j) -> getr regs3 24 = Z_to_bv 64 SB ->
  regs_ok (arbB_E regs regs3 pace t T j) arbB_sr regs3.
Proof.
intros regs regs3 pace t T j out our H10 H11 H15 R2 R3 R4 R8 R9 R18 R19 R24.
set (E := arbB_E regs regs3 pace t T j).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbB_X regs3 pace t T j)) n)
  by (intros n Hn; subst E; unfold arbB_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 our) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (t + 48 * j)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EX : forall r : bv 5, ew E (36 + Z.to_nat (bv_unsigned r)) = getr regs3 r) by (intros r; exact (arbB_ew_ext regs regs3 pace t T j r)).
clearbody E. clear EL.
apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
repeat (destruct Hz as [<-|Hz];
  [ match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
    cbn [sv_denot];
    first
    [ rewrite getr_zero; reflexivity
    | lazymatch goal with |- getr _ ?zz = Z_to_bv 64 (bv_unsigned (ew E ?k) + _) =>
        replace k with (36 + Z.to_nat (bv_unsigned zz))%nat by reflexivity;
        rewrite (EX zz), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end
    | rewrite R2, E2; unfold spZ; f_equal; lia
    | first [ rewrite R3, E3 | rewrite R4, E4 | rewrite R8, E10 | rewrite R9, E11 | rewrite R18, E15 | rewrite R24, E32
            | rewrite R19, E34 ];
      rewrite Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity ]
  | ]).
destruct Hz.
Qed.

Lemma arbB_stka_chunks : forall E m (regs : bvmap 5 word),
  (forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n))) ->
  arb_frame m regs -> Forall (YP09.chunk_ok SEGS E m (spZ regs)) ARB_STKA.
Proof.
intros E m regs AG HS.
apply Forall_forall. intros c Hc. cbn [ARB_STKA In] in Hc.
repeat (destruct Hc as [<-|Hc];
  [ lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?od (CVal 8 (SOff ?n 0))) =>
      let p := eval vm_compute in (od + 144, Z.of_nat n) in
      let Hp := fresh "Hp" in
      pose proof (HS p ltac:(cbn [ARB_SAVES In]; repeat (first [left; reflexivity | right]))) as Hp;
      cbn [fst snd] in Hp;
      pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat n)))) as Rg; unfold bv_modulus in Rg;
      apply (chunk_ok_val SEGS E m (spZ regs) od 8 (SOff n 0) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat n)))));
      [ cbn [sv_denot]; rewrite AG by lia; rewrite Z.add_0_r; reflexivity
      | change (8 * Z.of_N 8) with 64; change (Z.of_N 64) with 64 in Rg; revert Rg;
        generalize (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat n)))); intros; lia
      | cbn; lia
      | change (N.to_nat 8) with 8%nat; replace (spZ regs + od) with (spZ regs - 144 + (od + 144)) by lia; exact Hp ]
    end
  | ]).
destruct Hc.
Qed.

Lemma arbB_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (j : Z) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invB ly S W regs mem md t our fsm pace now out T P j regs3 mem3 md3 ->
  st_ok_pi (fx := fq) SEGS VAL (arbB_E regs regs3 pace t T j) ss_arbB
    (restrict (w_H W) (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_B)) mem3 (seg_rom SEGS)))
  /\ sh_ok SEGS ARB_BX arbB_SH (arbB_E regs regs3 pace t T j) (mrestrict (w_H W) mem3).
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P j regs3 mem3 md3 HPRE HINV.
destruct HPRE as (HAF & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
destruct HINV as ((HJ & HK & HFR & HO & R2 & R3 & R4 & R9 & R24) & HSL & R18 & R19 & R8 & Hb & EST).
pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
pose proof (proj1 HJ) as HAR3.
destruct (al_blocks _ _ LAWS ly S W mem3 md3 bo No HAR3 Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
assert (Ht0 : t <> 0) by (intro E0; unfold reac_arbitrate_c.best in Hb; rewrite (proj2 (Z.eqb_eq t 0) E0) in Hb; discriminate).
assert (Rj : 0 <= j < disco_table_c.n_of T).
{ pose proof Hb as Hb'. rewrite reac_arbitrate.best_scanz in Hb' by exact Ht0. exact (reac_arbitrate.scanz_range _ _ _ _ _ _ Hb'). }
destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & (T1 & _) & Hdis).
unfold disco_table_c.tbl_T1 in T1.
destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & Ht4096 & Htceil & _).
assert (GT3 : garr8 SEGS (mrestrict (w_H W) mem3) t (map (fun b0 : byte => bv_unsigned b0) T)).
{ eapply garr8_frame; [exact GT|]. intros a Ha. rewrite length_map, LT in Ha. apply (mbyte_of_aview SEGS). apply HK; lia. }
rewrite arb_out0_split in HO.
apply garr8_app in HO as [O0 HO]. rewrite length_map, repeat_length in HO.
apply garr8_app in HO as [O8 HO]. rewrite length_map, repeat_length in HO.
apply garr8_app in HO as [O16 HO]. change (length (map (fun b0 : byte => bv_unsigned b0) (reac_arbitrate_c.z4 pace))) with 4%nat in HO.
apply garr8_app in HO as [O20 O24]. rewrite length_map, repeat_length in O24.
replace (out + Z.of_nat 8) with (out + 8) in O8 by lia.
replace (out + Z.of_nat 8 + Z.of_nat 8) with (out + 16) in O16 by lia.
replace (out + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 4) with (out + 20) in O20 by lia.
replace (out + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4) with (out + 24) in O24 by lia.
assert (V0 : val_mem SEGS (mrestrict (w_H W) mem3) (out + 0) 4 0).
{ pose proof (val_mem_garr8_sub _ out _ 0 4 O0 ltac:(lia) ltac:(rewrite repeat_length; lia)) as V. exact V. }
assert (V12 : val_mem SEGS (mrestrict (w_H W) mem3) (out + 12) 4 0).
{ pose proof (val_mem_garr8_sub _ (out + 8) _ 4 4 O8 ltac:(lia) ltac:(rewrite repeat_length; lia)) as V.
  replace (out + 8 + 4) with (out + 12) in V by lia. exact V. }
assert (V16 : val_mem SEGS (mrestrict (w_H W) mem3) (out + 16) 4 (pace mod 2 ^ 32)).
{ pose proof (val_mem_garr8_sub _ (out + 16) _ 0 4 O16 ltac:(lia) ltac:(cbn; lia)) as V.
  replace (out + 16 + 0) with (out + 16) in V by lia. change (disco_table_c.sub (reac_arbitrate_c.z4 pace) 0 4) with (reac_arbitrate_c.z4 pace) in V.
  rewrite arbB_z4_ble in V. exact V. }
assert (V20 : val_mem SEGS (mrestrict (w_H W) mem3) (out + 20) 4 0).
{ pose proof (val_mem_garr8_sub _ (out + 20) _ 0 4 O20 ltac:(lia) ltac:(rewrite repeat_length; lia)) as V.
  replace (out + 20 + 0) with (out + 20) in V by lia. exact V. }
assert (V24 : val_mem SEGS (mrestrict (w_H W) mem3) (out + 24) 4 0).
{ pose proof (val_mem_garr8_sub _ (out + 24) _ 0 4 O24 ltac:(lia) ltac:(rewrite repeat_length; lia)) as V.
  replace (out + 24 + 0) with (out + 24) in V by lia. exact V. }
assert (V28 : val_mem SEGS (mrestrict (w_H W) mem3) (out + 28) 4 0).
{ pose proof (val_mem_garr8_sub _ (out + 24) _ 4 4 O24 ltac:(lia) ltac:(rewrite repeat_length; lia)) as V.
  replace (out + 24 + 4) with (out + 28) in V by lia. exact V. }
clear O0 O8 O16 O20 O24.
remember (arbB_E regs regs3 pace t T j) as E eqn:HE.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbB_X regs3 pace t T j)) n)
  by (intros n Hn; subst E; unfold arbB_E; apply Eimg_low; exact Hn).
assert (AG : forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n)))
  by (intros n Hn; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_lt; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pace mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (t + 48 * j)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (reac_arbitrate_c.ch_of T j)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (HRS : regs_ok E arbB_sr regs3)
  by (subst E; exact (arbB_regs_ok regs regs3 pace t T j out our H10 H11 H15 R2 R3 R4 R8 R9 R18 R19 R24)).
assert (Rout47 : out + 32 <= 2 ^ 47 - 16) by lia.
assert (RK0 : region_ok SEGS E (mrestrict (w_H W) mem3) arbB_stk).
{ unfold region_ok, arbB_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold ARBB_STK. destruct HSL as (HS0 & HS8 & _).
  apply Forall_cons; [|apply Forall_cons; [|exact (arbB_stka_chunks E _ regs AG HFR)]].
  - apply (chunk_ok_val SEGS E _ (spZ regs) (-144) 8 _ (SB + (out + 16) / 8));
    [ exact (proj2 (arb_denot_shx E 15 out 16 E32 E15 ltac:(lia) ltac:(lia)))
    | unfold SB; split; [|apply Z.lt_le_trans with (2147450880 + 2 ^ 44); [apply Z.add_lt_mono_l, Z.div_lt_upper_bound|]]; cbn; lia
    | cbn; lia
    | change (N.to_nat 8) with 8%nat; replace (spZ regs + -144) with (spZ regs - 144) by lia; exact HS0 ].
  - apply (chunk_ok_val SEGS E _ (spZ regs) (-136) 8 _ (out + 16));
    [ cbn [sv_denot]; rewrite E15, unsigned_lit_small by lia; reflexivity
    | cbn; lia | cbn; lia
    | change (N.to_nat 8) with 8%nat; replace (spZ regs + -136) with (spZ regs - 144 + 8) by lia; exact HS8 ]. }
assert (RK1 : region_ok SEGS E (mrestrict (w_H W) mem3) arbB_o0).
{ unfold region_ok, arbB_o0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E15, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hopres (out + o) ltac:(lia)))|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ out 0 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V0]. }
assert (RK2 : region_ok SEGS E (mrestrict (w_H W) mem3) arbB_o12).
{ unfold region_ok, arbB_o12. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E15, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hopres (out + o) ltac:(lia)))|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ out 12 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V12].
  - apply (chunk_ok_val SEGS E _ out 16 4 (SOff 33 0) (pace mod 2 ^ 32));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (Z.mod_pos_bound pace (2 ^ 32) ltac:(lia)); cbn; lia | cbn; lia | exact V16].
  - apply (chunk_ok_val SEGS E _ out 20 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V20].
  - apply (chunk_ok_val SEGS E _ out 24 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V24].
  - apply (chunk_ok_val SEGS E _ out 28 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V28]. }
assert (RK3 : region_ok SEGS E (mrestrict (w_H W) mem3) arbB_bst).
{ unfold region_ok, arbB_bst. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E34, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  pose proof (reac_arbitrate.u_range T (48 * j + 20) 4 ltac:(lia) ltac:(rewrite LT; lia)) as Rc.
  apply (chunk_ok_val SEGS E _ (t + 48 * j) 20 4 (SOff 35 0) (reac_arbitrate_c.ch_of T j)).
  - cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - unfold reac_arbitrate_c.ch_of. cbn in Rc |- *. lia.
  - cbn; lia.
  - change (N.to_nat 4) with 4%nat. replace (t + 48 * j + 20) with (t + (48 * j + 20)) by lia.
    unfold reac_arbitrate_c.ch_of, disco_table_c.u_at. apply val_mem_garr8_sub; [exact GT3 | lia | rewrite LT; lia]. }
split.
- rewrite restrict_mkst_fx. unfold ss_arbB. apply pa_entry_st_ok_full.
  + exact HRS.
  + vm_compute; reflexivity.
  + unfold arbB_regions. repeat apply Forall_cons; try apply Forall_nil; assumption.
  + apply pairwise_disjoint_of_extents.
    unfold arbB_regions, arbB_stk, arbB_o0, arbB_o12, arbB_bst, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Usp, E15, E34, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]]. cbn [arbB_facts f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite Usp, E15, E32, E34, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16; change (2 ^ 3) with 8; change (2 ^ 2) with 4; rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
    all: rewrite Z.add_mod by lia; rewrite Ht8; replace (48 * j) with ((6 * j) * 8) by lia; rewrite Z.mod_mul by lia; reflexivity.
- unfold sh_ok, arbB_SH. constructor; [|constructor; [|constructor]].
  + apply (arb_shent ly S W mem3 md3 E 15 bo No out 0 32 HAR3 Hbo); [apply arb_U_BX; exact E32 | apply arb_U_atom; [exact E15 | lia] | lia | lia | lia].
  + apply (arb_shent ly S W mem3 md3 E 34 bt Nt (t + 48 * j) 0 48 HAR3 Hbt);
    [apply arb_U_BX; exact E32 | apply arb_U_atom; [exact E34 | lia] | lia | lia | lia].
Qed.

Lemma arbB_post_intro : forall (fq fq' : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) ly' S' (regs' : bvmap 5 word) mem' md',
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fq') k = Sem.reg_get (@YK11.fp_regs fq) k) ->
  (@YK11.fp_csr fq' = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fq')) 5) 7 = 0) ->
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly' S' W mem' md' 0 ->
  aregs_preserved regs regs' -> getr regs' 1 = getr regs 1 ->
  Permutation (ablocks B ly' S') (ablocks B ly S) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  garr8 SEGS (mrestrict (w_H W) mem') out
    (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.arb_model t our T P fsm pace now)) ->
  treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P W
    (mkCfg (mkst (fx := fq') regs' (getr regs 1) mem' (seg_rom SEGS)) md').
Proof.
intros fq fq' ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ly' S' regs' mem' md'
  HFX HCX HA HJ HPR Hra HPerm HK Hout.
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HPP).
pose proof HPRE as (HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
unfold treac_arbitrate_post, apost_base.
exists fq', ly', S', regs', mem', md'.
split; [reflexivity|]. split; [exact HFX|]. split; [exact HCX|]. split; [exact HJ|]. split; [exact HPR|].
split; [exact Hra|]. split; [exact HPerm|]. split; [exact Hout|].
split; [|split; [|split; [reflexivity|]]].
- intros Ht0. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis).
  destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & Ht4096 & Htceil & _).
  apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem' t _); [|exact GT].
  intros a Ha. rewrite length_map, LT in Ha. apply HK; lia.
- intros Hu0. destruct (HPP Hu0) as (Hbp & Hbp1 & Hbp2 & LP & GP & Hdis).
  destruct (al_blocks _ _ LAWS ly S W mem md bp Np HAR Hbp) as (_ & Hp4096 & Hpceil & _).
  apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem' our _); [|exact GP].
  intros a Ha. rewrite length_map, LP in Ha. apply HK; lia.
- intros a N1 N2. pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra. apply HK; [lia | exact N1 | exact N2].
Qed.

Lemma arbB_ret : forall (fq fq' : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (j : Z) (regs3 : bvmap 5 word)
    Ec ss ms md' ly' S',
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fq') k = Sem.reg_get (@YK11.fp_regs fq) k) ->
  (@YK11.fp_csr fq' = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fq')) 5) 7 = 0) ->
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  (forall n, (n < 240)%nat -> ew Ec n = ew (arbB_E regs regs3 pace t T j) n) -> ed Ec = ed (arbB_E regs regs3 pace t T j) ->
  st_ok_pi (fx := fq') SEGS VAL Ec ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  plookup (@pl_tpi lib_both3_0_listing PL_both3_0) (ss_pc ss) = Some (PW RET_WORD_r) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  sr_get (ss_regs ss) 1 = SOff 1 0 ->
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly' S' W (ms_mem ms) md' 0 ->
  Permutation (ablocks B ly' S') (ablocks B ly S) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a) ->
  garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) out
    (map (fun b0 : byte => bv_unsigned b0) (reac_arbitrate_c.arb_model t our T P fsm pace now)) ->
  SRr SEGS W (mkCfg ms md') (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).
Proof.
intros fq fq' ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P j regs3 Ec ss ms md' ly' S'
  HFX HCX HPRE HA HD HS Hrv Hpl Hcs Hr1 HJ HPerm HK Hout.
pose proof HPRE as ((HAR & Hra & _) & _).
assert (EL : forall n, (n < 32)%nat -> ew Ec n = ew (Ereg regs (arbB_X regs3 pace t T j)) n)
  by (intros n Hn; rewrite HA by lia; unfold arbB_E; apply Eimg_low; unfold A_TEXT; lia).
assert (R1 : getr (ms_regs ms) 1 = getr regs 1).
{ rewrite (st_ok_pi_restrict_reg (fx := fq') (w_H W) Ec ss ms 1 HS), Hr1. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EL by lia. exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
eapply (paj_ret_at (fx := fq') (PL := PL_both3_0) (PI := PI) W Ec ss ms md' _ HS Hrv Hpl).
intros mat'. rewrite R1, Hra.
apply (arbB_post_intro fq fq' ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ly' S' (ms_regs ms) (ms_mem ms) _ HFX HCX HPRE).
- apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
- apply (aregs_preserved_of_st_ok SEGS (w_H W) Ec (abs_ss VAL ss) ms regs (arbB_X regs3 pace t T j) HS); [|exact Hcs].
  split; [intros n Hn; apply EL; exact Hn | rewrite HD; reflexivity].
- exact R1.
- exact HPerm.
- exact HK.
- exact Hout.
Qed.

Lemma arbB_rival_at : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md (out : Z) ly3 S3
    (regsT : bvmap 5 word) memT md3 (e r d s c : Z) (raw : word),
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly3 S3 W memT md3 0 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regsT 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 ->
  (e <> 0 ->
     e + 24 <= 2 ^ 63 /\ in_app (e + 8) 16 /\ off_img (e + 8) 16 /\
     range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF (e + 8) 16 /\
     (forall a, e + 8 <= a < e + 24 -> apresent (w_H W) memT a) /\
     -2 ^ 31 <= r < 2 ^ 31 /\ 0 <= d < 2 ^ 8 /\ 0 <= s < 2 ^ 8 /\ 0 <= c < 2 ^ 32 /\
     val_mem SEGS (mrestrict (w_H W) memT) (e + 8) 4 r /\
     val_mem SEGS (mrestrict (w_H W) memT) (e + 12) 1 d /\
     val_mem SEGS (mrestrict (w_H W) memT) (e + 16) 1 s /\
     val_mem SEGS (mrestrict (w_H W) memT) (e + 20) 4 c) ->
  spZ regsT = spZ regs - 144 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> s0Z regsT < alloc_ceiling ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regsT (Z_to_bv 64 (SIGMA AS_reac_rival_kind_of)) memT (seg_rom SEGS)) md3)
    (fun W2 c2 => W2 = W /\ exists (fq2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
       c2 = mkCfg (mkst (fx := fq2) regs2 raw mem2 (seg_rom SEGS)) md2 /\
       (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fq2) k = Sem.reg_get (@YK11.fp_regs fq) k) /\
       (@YK11.fp_csr fq2 = @YK11.fp_csr fq \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fq2)) 5) 7 = 0) /\
       ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly2 S2 W mem2 md2 0 /\
       aregs_preserved regsT regs2 /\
       getr regs2 10 = w64 (if e =? 0 then 0 else reac_rival_kind_of_c.reac_rival_kind_model d r s c) /\
       Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\
       (forall a : word, ~ (spZ regs - 144 - REAC_RIVAL_KIND_OF_STK <= bv_unsigned a < spZ regs - 144) -> mem2 a = memT a)).
Proof.
intros fq ly S W regs mem md out ly3 S3 regsT memT md3 e r d s c raw HJ HROD H10 Re He8 HE Hsp Hgp Htp Hra Hraw Hraw4 Hs0.
pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & HQT).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity. assert (WR : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
rewrite pa_sigma_reac_rival_kind_of.
eapply SRr_mono.
{ apply (TRIVAL fq ly3 S3 W regsT memT md3 [] e r d s c).
  - apply (afn_pre_at SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly3 S3 W memT md3 0 regsT
      REAC_RIVAL_KIND_OF_STK (-144) [] HJ).
    + rewrite Hsp. lia.
    + reflexivity.
    + lia.
    + rewrite WR. unfold ESTACK. lia.
    + rewrite WR, WS. unfold ESTACK. lia.
    + rewrite Hra. exact Hraw.
    + unfold raZ. rewrite Hra. exact Hraw4.
    + exact Hgp.
    + exact Htp.
    + apply achain_low. exact Hs0.
  - exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD).
  - exact H10.
  - exact Re.
  - exact He8.
  - exact HE. }
cbv beta. intros W2 c2 HW2 HPOST.
unfold treac_rival_kind_of_post, apost_base in HPOST.
destruct HPOST as (fq2 & ly2 & S2 & regs2 & mem2 & md2 & Hc & Hfr2 & Hcsr2 & HJ1 & HP & Ha0 & HPerm & -> & Hkeep).
split; [reflexivity|]. exists fq2, ly2, S2, regs2, mem2, md2.
split; [rewrite Hc, Hra; reflexivity|]. split; [exact Hfr2|]. split; [exact Hcsr2|].
split.
{ change (@nil (Z * Z)) with (@nil (Z * Z) ++ @nil (Z * Z)). replace 0 with (0 + 0) by lia.
  eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | rewrite Hsp, WR, WS; unfold ESTACK; lia | rewrite Hsp; lia |].
  intros a Ha. exfalso. exact (inFP_nil a Ha). }
split; [exact HP|]. split; [exact Ha0|]. split; [exact HPerm|].
intros a Ha. apply Hkeep. rewrite Hsp. exact Ha.
Qed.

Lemma arbB_swrap32 : forall u, bv_swrap 32 u mod 2 ^ 32 = u mod 2 ^ 32.
Proof.
intros u. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite Zminus_mod_idemp_l. f_equal. ring.
Qed.

Lemma arbB_sext32 : forall x : word, bv_unsigned (sext 64 (bv_extract 0 32 x)) mod 2 ^ 32 = bv_unsigned x mod 2 ^ 32.
Proof.
intros x. rewrite YK11.sext32_unsigned. unfold bv_wrap at 1. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 32 * 2 ^ 32).
rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_mod by lia. rewrite arbB_swrap32.
rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 32) with (2 ^ 32). apply Z.mod_mod. lia.
Qed.

Lemma arbB_vm_mod : forall m a v v', v mod 2 ^ 32 = v' mod 2 ^ 32 -> val_mem SEGS m a 4 v -> val_mem SEGS m a 4 v'.
Proof.
intros m a v v' Hv H jj Hj. rewrite (H jj Hj). unfold YO0f.le_byte.
assert (Hv' : v mod 2 ^ (8 * Z.of_nat 4) = v' mod 2 ^ (8 * Z.of_nat 4)) by exact Hv.
rewrite Hv'. reflexivity.
Qed.

Lemma arbB_keep_aview : forall H (m2 m : word -> option byte) lo hi,
  (forall w : word, ~ (lo <= bv_unsigned w < hi) -> m2 w = m w) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m2 a = aview SEGS H m a.
Proof.
intros H m2 m lo hi Hk a Ha Hn. unfold aview, mbyte, mrestrict.
rewrite (Hk (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma arbB_rkept : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> m2 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  lo <= wlo -> whi <= hi ->
  region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hq Hl Hh.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- unfold mbyte, mrestrict. rewrite (Hq a Ha). reflexivity.
- apply writable_kept. intros [Hh0 [x Hx]]. split; [exact Hh0|]. exists x. rewrite (Hq a ltac:(lia)). exact Hx.
Qed.

Ltac arbB_awr HA Eout Hbo out :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [azlit_tac|]
  | eapply awr_ok_cons_gen with (n := 15%nat) (b := out);
    [ reflexivity | try (rewrite (HA 15%nat) by lia); rewrite Eout; apply unsigned_lit_small; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; left; split;
      [ eexists; split; [left; reflexivity | cbn; lia] | do 2 eexists; split; [exact Hbo | lia] ]
    | ] ].
Ltac arbB_env E0 HA HD :=
  let Ev := lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ => Ev | HS : st_ok _ ?Ev _ _ |- _ => Ev end in
  let E1 := fresh "Ec" in
  lazymatch goal with HS : st_ok_pi _ _ Ev _ _ , SHOK : sh_ok _ _ _ Ev _ |- _ => set (E1 := Ev) in HS, SHOK
                    | HS : st_ok _ Ev _ _ , SHOK : sh_ok _ _ _ Ev _ |- _ => set (E1 := Ev) in HS, SHOK end;
  let HEIn := fresh "HEI" in
  assert (HEIn : img_env pa_val A_LIM E1) by (subst E1; assumption);
  let HA' := fresh "HA" in
  assert (HA' : forall n, (n < 240)%nat -> ew E1 n = ew E0 n)
    by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; subst E1;
        rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply HA; exact Hn);
  let HD' := fresh "HD" in
  assert (HD' : ed E1 = ed E0) by (subst E1; exact HD);
  clearbody E1; clear HA HD; rename HA' into HA; rename HD' into HD.
Ltac arbB_win HA E15 :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta;
      first [ lia
            | try (rewrite (HA 15%nat) in Hrr by lia); rewrite E15 in Hrr; rewrite unsigned_lit_small in Hrr by lia; lia ]
    | ]);
  destruct Hin.
Ltac arbB_kstep K HA E15 :=
  lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m) (mrestrict _ ?m') |- _ =>
    lazymatch type of K with arbB_kept ?W ?m0 _ ?Zx =>
      let K' := fresh "K" in
      assert (K' : arbB_kept W m0 m' Zx);
      [ apply (arbB_kept_frame W m0 m m' Zx Ef rs K HFr); arbB_win HA E15 | clear K HFr; rename K' into K ] end end.
Ltac arbB_zc HS HA E15 out i off v G :=
  lazymatch type of HS with st_ok_pi ?sg _ ?Ex ?ss (restrict ?H ?msX) =>
  let r := eval vm_compute in (nth_error (ss_mem ss) i) in
  lazymatch r with Some ?rr =>
  let cs := eval vm_compute in (YP09.r_chunks rr) in
  let e := lazymatch cs with context [YP09.mkChunk off (CVal 4 ?e)] => e end in
  let V := fresh "V" in
  pose proof (arbB_chunk_val _ Ex ss (restrict H msX) i rr off 4 e HS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
  cbn [YP09.r_base base_val ms_mem restrict] in V;
  rewrite (HA 15%nat) in V by lia; rewrite E15 in V; rewrite unsigned_lit_small in V by lia;
  change (N.to_nat 4) with 4%nat in V; change (8 * Z.of_N 4) with 32 in V;
  assert (G : garr8 sg (mrestrict H (ms_mem msX)) (out + off) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)));
  [ apply (arbB_z4_chunk _ _ _ v V); cbn [sv_denot]; apply arbB_u64_mod32
  | clear V ]
  end end.
Ltac arbB_cv HS HA E15 i off V :=
  lazymatch type of HS with st_ok_pi ?sg _ ?Ex ?ss (restrict ?H ?msX) =>
  let r := eval vm_compute in (nth_error (ss_mem ss) i) in
  lazymatch r with Some ?rr =>
  let cs := eval vm_compute in (YP09.r_chunks rr) in
  let e := lazymatch cs with context [YP09.mkChunk off (CVal 4 ?e)] => e end in
  pose proof (arbB_chunk_val _ Ex ss (restrict H msX) i rr off 4 e HS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
  cbn [YP09.r_base base_val ms_mem restrict] in V;
  rewrite (HA 15%nat) in V by lia; rewrite E15 in V; rewrite unsigned_lit_small in V by lia;
  change (N.to_nat 4) with 4%nat in V; change (8 * Z.of_N 4) with 32 in V
  end end.
Ltac arbB_envk E0 HA HD EK :=
  let Ev := lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ => Ev | HS : st_ok _ ?Ev _ _ |- _ => Ev end in
  let E1 := fresh "Ec" in
  lazymatch goal with HS : st_ok_pi _ _ Ev _ _ , SHOK : sh_ok _ _ _ Ev _ |- _ => set (E1 := Ev) in HS, SHOK
                    | HS : st_ok _ Ev _ _ , SHOK : sh_ok _ _ _ Ev _ |- _ => set (E1 := Ev) in HS, SHOK end;
  let HEIn := fresh "HEI" in
  assert (HEIn : img_env pa_val A_LIM E1) by (subst E1; assumption);
  let HA' := fresh "HA" in
  assert (HA' : forall n, (n < 240)%nat -> ew E1 n = ew E0 n)
    by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; subst E1;
        rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply HA; exact Hn);
  let HD' := fresh "HD" in
  assert (HD' : ed E1 = ed E0) by (subst E1; exact HD);
  let EK' := fresh "EK" in
  lazymatch type of EK with ew _ ?ka = ?v =>
    assert (EK' : ew E1 ka = v) by (subst E1; rewrite ?ew_ewset_other by lia; exact EK) end;
  clearbody E1; clear HA HD EK; rename HA' into HA; rename HD' into HD; rename EK' into EK.

Lemma arb_segB : ARB_SEGB.
Proof.
unfold ARB_SEGB.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P j regs3 mem3 md3 HPRE HINV.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
destruct (arbB_entry fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P j regs3 mem3 md3 HPRE HINV) as [HS SHOK].
pose proof HINV as ((HJ & HK & HFR & HO & R2 & R3 & R4 & R9 & R24) & HSL & R18 & R19 & R8 & Hb & EST).
pose proof HPRE as (HAF & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8336) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
assert (Ht0 : t <> 0) by (intro E0; unfold reac_arbitrate_c.best in Hb; rewrite (proj2 (Z.eqb_eq t 0) E0) in Hb; discriminate).
assert (Rj : 0 <= j < disco_table_c.n_of T).
{ pose proof Hb as Hb'. rewrite reac_arbitrate.best_scanz in Hb' by exact Ht0. exact (reac_arbitrate.scanz_range _ _ _ _ _ _ Hb'). }
destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis).
pose proof TOK as (T1 & T2 & T3 & T4). unfold disco_table_c.tbl_T1 in T1.
destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (Ht16 & Ht4096 & Htceil & Htia & Htpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ bt Nt HAR Hbt) as Htimg.
assert (GT3 : garr8 SEGS (mrestrict (w_H W) mem3) t (map (fun b0 : byte => bv_unsigned b0) T)).
{ eapply garr8_frame; [exact GT|]. intros a Ha. rewrite length_map, LT in Ha. apply (mbyte_of_aview SEGS). apply HK; lia. }
assert (Lm : length (disco_table_c.mac_of T j) = 6%nat).
{ unfold disco_table_c.mac_of, disco_table_c.sub. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, LT. lia. }
assert (GMT : garr8 SEGS (mrestrict (w_H W) mem3) (t + 48 * j) (map (fun b0 : byte => bv_unsigned b0) (disco_table_c.mac_of T j))).
{ pose proof (garr8_sub_x SEGS _ t _ (Z.to_nat (48 * j)) 6 GT3 ltac:(rewrite length_map, LT; lia)) as G.
  rewrite Z2Nat.id in G by lia. rewrite skipn_map, firstn_map in G. exact G. }
unfold arb_post_cfg.
remember (arbB_E regs regs3 pace t T j) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold arbB_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbB_X regs3 pace t T j)) n)
  by (intros n Hn; subst E; unfold arbB_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (t + 48 * j)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (reac_arbitrate_c.ch_of T j)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (HA : forall n, (n < 240)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (HD : ed E = ed E) by reflexivity.
pose proof (arbB_kept_refl W mem3 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as K.
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbB_awr HA E15 Hbo out |].
arbB_kstep K HA E15. clear HF HG.
arbB_env E HA HD.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt Nt (proj1 HJ) Hbt) as (_ & _ & _ & _ & Httpres & _).
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
rewrite (HA 15%nat) in Ra0 by lia. rewrite E15, unsigned_lit_small in Ra0 by lia.
rewrite (HA 34%nat) in Ra1 by lia. rewrite E34 in Ra1.
rewrite (HA 2%nat) in Qsp by lia. rewrite Usp in Qsp.
rewrite (HA 3%nat) in Qgp by lia. rewrite E3 in Qgp.
rewrite (HA 4%nat) in Qtp by lia. rewrite E4 in Qtp.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA AS___asan_memcpy) (AMEMCPY fq) W (ms_regs msX) (ms_mem msX)
     REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S _ 0 (out + 4) (t + 48 * j) 6 (-144) _ HJ) end.
  - rewrite Ra0. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite Qsp. apply unsigned_lit_small. lia.
  - reflexivity.
  - lia.
  - rewrite WS. unfold ESTACK. lia.
  - rewrite Qgp. exact Hgp.
  - rewrite Qtp. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [right; left; split; [exists (out, out + 32); split; [left; reflexivity | cbn; lia] | exists bo, No; split; [exact Hbo | lia]] | unfold ESTACK; lia].
  - apply (amem_range_of_block SEGS B LAWS ly S W _ _ bo No (out + 4) 6 (proj1 HJ) Hbo); lia.
  - apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bo No (out + 4) 6 (proj1 HJ) Hbo); lia.
  - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bo No (out + 4) 6 (proj1 HJ) Hbo); lia.
  - split; [lia|]. split; [lia|]. split.
    + intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (Httpres a ltac:(lia))) |].
      unfold spZ. rewrite Qsp. rewrite unsigned_lit_small by lia. unfold ESTACK. lia.
    + split; [lia|]. split; [apply (amem_range_of_block SEGS B LAWS ly S W _ _ bt Nt (t + 48 * j) 6 (proj1 HJ) Hbt); lia|].
      split; [apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bt Nt (t + 48 * j) 6 (proj1 HJ) Hbt); lia|].
      intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bt Nt (t + 48 * j) 6 (proj1 HJ) Hbt); lia. }
cbv beta. clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2 & HSM).
lazymatch type of Hfr with forall a, _ -> _ -> _ -> _ = aview _ _ ?mq a =>
assert (HfrZ : forall a, 0 <= a < 2 ^ 64 -> ~ ((out + 4 <= a < out + 10) \/ (spZ regs - 144 - ESTACK <= a < spZ regs - 144)) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mq a) end.
{ intros a Ha Hz. apply Hfr; [exact Ha | intro; apply Hz; left; lia | intro; apply Hz; right; lia]. }
assert (GM : garr8 SEGS (mrestrict (w_H W) mem2) (out + 4) (map (fun b0 : byte => bv_unsigned b0) (disco_table_c.mac_of T j))).
{ apply (arbB_garr8_copy _ mem3 _ (t + 48 * j) (out + 4) _ GMT). intros i Hi. rewrite length_map, Lm in Hi.
  rewrite Heff by lia. apply (K (t + 48 * j + i)); [lia | cbv beta; lia]. }
destruct (arbB_out0_rest _ out pace HO) as [_ G10].
assert (G10m : garr8 SEGS (mrestrict (w_H W) mem2) (out + 10) [0; 0]).
{ apply (arbB_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi.
  rewrite HfrZ by (try lia; cbv beta; unfold ESTACK; lia). apply K; [lia | cbv beta; lia]. }
pose proof (arbB_kept_step _ _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) K HfrZ
  ltac:(intros a Hq; cbv beta in Hq |- *; lia) ltac:(intros a Hq; cbv beta in Hq |- *; rewrite WS; unfold ESTACK in Hq; lia)) as K2.
clear K.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [ | | | | apply Forall_nil].
  - eapply region_kept_aview; [rewrite (HA 2%nat) by lia; exact Usp | | exact Hpres2].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
  - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact Hpres2].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
  - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact Hpres2].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
  - eapply region_kept_aview; [rewrite (HA 34%nat) by lia; rewrite E34; apply unsigned_lit_small; lia | | exact Hpres2].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
  assert (SHOK2 : sh_ok SEGS ARB_BX arbB_SH Ea (mrestrict (w_H W) mem2)) end.
{ constructor; [|constructor; [|constructor]].
  - apply (arb_shent ly S W mem2 md2 _ 15 bo No out 0 32 (proj1 HJ2) Hbo);
    [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
    | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 15%nat) by lia; exact E15 | lia] | lia | lia | lia].
  - apply (arb_shent ly S W mem2 md2 _ 34 bt Nt (t + 48 * j) 0 48 (proj1 HJ2) Hbt);
    [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
    | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 34%nat) by lia; exact E34 | lia] | lia | lia | lia]. }
clear SHOK. rename SHOK2 into SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
  assert (HEIa : img_env VAL A_LIM Ea) by (apply img_env_havoc_hi; [assumption | cbv; lia]) end.
arbB_env E HA HD.
pose proof (arbB_kept_refl W mem2 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as KM.
paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbB_awr HA E15 Hbo out |].
lazymatch goal with HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => pose proof HFr' as HFr2 end.
arbB_kstep K2 HA E15. arbB_kstep KM HA E15. clear HF HG.
arbB_env E HA HD.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt Nt (proj1 HJ2) Hbt) as (_ & _ & _ & _ & Htpres2 & _).
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (8%bv : bv 5) Qs0.
rewrite (HA 34%nat) in Ra0 by lia. rewrite E34 in Ra0.
rewrite (HA 2%nat) in Qsp by lia. rewrite Usp in Qsp.
rewrite (HA 3%nat) in Qgp by lia. rewrite E3 in Qgp.
rewrite (HA 4%nat) in Qtp by lia. rewrite E4 in Qtp.
rewrite (HA 10%nat) in Qs0 by lia. rewrite E10 in Qs0.
pmkst HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  assert (GTR : garr8 SEGS (mrestrict (w_H W) (ms_mem msX)) t (map (fun b0 : byte => bv_unsigned b0) T)) end.
{ apply (arbB_garr8_copy _ mem3 _ t t _ GT3). intros i Hi. rewrite length_map, LT in Hi. apply K2; [lia | cbv beta; lia]. }
pose proof (reac_arbitrate.u_range T (48 * j + 12) 1 ltac:(lia) ltac:(rewrite LT; lia)) as Rd.
pose proof (reac_arbitrate.u_range T (48 * j + 16) 1 ltac:(lia) ltac:(rewrite LT; lia)) as Rs.
pose proof (reac_arbitrate.u_range T (48 * j + 20) 4 ltac:(lia) ltac:(rewrite LT; lia)) as Rc.
change (2 ^ (8 * Z.of_nat 1)) with 256 in Rd, Rs. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Rc.
assert (Hrr : disco_table_c.role_of_e T j = 0 \/ disco_table_c.role_of_e T j = 1 \/ disco_table_c.role_of_e T j = 2) by exact (T2 j Rj).
pose proof (@pa_B_ok _ lib_both3_0_listing PI) as HB.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (arbB_rival_at fq ly S W regs mem md out ly S (ms_regs msX) (ms_mem msX) _ (t + 48 * j)
    (disco_table_c.role_of_e T j) (disco_table_c.hd_of T j) (reac_arbitrate_c.slots_of T j) (reac_arbitrate_c.ch_of T j) _ HJ2 HROD) end.
  - rewrite Ra0. reflexivity.
  - lia.
  - replace (t + 48 * j) with (t + (6 * j) * 8) by lia. rewrite Z_mod_plus_full. exact Ht8.
  - intros _.
    split; [lia|].
    split; [apply (in_app_sub bt (req_size Nt)); [exact Htia | lia | lia | lia]|].
    split; [unfold off_img, IMG_LO, IMG_TOP in Htimg |- *; lia|].
    split; [apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bt Nt (t + 48 * j + 8) 16 (proj1 HJ2) Hbt); lia|].
    split; [intros a Ha; exact (proj1 (Htpres2 a ltac:(lia)))|].
    split; [lia|].
    split; [unfold disco_table_c.hd_of; lia|].
    split; [unfold reac_arbitrate_c.slots_of; lia|].
    split; [unfold reac_arbitrate_c.ch_of; lia|].
    split; [apply (arbB_vm_mod _ _ (disco_table_c.u_at T (48 * j + 8) 4));
            [unfold disco_table_c.role_of_e, disco_table_c.s32_at; rewrite arbB_swrap32; reflexivity
            | replace (t + 48 * j + 8) with (t + (48 * j + 8)) by lia; apply val_mem_garr8_sub; [exact GTR | lia | rewrite LT; lia]]|].
    split; [replace (t + 48 * j + 12) with (t + (48 * j + 12)) by lia; unfold disco_table_c.hd_of, disco_table_c.u_at;
            apply val_mem_garr8_sub; [exact GTR | lia | rewrite LT; lia]|].
    split; [replace (t + 48 * j + 16) with (t + (48 * j + 16)) by lia; unfold reac_arbitrate_c.slots_of, disco_table_c.u_at;
            apply val_mem_garr8_sub; [exact GTR | lia | rewrite LT; lia]|].
    replace (t + 48 * j + 20) with (t + (48 * j + 20)) by lia. unfold reac_arbitrate_c.ch_of, disco_table_c.u_at.
    apply val_mem_garr8_sub; [exact GTR | lia | rewrite LT; lia].
  - unfold spZ at 1. rewrite Qsp, unsigned_lit_small by lia. lia.
  - rewrite Qgp. exact Hgp.
  - rewrite Qtp. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite Qs0, unsigned_lit_small by lia. lia. }
cbv beta. clear Ra0 Rra Qsp Qgp Qtp Qs0.
intros W2 c2 _ (-> & fq2 & ly2 & S2 & regs4 & mem4 & md4 & -> & Hfr2 & Hcsr2 & HJ3 & HP3 & Hrv & HPerm & Hkeep).
assert (Hrv' : getr regs4 10 = w64 (reac_arbitrate_c.rival_of T j)).
{ rewrite Hrv. replace (t + 48 * j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
clear Hrv.
assert (WR : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
lazymatch type of Hkeep with forall a : word, _ -> _ = ?mr a =>
  pose proof (arbB_keep_aview (w_H W) mem4 mr _ _ Hkeep) as KR end.
pose proof (arbB_kept_step _ _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) K2 KR
  ltac:(intros a Hq; exact Hq) ltac:(intros a Hq; cbv beta in Hq |- *; rewrite WS; rewrite WR in Hq; lia)) as K3.
clear K2. rename K3 into K2.
pose proof (arbB_kept_step _ _ _ _ _ _ (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) KM KR
  ltac:(intros a Hq; exact Hq) ltac:(intros a Hq; cbv beta in Hq |- *; rewrite WS; rewrite WR in Hq; lia)) as KM3.
clear KM. rename KM3 into KM.
assert (Hbo' : In (bo, No) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HPerm) Hbo).
assert (Hbt' : In (bt, Nt) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HPerm) Hbt).
pose proof (YA0o.st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms. rewrite Hms in HS. clear Hms.
rewrite restrict_mkst_fx in HS.
pose proof (FpStep.fp_st_ok_fx SEGS fq fq2 _ _ _ _ _ _ HS) as HSq. clear HS. rename HSq into HS.
clear RUN. pose proof (paj_run (fx := fq2) B LAWS) as RUN.
lazymatch type of HS with st_ok _ _ ?ssv _ =>
  let kk := eval vm_compute in (run_K A_LIM ARB_BX arbB_SH ssv) in
  jafter_call_keep_hi HS kk regs4 (mrestrict (w_H W) mem4) HP3 [0; 1; 2; 3]%nat HS2 end.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; [ | | | | apply Forall_nil].
  - apply (arbB_rkept _ _ _ _ _ (spZ regs)); [rewrite (HA 2%nat) by lia; exact Usp | | lia | lia].
    intros a Ha. apply Hkeep. rewrite unsigned_lit_small by lia. rewrite WR. lia.
  - apply (arbB_rkept _ _ _ _ _ out); [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | lia | lia].
    intros a Ha. apply Hkeep. rewrite unsigned_lit_small by lia. rewrite WR. lia.
  - apply (arbB_rkept _ _ _ _ _ out); [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | lia | lia].
    intros a Ha. apply Hkeep. rewrite unsigned_lit_small by lia. rewrite WR. lia.
  - apply (arbB_rkept _ _ _ _ _ (t + 48 * j)); [rewrite (HA 34%nat) by lia; rewrite E34; apply unsigned_lit_small; lia | | lia | lia].
    intros a Ha. apply Hkeep. rewrite unsigned_lit_small by lia. rewrite WR. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ea ?ssv _ =>
  let e := eval vm_compute in (sr_get (ss_regs ssv) (10%bv : bv 5)) in
  lazymatch e with SOff ?ka 0 =>
    assert (EK : ew Ea ka = w64 (reac_arbitrate_c.rival_of T j)) by (rewrite <- Hrv'; reflexivity) end end.
lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
  assert (SHOK2 : sh_ok SEGS ARB_BX arbB_SH Ea (mrestrict (w_H W) mem4)) end.
{ constructor; [|constructor; [|constructor]].
  - apply (arb_shent ly2 S2 W mem4 md4 _ 15 bo No out 0 32 (proj1 HJ3) Hbo');
    [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
    | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 15%nat) by lia; exact E15 | lia] | lia | lia | lia].
  - apply (arb_shent ly2 S2 W mem4 md4 _ 34 bt Nt (t + 48 * j) 0 48 (proj1 HJ3) Hbt');
    [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
    | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 34%nat) by lia; exact E34 | lia] | lia | lia | lia]. }
clear SHOK. rename SHOK2 into SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
  assert (HEIb : img_env VAL A_LIM Ea) by (apply img_env_havoc_hi; [assumption | cbv; lia]) end.
arbB_envk E HA HD EK.
paj_run_tok RUN HS HJ3 SHOK ARB_SPAN; [arbB_awr HA E15 Hbo' out |].
lazymatch goal with HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => pose proof HFr' as HFr2 end.
arbB_kstep K2 HA E15. arbB_kstep KM HA E15. clear HF HG.
arbB_envk E HA HD EK.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
   aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno Hns. rewrite (K2 a Ha) by (cbv beta; lia). apply HK; assumption. }
arbB_zc HS HA E15 out 1%nat 0 2 G0. rewrite Z.add_0_r in G0.
arbB_zc HS HA E15 out 2%nat 12 1 G12.
arbB_zc HS HA E15 out 2%nat 16 1 G16.
arbB_zc HS HA E15 out 2%nat 20 0 G20.
arbB_cv HS HA E15 2%nat 24 V24.
assert (G24 : garr8 SEGS (mrestrict (w_H W) mF) (out + 24) (map (fun b0 : byte => bv_unsigned b0) (reac_arbitrate_c.z4 (reac_arbitrate_c.rival_of T j)))).
{ apply (arbB_z4_chunk _ _ _ _ V24). cbn [sv_denot]. rewrite EK, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. apply arbB_u64_mod32. }
clear V24.
arbB_cv HS HA E15 2%nat 28 V28.
assert (G28 : garr8 SEGS (mrestrict (w_H W) mF) (out + 28) (map (fun b0 : byte => bv_unsigned b0) (reac_arbitrate_c.z4 (reac_arbitrate_c.ch_of T j)))).
{ apply (arbB_z4_chunk _ _ _ _ V28). cbn [sv_denot]. rewrite arbB_sext32. rewrite (HA 35%nat) by lia.
  rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. apply arbB_u64_mod32. }
clear V28.
assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) (disco_table_c.mac_of T j))).
{ apply (arbB_garr8_copy _ mem2 _ (out + 4) (out + 4) _ GM). intros i Hi. rewrite length_map, Lm in Hi. apply KM; [lia | cbv beta; lia]. }
assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
{ apply (arbB_garr8_copy _ mem2 _ (out + 10) (out + 10) _ G10m). intros i Hi. cbn in Hi. apply KM; [lia | cbv beta; lia]. }
eapply (arbB_ret fq fq2 ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P j regs3 _ _ _ _ ly2 S2 Hfr2 Hcsr2 HPRE
  ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ3 HPerm KF).
unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite Hb. unfold arb_est in EST. rewrite EST. cbv iota.
exact (arbB_bytes_garr8 _ out 2 (disco_table_c.mac_of T j) 1 1 0 (reac_arbitrate_c.rival_of T j) (reac_arbitrate_c.ch_of T j)
  G0 Lm GM2 G102 G12 G16 G20 G24 G28).
Qed.

Lemma arb_loop : forall (k : nat) (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (i : Z) (b : option Z) (regs3 : bvmap 5 word) mem3 md3,
  Z.to_nat (disco_table_c.n_of T - i) = k ->
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invL ly S W regs mem md t our fsm pace now out T P i b regs3 mem3 md3 ->
  SRr SEGS W (arb_post_cfg fq AF_ARB_L regs3 mem3 md3) (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).
Proof.
induction k as [|k IH]; intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b regs3 mem3 md3 Hk HA HI.
- exfalso. pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi). lia.
- apply (arb_segL fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b regs3 mem3 md3 _ HA HI).
  + intros regs4 mem4 md4 HI4. apply (IH fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P (i + 1) (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4); [lia | exact HA | exact HI4].
  + intros regs4 mem4 md4 HE4. exact (arb_segE fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 HA HE4).
  + intros regs4 mem4 md4 HN4. exact (arb_segN fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs4 mem4 md4 HA HN4).
  + intros j regs4 mem4 md4 HB4. exact (arb_segB fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P j regs4 mem4 md4 HA HB4).
Qed.

Theorem pb_reac_arbitrate : treac_arbitrate_spec.
Proof.
unfold treac_arbitrate_spec.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P
  HPRE HROD H10 H11 H12 H13 H14 H15 Rt Rour Rfsm Rpace Rnow Rout Hbo Hbo1 Hbo2 Ho4 HT HPP.
assert (HA : arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P)
  by (unfold arb_pre; repeat (split; [assumption|]); assumption).
apply (arb_segA fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P _ HA).
- intros regs3 mem3 md3 HI.
  exact (arb_loop _ fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P 0 None regs3 mem3 md3 eq_refl HA HI).
- intros regs3 mem3 md3 HE3. exact (arb_segE fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P None regs3 mem3 md3 HA HE3).
- intros regs3 mem3 md3 HN3. exact (arb_segN fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs3 mem3 md3 HA HN3).
Qed.
End h.
End f.
End d.
