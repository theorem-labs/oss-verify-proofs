(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_of.v, with its module paths and module names changed; 3511 of its 3597 lines of code are new or changed and 761 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacRivalKindOf.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s YImgTop YA0o YCbm YA0q YI67.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require FpStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 DiscoFrame YC85 YC88 DiscoACjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_arbitrate_c reac_arbitrate.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
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
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
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
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Hypothesis TRIVAL : treac_rival_kind_of_spec B.
Definition REAC_ARBITRATE_STK : Z := 128 + 2 * ESTACK.
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
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_arbitrate) regs mem md)
    (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

Definition ARB_BX : sv := SOff 32 0.
Definition ARB_SPAN : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition arbA_regions : smem :=
  [ stack_region 128; got_regionP; bcell_regionP 32;
    YP09.mkRegion (Some 15%nat) 0 32 0 32 [];
    YP09.mkRegion (Some 10%nat) 0 400 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 33 0))] ].
Definition arbA_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 3);
            (15%nat, mkAF 4096 140737479966720 2); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 8 0) ] [] [].
Definition ss_arbA : sstate := mkSS AF_reac_arbitrate sr_atoms arbA_regions None arbA_facts.
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
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_reac_arbitrate)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS ARB_BX arbA_SH (EA regs (disco_table_c.n_of T)) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch t out bt Nt bo No T HPRE H10 H15 Rt Rout Hbo Hbo1 Hbo2 Ho4 Ht0 Hbt Hbt1 Hbt2 Ht8 LT GT RN Hdis.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ bo No HAR Hbo) as Hoimg.
destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (Ht16 & Ht4096 & Htceil & Htia & Htpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ bt Nt HAR Hbt) as Htimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
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
assert (Eo66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; unfold EA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
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
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
      [cbn [sv_denot]; rewrite Eo66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Eo66) by (pose proof (pa_val_range (A_OBJ 66)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 ARB_BX SB);
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
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Eo66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
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

Definition AF_ARB_L : Z := AF_reac_arbitrate + 208.
Definition AF_ARB_P : Z := AF_reac_arbitrate + 364.
Definition ARB_STALE : Z := 5000000000.
Definition ARB_SAVES : list (Z * Z) :=
  [(120, 1); (112, 8); (104, 9); (96, 18); (88, 19); (80, 20); (72, 21); (64, 22); (56, 23); (48, 24); (40, 25); (32, 26); (24, 27)].
Definition arb_out0 (pace : Z) : list Z :=
  map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.arb_bytes 0 reac_arbitrate_c.MAC0 0 pace 0 0 0).

Definition arb_frame (m : word -> option byte) (regs : bvmap 5 word) (out : Z) : Prop :=
  (forall p, In p ARB_SAVES -> val_mem SEGS m (spZ regs - 128 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) /\
  val_mem SEGS m (spZ regs - 128 + 16) 8 (SB + (out + 16) / 8) /\
  val_mem SEGS m (spZ regs - 128 + 8) 8 (out + 16).

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

Definition arb_cmn ly S W (regs : bvmap 5 word) mem md (our fsm pace out : Z)
    (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S W mem3 md3 0 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a) /\
  arb_frame (mrestrict (w_H W) mem3) regs out /\
  garr8 SEGS (mrestrict (w_H W) mem3) out (arb_out0 pace) /\
  getr regs3 2 = Z_to_bv 64 (spZ regs - 128) /\ getr regs3 3 = getr regs 3 /\ getr regs3 4 = getr regs 4 /\
  getr regs3 8 = Z_to_bv 64 out /\ getr regs3 9 = Z_to_bv 64 our /\ getr regs3 18 = Z_to_bv 64 fsm /\
  getr regs3 25 = Z_to_bv 64 SB.

Definition arb_invP ly S W (regs : bvmap 5 word) mem md (t our fsm pace now out : Z) (T P : list byte) (b : option Z)
    (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
  arb_cmn ly S W regs mem md our fsm pace out regs3 mem3 md3 /\
  getr regs3 19 = Z_to_bv 64 (reac_arbitrate.baddr t b) /\ b = reac_arbitrate_c.best t T P our now.

Definition arb_invL ly S W (regs : bvmap 5 word) mem md (t our fsm pace now out : Z) (T P : list byte) (i : Z) (b : option Z)
    (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
  arb_cmn ly S W regs mem md our fsm pace out regs3 mem3 md3 /\
  getr regs3 19 = Z_to_bv 64 (reac_arbitrate.baddr t b) /\ b = reac_arbitrate.scanz T P our now i /\
  t <> 0 /\ 0 <= i < disco_table_c.n_of T /\
  getr regs3 20 = Z_to_bv 64 ARB_STALE /\ getr regs3 21 = Z_to_bv 64 now /\
  getr regs3 22 = Z_to_bv 64 (t + 48 * i) /\ getr regs3 23 = Z_to_bv 64 (t + 48 * i + 40) /\
  getr regs3 24 = Z_to_bv 64 (SB + (t + 48 * i + 8) / 8) /\
  getr regs3 26 = Z_to_bv 64 (disco_table_c.n_of T - i) /\ getr regs3 27 = Z_to_bv 64 2.

Definition ARB_STKA : list YP09.chunk :=
  [ YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
    YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
    YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 27 0));
    YP09.mkChunk (-112) (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 15 16) (SLit 3)) (SOff 32 0)));
    YP09.mkChunk (-120) (CVal 8 (SOff 15 16)) ].

Lemma arb_frameA : forall E m (regs : bvmap 5 word) out cs wlo whi,
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (-128) 0 wlo whi cs) ->
  bv_unsigned (ew E 2) = spZ regs ->
  (forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n))) ->
  ew E 32 = Z_to_bv 64 SB -> ew E 15 = Z_to_bv 64 out -> 0 <= out < 2 ^ 47 - 16 ->
  incl ARB_STKA cs -> arb_frame m regs out.
Proof.
intros E m regs out cs wlo whi HR Hsp AG H32 H15 Rout Hin.
assert (SL : forall od e v, In (YP09.mkChunk od (CVal 8 e)) ARB_STKA -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (spZ regs + od) 8 v).
{ intros od e v Hc He Hv. exact (slot_of_region E m (spZ regs) cs (-128) 0 wlo whi od e v HR Hsp (Hin _ Hc) He Hv). }
assert (RG : forall (n : nat) (r : Z), (n < 32)%nat -> r = Z.of_nat n ->
  sv_denot E (SOff n 0) = Z_to_bv 64 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros n r Hn ->. cbn [sv_denot]. rewrite (AG n Hn), Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity. }
split; [|split].
- intros p Hp. pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (snd p)))) as Rg. unfold bv_modulus in Rg.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rg.
  cbn [ARB_SAVES In] in Hp.
  repeat (destruct Hp as [<-|Hp];
    [ cbn [fst snd] in Rg |- *;
      match goal with |- val_mem _ _ (spZ regs - 128 + ?o) _ _ =>
        let o' := eval vm_compute in (o - 128) in replace (spZ regs - 128 + o) with (spZ regs + o') by lia end;
      eapply SL; [cbn [ARB_STKA In]; repeat (first [left; reflexivity | right]) | apply RG; [lia | reflexivity] | lia] |]).
  destruct Hp.
- replace (spZ regs - 128 + 16) with (spZ regs + -112) by lia. eapply SL.
  + cbn [ARB_STKA In]. repeat (first [left; reflexivity | right]).
  + exact (proj2 (arb_denot_shx E 15 out 16 H32 H15 ltac:(lia) ltac:(lia))).
  + unfold SB. split; [|apply Z.lt_le_trans with (2147450880 + 2 ^ 44); [apply Z.add_lt_mono_l, Z.div_lt_upper_bound|]]; try lia.
- replace (spZ regs - 128 + 8) with (spZ regs + -120) by lia. eapply SL.
  + cbn [ARB_STKA In]. repeat (first [left; reflexivity | right]).
  + cbn [sv_denot]. rewrite H15. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
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

Definition ARB_SEGP : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (b : option Z) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invP ly S W regs mem md t our fsm pace now out T P b regs3 mem3 md3 ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_P)) mem3 (seg_rom SEGS)) md3)
    (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).

Definition ARB_SEGL : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (i : Z) (b : option Z) (regs3 : bvmap 5 word) mem3 md3
    (Q : world SEGS -> config -> Prop),
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invL ly S W regs mem md t our fsm pace now out T P i b regs3 mem3 md3 ->
  (forall regs4 mem4 md4,
     arb_invL ly S W regs mem md t our fsm pace now out T P (i + 1) (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + AF_ARB_L)) mem4 (seg_rom SEGS)) md4) Q) ->
  (forall regs4 mem4 md4,
     arb_invP ly S W regs mem md t our fsm pace now out T P (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + AF_ARB_P)) mem4 (seg_rom SEGS)) md4) Q) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_L)) mem3 (seg_rom SEGS)) md3) Q.

Definition ARB_SEGA : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (Q : world SEGS -> config -> Prop),
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  (forall regs3 mem3 md3,
     arb_invL ly S W regs mem md t our fsm pace now out T P 0 None regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_L)) mem3 (seg_rom SEGS)) md3) Q) ->
  (forall regs3 mem3 md3,
     arb_invP ly S W regs mem md t our fsm pace now out T P None regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_P)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_arbitrate) regs mem md) Q.

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
  intros c Hc; cbn [In ARB_STKA ARB_OUTA] in Hc;
  repeat (destruct Hc as [<-|Hc]; [cbn [In]; repeat (first [left; reflexivity | right]) |]); destruct Hc.

Lemma arb_bge0 : forall E (m : nat) v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff m 0)) = negb (0 <? v).
Proof.
intros E m v H Hv. cbn [branch_taken sv_denot]. rewrite H, unsigned_lit_small, Z.add_0_r by lia.
unfold bv_lts. rewrite !YK11.bv_signed_small by (rewrite unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma arb_segA_t : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (Q : world SEGS -> config -> Prop),
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P -> t <> 0 ->
  (forall regs3 mem3 md3,
     arb_invL ly S W regs mem md t our fsm pace now out T P 0 None regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_L)) mem3 (seg_rom SEGS)) md3) Q) ->
  (forall regs3 mem3 md3,
     arb_invP ly S W regs mem md t our fsm pace now out T P None regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_P)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_arbitrate) regs mem md) Q.
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P Q HA Ht0 HL HP.
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
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (Ht16 & Ht4096 & Htceil & Htia & Htpres & _).
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
pose proof (blk_off_imgP _ _ _ _ _ _ bo No HAR Hbo) as Hoimg. pose proof (blk_off_imgP _ _ _ _ _ _ bt Nt HAR Hbt) as Htimg.
unfold off_img, IMG_LO, IMG_TOP in HcellR, HgotR, Hoimg, Htimg. cbv [A_OBJ Nat.add] in HcellR, HgotR.
remember (EA regs (disco_table_c.n_of T)) as E eqn:HE.
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
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_reac_arbitrate)) with (Z_to_bv 64 (BASE + AF_reac_arbitrate)).
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
  eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIGMA DS___asan_memset) (AMEMSET fq) W (ms_regs msX) (ms_mem msX)
     REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S _ 0 out 0 32 (-128) _ HJ) end.
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
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 4]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [ | | | | apply Forall_nil].
  - eapply region_kept_aview; [exact Usp | | exact Hpres2].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
  - apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (VAL (A_OBJ 66)));
    [exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot1)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 66) (VAL (A_OBJ 66)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 66) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell1)
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
  rewrite E15b, E10b, Uspb, (HEI2 242%nat ltac:(unfold A_TEXT, A_LIM; lia)), (HEI2 307%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  rewrite !unsigned_lit_small by lia. repeat split; lia. }
clear HS SHOK. rename HS3 into HS.
assert (SHOK : sh_ok SEGS ARB_BX arbA_SH Ea (mrestrict (w_H W) mem2)).
{ constructor; [|constructor; [|constructor]].
  - apply (arb_shent ly S W mem2 md2 Ea 15 bo No out 0 32 (proj1 HJ2) Hbo); [apply arb_U_BX; exact E32b | apply arb_U_atom; [exact E15b | lia] | lia | lia | lia].
  - apply (arb_shent ly S W mem2 md2 Ea 10 bt Nt t 0 400 (proj1 HJ2) Hbt); [apply arb_U_BX; exact E32b | apply arb_U_atom; [exact E10b | lia] | lia | lia | lia]. }
paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arb_awr Uspb E15b Hbo |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) HFr ltac:(arb_win Uspb E15b)) as K2. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
- paj_run_to_tok RUNTO HS HJ2 SHOK ARB_SPAN 31968; [arb_awr Uspb E15b Hbo |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) HFr ltac:(arb_win Uspb E15b)) as K3. clear HF HFr HG.
  rewrite (arb_bge0 Ea 33 (disco_table_c.n_of T) E33b ltac:(lia)) in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  pmkst HS. change (BASE + 31968) with (BASE + AF_ARB_P). apply HP.
  split; [|split].
    { split. { exact HJ2. }
      split. { intros a Ha N1 N2. rewrite (K3 a Ha) by (cbv beta; lia). rewrite (K2 a Ha) by (cbv beta; lia).
        rewrite (Hfr a Ha N1) by (unfold ESTACK; lia). rewrite (K1 a Ha) by (cbv beta; lia). reflexivity. }
      split. { arb_region HS 1%nat HRs. apply (arb_frameA Ea _ regs out _ _ _ HRs Uspb AG2 E32b E15b ltac:(lia)). arb_incl. }
      split. { arb_region HS 0%nat HRo. apply (arb_outA Ea _ out pace _ HRo ltac:(rewrite E15b; apply unsigned_lit_small; lia)
        ltac:(rewrite (AG2 13%nat) by lia; exact H13)). arb_incl. }
      split. { arb_rreg HS (2%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite Uspb. reflexivity. }
      split. { arb_rreg HS (3%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 3%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      split. { arb_rreg HS (4%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 4%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      split. { arb_rreg HS (8%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite E15b, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      split. { arb_rreg HS (9%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 11%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H11. }
      split. { arb_rreg HS (18%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 12%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H12. }
      { arb_rreg HS (25%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite E32b, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. } }
  + arb_rreg HS (19%bv : bv 5) R. rewrite R. reflexivity.
  + unfold reac_arbitrate_c.best. replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ht0).
    unfold reac_arbitrate_c.cands. replace (Z.to_nat (disco_table_c.n_of T)) with 0%nat by lia. reflexivity.
- paj_run_to_tok RUNTO HS HJ2 SHOK ARB_SPAN 31812; [arb_awr Uspb E15b Hbo |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) HFr ltac:(arb_win Uspb E15b)) as K3. clear HF HFr HG.
  rewrite (arb_bge0 Ea 33 (disco_table_c.n_of T) E33b ltac:(lia)) in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  pmkst HS. change (BASE + 31812) with (BASE + AF_ARB_L). apply HL.
  split; [|split].
    { split. { exact HJ2. }
      split. { intros a Ha N1 N2. rewrite (K3 a Ha) by (cbv beta; lia). rewrite (K2 a Ha) by (cbv beta; lia).
        rewrite (Hfr a Ha N1) by (unfold ESTACK; lia). rewrite (K1 a Ha) by (cbv beta; lia). reflexivity. }
      split. { arb_region HS 1%nat HRs. apply (arb_frameA Ea _ regs out _ _ _ HRs Uspb AG2 E32b E15b ltac:(lia)). arb_incl. }
      split. { arb_region HS 0%nat HRo. apply (arb_outA Ea _ out pace _ HRo ltac:(rewrite E15b; apply unsigned_lit_small; lia)
        ltac:(rewrite (AG2 13%nat) by lia; exact H13)). arb_incl. }
      split. { arb_rreg HS (2%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite Uspb. reflexivity. }
      split. { arb_rreg HS (3%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 3%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      split. { arb_rreg HS (4%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 4%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      split. { arb_rreg HS (8%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite E15b, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      split. { arb_rreg HS (9%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 11%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H11. }
      split. { arb_rreg HS (18%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 12%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H12. }
      { arb_rreg HS (25%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite E32b, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. } }
  + arb_rreg HS (19%bv : bv 5) R. rewrite R. reflexivity.
  + split. { reflexivity. }
    split. { exact Ht0. }
    split. { lia. }
    split. { arb_rreg HS (20%bv : bv 5) R. rewrite R. reflexivity. }
    split. { arb_rreg HS (21%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 14%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H14. }
    split. { arb_rreg HS (22%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite E10b, unsigned_lit_small by lia. f_equal; lia. }
    split. { arb_rreg HS (23%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite E10b, unsigned_lit_small by lia. f_equal; lia. }
    split. { arb_rreg HS (24%bv : bv 5) R. rewrite R. rewrite (proj1 (arb_denot_shx Ea 10 t 8 E32b E10b ltac:(lia) ltac:(lia))).
      rewrite Z.mul_0_r, Z.add_0_r. reflexivity. }
    split. { arb_rreg HS (26%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite E33b, Z.add_0_r, Z_to_bv_bv_unsigned; try (rewrite Z.sub_0_r; reflexivity). }
    { arb_rreg HS (27%bv : bv 5) R. rewrite R. reflexivity. }
Qed.

Definition arbA0_regions : smem :=
  [ stack_region 128; got_regionP; bcell_regionP 32; YP09.mkRegion (Some 15%nat) 0 32 0 32 [] ].
Definition arbA0_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0 0 0);
            (15%nat, mkAF 4096 140737479966720 2); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_arbA0 : sstate := mkSS AF_reac_arbitrate sr_atoms arbA0_regions None arbA0_facts.
Definition arbA0_SH : list shent := [ mkSHE 15 0 32 ].
Definition EA0 (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SB]).

Lemma arbA0_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (out bo No : Z),
  afn_pre SEGS B REAC_ARBITRATE_STK ly S W regs mem md ch ->
  getr regs 10 = w64 0 -> getr regs 15 = w64 out -> 0 < out < 2 ^ 64 ->
  In (bo, No) (ablocks B ly S) -> bo <= out -> out + 32 <= bo + req_size No -> out mod 4 = 0 ->
  st_ok_pi (fx := fq) SEGS VAL (EA0 regs) ss_arbA0
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_reac_arbitrate)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS ARB_BX arbA0_SH (EA0 regs) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch out bo No HPRE H10 H15 Rout Hbo Hbo1 Hbo2 Ho4.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ bo No HAR Hbo) as Hoimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
unfold off_img, IMG_LO, IMG_TOP in HcellR, HgotR, Hoimg.
rewrite restrict_mkst_fx.
set (E := EA0 regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n)
  by (intros n Hn; subst E; unfold EA0; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Eo66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; unfold EA0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EA0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
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
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
      [cbn [sv_denot]; rewrite Eo66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Eo66) by (pose proof (pa_val_range (A_OBJ 66)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 ARB_BX SB);
      [cbn [sv_denot ARB_BX]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. unfold SB. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 15%nat out E15) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hopres (out + o) ltac:(lia))).
  + apply pairwise_disjoint_of_extents. unfold arbA0_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 15%nat out E15) by lia.
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Eo66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
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
     arb_invP ly S W regs mem md t our fsm pace now out T P None regs3 mem3 md3 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_P)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_arbitrate) regs mem md) Q.
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P Q HA Ht0 HL HP.
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HPP).
subst t.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
destruct (arbA0_entry fq ly S W regs mem md ch out bo No HPRE H10 H15 Rout Hbo Hbo1 Hbo2 Ho4) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_ARBITRATE_STK [(out, out + 32)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
pose proof (blk_off_imgP _ _ _ _ _ _ bo No HAR Hbo) as Hoimg.
unfold off_img, IMG_LO, IMG_TOP in HcellR, HgotR, Hoimg. cbv [A_OBJ Nat.add] in HcellR, HgotR.
remember (EA0 regs) as E eqn:HE.
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
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_reac_arbitrate)) with (Z_to_bv 64 (BASE + AF_reac_arbitrate)).
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
  eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIGMA DS___asan_memset) (AMEMSET fq) W (ms_regs msX) (ms_mem msX)
     REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S _ 0 out 0 32 (-128) _ HJ) end.
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
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [ | | | apply Forall_nil].
  - eapply region_kept_aview; [exact Usp | | exact Hpres2].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
  - apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (VAL (A_OBJ 66)));
    [exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot1)
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 66) (VAL (A_OBJ 66)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 66) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell1)
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
  rewrite E15b, Uspb, (HEI2 242%nat ltac:(unfold A_TEXT, A_LIM; lia)), (HEI2 307%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  rewrite !unsigned_lit_small by lia. repeat split; lia. }
clear HS SHOK. rename HS3 into HS.
assert (SHOK : sh_ok SEGS ARB_BX arbA0_SH Ea (mrestrict (w_H W) mem2)).
{ constructor; [|constructor].
  apply (arb_shent ly S W mem2 md2 Ea 15 bo No out 0 32 (proj1 HJ2) Hbo); [apply arb_U_BX; exact E32b | apply arb_U_atom; [exact E15b | lia] | lia | lia | lia]. }
paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arb_awr Uspb E15b Hbo |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) HFr ltac:(arb_win Uspb E15b)) as K2. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
2: { exfalso. rewrite branch_eq_U, (U_atom Ea 10 0 E10b ltac:(lia)), U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
paj_run_to_tok RUNTO HS HJ2 SHOK ARB_SPAN 31968; [arb_awr Uspb E15b Hbo |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) HFr ltac:(arb_win Uspb E15b)) as K3. clear HF HFr HG.
  pmkst HS. change (BASE + 31968) with (BASE + AF_ARB_P). apply HP.
split; [|split].
{ split. { exact HJ2. }
      split. { intros a Ha N1 N2. rewrite (K3 a Ha) by (cbv beta; lia). rewrite (K2 a Ha) by (cbv beta; lia).
        rewrite (Hfr a Ha N1) by (unfold ESTACK; lia). rewrite (K1 a Ha) by (cbv beta; lia). reflexivity. }
      split. { arb_region HS 1%nat HRs. apply (arb_frameA Ea _ regs out _ _ _ HRs Uspb AG2 E32b E15b ltac:(lia)). arb_incl. }
      split. { arb_region HS 0%nat HRo. apply (arb_outA Ea _ out pace _ HRo ltac:(rewrite E15b; apply unsigned_lit_small; lia)
        ltac:(rewrite (AG2 13%nat) by lia; exact H13)). arb_incl. }
      split. { arb_rreg HS (2%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite Uspb. reflexivity. }
      split. { arb_rreg HS (3%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 3%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      split. { arb_rreg HS (4%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 4%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      split. { arb_rreg HS (8%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite E15b, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      split. { arb_rreg HS (9%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 11%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H11. }
      split. { arb_rreg HS (18%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite (AG2 12%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H12. }
      { arb_rreg HS (25%bv : bv 5) R. rewrite R. cbn [sv_denot]. rewrite E32b, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. } }
+ arb_rreg HS (19%bv : bv 5) R. rewrite R. reflexivity.
+ reflexivity.
Qed.

Lemma arb_segA : ARB_SEGA.
Proof.
unfold ARB_SEGA.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P Q HA HL HP.
destruct (Z.eq_dec t 0) as [Ht0|Ht0].
- exact (arb_segA_0 fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P Q HA Ht0 HL HP).
- exact (arb_segA_t fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P Q HA Ht0 HL HP).
Qed.

(* The FP state a callee may leave (apost_base's two FP clauses), from the entry state fq0 to the current fq.
   After reac_rival_kind_of returns, the walk runs in the callee's final FP state, not in the entry one. *)
Definition arb_fprel (fq0 fq : YK11.FPState) : Prop :=
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fq) k = Sem.reg_get (@YK11.fp_regs fq0) k) /\
  (@YK11.fp_csr fq = @YK11.fp_csr fq0 \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fq)) 5) 7 = 0).
Lemma arb_fprel_refl : forall fq, arb_fprel fq fq.
Proof. intros fq. split; [intros; reflexivity | left; reflexivity]. Qed.
(* The symbolic state does not track FP registers: it moves to the FP state the callee left. *)
Lemma arb_st_ok_xfx : forall (fa fb : YK11.FPState) E ss (H : word -> bool) regs pc mem,
  st_ok_pi (fx := fa) SEGS VAL E ss (restrict H (@mkst fa regs pc mem (seg_rom SEGS))) ->
  st_ok_pi (fx := fb) SEGS VAL E ss (restrict H (@mkst fb regs pc mem (seg_rom SEGS))).
Proof.
intros fa fb E ss H regs pc mem HS. unfold st_ok_pi in *. rewrite restrict_mkst_fx in *.
exact (FpStep.fp_st_ok_fx SEGS fa fb E _ _ _ _ _ HS).
Qed.

Lemma arb_post_intro : forall (fq0 fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) ly' S' (regs' : bvmap 5 word) mem' md',
  arb_fprel fq0 fq ->
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly' S' W mem' md' 0 ->
  aregs_preserved regs regs' -> getr regs' 1 = getr regs 1 ->
  Permutation (ablocks B ly' S') (ablocks B ly S) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  garr8 SEGS (mrestrict (w_H W) mem') out
    (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.arb_model t our T P fsm pace now)) ->
  treac_arbitrate_post fq0 regs ly S W mem md t our fsm pace now out T P W
    (mkCfg (mkst (fx := fq) regs' (getr regs 1) mem' (seg_rom SEGS)) md').
Proof.
intros fq0 fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ly' S' regs' mem' md'
  FPR HA HJ HPR Hra HPerm HK Hout.
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HPP).
pose proof HPRE as (HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity.
unfold treac_arbitrate_post, apost_base.
exists fq, ly', S', regs', mem', md'.
split; [reflexivity|]. split; [exact (proj1 FPR)|]. split; [exact (proj2 FPR)|].
split; [exact HJ|]. split; [exact HPR|].
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

Lemma arb_rival_at : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md (out : Z) ly3 S3
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
  spZ regsT = spZ regs - 128 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> s0Z regsT < alloc_ceiling ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regsT (Z_to_bv 64 (SIGMA DS_reac_rival_kind_of)) memT (seg_rom SEGS)) md3)
    (fun W2 c2 => W2 = W /\ exists (fq2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
       c2 = mkCfg (mkst (fx := fq2) regs2 raw mem2 (seg_rom SEGS)) md2 /\ arb_fprel fq fq2 /\
       ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly2 S2 W mem2 md2 0 /\
       aregs_preserved regsT regs2 /\
       getr regs2 10 = w64 (if e =? 0 then 0 else reac_rival_kind_of_c.reac_rival_kind_model d r s c) /\
       Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\
       (forall a : word, ~ (spZ regs - 128 - REAC_RIVAL_KIND_OF_STK <= bv_unsigned a < spZ regs - 128) -> mem2 a = memT a)).
Proof.
intros fq ly S W regs mem md out ly3 S3 regsT memT md3 e r d s c raw HJ HROD H10 Re He8 HE Hsp Hgp Htp Hra Hraw Hraw4 Hs0.
pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & HQT).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity. assert (WR : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
rewrite pa_sigma_reac_rival_kind_of.
eapply SRr_mono.
{ apply (TRIVAL fq ly3 S3 W regsT memT md3 [] e r d s c).
  - apply (afn_pre_at SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly3 S3 W memT md3 0 regsT
      REAC_RIVAL_KIND_OF_STK (-128) [] HJ).
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
destruct HPOST as (fq2 & ly2 & S2 & regs2 & mem2 & md2 & Hc & Hfq2 & Hcsr2 & HJ1 & HP & Ha0 & HPerm & -> & Hkeep).
split; [reflexivity|]. exists fq2, ly2, S2, regs2, mem2, md2.
split; [rewrite Hc, Hra; reflexivity|]. split; [split; [exact Hfq2 | exact Hcsr2]|].
split.
{ change (@nil (Z * Z)) with (@nil (Z * Z) ++ @nil (Z * Z)). replace 0 with (0 + 0) by lia.
  eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | rewrite Hsp, WR, WS; unfold ESTACK; lia | rewrite Hsp; lia |].
  intros a Ha. exfalso. exact (inFP_nil a Ha). }
split; [exact HP|]. split; [exact Ha0|]. split; [exact HPerm|].
intros a Ha. apply Hkeep. rewrite Hsp. exact Ha.
Qed.

Lemma arb_z4_garr8 : forall (m : word -> option byte) a v V,
  val_mem SEGS m a 4 V -> V mod 2 ^ 32 = bv_unsigned (Z_to_bv 64 v) mod 2 ^ 32 ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)).
Proof.
intros m a v V HV HE.
assert (LZ : length (reac_arbitrate_c.z4 v) = 4%nat) by reflexivity.
apply (arb_garr8_val_mem m a _ V); [rewrite LZ; exact HV|].
rewrite LZ. change (reac_arbitrate_c.z4 v) with (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v))).
rewrite bytes_le_Z_to_le by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 v)); lia). exact HE.
Qed.

Lemma arb_bytes_garr8 : forall (m : word -> option byte) out st (mac : list byte) hv pc cf rv ch,
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

Definition arbL_regs (regs5 : bvmap 5 word) (t now : Z) (T : list byte) (i : Z) : Prop :=
  getr regs5 20 = Z_to_bv 64 ARB_STALE /\ getr regs5 21 = Z_to_bv 64 now /\
  getr regs5 22 = Z_to_bv 64 (t + 48 * i) /\ getr regs5 23 = Z_to_bv 64 (t + 48 * i + 40) /\
  getr regs5 24 = Z_to_bv 64 (SB + (t + 48 * i + 8) / 8) /\
  getr regs5 26 = Z_to_bv 64 (disco_table_c.n_of T - i) /\ getr regs5 27 = Z_to_bv 64 2.

Lemma arb_stk : forall ly S W (regs : bvmap 5 word) mem md ch,
  afn_pre SEGS B REAC_ARBITRATE_STK ly S W regs mem md ch ->
  alloc_ceiling + REAC_ARBITRATE_STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\ spZ regs mod 16 = 0.
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
lia.
Qed.

Lemma arb_blk : forall ly S W mem md p n a k,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a -> a + k <= p + req_size n ->
  4096 <= p /\ a + k <= alloc_ceiling /\ in_app p (req_size n).
Proof.
intros ly S W mem md p n a k HAR Hin H1 H2.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & Hia & _). split; [lia | split; [lia | exact Hia]].
Qed.

Lemma arb_frame_ro : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hb a Ha. apply (kept_of_frame (segs := SEGS) E rs H m m' (fun _ => False) HF); [|exact Ha|tauto].
intros b wlo whi x Hin Hx. unfold windows in Hin. apply in_map_iff in Hin. destruct Hin as (r & Hr & Hin).
rewrite forallb_forall in Hb. specialize (Hb r Hin). apply Z.leb_le in Hb. inversion Hr; subst. lia.
Qed.

Lemma arb_cmn_step : forall ly S W (regs : bvmap 5 word) mem md our fsm pace out regs3 mem3 md3 (regs4 : bvmap 5 word) mem4 md4,
  arb_cmn ly S W regs mem md our fsm pace out regs3 mem3 md3 ->
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S W mem4 md4 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs - 128) ->
     aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a) ->
  0 <= out -> out + 32 <= spZ regs - REAC_ARBITRATE_STK ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  getr regs4 8 = getr regs3 8 -> getr regs4 9 = getr regs3 9 -> getr regs4 18 = getr regs3 18 ->
  getr regs4 25 = getr regs3 25 ->
  arb_cmn ly S W regs mem md our fsm pace out regs4 mem4 md4.
Proof.
intros ly S W regs mem md our fsm pace out regs3 mem3 md3 regs4 mem4 md4
  (HJ & HK & HFR & HOUT & R2 & R3 & R4 & R8 & R9 & R18 & R25) HJ4 HV Ho0 Hos Q2 Q3 Q4 Q8 Q9 Q18 Q25.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity.
pose proof alloc_ceiling_value as (AC & _). pose proof alloc_ceiling_lt as AC2.
split; [exact HJ4|].
split.
{ intros a Ha Hno Hns. rewrite (HV a Ha) by lia. exact (HK a Ha Hno Hns). }
split.
{ destruct HFR as (F1 & F2 & F3). split; [|split].
  - intros p Hp.
    assert (Hb : 8 <= fst p <= 120).
    { cbn [ARB_SAVES In] in Hp. repeat (destruct Hp as [<-|Hp]; [cbn [fst]; lia|]). destruct Hp. }
    apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 mem4); [|exact (F1 p Hp)].
    intros x Hx. apply HV; lia.
  - apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 mem4); [|exact F2].
    intros x Hx. apply HV; lia.
  - apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 mem4); [|exact F3].
    intros x Hx. apply HV; lia. }
split.
{ assert (Hl : length (arb_out0 pace) = 32%nat) by (unfold arb_out0; rewrite length_map; reflexivity).
  apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact HOUT].
  rewrite Hl. intros a Ha. apply HV; lia. }
rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q25. tauto.
Qed.

Ltac arb_views :=
  repeat match goal with HF' : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let V := fresh "V" in pose proof (arb_frame_ro _ _ _ _ _ HF' ltac:(vm_compute; reflexivity)) as V; clear HF' end;
  repeat match goal with HF' : frame_of _ _ _ _ |- _ => clear HF' end.

Ltac arb_vchain := let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha ?;
  repeat match goal with V : forall x, 0 <= x < 2 ^ 64 -> aview _ _ _ x = aview _ _ _ x |- _ => rewrite (V a Ha); clear V end;
  reflexivity.

Lemma arb_U0 : forall E, U E (SLit 0) = 0.
Proof. intros E. rewrite U_SLit. apply zcanon_id. unfold M64. lia. Qed.

Lemma arb_sx_small : forall r, 0 <= r <= 2 -> zcanon (bv_swrap 32 (r mod 2 ^ 32)) = r.
Proof.
intros r H. rewrite (Z.mod_small r) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
change (4294967296 / 2) with 2147483648. rewrite (Z.mod_small (r + 2147483648)) by lia.
replace (r + 2147483648 - 2147483648) with r by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma arb_U_sub : forall E (na nb : nat) a b, ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b ->
  0 <= a < 2 ^ 64 -> 0 <= b <= a ->
  U E (SAlu ALU_ADD (SOff na 0) (SMd M_MUL (SOff nb 0) (SLit (-1)))) = a - b.
Proof.
intros E na nb a b Ha Hb Ra Rb.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit.
rewrite (U_atom E na a Ha), (U_atom E nb b Hb) by lia.
change (zcanon (-1)) with (2 ^ 64 - 1).
unfold zcanon, M64. rewrite Zplus_mod_idemp_r.
replace (a + b * (2 ^ 64 - 1)) with ((a - b) + b * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma arb_regs_ok_set : forall E sr (regs : bvmap 5 word) (r : bv 5) e,
  YP0l.regs_ok E sr regs -> sv_denot E e = getr regs r -> YP0l.regs_ok E (YP0l.sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hv r'. unfold YP0l.sr_set. destruct (bv_eqb r 0) eqn:Hr0; [apply Hr|].
specialize (Hr r'). unfold YP0l.sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite YP0l.nth_sr_upd. destruct (Nat.eqb (YP0l.ridx r') (YP0l.ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply YP0l.ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.

Lemma arb_mod8 : forall t j, t mod 8 = 0 -> (t + 48 * j) mod 8 = 0.
Proof. intros t j H. replace (t + 48 * j) with (t + (6 * j) * 8) by lia. rewrite Z_mod_plus_full. exact H. Qed.

Lemma arb_garr8_T : forall ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (regs5 : bvmap 5 word) mem5 md5,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_cmn ly S W regs mem md our fsm pace out regs5 mem5 md5 -> t <> 0 ->
  garr8 SEGS (mrestrict (w_H W) mem5) t (map (fun b : byte => bv_unsigned b) T).
Proof.
intros ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs5 mem5 md5 HA HC Ht0.
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis).
destruct (arb_stk ly S W regs mem md ch HPRE) as (SK1 & SK2 & SK3).
destruct (arb_blk ly S W mem md bt Nt t 400 (proj1 HPRE) Hbt Hbt1 Hbt2) as (Bt1 & Bt2 & _).
pose proof alloc_ceiling_lt as AC2.
destruct HC as (HJ & HK & _).
apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem5); [|exact GT].
rewrite length_map, LT. intros a Ha. apply HK; lia.
Qed.

Lemma arb_garr8_P : forall ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (regs5 : bvmap 5 word) mem5 md5,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_cmn ly S W regs mem md our fsm pace out regs5 mem5 md5 -> our <> 0 ->
  garr8 SEGS (mrestrict (w_H W) mem5) our (map (fun b : byte => bv_unsigned b) P).
Proof.
intros ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs5 mem5 md5 HA HC Hu0.
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
destruct (HP Hu0) as (Hbp & Hbp1 & Hbp2 & LP & GP & Hdis).
destruct (arb_stk ly S W regs mem md ch HPRE) as (SK1 & SK2 & SK3).
destruct (arb_blk ly S W mem md bp Np our 6 (proj1 HPRE) Hbp Hbp1 Hbp2) as (Bp1 & Bp2 & _).
pose proof alloc_ceiling_lt as AC2.
destruct HC as (HJ & HK & _).
apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem5); [|exact GP].
rewrite length_map, LP. intros a Ha. apply HK; lia.
Qed.

Lemma arb_map_skipn : forall (f : byte -> Z) n (l : list byte), map f (skipn n l) = skipn n (map f l).
Proof. intros f n. induction n as [|n IH]; intros [|x l]; cbn; auto. Qed.

Lemma arb_map_firstn : forall (f : byte -> Z) n (l : list byte), map f (firstn n l) = firstn n (map f l).
Proof. intros f n. induction n as [|n IH]; intros [|x l]; cbn; auto. rewrite IH. reflexivity. Qed.

Lemma arb_garr8_sub6 : forall (m : word -> option byte) p (L : list byte) k,
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) -> 0 <= k -> k + 6 <= Z.of_nat (length L) ->
  garr8 SEGS m (p + k) (map (fun b : byte => bv_unsigned b) (disco_table_c.sub L k 6)).
Proof.
intros m p L k HG Hk Hkn.
unfold disco_table_c.sub. rewrite arb_map_firstn, arb_map_skipn.
replace (p + k) with (p + Z.of_nat (Z.to_nat k)) by lia.
apply (garr8_sub_x SEGS m p (map (fun b : byte => bv_unsigned b) L) (Z.to_nat k) 6 HG).
rewrite length_map. lia.
Qed.

Lemma arb_aview_nth : forall H (m : word -> option byte) p (L : list byte) (j : nat), (j < length L)%nat ->
  garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) L) ->
  aview SEGS H m (p + Z.of_nat j) = Some (bv_unsigned (nth j L (Z_to_bv 8 0))).
Proof.
intros H m p L j Hj HG.
assert (Hj2 : (j < length (map (fun b : byte => bv_unsigned b) L))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte SEGS (mrestrict H m) p _ j HG Hj2) as Hb.
unfold aview. rewrite Hb. cbn [option_map]. f_equal. f_equal.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite map_nth. apply Z_to_bv_bv_unsigned.
Qed.

Lemma arb_mac_eq : forall H (m : word -> option byte) x y (L R : list byte),
  garr8 SEGS (mrestrict H m) x (map (fun b : byte => bv_unsigned b) L) ->
  garr8 SEGS (mrestrict H m) y (map (fun b : byte => bv_unsigned b) R) ->
  length L = 6%nat -> length R = 6%nat ->
  ((forall i0 : Z, 0 <= i0 < 6 -> aview SEGS H m (x + i0) = aview SEGS H m (y + i0)) <-> L = R).
Proof.
intros H m x y L R GL GR HL HR. split.
- intros HE. apply (nth_ext L R (Z_to_bv 8 0) (Z_to_bv 8 0)); [lia|].
  intros j Hj. specialize (HE (Z.of_nat j) ltac:(lia)).
  rewrite (arb_aview_nth H m x L j ltac:(lia) GL), (arb_aview_nth H m y R j ltac:(lia) GR) in HE.
  injection HE as HE. apply bv_eq. exact HE.
- intros ->. intros i0 Hi0.
  replace i0 with (Z.of_nat (Z.to_nat i0)) by lia.
  rewrite (arb_aview_nth H m x R (Z.to_nat i0) ltac:(lia) GL), (arb_aview_nth H m y R (Z.to_nat i0) ltac:(lia) GR).
  reflexivity.
Qed.

Ltac arb_vlist a Ha :=
  repeat match goal with V : forall x, 0 <= x < 2 ^ 64 -> aview _ _ _ x = aview _ _ _ x |- _ =>
    rewrite (V a Ha); clear V end.

Lemma arbL_E : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (i : Z) (regs5 : bvmap 5 word) mem5 md5
    (Q : world SEGS -> config -> Prop),
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_cmn ly S W regs mem md our fsm pace out regs5 mem5 md5 ->
  getr regs5 19 = Z_to_bv 64 (reac_arbitrate.baddr t (reac_arbitrate.scanz T P our now (i + 1))) ->
  t <> 0 -> 0 <= i < disco_table_c.n_of T -> arbL_regs regs5 t now T i ->
  (forall regs4 mem4 md4,
     arb_invL ly S W regs mem md t our fsm pace now out T P (i + 1) (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + AF_ARB_L)) mem4 (seg_rom SEGS)) md4) Q) ->
  (forall regs4 mem4 md4,
     arb_invP ly S W regs mem md t our fsm pace now out T P (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + AF_ARB_P)) mem4 (seg_rom SEGS)) md4) Q) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs5 (Z_to_bv 64 (BASE + 31920)) mem5 (seg_rom SEGS)) md5) Q.
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i regs5 mem5 md5 Q HA HC H19 Ht0 Hi HR KL KP.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis).
pose proof TOK as (TN & _).
unfold disco_table_c.tbl_T1 in TN.
destruct (arb_stk ly S W regs mem md ch HPRE) as (SK1 & SK2 & SK3).
destruct (arb_blk ly S W mem md bo No out 32 (proj1 HPRE) Hbo Hbo1 Hbo2) as (Bo1 & Bo2 & _).
destruct (arb_blk ly S W mem md bt Nt t 400 (proj1 HPRE) Hbt Hbt1 Hbt2) as (Bt1 & Bt2 & _).
pose proof alloc_ceiling_lt as AC2.
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity.
pose proof HC as (HJ & _).
destruct HR as (R20 & R21 & R22 & R23 & R24 & R26 & R27).
remember (Eimg (Ereg regs5 [Z_to_bv 64 SB])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs5 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. }
assert (HS : st_ok_pi (fx := fq) SEGS VAL E (mkSS 31920 sr_atoms [] None (mkFacts [] [] []))
   (restrict (w_H W) (mkst (fx := fq) regs5 (Z_to_bv 64 (BASE + 31920)) mem5 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. subst E. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; exact I | unfold facts_ok; cbn; tauto]. }
assert (SHOK : sh_ok SEGS ARB_BX [] E (mrestrict (w_H W) mem5)) by constructor.
clear HE.
assert (E2 : ew E 2 = getr regs5 2) by (apply EL; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs5 3) by (apply EL; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs5 4) by (apply EL; [lia | reflexivity]).
assert (E8 : ew E 8 = getr regs5 8) by (apply EL; [lia | reflexivity]).
assert (E9 : ew E 9 = getr regs5 9) by (apply EL; [lia | reflexivity]).
assert (E18 : ew E 18 = getr regs5 18) by (apply EL; [lia | reflexivity]).
assert (E19 : ew E 19 = getr regs5 19) by (apply EL; [lia | reflexivity]).
assert (E20 : ew E 20 = getr regs5 20) by (apply EL; [lia | reflexivity]).
assert (E21 : ew E 21 = getr regs5 21) by (apply EL; [lia | reflexivity]).
assert (E22 : ew E 22 = getr regs5 22) by (apply EL; [lia | reflexivity]).
assert (E23 : ew E 23 = getr regs5 23) by (apply EL; [lia | reflexivity]).
assert (E24 : ew E 24 = getr regs5 24) by (apply EL; [lia | reflexivity]).
assert (E25 : ew E 25 = getr regs5 25) by (apply EL; [lia | reflexivity]).
assert (E26 : ew E 26 = getr regs5 26) by (apply EL; [lia | reflexivity]).
assert (E27 : ew E 27 = getr regs5 27) by (apply EL; [lia | reflexivity]).
rewrite R22 in E22. rewrite R23 in E23. rewrite R24 in E24. rewrite R26 in E26.
assert (SBv : SB = 2147450880) by reflexivity.
assert (D8 : (t + 48 * (i + 1) + 8) / 8 = (t + 48 * i + 8) / 8 + 6).
{ replace (t + 48 * (i + 1) + 8) with ((t + 48 * i + 8) + 6 * 8) by lia. apply Z.div_add. lia. }
assert (D8b : 0 <= (t + 48 * i + 8) / 8 < 2 ^ 47) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [awr_ok_tac |].
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
- rewrite branch_ne_U, arb_U0, (U_atom_off E 26 (disco_table_c.n_of T - i) (-1) E26) in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 31812; [awr_ok_tac |].
  pmkst HS. arb_views.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  apply KL. unfold arb_invL.
  split.
  { eapply (arb_cmn_step ly S W regs mem md our fsm pace out regs5 mem5 md5 _ _ _ HC HJ); [arb_vchain | lia | lia | ..];
    [rewrite Q2; exact E2 | rewrite Q3; exact E3 | rewrite Q4; exact E4 | rewrite Q8; exact E8 | rewrite Q9; exact E9
    | rewrite Q18; exact E18 | rewrite Q25; exact E25]. }
  split; [rewrite Q19, E19; exact H19|]. split; [reflexivity|]. split; [exact Ht0|]. split; [lia|].
  split; [rewrite Q20, E20; exact R20|]. split; [rewrite Q21, E21; exact R21|].
  split; [rewrite Q22, E22, unsigned_lit_small by lia; f_equal; lia|].
  split; [rewrite Q23, E23, unsigned_lit_small by lia; f_equal; lia|].
  split; [rewrite Q24, E24, unsigned_lit_small by lia; f_equal; lia|].
  split; [rewrite Q26, E26, unsigned_lit_small by lia; f_equal; lia|].
  rewrite Q27, E27; exact R27.
- rewrite branch_ne_U, arb_U0, (U_atom_off E 26 (disco_table_c.n_of T - i) (-1) E26) in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 31968; [awr_ok_tac |].
  pmkst HS. arb_views.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (25%bv : bv 5) Q25.
  apply KP. unfold arb_invP.
  split.
  { eapply (arb_cmn_step ly S W regs mem md our fsm pace out regs5 mem5 md5 _ _ _ HC HJ); [arb_vchain | lia | lia | ..];
    [rewrite Q2; exact E2 | rewrite Q3; exact E3 | rewrite Q4; exact E4 | rewrite Q8; exact E8 | rewrite Q9; exact E9
    | rewrite Q18; exact E18 | rewrite Q25; exact E25]. }
  split; [rewrite Q19, E19; exact H19|].
  rewrite (reac_arbitrate.best_scanz t T P our now Ht0). f_equal. lia.
Qed.

Ltac arb_pre_facts HA HC Ht0 :=
  pose proof HA as (HPRE & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP);
  destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis);
  pose proof TOK as (TN & TR & _); unfold disco_table_c.tbl_T1 in TN;
  destruct (arb_stk _ _ _ _ _ _ _ HPRE) as (SK1 & SK2 & SK3);
  destruct (arb_blk _ _ _ _ _ _ _ _ _ (proj1 HPRE) Hbo Hbo1 Hbo2) as (Bo1 & Bo2 & _);
  destruct (arb_blk _ _ _ _ _ _ _ _ _ (proj1 HPRE) Hbt Hbt1 Hbt2) as (Bt1 & Bt2 & Bt3);
  pose proof alloc_ceiling_lt as AC2; pose proof alloc_ceiling_value as (AC1 & _);
  assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity;
  pose proof HC as (HJ & HK5 & HFR5 & HOUT5 & C2 & C3 & C4 & C8 & C9 & C18 & C25).

Ltac arb_Efacts E EL regs5 :=
  assert (E2 : ew E 2 = getr regs5 2) by (apply EL; [lia | reflexivity]);
  assert (E3 : ew E 3 = getr regs5 3) by (apply EL; [lia | reflexivity]);
  assert (E4 : ew E 4 = getr regs5 4) by (apply EL; [lia | reflexivity]);
  assert (E8 : ew E 8 = getr regs5 8) by (apply EL; [lia | reflexivity]);
  assert (E9 : ew E 9 = getr regs5 9) by (apply EL; [lia | reflexivity]);
  assert (E11 : ew E 11 = getr regs5 11) by (apply EL; [lia | reflexivity]);
  assert (E18 : ew E 18 = getr regs5 18) by (apply EL; [lia | reflexivity]);
  assert (E19 : ew E 19 = getr regs5 19) by (apply EL; [lia | reflexivity]);
  assert (E20 : ew E 20 = getr regs5 20) by (apply EL; [lia | reflexivity]);
  assert (E21 : ew E 21 = getr regs5 21) by (apply EL; [lia | reflexivity]);
  assert (E22 : ew E 22 = getr regs5 22) by (apply EL; [lia | reflexivity]);
  assert (E23 : ew E 23 = getr regs5 23) by (apply EL; [lia | reflexivity]);
  assert (E24 : ew E 24 = getr regs5 24) by (apply EL; [lia | reflexivity]);
  assert (E25 : ew E 25 = getr regs5 25) by (apply EL; [lia | reflexivity]);
  assert (E26 : ew E 26 = getr regs5 26) by (apply EL; [lia | reflexivity]);
  assert (E27 : ew E 27 = getr regs5 27) by (apply EL; [lia | reflexivity]).

Ltac arb_prregs HS Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 :=
  prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8;
  prreg HS (9%bv : bv 5) Q9; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19; prreg HS (20%bv : bv 5) Q20;
  prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23; prreg HS (24%bv : bv 5) Q24;
  prreg HS (25%bv : bv 5) Q25; prreg HS (26%bv : bv 5) Q26; prreg HS (27%bv : bv 5) Q27.

Ltac arb_cmn_tac HC HJ Q2 Q3 Q4 Q8 Q9 Q18 Q25 E2 E3 E4 E8 E9 E18 E25 E32 C25 :=
  eapply (arb_cmn_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC HJ); [arb_vchain | lia | lia | ..];
  [rewrite Q2; exact E2 | rewrite Q3; exact E3 | rewrite Q4; exact E4 | rewrite Q8; exact E8 | rewrite Q9; exact E9
  | rewrite Q18; exact E18 | rewrite Q25; first [exact E25 | rewrite E32; symmetry; exact C25]].

Ltac arb_E_regs Q20 Q21 Q22 Q23 Q24 Q26 Q27 E20 E21 E22 E23 E24 E26 E27 R20 R21 R22 R23 R24 R26 R27 SH24 :=
  unfold arbL_regs;
  split; [rewrite Q20; first [rewrite E20; exact R20 | reflexivity]|];
  split; [rewrite Q21, E21; exact R21|];
  split; [rewrite Q22, E22; exact R22|];
  split; [rewrite Q23; first [rewrite E23; exact R23 | rewrite E22, R22, unsigned_lit_small by lia; f_equal; lia]|];
  split; [rewrite Q24; first [rewrite E24; exact R24 | rewrite SH24; reflexivity]|];
  split; [rewrite Q26, E26; exact R26|];
  rewrite Q27; first [rewrite E27; exact R27 | reflexivity].

Lemma arbL_D : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (i : Z) (b : option Z) (regs5 : bvmap 5 word) mem5 md5
    (Q : world SEGS -> config -> Prop),
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_cmn ly S W regs mem md our fsm pace out regs5 mem5 md5 ->
  getr regs5 19 = Z_to_bv 64 (reac_arbitrate.baddr t b) -> b = reac_arbitrate.scanz T P our now i ->
  t <> 0 -> 0 <= i < disco_table_c.n_of T -> arbL_regs regs5 t now T i ->
  getr regs5 11 = Z_to_bv 64 (disco_table_c.last_of T i) ->
  reac_arbitrate_c.cand T P our now i = true ->
  (forall regs4 mem4 md4,
     arb_invL ly S W regs mem md t our fsm pace now out T P (i + 1) (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + AF_ARB_L)) mem4 (seg_rom SEGS)) md4) Q) ->
  (forall regs4 mem4 md4,
     arb_invP ly S W regs mem md t our fsm pace now out T P (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + AF_ARB_P)) mem4 (seg_rom SEGS)) md4) Q) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs5 (Z_to_bv 64 (BASE + 31884)) mem5 (seg_rom SEGS)) md5) Q.
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b regs5 mem5 md5 Q HA HC H19 Hb Ht0 Hi HR H11c Hcand KL KP.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
arb_pre_facts HA HC Ht0.
pose proof HR as (R20 & R21 & R22 & R23 & R24 & R26 & R27).
destruct b as [j|].
- assert (Hj : 0 <= j < i) by (apply (reac_arbitrate.scanz_range T P our now i j); symmetry; exact Hb).
  pose proof (arb_garr8_T ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs5 mem5 md5 HA HC Ht0) as GT5.
  assert (VJ : val_mem SEGS (mrestrict (w_H W) mem5) (t + 48 * j + 40) 8 (disco_table_c.last_of T j)).
  { unfold disco_table_c.last_of, disco_table_c.u_at. replace (t + 48 * j + 40) with (t + (48 * j + 40)) by lia.
    apply val_mem_garr8_sub; [exact GT5 | lia | rewrite LT; lia]. }
  pose proof (reac_arbitrate.u_range T (48 * j + 40) 8 ltac:(lia) ltac:(rewrite LT; lia)) as RJ.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RJ. change (disco_table_c.u_at T (48 * j + 40) 8) with (disco_table_c.last_of T j) in RJ.
  pose proof (reac_arbitrate.u_range T (48 * i + 40) 8 ltac:(lia) ltac:(rewrite LT; lia)) as RI.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RI. change (disco_table_c.u_at T (48 * i + 40) 8) with (disco_table_c.last_of T i) in RI.
  remember (Eimg (Ereg regs5 [Z_to_bv 64 SB; Z_to_bv 64 (disco_table_c.last_of T j)])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs5 r).
  { intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. }
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (disco_table_c.last_of T j)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 1)).
  arb_Efacts E EL regs5.
  assert (E19v : ew E 19 = Z_to_bv 64 (t + 48 * j)) by (rewrite E19; exact H19).
  assert (E11v : ew E 11 = Z_to_bv 64 (disco_table_c.last_of T i)) by (rewrite E11; exact H11c).
  assert (E22v : ew E 22 = Z_to_bv 64 (t + 48 * i)) by (rewrite E22; exact R22).
  pose proof (proj1 (arb_denot_shx E 22 (t + 48 * i) 8 E32 E22v ltac:(lia) ltac:(lia))) as SH24.
  cbn [sv_denot] in SH24. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in SH24.
  assert (HS : st_ok_pi (fx := fq) SEGS VAL E
     (mkSS 31884 (YP0l.sr_set sr_atoms (25%bv : bv 5) (SOff 32 0))
        [YP09.mkRegion (Some 19%nat) 0 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 33 0))]] None
        (mkFacts [(19%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF SB SB 0)] [] []))
     (restrict (w_H W) (mkst (fx := fq) regs5 (Z_to_bv 64 (BASE + 31884)) mem5 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - apply arb_regs_ok_set; [subst E; apply regs_ok_Eimg_Ereg|].
      cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. exact C25.
    - vm_compute. reflexivity.
    - constructor; [|constructor]. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E19v, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (t + 48 * j) 40 8 (SOff 33 0) (disco_table_c.last_of T j));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VJ].
    - apply pairwise_disjoint_of_extents. cbn. tauto.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E19v, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. pose proof (arb_mod8 t j Ht8).
      unfold SB. repeat match goal with |- _ /\ _ => split end; first [lia | exact I]. }
  assert (SHOK : sh_ok SEGS ARB_BX [mkSHE 19 0 48] E (mrestrict (w_H W) mem5)).
  { constructor; [|constructor].
    apply (arb_shent ly S W mem5 md5 E 19 bt Nt (t + 48 * j) 0 48 (proj1 HJ) Hbt);
    [apply arb_U_BX; exact E32 | apply arb_U_atom; [exact E19v | lia] | lia | lia | lia]. }
  clear HE.
  paj_run_tok RUN HS HJ SHOK ARB_SPAN; [awr_ok_tac |].
  psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
  + rewrite branch_geu_U, (U_atom E 33 _ E33), (U_atom E 11 _ E11v) in Hc by lia.
    apply negb_true_iff, Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 31920; [awr_ok_tac |].
    pmkst HS. arb_views. arb_prregs HS Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
    eapply (arbL_E fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i _ _ _ Q HA);
    [arb_cmn_tac HC HJ Q2 Q3 Q4 Q8 Q9 Q18 Q25 E2 E3 E4 E8 E9 E18 E25 E32 C25 | | exact Ht0 | exact Hi
    | arb_E_regs Q20 Q21 Q22 Q23 Q24 Q26 Q27 E20 E21 E22 E23 E24 E26 E27 R20 R21 R22 R23 R24 R26 R27 SH24 | exact KL | exact KP].
    rewrite Q19, E19, H19. rewrite reac_arbitrate.scanz_succ by lia. rewrite <- Hb.
    unfold reac_arbitrate.stp. rewrite Hcand, (proj2 (Z.ltb_ge _ _) Hc). reflexivity.
  + rewrite branch_geu_U, (U_atom E 33 _ E33), (U_atom E 11 _ E11v) in Hc by lia.
    apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 31920; [awr_ok_tac |].
    pmkst HS. arb_views. arb_prregs HS Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
    eapply (arbL_E fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i _ _ _ Q HA);
    [arb_cmn_tac HC HJ Q2 Q3 Q4 Q8 Q9 Q18 Q25 E2 E3 E4 E8 E9 E18 E25 E32 C25 | | exact Ht0 | exact Hi
    | arb_E_regs Q20 Q21 Q22 Q23 Q24 Q26 Q27 E20 E21 E22 E23 E24 E26 E27 R20 R21 R22 R23 R24 R26 R27 SH24 | exact KL | exact KP].
    rewrite Q19, E22v. rewrite reac_arbitrate.scanz_succ by lia. rewrite <- Hb.
    unfold reac_arbitrate.stp. rewrite Hcand, (proj2 (Z.ltb_lt _ _) Hc). reflexivity.
- remember (Eimg (Ereg regs5 [Z_to_bv 64 SB])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs5 r).
  { intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. }
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 0)).
  arb_Efacts E EL regs5.
  assert (E22v : ew E 22 = Z_to_bv 64 (t + 48 * i)) by (rewrite E22; exact R22).
  pose proof (proj1 (arb_denot_shx E 22 (t + 48 * i) 8 E32 E22v ltac:(lia) ltac:(lia))) as SH24.
  cbn [sv_denot] in SH24. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in SH24.
  assert (HS : st_ok_pi (fx := fq) SEGS VAL E (mkSS 31884 (YP0l.sr_set sr_atoms (19%bv : bv 5) (SLit 0)) [] None (mkFacts [] [] []))
     (restrict (w_H W) (mkst (fx := fq) regs5 (Z_to_bv 64 (BASE + 31884)) mem5 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
    [ apply arb_regs_ok_set; [subst E; apply regs_ok_Eimg_Ereg | rewrite H19; reflexivity]
    | vm_compute; reflexivity | constructor | cbn; exact I | unfold facts_ok; cbn; tauto]. }
  assert (SHOK : sh_ok SEGS ARB_BX [] E (mrestrict (w_H W) mem5)) by constructor.
  clear HE.
  paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 31920; [awr_ok_tac |].
  pmkst HS. arb_views. arb_prregs HS Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
  eapply (arbL_E fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i _ _ _ Q HA);
  [arb_cmn_tac HC HJ Q2 Q3 Q4 Q8 Q9 Q18 Q25 E2 E3 E4 E8 E9 E18 E25 E32 C25 | | exact Ht0 | exact Hi
  | arb_E_regs Q20 Q21 Q22 Q23 Q24 Q26 Q27 E20 E21 E22 E23 E24 E26 E27 R20 R21 R22 R23 R24 R26 R27 SH24 | exact KL | exact KP].
  rewrite Q19, E22, R22. rewrite reac_arbitrate.scanz_succ by lia. rewrite <- Hb.
  unfold reac_arbitrate.stp. rewrite Hcand. reflexivity.
Qed.

Lemma arbL_C : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (i : Z) (b : option Z) (regs5 : bvmap 5 word) mem5 md5
    (Q : world SEGS -> config -> Prop),
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_cmn ly S W regs mem md our fsm pace out regs5 mem5 md5 ->
  getr regs5 19 = Z_to_bv 64 (reac_arbitrate.baddr t b) -> b = reac_arbitrate.scanz T P our now i ->
  t <> 0 -> 0 <= i < disco_table_c.n_of T -> arbL_regs regs5 t now T i ->
  disco_table_c.role_of_e T i = 2 ->
  ((our =? 0) || negb (reac_arbitrate_c.bytes_eqb (disco_table_c.mac_of T i) P)) = true ->
  (forall regs4 mem4 md4,
     arb_invL ly S W regs mem md t our fsm pace now out T P (i + 1) (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + AF_ARB_L)) mem4 (seg_rom SEGS)) md4) Q) ->
  (forall regs4 mem4 md4,
     arb_invP ly S W regs mem md t our fsm pace now out T P (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + AF_ARB_P)) mem4 (seg_rom SEGS)) md4) Q) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs5 (Z_to_bv 64 (BASE + 31852)) mem5 (seg_rom SEGS)) md5) Q.
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b regs5 mem5 md5 Q HA HC H19 Hb Ht0 Hi HR Hrole Hmac KL KP.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
arb_pre_facts HA HC Ht0.
pose proof HR as (R20 & R21 & R22 & R23 & R24 & R26 & R27).
pose proof (arb_garr8_T ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs5 mem5 md5 HA HC Ht0) as GT5.
assert (VI : val_mem SEGS (mrestrict (w_H W) mem5) (t + 48 * i + 40) 8 (disco_table_c.last_of T i)).
{ unfold disco_table_c.last_of, disco_table_c.u_at. replace (t + 48 * i + 40) with (t + (48 * i + 40)) by lia.
  apply val_mem_garr8_sub; [exact GT5 | lia | rewrite LT; lia]. }
pose proof (reac_arbitrate.u_range T (48 * i + 40) 8 ltac:(lia) ltac:(rewrite LT; lia)) as RI.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RI. change (disco_table_c.u_at T (48 * i + 40) 8) with (disco_table_c.last_of T i) in RI.
remember (Eimg (Ereg regs5 [Z_to_bv 64 SB; Z_to_bv 64 (disco_table_c.last_of T i)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs5 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (disco_table_c.last_of T i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 1)).
arb_Efacts E EL regs5.
assert (E22v : ew E 22 = Z_to_bv 64 (t + 48 * i)) by (rewrite E22; exact R22).
assert (E21v : ew E 21 = Z_to_bv 64 now) by (rewrite E21; exact R21).
pose proof (proj1 (arb_denot_shx E 22 (t + 48 * i) 8 E32 E22v ltac:(lia) ltac:(lia))) as SH24.
cbn [sv_denot] in SH24. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in SH24.
assert (HS : st_ok_pi (fx := fq) SEGS VAL E
   (mkSS 31852 (YP0l.sr_set (YP0l.sr_set (YP0l.sr_set sr_atoms (25%bv : bv 5) (SOff 32 0)) (23%bv : bv 5) (SOff 22 40))
                  (20%bv : bv 5) (SLit 5000000000))
      [YP09.mkRegion (Some 22%nat) 0 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 33 0))]] None
      (mkFacts [(22%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF SB SB 0)] [] []))
   (restrict (w_H W) (mkst (fx := fq) regs5 (Z_to_bv 64 (BASE + 31852)) mem5 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply arb_regs_ok_set; [apply arb_regs_ok_set; [apply arb_regs_ok_set; [subst E; apply regs_ok_Eimg_Ereg|]|]|].
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. exact C25.
    + cbn [sv_denot]. rewrite E22v, unsigned_lit_small by lia. rewrite R23. reflexivity.
    + rewrite R20. reflexivity.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E22v, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (t + 48 * i) 40 8 (SOff 33 0) (disco_table_c.last_of T i));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VI].
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22v, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. pose proof (arb_mod8 t i Ht8).
    unfold SB. repeat match goal with |- _ /\ _ => split end; first [lia | exact I]. }
assert (SHOK : sh_ok SEGS ARB_BX [mkSHE 22 0 48] E (mrestrict (w_H W) mem5)).
{ constructor; [|constructor].
  apply (arb_shent ly S W mem5 md5 E 22 bt Nt (t + 48 * i) 0 48 (proj1 HJ) Hbt);
  [apply arb_U_BX; exact E32 | apply arb_U_atom; [exact E22v | lia] | lia | lia | lia]. }
clear HE.
assert (Hr2 : (disco_table_c.role_of_e T i =? 2) = true) by (apply Z.eqb_eq; exact Hrole).
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [awr_ok_tac |].
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
- rewrite branch_geu_U, (U_atom E 33 _ E33), (U_atom E 21 _ E21v) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 31884; [awr_ok_tac |].
  pmkst HS. arb_views. arb_prregs HS Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
  prreg HS (11%bv : bv 5) Q11.
  eapply (arbL_D fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b _ _ _ Q HA);
  [arb_cmn_tac HC HJ Q2 Q3 Q4 Q8 Q9 Q18 Q25 E2 E3 E4 E8 E9 E18 E25 E32 C25 | rewrite Q19, E19; exact H19
  | exact Hb | exact Ht0 | exact Hi
  | arb_E_regs Q20 Q21 Q22 Q23 Q24 Q26 Q27 E20 E21 E22 E23 E24 E26 E27 R20 R21 R22 R23 R24 R26 R27 SH24
  | rewrite Q11; exact E33 | | exact KL | exact KP].
  unfold reac_arbitrate_c.cand, reac_arbitrate_c.stale. rewrite Hr2, Hmac, (proj2 (Z.ltb_ge _ _) Hc). reflexivity.
- rewrite branch_geu_U, (U_atom E 33 _ E33), (U_atom E 21 _ E21v) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_tok RUN HS HJ SHOK ARB_SPAN; [awr_ok_tac |].
  psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
  + rewrite branch_ltu_U, U_SLit, (arb_U_sub E 21 33 now (disco_table_c.last_of T i) E21v E33) in Hc0 by lia.
    rewrite (zcanon_id 5000000000) in Hc0 by (unfold M64; lia).
    assert (Hcf : reac_arbitrate_c.cand T P our now i = false).
    { unfold reac_arbitrate_c.cand, reac_arbitrate_c.stale. change reac_arbitrate_c.REAC_DISCO_STALE_NS with 5000000000.
      rewrite Hr2, Hmac, (proj2 (Z.ltb_lt _ _) Hc), Hc0. reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 31920; [awr_ok_tac |].
    pmkst HS. arb_views. arb_prregs HS Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
    eapply (arbL_E fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i _ _ _ Q HA);
    [arb_cmn_tac HC HJ Q2 Q3 Q4 Q8 Q9 Q18 Q25 E2 E3 E4 E8 E9 E18 E25 E32 C25 | | exact Ht0 | exact Hi
    | arb_E_regs Q20 Q21 Q22 Q23 Q24 Q26 Q27 E20 E21 E22 E23 E24 E26 E27 R20 R21 R22 R23 R24 R26 R27 SH24 | exact KL | exact KP].
    rewrite Q19, E19, H19. rewrite reac_arbitrate.scanz_succ by lia. rewrite <- Hb.
    unfold reac_arbitrate.stp. rewrite Hcf. reflexivity.
  + rewrite branch_ltu_U, U_SLit, (arb_U_sub E 21 33 now (disco_table_c.last_of T i) E21v E33) in Hc0 by lia.
    rewrite (zcanon_id 5000000000) in Hc0 by (unfold M64; lia).
    paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 31884; [awr_ok_tac |].
    pmkst HS. arb_views. arb_prregs HS Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
    prreg HS (11%bv : bv 5) Q11.
    eapply (arbL_D fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b _ _ _ Q HA);
    [arb_cmn_tac HC HJ Q2 Q3 Q4 Q8 Q9 Q18 Q25 E2 E3 E4 E8 E9 E18 E25 E32 C25 | rewrite Q19, E19; exact H19
    | exact Hb | exact Ht0 | exact Hi
    | arb_E_regs Q20 Q21 Q22 Q23 Q24 Q26 Q27 E20 E21 E22 E23 E24 E26 E27 R20 R21 R22 R23 R24 R26 R27 SH24
    | rewrite Q11; exact E33 | | exact KL | exact KP].
    unfold reac_arbitrate_c.cand, reac_arbitrate_c.stale. change reac_arbitrate_c.REAC_DISCO_STALE_NS with 5000000000.
    rewrite Hr2, Hmac, (proj2 (Z.ltb_lt _ _) Hc), Hc0. reflexivity.
Qed.

Lemma arb_role_u : forall T i, disco_table_c.role_of_e T i = 0 \/ disco_table_c.role_of_e T i = 1 \/ disco_table_c.role_of_e T i = 2 ->
  length T = 400%nat -> 0 <= i -> 48 * i + 12 <= 400 ->
  disco_table_c.u_at T (48 * i + 8) 4 = disco_table_c.role_of_e T i.
Proof.
intros T i Hr LT Hi0 Hi.
pose proof (reac_arbitrate.u_range T (48 * i + 8) 4 ltac:(lia) ltac:(rewrite LT; lia)) as RU.
change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in RU.
unfold disco_table_c.role_of_e, disco_table_c.s32_at in *.
set (u := disco_table_c.u_at T (48 * i + 8) 4) in *.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 32) with 4294967296 in *.
change (4294967296 / 2) with 2147483648 in *.
destruct (Z_lt_le_dec u 2147483648) as [Hs|Hs].
- rewrite Z.mod_small by lia. lia.
- exfalso. replace (u + 2147483648) with ((u - 2147483648) + 1 * 4294967296) in Hr by lia.
  rewrite Z_mod_plus_full, Z.mod_small in Hr by lia. lia.
Qed.

Lemma arbL_A : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (i : Z) (b : option Z) (regs5 : bvmap 5 word) mem5 md5
    (Q : world SEGS -> config -> Prop),
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_cmn ly S W regs mem md our fsm pace out regs5 mem5 md5 ->
  getr regs5 19 = Z_to_bv 64 (reac_arbitrate.baddr t b) -> b = reac_arbitrate.scanz T P our now i ->
  t <> 0 -> 0 <= i < disco_table_c.n_of T -> arbL_regs regs5 t now T i ->
  (forall regs4 mem4 md4,
     arb_invL ly S W regs mem md t our fsm pace now out T P (i + 1) (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + AF_ARB_L)) mem4 (seg_rom SEGS)) md4) Q) ->
  (forall regs4 mem4 md4,
     arb_invP ly S W regs mem md t our fsm pace now out T P (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4 ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + AF_ARB_P)) mem4 (seg_rom SEGS)) md4) Q) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs5 (Z_to_bv 64 (BASE + 31812)) mem5 (seg_rom SEGS)) md5) Q.
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b regs5 mem5 md5 Q HA HC H19 Hb Ht0 Hi HR KL KP.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
arb_pre_facts HA HC Ht0.
pose proof HR as (R20 & R21 & R22 & R23 & R24 & R26 & R27).
pose proof (arb_garr8_T ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs5 mem5 md5 HA HC Ht0) as GT5.
pose proof (TR i ltac:(lia)) as Hr3.
assert (Hru : disco_table_c.u_at T (48 * i + 8) 4 = disco_table_c.role_of_e T i)
  by (apply arb_role_u; [exact Hr3 | exact LT | lia | lia]).
assert (VR : val_mem SEGS (mrestrict (w_H W) mem5) (t + 48 * i + 8) 4 (disco_table_c.role_of_e T i)).
{ rewrite <- Hru. unfold disco_table_c.u_at. replace (t + 48 * i + 8) with (t + (48 * i + 8)) by lia.
  apply val_mem_garr8_sub; [exact GT5 | lia | rewrite LT; lia]. }
remember (Eimg (Ereg regs5 [Z_to_bv 64 SB; Z_to_bv 64 (disco_table_c.role_of_e T i)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs5 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (disco_table_c.role_of_e T i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 1)).
arb_Efacts E EL regs5.
assert (E22v : ew E 22 = Z_to_bv 64 (t + 48 * i)) by (rewrite E22; exact R22).
assert (E24v : ew E 24 = Z_to_bv 64 (SB + (t + 48 * i + 8) / 8)) by (rewrite E24; exact R24).
pose proof (proj1 (arb_denot_shx E 22 (t + 48 * i) 8 E32 E22v ltac:(lia) ltac:(lia))) as SH24.
cbn [sv_denot] in SH24. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in SH24.
assert (HS : st_ok_pi (fx := fq) SEGS VAL E
   (mkSS 31812 (YP0l.sr_set (YP0l.sr_set (YP0l.sr_set (YP0l.sr_set sr_atoms (25%bv : bv 5) (SOff 32 0))
                  (23%bv : bv 5) (SOff 22 40)) (20%bv : bv 5) (SLit 5000000000))
                  (24%bv : bv 5) (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 22 8) (SLit 3))))
      [YP09.mkRegion (Some 22%nat) 0 48 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 33 0))]] None
      (mkFacts [(22%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF SB SB 0); (26%nat, mkAF 1 8 0)] [] []))
   (restrict (w_H W) (mkst (fx := fq) regs5 (Z_to_bv 64 (BASE + 31812)) mem5 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply arb_regs_ok_set; [apply arb_regs_ok_set; [apply arb_regs_ok_set; [apply arb_regs_ok_set; [subst E; apply regs_ok_Eimg_Ereg|]|]|]|].
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. exact C25.
    + cbn [sv_denot]. rewrite E22v, unsigned_lit_small by lia. rewrite R23. reflexivity.
    + rewrite R20. reflexivity.
    + cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. rewrite SH24. symmetry. exact R24.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E22v, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (t + 48 * i) 8 4 (SOff 33 0) (disco_table_c.role_of_e T i));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VR].
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22v, E32, E26, R26, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. pose proof (arb_mod8 t i Ht8).
    unfold SB. repeat match goal with |- _ /\ _ => split end; first [lia | exact I]. }
assert (SHOK : sh_ok SEGS ARB_BX [mkSHE 22 0 48] E (mrestrict (w_H W) mem5)).
{ constructor; [|constructor].
  apply (arb_shent ly S W mem5 md5 E 22 bt Nt (t + 48 * i) 0 48 (proj1 HJ) Hbt);
  [apply arb_U_BX; exact E32 | apply arb_U_atom; [exact E22v | lia] | lia | lia | lia]. }
clear HE.
assert (E9v : ew E 9 = Z_to_bv 64 our) by (rewrite E9; exact C9).
assert (E27v : ew E 27 = Z_to_bv 64 2) by (rewrite E27; exact R27).
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [awr_ok_tac |].
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
- rewrite branch_ne_U, U_SExt, (U_atom E 33 _ E33), (U_atom E 27 2 E27v) in Hc by lia.
  cbv iota in Hc. change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc.
  rewrite (arb_sx_small (disco_table_c.role_of_e T i)) in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 31920; [awr_ok_tac |].
  pmkst HS. arb_views. arb_prregs HS Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
  eapply (arbL_E fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i _ _ _ Q HA);
  [arb_cmn_tac HC HJ Q2 Q3 Q4 Q8 Q9 Q18 Q25 E2 E3 E4 E8 E9 E18 E25 E32 C25 | | exact Ht0 | exact Hi
  | arb_E_regs Q20 Q21 Q22 Q23 Q24 Q26 Q27 E20 E21 E22 E23 E24 E26 E27 R20 R21 R22 R23 R24 R26 R27 SH24 | exact KL | exact KP].
  rewrite Q19, E19, H19. rewrite reac_arbitrate.scanz_succ by lia. rewrite <- Hb.
  unfold reac_arbitrate.stp, reac_arbitrate_c.cand. rewrite (proj2 (Z.eqb_neq _ 2) Hc). reflexivity.
- rewrite branch_ne_U, U_SExt, (U_atom E 33 _ E33), (U_atom E 27 2 E27v) in Hc by lia.
  cbv iota in Hc. change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc.
  rewrite (arb_sx_small (disco_table_c.role_of_e T i)) in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK ARB_SPAN; [awr_ok_tac |].
  psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
  + rewrite branch_eq_U, arb_U0, (U_atom E 9 our E9v) in Hc0 by lia.
    apply Z.eqb_eq in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK ARB_SPAN 31852; [awr_ok_tac |].
    pmkst HS. arb_views. arb_prregs HS Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
    eapply (arbL_C fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b _ _ _ Q HA);
    [arb_cmn_tac HC HJ Q2 Q3 Q4 Q8 Q9 Q18 Q25 E2 E3 E4 E8 E9 E18 E25 E32 C25 | rewrite Q19, E19; exact H19
    | exact Hb | exact Ht0 | exact Hi
    | arb_E_regs Q20 Q21 Q22 Q23 Q24 Q26 Q27 E20 E21 E22 E23 E24 E26 E27 R20 R21 R22 R23 R24 R26 R27 SH24
    | exact Hc | rewrite Hc0; reflexivity | exact KL | exact KP].
  + rewrite branch_eq_U, arb_U0, (U_atom E 9 our E9v) in Hc0 by lia.
    apply Z.eqb_neq in Hc0.
    destruct (HP Hc0) as (Hbp & Hbp1 & Hbp2 & LP & GP & Hdisp).
    destruct (arb_blk ly S W mem md bp Np our 6 (proj1 HPRE) Hbp Hbp1 Hbp2) as (Bp1 & Bp2 & _).
    pose proof (arb_garr8_P ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs5 mem5 md5 HA HC Hc0) as GP5.
    paj_run_tok RUN HS HJ SHOK ARB_SPAN; [awr_ok_tac |].
    pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp & Htp & Hstk0 & Hpres0 & Hch0 & HQT0).
    assert (HES : ESTACK = 4096) by reflexivity.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ bt Nt (proj1 HJ) Hbt) as (_ & _ & _ & _ & HtP & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ bp Np (proj1 HJ) Hbp) as (_ & _ & _ & _ & HpP & _).
    prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
    prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
    lazymatch type of Qsp with getr ?rg _ = _ =>
      assert (HspU : spZ rg = spZ regs - 128) by (unfold spZ at 1; rewrite Qsp, E2, C2; apply unsigned_lit_small; lia) end.
    pmkst HS.
    eapply SRr_bind.
    { lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
      eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA DS___interceptor_trampoline_bcmp) (ABCMP fq) W (ms_regs msX) (ms_mem msX)
        REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S _ 0 (t + 48 * i) our 6 (-128) _ HJ) end.
      - rewrite Ra0, E22v. reflexivity.
      - rewrite Ra1, E9v. reflexivity.
      - rewrite Ra2. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - rewrite HspU. lia.
      - reflexivity.
      - lia.
      - rewrite WS, HES. lia.
      - rewrite Qgp, E3, C3. exact Hgp.
      - rewrite Qtp, E4, C4. exact Htp.
      - exact Rra.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HtP a ltac:(lia))) | rewrite HspU, HES; lia].
      - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HpP a ltac:(lia))) | rewrite HspU, HES; lia].
      - intros a Ha. rewrite HES. lia.
      - intros a Ha. rewrite HES. lia.
      - apply (amem_range_of_block SEGS B LAWS ly S W _ _ bt Nt (t + 48 * i) 6 (proj1 HJ) Hbt); lia.
      - apply (amem_range_of_block SEGS B LAWS ly S W _ _ bp Np our 6 (proj1 HJ) Hbp); lia.
      - apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bt Nt (t + 48 * i) 6 (proj1 HJ) Hbt); lia.
      - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bt Nt (t + 48 * i) 6 (proj1 HJ) Hbt); lia.
      - apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bp Np our 6 (proj1 HJ) Hbp); lia.
      - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bp Np our 6 (proj1 HJ) Hbp); lia. }
    cbv beta. clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp.
    intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2).
    assert (LM : length (disco_table_c.mac_of T i) = 6%nat).
    { unfold disco_table_c.mac_of, disco_table_c.sub. rewrite firstn_length_le; [reflexivity|].
      rewrite length_skipn. lia. }
    assert (GTmac5 : garr8 SEGS (mrestrict (w_H W) mem5) (t + 48 * i) (map (fun b : byte => bv_unsigned b) (disco_table_c.mac_of T i))).
    { unfold disco_table_c.mac_of. apply (arb_garr8_sub6 (mrestrict (w_H W) mem5) t T (48 * i) GT5); [lia | rewrite LT; lia]. }
    arb_views.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
      assert (VM : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) mem5 a)
        by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; arb_vlist a Ha; reflexivity) end.
    assert (HMACv : v = w64 0 <-> disco_table_c.mac_of T i = P).
    { rewrite Hcmp. apply arb_mac_eq.
      - apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem5); [|exact GTmac5].
        rewrite length_map, LM. intros a Ha. apply VM. lia.
      - apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem5); [|exact GP5].
        rewrite length_map, LP. intros a Ha. apply VM. lia.
      - exact LM.
      - exact LP. }
    jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 ([] : list nat) HS2.
    match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. apply Forall_nil. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ea := Ev) in HS end.
    assert (HEIb : img_env VAL A_LIM Ea) by (subst Ea; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
    assert (OLDb : forall n, (n < 512)%nat -> ew Ea n = ew E n) by (intros n Hn; subst Ea; rewrite YN3v.ew_havoc_old by lia; reflexivity).
    clearbody Ea.
    assert (SHOK2 : sh_ok SEGS ARB_BX [] Ea (mrestrict (w_H W) mem2)) by constructor.
    clear SHOK HEI. rename HEIb into HEI.
    assert (A2 : ew Ea 2 = getr regs5 2) by (rewrite OLDb by lia; exact E2).
    assert (A3 : ew Ea 3 = getr regs5 3) by (rewrite OLDb by lia; exact E3).
    assert (A4 : ew Ea 4 = getr regs5 4) by (rewrite OLDb by lia; exact E4).
    assert (A8 : ew Ea 8 = getr regs5 8) by (rewrite OLDb by lia; exact E8).
    assert (A9 : ew Ea 9 = getr regs5 9) by (rewrite OLDb by lia; exact E9).
    assert (A18 : ew Ea 18 = getr regs5 18) by (rewrite OLDb by lia; exact E18).
    assert (A19 : ew Ea 19 = getr regs5 19) by (rewrite OLDb by lia; exact E19).
    assert (A20 : ew Ea 20 = getr regs5 20) by (rewrite OLDb by lia; exact E20).
    assert (A21 : ew Ea 21 = getr regs5 21) by (rewrite OLDb by lia; exact E21).
    assert (A22 : ew Ea 22 = getr regs5 22) by (rewrite OLDb by lia; exact E22).
    assert (A23 : ew Ea 23 = getr regs5 23) by (rewrite OLDb by lia; exact E23).
    assert (A24 : ew Ea 24 = getr regs5 24) by (rewrite OLDb by lia; exact E24).
    assert (A25 : ew Ea 25 = getr regs5 25) by (rewrite OLDb by lia; exact E25).
    assert (A26 : ew Ea 26 = getr regs5 26) by (rewrite OLDb by lia; exact E26).
    assert (A27 : ew Ea 27 = getr regs5 27) by (rewrite OLDb by lia; exact E27).
    assert (A32 : ew Ea 32 = Z_to_bv 64 SB) by (rewrite OLDb by lia; exact E32).
    assert (A22v : ew Ea 22 = Z_to_bv 64 (t + 48 * i)) by (rewrite A22; exact R22).
    pose proof (proj1 (arb_denot_shx Ea 22 (t + 48 * i) 8 A32 A22v ltac:(lia) ltac:(lia))) as ASH24.
    cbn [sv_denot] in ASH24. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in ASH24.
    prreg HS (10%bv : bv 5) Rv.
    assert (E516 : ew Ea 516 = Z_to_bv 64 (bv_unsigned v)).
    { rewrite <- Rv, Hv. symmetry. apply Z_to_bv_bv_unsigned. }
    pose proof (bv_unsigned_in_range 64 v) as RVB. change (bv_modulus 64) with (2 ^ 64) in RVB.
    assert (HV0 : v = w64 0 <-> bv_unsigned v = 0).
    { split; [intros ->; apply unsigned_lit_small; lia | intros HH; apply bv_eq; rewrite HH; symmetry; apply unsigned_lit_small; lia]. }
    psrr_branch_tok RUN BR HS SHOK2 ARB_SPAN.
    * rewrite branch_eq_U, arb_U0, (U_atom Ea 516 (bv_unsigned v) E516) in Hc1 by lia.
      apply Z.eqb_eq in Hc1.
      assert (HMq : disco_table_c.mac_of T i = P) by (apply HMACv, HV0; exact Hc1).
      assert (Hcf : reac_arbitrate_c.cand T P our now i = false).
      { unfold reac_arbitrate_c.cand. rewrite (proj2 (Z.eqb_neq our 0) Hc0).
        rewrite (proj2 (reac_arbitrate.bytes_eqb_true _ _) HMq). cbn [orb negb].
        rewrite andb_false_r, andb_false_l. reflexivity. }
      paj_run_to_tok RUNTO HS HJ2 SHOK2 ARB_SPAN 31920; [awr_ok_tac |].
      pmkst HS. arb_views. arb_prregs HS Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
      eapply (arbL_E fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i _ _ _ Q HA);
      [ eapply (arb_cmn_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC HJ2);
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha ?;
          arb_vlist a Ha; rewrite (Hfr2 a Ha ltac:(rewrite HES; lia)), (VM a Ha); reflexivity
        | lia | lia
        | rewrite Q2; exact A2 | rewrite Q3; exact A3 | rewrite Q4; exact A4 | rewrite Q8; exact A8
        | rewrite Q9; exact A9 | rewrite Q18; exact A18 | rewrite Q25; rewrite A32; symmetry; exact C25 ]
      | | exact Ht0 | exact Hi
      | arb_E_regs Q20 Q21 Q22 Q23 Q24 Q26 Q27 A20 A21 A22 A23 A24 A26 A27 R20 R21 R22 R23 R24 R26 R27 ASH24
      | exact KL | exact KP].
      rewrite Q19, A19, H19. rewrite reac_arbitrate.scanz_succ by lia. rewrite <- Hb.
      unfold reac_arbitrate.stp. rewrite Hcf. reflexivity.
    * rewrite branch_eq_U, arb_U0, (U_atom Ea 516 (bv_unsigned v) E516) in Hc1 by lia.
      apply Z.eqb_neq in Hc1.
      assert (HMq : disco_table_c.mac_of T i <> P).
      { intros HH. apply Hc1. apply HV0, HMACv. exact HH. }
      assert (Hmac : ((our =? 0) || negb (reac_arbitrate_c.bytes_eqb (disco_table_c.mac_of T i) P)) = true).
      { destruct (reac_arbitrate_c.bytes_eqb (disco_table_c.mac_of T i) P) eqn:HB2;
        [exfalso; apply HMq, (proj1 (reac_arbitrate.bytes_eqb_true _ _) HB2) | apply orb_true_r]. }
      paj_run_to_tok RUNTO HS HJ2 SHOK2 ARB_SPAN 31852; [awr_ok_tac |].
      pmkst HS. arb_views. arb_prregs HS Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
      eapply (arbL_C fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b _ _ _ Q HA);
      [ eapply (arb_cmn_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC HJ2);
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha ?;
          arb_vlist a Ha; rewrite (Hfr2 a Ha ltac:(rewrite HES; lia)), (VM a Ha); reflexivity
        | lia | lia
        | rewrite Q2; exact A2 | rewrite Q3; exact A3 | rewrite Q4; exact A4 | rewrite Q8; exact A8
        | rewrite Q9; exact A9 | rewrite Q18; exact A18 | rewrite Q25; rewrite A32; symmetry; exact C25 ]
      | rewrite Q19, A19; exact H19 | exact Hb | exact Ht0 | exact Hi
      | arb_E_regs Q20 Q21 Q22 Q23 Q24 Q26 Q27 A20 A21 A22 A23 A24 A26 A27 R20 R21 R22 R23 R24 R26 R27 ASH24
      | exact Hc | exact Hmac | exact KL | exact KP].
Qed.

Lemma arb_segL : ARB_SEGL.
Proof.
unfold ARB_SEGL.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b regs3 mem3 md3 Q HA HL KL KP.
destruct HL as (HC & H19 & Hb & Ht0 & Hi & R20 & R21 & R22 & R23 & R24 & R26 & R27).
change (BASE + AF_ARB_L) with (BASE + 31812).
exact (arbL_A fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b regs3 mem3 md3 Q
  HA HC H19 Hb Ht0 Hi (conj R20 (conj R21 (conj R22 (conj R23 (conj R24 (conj R26 R27)))))) KL KP).
Qed.

Ltac arbQ_awr HA Eout Hbo out :=
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
Ltac arbQ_env E0 HA HD :=
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
Lemma arbQ_nth_regs : forall r : bv 5, nth (Z.to_nat (bv_unsigned r)) all_regs 0%bv = r.
Proof.
apply (reg_cases_lit (fun r => nth (Z.to_nat (bv_unsigned r)) all_regs 0%bv = r)).
intros r Hr. cbv [all_regs In] in Hr. repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]). destruct Hr.
Qed.
Lemma arbQ_z4_ble : forall x, bytes_le_to_Z (reac_arbitrate_c.z4 x) = x mod 2 ^ 32.
Proof.
intros x. change (reac_arbitrate_c.z4 x) with (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 x))).
rewrite bytes_le_Z_to_le by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 x)); lia).
change (8 * Z.of_nat 4) with 32. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 32 * 2 ^ 32).
rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.
Lemma arbQ_fsm_cond : forall E fsm, ew E 12 = Z_to_bv 64 fsm -> - 2 ^ 31 <= fsm < 2 ^ 31 ->
  (U E (SAlu ALU_AND (SOff 12 0) (SLit (-2))) =? U E (SLit 2)) = (fsm =? 2) || (fsm =? 3).
Proof.
intros E fsm H Hf. rewrite U_SAlu, U_SOff, !U_SLit, H, Z.add_0_r. cbn [zalu_raw].
assert (Hu : zcanon (bv_unsigned (Z_to_bv 64 fsm)) = if fsm <? 0 then fsm + 2 ^ 64 else fsm).
{ rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. destruct (Z.ltb_spec fsm 0).
  - rewrite <- (Z_mod_plus_full fsm 1 (2 ^ 64)). apply Z.mod_small. lia.
  - apply Z.mod_small. lia. }
rewrite Hu. change (zcanon (-2)) with 18446744073709551614. change (zcanon 2) with 2.
assert (Ey : forall y, y = (if fsm <? 0 then fsm + 2 ^ 64 else fsm) ->
  0 <= y < 2 ^ 64 /\ ((y =? 2) || (y =? 3)) = ((fsm =? 2) || (fsm =? 3))).
{ intros y ->. destruct (Z.ltb_spec fsm 0); (split; [lia|]);
  destruct (Z.eqb_spec fsm 2); destruct (Z.eqb_spec fsm 3); destruct (Z.eqb_spec (fsm + 2 ^ 64) 2);
  destruct (Z.eqb_spec (fsm + 2 ^ 64) 3); cbn [orb]; first [reflexivity | exfalso; lia]. }
destruct (Ey _ eq_refl) as [Ry Eyy]. revert Ry Eyy. generalize (if fsm <? 0 then fsm + 2 ^ 64 else fsm). intros y Ry Eyy.
rewrite reac_arbitrate.land_m2 by exact Ry.
unfold zcanon, M64. pose proof (Z.div_mod y 2 ltac:(lia)) as D. pose proof (Z.mod_pos_bound y 2 ltac:(lia)) as M.
rewrite (Z.mod_small (2 * (y / 2))) by lia.
rewrite <- Eyy. destruct (Z.eqb_spec (2 * (y / 2)) 2); destruct (Z.eqb_spec y 2); destruct (Z.eqb_spec y 3); cbn [orb];
first [reflexivity | exfalso; lia].
Qed.
Lemma arbQ_u64_mod32 : forall v, bv_unsigned (Z_to_bv 64 v) mod 2 ^ 32 = v mod 2 ^ 32.
Proof.
intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 32 * 2 ^ 32).
rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.
Definition arbQ_X (regs3 : bvmap 5 word) (pace t : Z) (T : list byte) (b : option Z) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 (pace mod 2 ^ 32); Z_to_bv 64 (reac_arbitrate.baddr t b);
   Z_to_bv 64 (match b with Some j => reac_arbitrate_c.ch_of T j | None => 0 end)] ++ map (getr regs3) all_regs.
Definition EQ (regs regs3 : bvmap 5 word) (pace t : Z) (T : list byte) (b : option Z) : env :=
  Eimg (Ereg regs (arbQ_X regs3 pace t T b)).
Definition arbQ_sr (s3v : sv) : list sv :=
  [SLit 0; SOff 37 0; SOff 2 (-128); SOff 3 0; SOff 4 0; SOff 41 0; SOff 42 0; SOff 43 0;
   SOff 15 0; SOff 11 0; SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0; SOff 51 0;
   SOff 52 0; SOff 53 0; SOff 12 0; s3v; SOff 56 0; SOff 57 0; SOff 58 0; SOff 59 0;
   SOff 60 0; SOff 32 0; SOff 62 0; SOff 63 0; SOff 64 0; SOff 65 0; SOff 66 0; SOff 67 0].
Definition arbQ_s3 (b : option Z) : sv := match b with None => SLit 0 | Some _ => SOff 34 0 end.
Definition arbQ_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-128) 0 0 0 ARB_STKA.
Definition arbQ_o0 : YP09.region := YP09.mkRegion (Some 15%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SLit 0))].
Definition arbQ_o12 : YP09.region := YP09.mkRegion (Some 15%nat) 12 32 12 32
  [YP09.mkChunk 12 (CVal 4 (SLit 0)); YP09.mkChunk 16 (CVal 4 (SOff 33 0)); YP09.mkChunk 20 (CVal 4 (SLit 0));
   YP09.mkChunk 24 (CVal 4 (SLit 0)); YP09.mkChunk 28 (CVal 4 (SLit 0))].
Definition arbQ_bst : YP09.region := YP09.mkRegion (Some 34%nat) 0 48 0 0 [YP09.mkChunk 20 (CVal 4 (SOff 35 0))].
Definition arbQ_regions (b : option Z) : smem :=
  match b with None => [arbQ_stk; arbQ_o0; arbQ_o12] | Some _ => [arbQ_stk; arbQ_o0; arbQ_o12; arbQ_bst] end.
Definition arbQ_facts (b : option Z) : facts :=
  match b with
  | None => mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (15%nat, mkAF 4096 140737479966720 2); (32%nat, mkAF SB SB 0)] [] []
  | Some _ => mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (15%nat, mkAF 4096 140737479966720 2); (32%nat, mkAF SB SB 0);
                       (34%nat, mkAF 4096 140737479966720 3)] [] []
  end.
Definition ss_arbQ (b : option Z) : sstate := mkSS 31968 (arbQ_sr (arbQ_s3 b)) (arbQ_regions b) None (arbQ_facts b).
Definition arbQ_SH (b : option Z) : list shent :=
  match b with None => [mkSHE 15 0 32] | Some _ => [mkSHE 15 0 32; mkSHE 34 0 48] end.

Lemma arbQ_ew_ext : forall regs regs3 pace t T b (r : bv 5),
  ew (EQ regs regs3 pace t T b) (36 + Z.to_nat (bv_unsigned r)) = getr regs3 r.
Proof.
intros regs regs3 pace t T b r. pose proof (u5_range r) as Hr. unfold EQ. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (36 + Z.to_nat (bv_unsigned r))%nat with (32 + (4 + Z.to_nat (bv_unsigned r)))%nat by lia.
rewrite ew_Ereg_extra. unfold arbQ_X. rewrite app_nth2 by (cbn [length]; lia). cbn [length].
replace (4 + Z.to_nat (bv_unsigned r) - 4)%nat with (Z.to_nat (bv_unsigned r)) by lia.
rewrite (nth_indep _ _ (getr regs3 0%bv)) by (rewrite length_map; cbn [length all_regs]; lia).
rewrite map_nth, arbQ_nth_regs. reflexivity.
Qed.

Lemma arbQ_regs_ok : forall (regs regs3 : bvmap 5 word) pace t T b out our fsm,
  getr regs 15 = w64 out -> getr regs 11 = w64 our -> getr regs 12 = w64 fsm ->
  getr regs3 2 = Z_to_bv 64 (spZ regs - 128) -> getr regs3 3 = getr regs 3 -> getr regs3 4 = getr regs 4 ->
  getr regs3 8 = Z_to_bv 64 out -> getr regs3 9 = Z_to_bv 64 our -> getr regs3 18 = Z_to_bv 64 fsm ->
  getr regs3 19 = Z_to_bv 64 (reac_arbitrate.baddr t b) -> getr regs3 25 = Z_to_bv 64 SB ->
  regs_ok (EQ regs regs3 pace t T b) (arbQ_sr (arbQ_s3 b)) regs3.
Proof.
intros regs regs3 pace t T b out our fsm H15 H11 H12 R2 R3 R4 R8 R9 R18 R19 R25.
set (E := EQ regs regs3 pace t T b).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbQ_X regs3 pace t T b)) n)
  by (intros n Hn; subst E; unfold EQ; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E11 : ew E 11 = Z_to_bv 64 our) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 fsm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (reac_arbitrate.baddr t b)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EX : forall r : bv 5, ew E (36 + Z.to_nat (bv_unsigned r)) = getr regs3 r) by (intros r; exact (arbQ_ew_ext regs regs3 pace t T b r)).
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
    | first [ rewrite R3, E3 | rewrite R4, E4 | rewrite R8, E15 | rewrite R9, E11 | rewrite R18, E12 | rewrite R25, E32
            | rewrite R19, E34 ];
      rewrite Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity ]
  | ]); try (exfalso; exact Hz)).
Qed.

Lemma arbQ_stk_chunks : forall E m (regs : bvmap 5 word) out,
  (forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n))) ->
  ew E 32 = Z_to_bv 64 SB -> ew E 15 = Z_to_bv 64 out -> 0 <= out < 2 ^ 47 - 16 ->
  arb_frame m regs out -> Forall (YP09.chunk_ok SEGS E m (spZ regs)) ARB_STKA.
Proof.
intros E m regs out AG H32 H15 Rout (HS & H16 & H8).
apply Forall_forall. intros c Hc. cbn [ARB_STKA In] in Hc.
repeat (destruct Hc as [<-|Hc];
  [ first
    [ lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?od (CVal 8 (SOff ?n 0))) =>
        let p := eval vm_compute in (od + 128, Z.of_nat n) in
        let Hp := fresh "Hp" in
        pose proof (HS p ltac:(cbn [ARB_SAVES In]; repeat (first [left; reflexivity | right]))) as Hp;
        cbn [fst snd] in Hp;
        pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat n)))) as Rg; unfold bv_modulus in Rg;
        apply (chunk_ok_val SEGS E m (spZ regs) od 8 (SOff n 0) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat n)))));
        [ cbn [sv_denot]; rewrite AG by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; change (Z.of_N 64) with 64 in Rg; revert Rg; generalize (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat n)))); intros; lia | cbn; lia
        | change (N.to_nat 8) with 8%nat; replace (spZ regs + od) with (spZ regs - 128 + (od + 128)) by lia; exact Hp ]
      end
    | apply (chunk_ok_val SEGS E m (spZ regs) (-112) 8 _ (SB + (out + 16) / 8));
      [ exact (proj2 (arb_denot_shx E 15 out 16 H32 H15 ltac:(lia) ltac:(lia)))
      | unfold SB; split; [|apply Z.lt_le_trans with (2147450880 + 2 ^ 44); [apply Z.add_lt_mono_l, Z.div_lt_upper_bound|]]; cbn; lia
      | cbn; lia
      | change (N.to_nat 8) with 8%nat; replace (spZ regs + -112) with (spZ regs - 128 + 16) by lia; exact H16 ]
    | apply (chunk_ok_val SEGS E m (spZ regs) (-120) 8 _ (out + 16));
      [ cbn [sv_denot]; rewrite H15, unsigned_lit_small by lia; reflexivity
      | cbn; lia | cbn; lia
      | change (N.to_nat 8) with 8%nat; replace (spZ regs + -120) with (spZ regs - 128 + 8) by lia; exact H8 ] ]
  | ]).
destruct Hc.
Qed.

Definition arbQ_kept (W : world SEGS) (m0 m : word -> option byte) (Zx : Z -> Prop) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ Zx a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m0 a.

Lemma arbQ_kept_refl : forall W m Zx, arbQ_kept W m m Zx.
Proof. intros W m Zx a _ _. reflexivity. Qed.

Lemma arbQ_kept_step : forall W m0 m m' (Zx Zy Zz : Z -> Prop),
  arbQ_kept W m0 m Zx -> (forall a, 0 <= a < 2 ^ 64 -> ~ Zy a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, Zx a -> Zz a) -> (forall a, Zy a -> Zz a) -> arbQ_kept W m0 m' Zz.
Proof.
intros W m0 m m' Zx Zy Zz K St Hx Hy a Ha Hz.
rewrite St by (try exact Ha; intro Q; apply Hz; apply Hy; exact Q).
apply K; [exact Ha | intro Q; apply Hz; apply Hx; exact Q].
Qed.

Lemma arbQ_kept_frame : forall W m0 m m' (Zx : Z -> Prop) E rs,
  arbQ_kept W m0 m Zx -> frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zx a) ->
  arbQ_kept W m0 m' Zx.
Proof.
intros W m0 m m' Zx E rs K HF Hw a Ha Hz.
rewrite (kept_of_frame (segs := SEGS) E rs (w_H W) m m' Zx HF Hw a Ha Hz). exact (K a Ha Hz).
Qed.

Lemma arbQ_garr8_copy : forall H m0 m s d l,
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

Lemma arbQ_chunk_val : forall (fq : YK11.FPState) E ss ms i r off (w : N) e,
  st_ok_pi (fx := fq) SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) -> (Z.of_N w <= 8) ->
  val_mem SEGS (ms_mem ms) (base_val E (YP09.r_base r) + off) (N.to_nat w) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros fq E ss ms i r off w e HS Hi Hc Hw.
pose proof (st_ok_region_nth (fx := fq) E (abs_ss VAL ss) ms i r HS Hi) as (_ & _ & _ & Hcs).
apply (val_mem_low_of_chunk SEGS E (ms_mem ms) _ off w e); [| exact Hw].
exact (proj1 (Forall_forall _ _) Hcs _ Hc).
Qed.

Lemma arbQ_out0_rest : forall m out pace, garr8 SEGS m out (arb_out0 pace) ->
  garr8 SEGS m (out + 4) (map (fun b : byte => bv_unsigned b) reac_arbitrate_c.MAC0) /\ garr8 SEGS m (out + 10) [0; 0].
Proof.
intros m out pace HO.
assert (L : length (arb_out0 pace) = 32%nat) by (unfold arb_out0, reac_arbitrate_c.arb_bytes; rewrite length_map, !length_app; reflexivity).
split.
- pose proof (garr8_sub_x SEGS m out (arb_out0 pace) 4 6 HO ltac:(rewrite L; lia)) as G. exact G.
- pose proof (garr8_sub_x SEGS m out (arb_out0 pace) 10 2 HO ltac:(rewrite L; lia)) as G. exact G.
Qed.

Lemma arbQ_z4_chunk : forall m a V v, val_mem SEGS m a 4 (V mod 2 ^ 32) -> V mod 2 ^ 32 = v mod 2 ^ 32 ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)).
Proof.
intros m a V v H Hv. apply (arb_z4_garr8 m a v (V mod 2 ^ 32) H). rewrite Z.mod_mod by lia. rewrite Hv. symmetry. apply arbQ_u64_mod32.
Qed.
Lemma arbQ_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (b : option Z) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invP ly S W regs mem md t our fsm pace now out T P b regs3 mem3 md3 ->
  st_ok_pi (fx := fq) SEGS VAL (EQ regs regs3 pace t T b) (ss_arbQ b)
    (restrict (w_H W) (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + 31968)) mem3 (seg_rom SEGS)))
  /\ sh_ok SEGS ARB_BX (arbQ_SH b) (EQ regs regs3 pace t T b) (mrestrict (w_H W) mem3).
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P b regs3 mem3 md3 HPRE HINV.
destruct HPRE as (HAF & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
destruct HINV as ((HJ & HK & HFR & HO & R2 & R3 & R4 & R8 & R9 & R18 & R25) & H19 & Hb).
pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity.
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
  rewrite arbQ_z4_ble in V. exact V. }
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
remember (EQ regs regs3 pace t T b) as E eqn:HE.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbQ_X regs3 pace t T b)) n)
  by (intros n Hn; subst E; unfold EQ; apply Eimg_low; exact Hn).
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
assert (HRS : regs_ok E (arbQ_sr (arbQ_s3 b)) regs3)
  by (subst E; exact (arbQ_regs_ok regs regs3 pace t T b out our fsm H15 H11 H12 R2 R3 R4 R8 R9 R18 H19 R25)).
assert (Rout47 : out + 32 <= 2 ^ 47 - 16) by lia.
assert (RK0 : region_ok SEGS E (mrestrict (w_H W) mem3) arbQ_stk).
{ unfold region_ok, arbQ_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  exact (arbQ_stk_chunks E _ regs out AG E32 E15 ltac:(lia) HFR). }
assert (RK1 : region_ok SEGS E (mrestrict (w_H W) mem3) arbQ_o0).
{ unfold region_ok, arbQ_o0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E15, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hopres (out + o) ltac:(lia)))|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ out 0 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V0]. }
assert (RK2 : region_ok SEGS E (mrestrict (w_H W) mem3) arbQ_o12).
{ unfold region_ok, arbQ_o12. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
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
- rewrite restrict_mkst_fx. unfold ss_arbQ. apply pa_entry_st_ok_full.
  + exact HRS.
  + destruct b; vm_compute; reflexivity.
  + destruct b as [j|]; cbn [arbQ_regions]; repeat apply Forall_cons; try apply Forall_nil; try assumption.
    destruct (BJ j eq_refl) as [Ht0 Rj]. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & (T1 & _) & Hdis).
    unfold disco_table_c.tbl_T1 in T1.
    destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & Ht4096 & Htceil & _).
    unfold region_ok, arbQ_bst. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
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
    destruct b as [j|]; cbn [arbQ_regions]; unfold arbQ_stk, arbQ_o0, arbQ_o12, arbQ_bst, extent_of_region;
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Usp, E15, unsigned_lit_small by lia;
    cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
    * destruct (BJ j eq_refl) as [Ht0 Rj]. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & (T1 & _) & Hdis).
      unfold disco_table_c.tbl_T1 in T1.
      destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & Ht4096 & Htceil & _).
      rewrite E34. cbn [reac_arbitrate.baddr]. rewrite unsigned_lit_small by lia.
      repeat split; lia.
    * repeat split; lia.
  + destruct b as [j|]; (split; [|split; [exact I | exact I]]); cbn [arbQ_facts f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
    rewrite Usp, E15, E32, !unsigned_lit_small by (unfold SB; lia);
    change (2 ^ 4) with 16; change (2 ^ 3) with 8; change (2 ^ 2) with 4; rewrite !Z.pow_0_r, !Z.mod_1_r.
    * destruct (BJ j eq_refl) as [Ht0 Rj]. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & (T1 & _) & Hdis).
      unfold disco_table_c.tbl_T1 in T1.
      destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & Ht4096 & Htceil & _).
      rewrite E34. cbn [reac_arbitrate.baddr]. rewrite unsigned_lit_small by lia.
      unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
      all: rewrite Z.add_mod by lia; rewrite Ht8; replace (48 * j) with ((6 * j) * 8) by lia; rewrite Z.mod_mul by lia; reflexivity.
    * unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
- destruct b as [j|]; unfold sh_ok, arbQ_SH; constructor;
  [apply (arb_shent ly S W mem3 md3 E 15 bo No out 0 32 HAR3 Hbo); [apply arb_U_BX; exact E32 | apply arb_U_atom; [exact E15 | lia] | lia | lia | lia] | | 
   apply (arb_shent ly S W mem3 md3 E 15 bo No out 0 32 HAR3 Hbo); [apply arb_U_BX; exact E32 | apply arb_U_atom; [exact E15 | lia] | lia | lia | lia] | constructor].
  destruct (BJ j eq_refl) as [Ht0 Rj]. destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & (T1 & _) & Hdis).
  unfold disco_table_c.tbl_T1 in T1.
  destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (_ & Ht4096 & Htceil & _).
  constructor; [|constructor].
  apply (arb_shent ly S W mem3 md3 E 34 bt Nt (t + 48 * j) 0 48 HAR3 Hbt);
  [apply arb_U_BX; exact E32 | apply arb_U_atom; [rewrite E34; reflexivity | lia] | lia | lia | lia].
Qed.

Lemma arbQ_ret : forall (fq0 fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (b : option Z) (regs3 : bvmap 5 word)
    Ec ss ms md' ly' S',
  arb_fprel fq0 fq ->
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  (forall n, (n < 240)%nat -> ew Ec n = ew (EQ regs regs3 pace t T b) n) -> ed Ec = ed (EQ regs regs3 pace t T b) ->
  st_ok_pi (fx := fq) SEGS VAL Ec ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  plookup pl_tpi (ss_pc ss) = Some (PW RET_WORD_r) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  sr_get (ss_regs ss) 1 = SOff 1 0 ->
  ajournal SEGS B REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly' S' W (ms_mem ms) md' 0 ->
  Permutation (ablocks B ly' S') (ablocks B ly S) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a) ->
  garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) out
    (map (fun b0 : byte => bv_unsigned b0) (reac_arbitrate_c.arb_model t our T P fsm pace now)) ->
  SRr SEGS W (mkCfg ms md') (treac_arbitrate_post fq0 regs ly S W mem md t our fsm pace now out T P).
Proof.
intros fq0 fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P b regs3 Ec ss ms md' ly' S'
  FPR HPRE HA HD HS Hrv Hpl Hcs Hr1 HJ HPerm HK Hout.
pose proof HPRE as ((HAR & Hra & _) & _).
assert (EL : forall n, (n < 32)%nat -> ew Ec n = ew (Ereg regs (arbQ_X regs3 pace t T b)) n)
  by (intros n Hn; rewrite HA by lia; unfold EQ; apply Eimg_low; unfold A_TEXT; lia).
assert (R1 : getr (ms_regs ms) 1 = getr regs 1).
{ rewrite (st_ok_pi_restrict_reg (fx := fq) (w_H W) Ec ss ms 1 HS), Hr1. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EL by lia. exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
eapply (paj_ret_at (fx := fq) (PI := PI) W Ec ss ms md' _ HS Hrv Hpl).
intros mat'. rewrite R1, Hra.
apply (arb_post_intro fq0 fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ly' S' (ms_regs ms) (ms_mem ms) _ FPR HPRE).
- apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
- apply (aregs_preserved_of_st_ok SEGS (w_H W) Ec (abs_ss VAL ss) ms regs (arbQ_X regs3 pace t T b) HS); [|exact Hcs].
  split; [intros n Hn; apply EL; exact Hn | rewrite HD; reflexivity].
- exact R1.
- exact HPerm.
- exact HK.
- exact Hout.
Qed.

Definition ARBQ_PA : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (b : option Z) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invP ly S W regs mem md t our fsm pace now out T P b regs3 mem3 md3 ->
  ((fsm =? 2) || (fsm =? 3)) = true ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_P)) mem3 (seg_rom SEGS)) md3)
    (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).

Definition ARBQ_PB : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (b : option Z) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invP ly S W regs mem md t our fsm pace now out T P b regs3 mem3 md3 ->
  ((fsm =? 2) || (fsm =? 3)) = false -> b <> None ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_P)) mem3 (seg_rom SEGS)) md3)
    (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).

Definition ARBQ_PC : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (b : option Z) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invP ly S W regs mem md t our fsm pace now out T P b regs3 mem3 md3 ->
  ((fsm =? 2) || (fsm =? 3)) = false -> b = None ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_P)) mem3 (seg_rom SEGS)) md3)
    (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).

Lemma arbQ_dispatch : ARBQ_PA -> ARBQ_PB -> ARBQ_PC -> ARB_SEGP.
Proof.
intros PA PB PC. unfold ARB_SEGP.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P b regs3 mem3 md3 HPRE HINV.
destruct ((fsm =? 2) || (fsm =? 3)) eqn:EST.
- exact (PA fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P b regs3 mem3 md3 HPRE HINV EST).
- destruct b as [j|].
  + exact (PB fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P (Some j) regs3 mem3 md3 HPRE HINV EST ltac:(discriminate)).
  + exact (PC fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P None regs3 mem3 md3 HPRE HINV EST eq_refl).
Qed.
Ltac arbQ_win HA E15 :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta;
      first [ lia
            | try (rewrite (HA 15%nat) in Hrr by lia); rewrite E15 in Hrr; rewrite unsigned_lit_small in Hrr by lia; lia ]
    | ]);
  destruct Hin.
Ltac arbQ_kstep K HA E15 :=
  lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m) (mrestrict _ ?m') |- _ =>
    lazymatch type of K with arbQ_kept ?W ?m0 _ ?Zx =>
      let K' := fresh "K" in
      assert (K' : arbQ_kept W m0 m' Zx);
      [ apply (arbQ_kept_frame W m0 m m' Zx Ef rs K HFr); arbQ_win HA E15 | clear K HFr; rename K' into K ] end end.
Ltac arbQ_zc HS HA E15 E33 out i off v G :=
  lazymatch type of HS with st_ok_pi ?sg _ ?Ex ?ss (restrict ?H ?msX) =>
  let r := eval vm_compute in (nth_error (ss_mem ss) i) in
  lazymatch r with Some ?rr =>
  let cs := eval vm_compute in (YP09.r_chunks rr) in
  let e := lazymatch cs with context [YP09.mkChunk off (CVal 4 ?e)] => e end in
  let V := fresh "V" in
  pose proof (arbQ_chunk_val _ Ex ss (restrict H msX) i rr off 4 e HS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
  cbn [YP09.r_base base_val ms_mem restrict] in V;
  rewrite (HA 15%nat) in V by lia; rewrite E15 in V; rewrite unsigned_lit_small in V by lia;
  change (N.to_nat 4) with 4%nat in V; change (8 * Z.of_N 4) with 32 in V;
  assert (G : garr8 sg (mrestrict H (ms_mem msX)) (out + off) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)));
  [ apply (arbQ_z4_chunk _ _ _ v V); cbn [sv_denot];
    first [ apply arbQ_u64_mod32
          | rewrite (HA 33%nat) by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned, arbQ_u64_mod32; apply Z.mod_mod; lia ]
  | clear V ]
  end end.

Lemma arbQ_pc : ARBQ_PC.
Proof.
unfold ARBQ_PC.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P b regs3 mem3 md3 HPRE HINV EST Hbn.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR. pose proof (paj_ret_at (fx := fq) (PI := PI)) as RET.
destruct (arbQ_entry fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P b regs3 mem3 md3 HPRE HINV) as [HS SHOK].
pose proof HINV as ((HJ & HK & HFR & HO & R2 & R3 & R4 & R8 & R9 & R18 & R25) & H19 & Hb).
pose proof HPRE as (HAF & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
subst b.
change (BASE + AF_ARB_P) with (BASE + 31968).
remember (EQ regs regs3 pace t T None) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EQ; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbQ_X regs3 pace t T None)) n)
  by (intros n Hn; subst E; unfold EQ; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E11 : ew E 11 = Z_to_bv 64 our) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 fsm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pace mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HA : forall n, (n < 240)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (HD : ed E = ed E) by reflexivity.
pose proof (arbQ_kept_refl W mem3 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as K.
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
arbQ_kstep K HA E15. clear HF HG.
arbQ_env E HA HD.
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
2: { exfalso. assert (E12c : ew Ec 12 = Z_to_bv 64 fsm) by (rewrite HA by lia; exact E12).
     rewrite branch_ne_U, (arbQ_fsm_cond _ fsm E12c Rfsm), EST in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
arbQ_kstep K HA E15. clear HF HG.
arbQ_env E HA HD.
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
- assert (F1 : fsm <> 1).
  { assert (E12c : ew Ec0 12 = Z_to_bv 64 fsm) by (rewrite HA by lia; exact E12).
    rewrite branch_ne_U, U_SOff, U_SLit, E12c, Z.add_0_r, Z_to_bv_unsigned in Hc.
    unfold zcanon, M64, bv_wrap, bv_modulus in Hc. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hc.
    rewrite Z.mod_mod in Hc by lia. change (1 mod 2 ^ 64) with 1 in Hc. intro F. subst fsm. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
  arbQ_kstep K HA E15. clear HF HG.
  arbQ_env E HA HD.
  destruct (arbQ_out0_rest _ out pace HO) as [GM G10].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno Hns. rewrite (K a Ha) by (cbv beta; lia). apply HK; assumption. }
  arbQ_zc HS HA E15 E33 out 1%nat 0 0 G0. rewrite Z.add_0_r in G0.
  arbQ_zc HS HA E15 E33 out 2%nat 12 0 G12.
  arbQ_zc HS HA E15 E33 out 2%nat 16 pace G16.
  arbQ_zc HS HA E15 E33 out 2%nat 20 0 G20.
  arbQ_zc HS HA E15 E33 out 2%nat 24 0 G24.
  arbQ_zc HS HA E15 E33 out 2%nat 28 0 G28.
  assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) reac_arbitrate_c.MAC0)).
  { apply (arbQ_garr8_copy _ mem3 _ (out + 4) (out + 4) _ GM). intros i Hi. cbn in Hi. apply K; [lia | cbv beta; lia]. }
  assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
  { apply (arbQ_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi. apply K; [lia | cbv beta; lia]. }
  eapply (arbQ_ret fq fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P None regs3 _ _ _ _ ly S (arb_fprel_refl fq) HPRE
    ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ (Permutation_refl _) KF).
  unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite <- Hb, EST, (proj2 (Z.eqb_neq fsm 1) F1). cbv iota.
  exact (arb_bytes_garr8 _ out 0 reac_arbitrate_c.MAC0 0 pace 0 0 0 G0 eq_refl GM2 G102 G12 G16 G20 G24 G28).
- assert (F1 : fsm = 1).
  { assert (E12c : ew Ec0 12 = Z_to_bv 64 fsm) by (rewrite HA by lia; exact E12).
    rewrite branch_ne_U, U_SOff, U_SLit, E12c, Z.add_0_r, Z_to_bv_unsigned in Hc.
    unfold zcanon, M64, bv_wrap, bv_modulus in Hc. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hc.
    rewrite Z.mod_mod in Hc by lia. change (1 mod 2 ^ 64) with 1 in Hc.
    destruct (Z.eqb_spec (fsm mod 2 ^ 64) 1) as [Hq|Hq]; [|discriminate Hc].
    destruct (Z_lt_le_dec fsm 0).
    - rewrite <- (Z_mod_plus_full fsm 1 (2 ^ 64)), Z.mod_small in Hq by lia. lia.
    - rewrite Z.mod_small in Hq by lia. exact Hq. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
  arbQ_kstep K HA E15. clear HF HG.
  arbQ_env E HA HD.
  psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
  + assert (U0 : our = 0).
    { assert (E11c : ew Ec1 11 = Z_to_bv 64 our) by (rewrite HA by lia; exact E11).
      rewrite branch_eq_U, U_SOff, U_SLit, E11c, Z.add_0_r, unsigned_lit_small in Hc by lia.
      unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia. change (0 mod 2 ^ 64) with 0 in Hc. apply Z.eqb_eq. exact Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
    arbQ_kstep K HA E15. clear HF HG.
    arbQ_env E HA HD.
    destruct (arbQ_out0_rest _ out pace HO) as [GM G10].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
    assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
       aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
    { intros a Ha Hno Hns. rewrite (K a Ha) by (cbv beta; lia). apply HK; assumption. }
    arbQ_zc HS HA E15 E33 out 1%nat 0 1 G0. rewrite Z.add_0_r in G0.
    arbQ_zc HS HA E15 E33 out 2%nat 12 0 G12.
    arbQ_zc HS HA E15 E33 out 2%nat 16 pace G16.
    arbQ_zc HS HA E15 E33 out 2%nat 20 0 G20.
    arbQ_zc HS HA E15 E33 out 2%nat 24 0 G24.
    arbQ_zc HS HA E15 E33 out 2%nat 28 0 G28.
    assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) reac_arbitrate_c.MAC0)).
    { apply (arbQ_garr8_copy _ mem3 _ (out + 4) (out + 4) _ GM). intros i Hi. cbn in Hi. apply K; [lia | cbv beta; lia]. }
    assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
    { apply (arbQ_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi. apply K; [lia | cbv beta; lia]. }
    eapply (arbQ_ret fq fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P None regs3 _ _ _ _ ly S (arb_fprel_refl fq) HPRE
      ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ (Permutation_refl _) KF).
    unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite <- Hb, EST, (proj2 (Z.eqb_eq fsm 1) F1), (proj2 (Z.eqb_eq our 0) U0). cbv iota.
    exact (arb_bytes_garr8 _ out 1 reac_arbitrate_c.MAC0 0 pace 0 0 0 G0 eq_refl GM2 G102 G12 G16 G20 G24 G28).
  + assert (U0 : our <> 0).
    { assert (E11c : ew Ec1 11 = Z_to_bv 64 our) by (rewrite HA by lia; exact E11).
      rewrite branch_eq_U, U_SOff, U_SLit, E11c, Z.add_0_r, unsigned_lit_small in Hc by lia.
      unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia. change (0 mod 2 ^ 64) with 0 in Hc. apply Z.eqb_neq. exact Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
    arbQ_kstep K HA E15. clear HF HG.
    arbQ_env E HA HD.
    destruct (HP U0) as (Hbp & Hbp1 & Hbp2 & LP & GP & Hdp).
    destruct (al_blocks _ _ LAWS ly S W mem md bp Np HAR Hbp) as (_ & Hp4096 & Hpceil & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ bp Np (proj1 HJ) Hbp) as (_ & _ & _ & _ & Hppres & _).
    prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
    prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
    rewrite (HA 15%nat) in Ra0 by lia. rewrite E15, unsigned_lit_small in Ra0 by lia.
    rewrite (HA 11%nat) in Ra1 by lia. rewrite E11 in Ra1.
    rewrite (HA 2%nat) in Qsp by lia. rewrite Usp in Qsp.
    rewrite (HA 3%nat) in Qgp by lia. rewrite E3 in Qgp.
    rewrite (HA 4%nat) in Qtp by lia. rewrite E4 in Qtp.
    pmkst HS.
    eapply SRr_bind.
    { lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
      eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA DS___asan_memcpy) (AMEMCPY fq) W (ms_regs msX) (ms_mem msX)
         REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S _ 0 (out + 4) our 6 (-128) _ HJ) end.
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
        + intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (Hppres a ltac:(lia))) |].
          unfold spZ. rewrite Qsp. rewrite unsigned_lit_small by lia. unfold ESTACK. lia.
        + split; [lia|]. split; [apply (amem_range_of_block SEGS B LAWS ly S W _ _ bp Np our 6 (proj1 HJ) Hbp); lia|].
          split; [apply (range_addressable_of_block SEGS B LAWS ly S W _ _ bp Np our 6 (proj1 HJ) Hbp); lia|].
          intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ bp Np our 6 (proj1 HJ) Hbp); lia. }
    cbv beta. clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp.
    intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2 & HSM).
    lazymatch type of Hfr with forall a, _ -> _ -> _ -> _ = aview _ _ ?mq a =>
    assert (HfrZ : forall a, 0 <= a < 2 ^ 64 -> ~ ((out + 4 <= a < out + 10) \/ (spZ regs - 128 - ESTACK <= a < spZ regs - 128)) ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mq a) end.
    { intros a Ha Hz. apply Hfr; [exact Ha | intro; apply Hz; left; lia | intro; apply Hz; right; lia]. }
    assert (GM : garr8 SEGS (mrestrict (w_H W) mem2) (out + 4) (map (fun b0 : byte => bv_unsigned b0) P)).
    { apply (arbQ_garr8_copy _ mem _ our (out + 4) _ GP). intros i Hi. rewrite length_map, LP in Hi.
      rewrite Heff by lia. rewrite (K (our + i)); [| lia | cbv beta; lia]. apply HK; lia. }
    destruct (arbQ_out0_rest _ out pace HO) as [_ G10].
    assert (G10m : garr8 SEGS (mrestrict (w_H W) mem2) (out + 10) [0; 0]).
    { apply (arbQ_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi.
      rewrite HfrZ by (try lia; cbv beta; unfold ESTACK; lia). apply K; [lia | cbv beta; lia]. }
    pose proof (arbQ_kept_step _ _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) K HfrZ
      ltac:(intros a Hq; cbv beta in Hq |- *; lia) ltac:(intros a Hq; cbv beta in Hq |- *; rewrite WS; unfold ESTACK in Hq; lia)) as K2.
    clear K.
    jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
    match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. repeat apply Forall_cons; [ | | | apply Forall_nil].
      - eapply region_kept_aview; [rewrite (HA 2%nat) by lia; exact Usp | | exact Hpres2].
        intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
      - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact Hpres2].
        intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia.
      - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact Hpres2].
        intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply Hfr; unfold ESTACK; lia. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
      assert (SHOK2 : sh_ok SEGS ARB_BX (arbQ_SH None) Ea (mrestrict (w_H W) mem2)) end.
    { constructor; [|constructor].
      apply (arb_shent ly S W mem2 md2 _ 15 bo No out 0 32 (proj1 HJ2) Hbo);
      [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
      | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 15%nat) by lia; exact E15 | lia] | lia | lia | lia]. }
    clear SHOK. rename SHOK2 into SHOK.
    lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
      assert (HEIa : img_env VAL A_LIM Ea) by (apply img_env_havoc_hi; [assumption | cbv; lia]) end.
    arbQ_env E HA HD.
    pose proof (arbQ_kept_refl W mem2 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as KM.
    paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
    lazymatch goal with HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => pose proof HFr' as HFr2 end.
    arbQ_kstep K2 HA E15. arbQ_kstep KM HA E15. clear HF HG.
    arbQ_env E HA HD.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
    assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
       aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
    { intros a Ha Hno Hns. rewrite (K2 a Ha) by (cbv beta; lia). apply HK; assumption. }
    arbQ_zc HS HA E15 E33 out 1%nat 0 1 G0. rewrite Z.add_0_r in G0.
    arbQ_zc HS HA E15 E33 out 2%nat 12 1 G12.
    arbQ_zc HS HA E15 E33 out 2%nat 16 pace G16.
    arbQ_zc HS HA E15 E33 out 2%nat 20 0 G20.
    arbQ_zc HS HA E15 E33 out 2%nat 24 0 G24.
    arbQ_zc HS HA E15 E33 out 2%nat 28 0 G28.
    assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) P)).
    { apply (arbQ_garr8_copy _ mem2 _ (out + 4) (out + 4) _ GM). intros i Hi. rewrite length_map, LP in Hi. apply KM; [lia | cbv beta; lia]. }
    assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
    { apply (arbQ_garr8_copy _ mem2 _ (out + 10) (out + 10) _ G10m). intros i Hi. cbn in Hi. apply KM; [lia | cbv beta; lia]. }
    eapply (arbQ_ret fq fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P None regs3 _ _ _ _ ly S (arb_fprel_refl fq) HPRE
      ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ2 (Permutation_refl _) KF).
    unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite <- Hb, EST, (proj2 (Z.eqb_eq fsm 1) F1), (proj2 (Z.eqb_neq our 0) U0). cbv iota.
    exact (arb_bytes_garr8 _ out 1 P 1 pace 0 0 0 G0 LP GM2 G102 G12 G16 G20 G24 G28).
Qed.

Lemma arbQb_swrap32 : forall u, bv_swrap 32 u mod 2 ^ 32 = u mod 2 ^ 32.
Proof.
intros u. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite Zminus_mod_idemp_l. f_equal. ring.
Qed.
Lemma arbQb_sext32 : forall x : word, bv_unsigned (sext 64 (bv_extract 0 32 x)) mod 2 ^ 32 = bv_unsigned x mod 2 ^ 32.
Proof.
intros x. rewrite YK11.sext32_unsigned. unfold bv_wrap at 1. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 32 * 2 ^ 32).
rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_mod by lia. rewrite arbQb_swrap32.
rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 32) with (2 ^ 32). apply Z.mod_mod. lia.
Qed.
Ltac arbQb_cv HS HA E15 i off V :=
  lazymatch type of HS with st_ok_pi ?sg _ ?Ex ?ss (restrict ?H ?msX) =>
  let r := eval vm_compute in (nth_error (ss_mem ss) i) in
  lazymatch r with Some ?rr =>
  let cs := eval vm_compute in (YP09.r_chunks rr) in
  let e := lazymatch cs with context [YP09.mkChunk off (CVal 4 ?e)] => e end in
  pose proof (arbQ_chunk_val _ Ex ss (restrict H msX) i rr off 4 e HS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
  cbn [YP09.r_base base_val ms_mem restrict] in V;
  rewrite (HA 15%nat) in V by lia; rewrite E15 in V; rewrite unsigned_lit_small in V by lia;
  change (N.to_nat 4) with 4%nat in V; change (8 * Z.of_N 4) with 32 in V
  end end.
Ltac arbQb_envk E0 HA HD EK :=
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
Lemma arbQb_vm_mod : forall m a v v', v mod 2 ^ 32 = v' mod 2 ^ 32 -> val_mem SEGS m a 4 v -> val_mem SEGS m a 4 v'.
Proof.
intros m a v v' Hv H jj Hj. rewrite (H jj Hj). unfold YO0f.le_byte.
assert (Hv' : v mod 2 ^ (8 * Z.of_nat 4) = v' mod 2 ^ (8 * Z.of_nat 4)) by exact Hv.
rewrite Hv'. reflexivity.
Qed.

Lemma arbQb_keep_aview : forall H (m2 m : word -> option byte) lo hi,
  (forall w : word, ~ (lo <= bv_unsigned w < hi) -> m2 w = m w) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m2 a = aview SEGS H m a.
Proof.
intros H m2 m lo hi Hk a Ha Hn. unfold aview, mbyte, mrestrict.
rewrite (Hk (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma arbQb_rkept : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
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
Lemma arbQ_pb : ARBQ_PB.
Proof.
unfold ARBQ_PB.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P b regs3 mem3 md3 HPRE HINV EST Hbn.
destruct b as [j|]; [|exfalso; apply Hbn; reflexivity]. clear Hbn.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
destruct (arbQ_entry fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P (Some j) regs3 mem3 md3 HPRE HINV) as [HS SHOK].
pose proof HINV as ((HJ & HK & HFR & HO & R2 & R3 & R4 & R8 & R9 & R18 & R25) & H19 & Hb).
pose proof HPRE as (HAF & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
assert (Ht0 : t <> 0) by (intro E0; unfold reac_arbitrate_c.best in Hb; rewrite (proj2 (Z.eqb_eq t 0) E0) in Hb; discriminate).
assert (Rj : 0 <= j < disco_table_c.n_of T).
{ pose proof Hb as Hb'. symmetry in Hb'. rewrite reac_arbitrate.best_scanz in Hb' by exact Ht0. exact (reac_arbitrate.scanz_range _ _ _ _ _ _ Hb'). }
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
change (BASE + AF_ARB_P) with (BASE + 31968).
remember (EQ regs regs3 pace t T (Some j)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EQ; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbQ_X regs3 pace t T (Some j))) n)
  by (intros n Hn; subst E; unfold EQ; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E12 : ew E 12 = Z_to_bv 64 fsm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pace mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (t + 48 * j)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (reac_arbitrate_c.ch_of T j)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (HA : forall n, (n < 240)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (HD : ed E = ed E) by reflexivity.
pose proof (arbQ_kept_refl W mem3 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as K.
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
arbQ_kstep K HA E15. clear HF HG.
arbQ_env E HA HD.
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
2: { exfalso. assert (E12c : ew Ec 12 = Z_to_bv 64 fsm) by (rewrite HA by lia; exact E12).
     rewrite branch_ne_U, (arbQ_fsm_cond _ fsm E12c Rfsm), EST in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
arbQ_kstep K HA E15. clear HF HG.
arbQ_env E HA HD.
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
  eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA DS___asan_memcpy) (AMEMCPY fq) W (ms_regs msX) (ms_mem msX)
     REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly S _ 0 (out + 4) (t + 48 * j) 6 (-128) _ HJ) end.
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
assert (HfrZ : forall a, 0 <= a < 2 ^ 64 -> ~ ((out + 4 <= a < out + 10) \/ (spZ regs - 128 - ESTACK <= a < spZ regs - 128)) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mq a) end.
{ intros a Ha Hz. apply Hfr; [exact Ha | intro; apply Hz; left; lia | intro; apply Hz; right; lia]. }
assert (GM : garr8 SEGS (mrestrict (w_H W) mem2) (out + 4) (map (fun b0 : byte => bv_unsigned b0) (disco_table_c.mac_of T j))).
{ apply (arbQ_garr8_copy _ mem3 _ (t + 48 * j) (out + 4) _ GMT). intros i Hi. rewrite length_map, Lm in Hi.
  rewrite Heff by lia. apply (K (t + 48 * j + i)); [lia | cbv beta; lia]. }
destruct (arbQ_out0_rest _ out pace HO) as [_ G10].
assert (G10m : garr8 SEGS (mrestrict (w_H W) mem2) (out + 10) [0; 0]).
{ apply (arbQ_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi.
  rewrite HfrZ by (try lia; cbv beta; unfold ESTACK; lia). apply K; [lia | cbv beta; lia]. }
pose proof (arbQ_kept_step _ _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) K HfrZ
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
  assert (SHOK2 : sh_ok SEGS ARB_BX (arbQ_SH (Some j)) Ea (mrestrict (w_H W) mem2)) end.
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
arbQ_env E HA HD.
pose proof (arbQ_kept_refl W mem2 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as KM.
paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
lazymatch goal with HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => pose proof HFr' as HFr2 end.
arbQ_kstep K2 HA E15. arbQ_kstep KM HA E15. clear HF HG.
arbQ_env E HA HD.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt Nt (proj1 HJ2) Hbt) as (_ & _ & _ & _ & Htpres2 & _).
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (8%bv : bv 5) Qs0.
rewrite (HA 34%nat) in Ra0 by lia. rewrite E34 in Ra0.
rewrite (HA 2%nat) in Qsp by lia. rewrite Usp in Qsp.
rewrite (HA 3%nat) in Qgp by lia. rewrite E3 in Qgp.
rewrite (HA 4%nat) in Qtp by lia. rewrite E4 in Qtp.
rewrite (HA 15%nat) in Qs0 by lia. rewrite E15 in Qs0.
pmkst HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  assert (GTR : garr8 SEGS (mrestrict (w_H W) (ms_mem msX)) t (map (fun b0 : byte => bv_unsigned b0) T)) end.
{ apply (arbQ_garr8_copy _ mem3 _ t t _ GT3). intros i Hi. rewrite length_map, LT in Hi. apply K2; [lia | cbv beta; lia]. }
pose proof (reac_arbitrate.u_range T (48 * j + 12) 1 ltac:(lia) ltac:(rewrite LT; lia)) as Rd.
pose proof (reac_arbitrate.u_range T (48 * j + 16) 1 ltac:(lia) ltac:(rewrite LT; lia)) as Rs.
pose proof (reac_arbitrate.u_range T (48 * j + 20) 4 ltac:(lia) ltac:(rewrite LT; lia)) as Rc.
change (2 ^ (8 * Z.of_nat 1)) with 256 in Rd, Rs. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Rc.
assert (Hrr : disco_table_c.role_of_e T j = 0 \/ disco_table_c.role_of_e T j = 1 \/ disco_table_c.role_of_e T j = 2) by exact (T2 j Rj).
pose proof (@pa_B_ok _ disco_listing PI) as HB.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (arb_rival_at fq ly S W regs mem md out ly S (ms_regs msX) (ms_mem msX) _ (t + 48 * j)
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
    split; [apply (arbQb_vm_mod _ _ (disco_table_c.u_at T (48 * j + 8) 4));
            [unfold disco_table_c.role_of_e, disco_table_c.s32_at; rewrite arbQb_swrap32; reflexivity
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
intros W2 c2 _ (-> & fq2 & ly2 & S2 & regs4 & mem4 & md4 & -> & FPR & HJ3 & HP3 & Hrv & HPerm & Hkeep).
clear RUN RUNTO BR. pose proof (paj_run (fx := fq2) B LAWS) as RUN. pose proof (paj_run_to (fx := fq2) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq2) (PI := PI)) as BR.
assert (Hrv' : getr regs4 10 = w64 (reac_arbitrate_c.rival_of T j)).
{ rewrite Hrv. replace (t + 48 * j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
clear Hrv.
assert (WR : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
lazymatch type of Hkeep with forall a : word, _ -> _ = ?mr a =>
  pose proof (arbQb_keep_aview (w_H W) mem4 mr _ _ Hkeep) as KR end.
pose proof (arbQ_kept_step _ _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) K2 KR
  ltac:(intros a Hq; exact Hq) ltac:(intros a Hq; cbv beta in Hq |- *; rewrite WS; rewrite WR in Hq; lia)) as K3.
clear K2. rename K3 into K2.
pose proof (arbQ_kept_step _ _ _ _ _ _ (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) KM KR
  ltac:(intros a Hq; exact Hq) ltac:(intros a Hq; cbv beta in Hq |- *; rewrite WS; rewrite WR in Hq; lia)) as KM3.
clear KM. rename KM3 into KM.
assert (Hbo' : In (bo, No) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HPerm) Hbo).
assert (Hbt' : In (bt, Nt) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HPerm) Hbt).
lazymatch type of HS with st_ok _ _ ?ssv _ =>
  let kk := eval vm_compute in (run_K A_LIM ARB_BX (arbQ_SH (Some j)) ssv) in
  jafter_call_keep_hi HS kk regs4 (mrestrict (w_H W) mem4) HP3 [0; 1; 2; 3]%nat HS2 end.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [ | | | | apply Forall_nil].
  - apply (arbQb_rkept _ _ _ _ _ (spZ regs)); [rewrite (HA 2%nat) by lia; exact Usp | | lia | lia].
    intros a Ha. apply Hkeep. rewrite unsigned_lit_small by lia. rewrite WR. lia.
  - apply (arbQb_rkept _ _ _ _ _ out); [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | lia | lia].
    intros a Ha. apply Hkeep. rewrite unsigned_lit_small by lia. rewrite WR. lia.
  - apply (arbQb_rkept _ _ _ _ _ out); [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | lia | lia].
    intros a Ha. apply Hkeep. rewrite unsigned_lit_small by lia. rewrite WR. lia.
  - apply (arbQb_rkept _ _ _ _ _ (t + 48 * j)); [rewrite (HA 34%nat) by lia; rewrite E34; apply unsigned_lit_small; lia | | lia | lia].
    intros a Ha. apply Hkeep. rewrite unsigned_lit_small by lia. rewrite WR. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. apply (arb_st_ok_xfx fq fq2) in HS.
lazymatch type of HS with st_ok_pi _ _ ?Ea ?ssv _ =>
  let e := eval vm_compute in (sr_get (ss_regs ssv) (10%bv : bv 5)) in
  lazymatch e with SOff ?ka 0 =>
    assert (EK : ew Ea ka = w64 (reac_arbitrate_c.rival_of T j)) by (rewrite <- Hrv'; reflexivity) end end.
lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
  assert (SHOK2 : sh_ok SEGS ARB_BX (arbQ_SH (Some j)) Ea (mrestrict (w_H W) mem4)) end.
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
arbQb_envk E HA HD EK.
paj_run_tok RUN HS HJ3 SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo' out |].
lazymatch goal with HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => pose proof HFr' as HFr2 end.
arbQ_kstep K2 HA E15. arbQ_kstep KM HA E15. clear HF HG.
arbQb_envk E HA HD EK.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
   aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno Hns. rewrite (K2 a Ha) by (cbv beta; lia). apply HK; assumption. }
arbQ_zc HS HA E15 E33 out 1%nat 0 2 G0. rewrite Z.add_0_r in G0.
arbQ_zc HS HA E15 E33 out 2%nat 12 1 G12.
arbQ_zc HS HA E15 E33 out 2%nat 16 1 G16.
arbQ_zc HS HA E15 E33 out 2%nat 20 0 G20.
arbQb_cv HS HA E15 2%nat 24 V24.
assert (G24 : garr8 SEGS (mrestrict (w_H W) mF) (out + 24) (map (fun b0 : byte => bv_unsigned b0) (reac_arbitrate_c.z4 (reac_arbitrate_c.rival_of T j)))).
{ apply (arbQ_z4_chunk _ _ _ _ V24). cbn [sv_denot]. rewrite EK, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. apply arbQ_u64_mod32. }
clear V24.
arbQb_cv HS HA E15 2%nat 28 V28.
assert (G28 : garr8 SEGS (mrestrict (w_H W) mF) (out + 28) (map (fun b0 : byte => bv_unsigned b0) (reac_arbitrate_c.z4 (reac_arbitrate_c.ch_of T j)))).
{ apply (arbQ_z4_chunk _ _ _ _ V28). cbn [sv_denot]. rewrite arbQb_sext32. rewrite (HA 35%nat) by lia.
  rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. apply arbQ_u64_mod32. }
clear V28.
assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) (disco_table_c.mac_of T j))).
{ apply (arbQ_garr8_copy _ mem2 _ (out + 4) (out + 4) _ GM). intros i Hi. rewrite length_map, Lm in Hi. apply KM; [lia | cbv beta; lia]. }
assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
{ apply (arbQ_garr8_copy _ mem2 _ (out + 10) (out + 10) _ G10m). intros i Hi. cbn in Hi. apply KM; [lia | cbv beta; lia]. }
eapply (arbQ_ret fq fq2 ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P (Some j) regs3 _ _ _ _ ly2 S2 FPR HPRE
  ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ3 HPerm KF).
unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite <- Hb, EST. cbv iota.
exact (arb_bytes_garr8 _ out 2 (disco_table_c.mac_of T j) 1 1 0 (reac_arbitrate_c.rival_of T j) (reac_arbitrate_c.ch_of T j)
  G0 Lm GM2 G102 G12 G16 G20 G24 G28).
Qed.

Lemma arbPA_swrap : forall x, -2 ^ 31 <= bv_swrap 32 x < 2 ^ 31 /\ bv_swrap 32 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
intros x. unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with 2147483648 by reflexivity. replace (bv_modulus 32) with 4294967296 by reflexivity.
change (2 ^ 31) with 2147483648. change (2 ^ 32) with 4294967296.
pose proof (Z.mod_pos_bound (x + 2147483648) 4294967296 ltac:(lia)) as M.
split; [set (y := (x + 2147483648) mod 4294967296) in *; lia|].
rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma arbPA_sext_mod : forall E e, bv_unsigned (sv_denot E (SExt true 32 e)) mod 2 ^ 32 = bv_unsigned (sv_denot E e) mod 2 ^ 32.
Proof.
intros E e. cbn [sv_denot]. rewrite sext32_unsigned, bv_extract_unsigned.
generalize (bv_unsigned (sv_denot E e)). intros x.
unfold bv_swrap. replace (bv_half_modulus 32) with 2147483648 by reflexivity.
unfold bv_wrap. replace (bv_modulus 64) with 18446744073709551616 by reflexivity.
replace (bv_modulus 32) with 4294967296 by reflexivity.
change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 32) with 4294967296.
Z.div_mod_to_equations. lia.
Qed.
Ltac arbPA_env E0 HA HD HR :=
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
Ltac arbPA_zc HS HA E15 out i off v G tac :=
  lazymatch type of HS with st_ok_pi ?sg _ ?Ex ?ss (restrict ?H ?msX) =>
  let r := eval vm_compute in (nth_error (ss_mem ss) i) in
  lazymatch r with Some ?rr =>
  let cs := eval vm_compute in (YP09.r_chunks rr) in
  let e := lazymatch cs with context [YP09.mkChunk off (CVal 4 ?e)] => e end in
  let V := fresh "V" in
  pose proof (arbQ_chunk_val _ Ex ss (restrict H msX) i rr off 4 e HS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
  cbn [YP09.r_base base_val ms_mem restrict] in V;
  rewrite (HA 15%nat) in V by lia; rewrite E15 in V; rewrite unsigned_lit_small in V by lia;
  change (N.to_nat 4) with 4%nat in V; change (8 * Z.of_N 4) with 32 in V;
  assert (G : garr8 sg (mrestrict H (ms_mem msX)) (out + off) (map (fun b : byte => bv_unsigned b) (reac_arbitrate_c.z4 v)));
  [ apply (arbQ_z4_chunk _ _ _ v V); tac | clear V ]
  end end.
Lemma arbPA_val_mem_eqv : forall (m : word -> option byte) a (n : nat) v v',
  val_mem SEGS m a n v -> v mod 2 ^ (8 * Z.of_nat n) = v' mod 2 ^ (8 * Z.of_nat n) -> val_mem SEGS m a n v'.
Proof.
intros m a n v v' H Hv k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite Hv. reflexivity.
Qed.

Lemma arbPA_pres_call : forall H (memT mem2 : word -> option byte) lo hi,
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

Lemma arbPA_aview_call : forall H (memT mem2 : word -> option byte) lo hi a,
  (forall w : word, ~ (lo <= bv_unsigned w < hi) -> mem2 w = memT w) -> 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  aview SEGS H mem2 a = aview SEGS H memT a.
Proof.
intros H memT mem2 lo hi a Hk Ha Hn. apply aview_eq_of. unfold mrestrict.
rewrite (Hk (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; exact Hn). reflexivity.
Qed.
Lemma arbQ_pa_some : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (j : Z) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invP ly S W regs mem md t our fsm pace now out T P (Some j) regs3 mem3 md3 ->
  ((fsm =? 2) || (fsm =? 3)) = true ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_P)) mem3 (seg_rom SEGS)) md3)
    (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P j regs3 mem3 md3 HPRE HINV EST.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR. pose proof (paj_ret_at (fx := fq) (PI := PI)) as RET.
destruct (arbQ_entry fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P (Some j) regs3 mem3 md3 HPRE HINV) as [HS SHOK].
pose proof HINV as ((HJ & HK & HFR & HO & R2 & R3 & R4 & R8 & R9 & R18 & R25) & H19 & Hb).
pose proof HPRE as (HAF & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
assert (Ht0 : t <> 0) by (intro E0; unfold reac_arbitrate_c.best in Hb; rewrite (proj2 (Z.eqb_eq t 0) E0) in Hb; discriminate).
assert (Rj : 0 <= j < disco_table_c.n_of T).
{ symmetry in Hb. rewrite reac_arbitrate.best_scanz in Hb by exact Ht0. exact (reac_arbitrate.scanz_range _ _ _ _ _ _ Hb). }
destruct (HT Ht0) as (Hbt & Hbt1 & Hbt2 & Ht8 & LT & GT & TOK & Hdis).
pose proof TOK as (T1 & _). unfold disco_table_c.tbl_T1 in T1.
destruct (al_blocks _ _ LAWS ly S W mem md bt Nt HAR Hbt) as (Ht16 & Ht4096 & Htceil & Htia & Htpres & _).
change (BASE + AF_ARB_P) with (BASE + 31968).
remember (EQ regs regs3 pace t T (Some j)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EQ; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbQ_X regs3 pace t T (Some j))) n)
  by (intros n Hn; subst E; unfold EQ; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E11 : ew E 11 = Z_to_bv 64 our) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 fsm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pace mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (t + 48 * j)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (reac_arbitrate_c.ch_of T j)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (HA : forall n, (n < 240)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (HD : ed E = ed E) by reflexivity.
pose proof (arbQ_kept_refl W mem3 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as K.
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
arbQ_kstep K HA E15. clear HF HG.
arbQ_env E HA HD.
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
1: { exfalso. assert (E12c : ew Ec 12 = Z_to_bv 64 fsm) by (rewrite HA by lia; exact E12).
     rewrite branch_ne_U, (arbQ_fsm_cond _ fsm E12c Rfsm), EST in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
arbQ_kstep K HA E15. clear HF HG.
arbQ_env E HA HD.
assert (WR : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
pose proof (blk_off_imgP _ _ _ _ _ _ bt Nt HAR Hbt) as Htimg. unfold off_img, IMG_LO, IMG_TOP in Htimg.
pose proof pa_B_ok as (HB0 & HB1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt Nt (proj1 HJ) Hbt) as (_ & _ & _ & _ & HtpT & _).
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (8%bv : bv 5) Qs0.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
rewrite (HA 34%nat) in Ra0 by lia. rewrite E34 in Ra0.
rewrite (HA 15%nat) in Qs0 by lia. rewrite E15 in Qs0.
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
  apply (arbPA_val_mem_eqv _ _ 4 _ _ V). unfold disco_table_c.role_of_e, disco_table_c.s32_at, disco_table_c.u_at.
  change (8 * Z.of_nat 4) with 32. symmetry. apply arbPA_swrap. }
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
destruct (arbPA_swrap (disco_table_c.u_at T (48 * j + 8) 4)) as [RR _].
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msX) _) ?mdX) _ =>
  eapply (arb_rival_at fq ly S W regs mem md out ly S (ms_regs msX) (ms_mem msX) mdX (t + 48 * j)
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
intros W2 c2 _ (-> & fq2 & ly2 & S2 & regs2 & mem2 & md2 & -> & FPR & HJ2 & HP2 & Ha02 & HPerm2 & Hkp2).
clear RUN RUNTO BR RET. pose proof (paj_run (fx := fq2) B LAWS) as RUN. pose proof (paj_run_to (fx := fq2) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq2) (PI := PI)) as BR. pose proof (paj_ret_at (fx := fq2) (PI := PI)) as RET.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HsP2 & _).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 - REAC_RIVAL_KIND_OF_STK <= a < spZ regs - 128) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem msX) a)
    by (intros a Ha Hn; exact (arbPA_aview_call (w_H W) (ms_mem msX) mem2 _ _ a Hkp2 Ha Hn));
  assert (PC : forall a, apresent (w_H W) (ms_mem msX) a -> apresent (w_H W) mem2 a)
    by (apply (arbPA_pres_call (w_H W) (ms_mem msX) mem2 _ _ Hkp2); intros a Ha; apply HsP2; rewrite WS; rewrite WR in Ha; lia) end.
lazymatch type of K with arbQ_kept _ _ ?mq ?Zx =>
  pose proof (arbQ_kept_step W mem3 mq mem2 Zx (fun a => spZ regs - 128 - REAC_RIVAL_KIND_OF_STK <= a < spZ regs - 128) Zx K KC
    ltac:(intros a Hq; exact Hq) ltac:(intros a Hq; cbv beta in Hq |- *; rewrite WR in Hq; rewrite WS; lia)) as K2 end.
clear K. rename K2 into K.
assert (HboX : In (bo, No) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); exact Hbo).
assert (HbtX : In (bt, Nt) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); exact Hbt).
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [ | | | | apply Forall_nil].
  - eapply region_kept_aview; [rewrite (HA 2%nat) by lia; exact Usp | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia.
  - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia.
  - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia.
  - eapply region_kept_aview; [rewrite (HA 34%nat) by lia; rewrite E34; apply unsigned_lit_small; lia | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. apply (arb_st_ok_xfx fq fq2) in HS.
lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
  assert (SHOK2 : sh_ok SEGS ARB_BX (arbQ_SH (Some j)) Ea (mrestrict (w_H W) mem2)) end.
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
arbPA_env E HA HD HR.
paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbQ_awr HA E15 HboX out |].
arbQ_kstep K HA E15. clear HF HG.
arbPA_env E HA HD HR.
destruct (arbQ_out0_rest _ out pace HO) as [GM0 G10].
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
- assert (U0 : our = 0).
  { rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite (HA 11%nat) in Hc by lia.
    rewrite E11, Z.add_0_r, unsigned_lit_small in Hc by lia.
    unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia. change (0 mod 2 ^ 64) with 0 in Hc. apply Z.eqb_eq. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbQ_awr HA E15 HboX out |].
  arbQ_kstep K HA E15. clear HF HG.
  arbPA_env E HA HD HR.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno Hns. rewrite (K a Ha) by (cbv beta; lia). apply HK; assumption. }
  arbQ_zc HS HA E15 E33 out 1%nat 0 1 G0. rewrite Z.add_0_r in G0.
  arbQ_zc HS HA E15 E33 out 2%nat 12 0 G12.
  arbQ_zc HS HA E15 E33 out 2%nat 16 pace G16.
  arbQ_zc HS HA E15 E33 out 2%nat 20 1 G20.
  arbPA_zc HS HA E15 out 2%nat 24 (reac_arbitrate_c.rival_of T j) G24
    ltac:(cbn [sv_denot]; rewrite HR, Z.add_0_r, Z_to_bv_bv_unsigned, Ha02; apply arbQ_u64_mod32).
  arbPA_zc HS HA E15 out 2%nat 28 (reac_arbitrate_c.ch_of T j) G28
    ltac:(rewrite arbPA_sext_mod; cbn [sv_denot]; rewrite (HA 35%nat) by lia; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; apply arbQ_u64_mod32).
  assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) reac_arbitrate_c.MAC0)).
  { apply (arbQ_garr8_copy _ mem3 _ (out + 4) (out + 4) _ GM0). intros i Hi. cbn in Hi. apply K; [lia | cbv beta; lia]. }
  assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
  { apply (arbQ_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi. apply K; [lia | cbv beta; lia]. }
  eapply (arbQ_ret fq fq2 ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P (Some j) regs3 _ _ _ _ ly2 S2 FPR HPRE
    ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ2 HPerm2 KF).
  unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite <- Hb, EST, (proj2 (Z.eqb_eq our 0) U0). cbv iota.
  exact (arb_bytes_garr8 _ out 1 reac_arbitrate_c.MAC0 0 pace 1 (reac_arbitrate_c.rival_of T j) (reac_arbitrate_c.ch_of T j)
    G0 eq_refl GM2 G102 G12 G16 G20 G24 G28).
- assert (U0 : our <> 0).
  { rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite (HA 11%nat) in Hc by lia.
    rewrite E11, Z.add_0_r, unsigned_lit_small in Hc by lia.
    unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia. change (0 mod 2 ^ 64) with 0 in Hc. apply Z.eqb_neq. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbQ_awr HA E15 HboX out |].
  arbQ_kstep K HA E15. clear HF HG.
  arbPA_env E HA HD HR.
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
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA DS___asan_memcpy) (AMEMCPY fq2) W (ms_regs msU) (ms_mem msU)
       REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly2 S2 _ 0 (out + 4) our 6 (-128) _ HJ2).
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
  assert (HfrZ : forall a, 0 <= a < 2 ^ 64 -> ~ ((out + 4 <= a < out + 10) \/ (spZ regs - 128 - ESTACK <= a < spZ regs - 128)) ->
    aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) (ms_mem msU) a).
  { intros a Ha Hz. apply Hfr; [exact Ha | intro; apply Hz; left; lia | intro; apply Hz; right; lia]. }
  assert (GM : garr8 SEGS (mrestrict (w_H W) mem4) (out + 4) (map (fun b0 : byte => bv_unsigned b0) P)).
  { apply (arbQ_garr8_copy _ mem _ our (out + 4) _ GP). intros i Hi. rewrite length_map, LP in Hi.
    rewrite Heff by lia. rewrite (K (our + i)); [| lia | cbv beta; lia]. apply HK; lia. }
  assert (G104 : garr8 SEGS (mrestrict (w_H W) mem4) (out + 10) [0; 0]).
  { apply (arbQ_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi.
    rewrite HfrZ by (unfold ESTACK; lia). apply K; [lia | cbv beta; lia]. }
  pose proof (arbQ_kept_step _ _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) K HfrZ
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
    assert (SHOK2 : sh_ok SEGS ARB_BX (arbQ_SH (Some j)) Ea (mrestrict (w_H W) mem4)) end.
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
  arbPA_env E HA HD HR.
  pose proof (arbQ_kept_refl W mem4 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as KM.
  paj_run_tok RUN HS HJ4 SHOK ARB_SPAN; [arbQ_awr HA E15 HboX out |].
  lazymatch goal with HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => pose proof HFr' as HFr2 end.
  arbQ_kstep K2 HA E15. arbQ_kstep KM HA E15. clear HF HG.
  arbPA_env E HA HD HR.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno Hns. rewrite (K2 a Ha) by (cbv beta; lia). apply HK; assumption. }
  arbQ_zc HS HA E15 E33 out 1%nat 0 1 G0. rewrite Z.add_0_r in G0.
  arbQ_zc HS HA E15 E33 out 2%nat 12 1 G12.
  arbQ_zc HS HA E15 E33 out 2%nat 16 pace G16.
  arbQ_zc HS HA E15 E33 out 2%nat 20 1 G20.
  arbPA_zc HS HA E15 out 2%nat 24 (reac_arbitrate_c.rival_of T j) G24
    ltac:(cbn [sv_denot]; rewrite HR, Z.add_0_r, Z_to_bv_bv_unsigned, Ha02; apply arbQ_u64_mod32).
  arbPA_zc HS HA E15 out 2%nat 28 (reac_arbitrate_c.ch_of T j) G28
    ltac:(rewrite arbPA_sext_mod; cbn [sv_denot]; rewrite (HA 35%nat) by lia; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; apply arbQ_u64_mod32).
  assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) P)).
  { apply (arbQ_garr8_copy _ mem4 _ (out + 4) (out + 4) _ GM). intros i Hi. rewrite length_map, LP in Hi.
    apply KM; [lia | cbv beta; lia]. }
  assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
  { apply (arbQ_garr8_copy _ mem4 _ (out + 10) (out + 10) _ G104). intros i Hi. cbn in Hi. apply KM; [lia | cbv beta; lia]. }
  eapply (arbQ_ret fq fq2 ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P (Some j) regs3 _ _ _ _ ly2 S2 FPR HPRE
    ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ4 HPerm2 KF).
  unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite <- Hb, EST, (proj2 (Z.eqb_neq our 0) U0). cbv iota.
  exact (arb_bytes_garr8 _ out 1 P 1 pace 1 (reac_arbitrate_c.rival_of T j) (reac_arbitrate_c.ch_of T j)
    G0 LP GM2 G102 G12 G16 G20 G24 G28).
Qed.

Lemma arbQ_pa_none : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (regs3 : bvmap 5 word) mem3 md3,
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invP ly S W regs mem md t our fsm pace now out T P None regs3 mem3 md3 ->
  ((fsm =? 2) || (fsm =? 3)) = true ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_P)) mem3 (seg_rom SEGS)) md3)
    (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).
Proof.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs3 mem3 md3 HPRE HINV EST.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR. pose proof (paj_ret_at (fx := fq) (PI := PI)) as RET.
destruct (arbQ_entry fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P None regs3 mem3 md3 HPRE HINV) as [HS SHOK].
pose proof HINV as ((HJ & HK & HFR & HO & R2 & R3 & R4 & R8 & R9 & R18 & R25) & H19 & Hb).
pose proof HPRE as (HAF & HROD & H10 & H11 & H12 & H13 & H14 & H15 & Rt & Rour & Rfsm & Rpace & Rnow & Rout & Hbo & Hbo1 & Hbo2 & Ho4 & HT & HP).
pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_ARBITRATE_STK = 8320) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md bo No HAR Hbo) as (Ho16 & Ho4096 & Hoceil & Hoia & Hopres & _).
change (BASE + AF_ARB_P) with (BASE + 31968).
remember (EQ regs regs3 pace t T None) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EQ; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (arbQ_X regs3 pace t T None)) n)
  by (intros n Hn; subst E; unfold EQ; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E15 : ew E 15 = Z_to_bv 64 out) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E11 : ew E 11 = Z_to_bv 64 our) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 fsm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pace mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HA : forall n, (n < 240)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (HD : ed E = ed E) by reflexivity.
pose proof (arbQ_kept_refl W mem3 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as K.
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
arbQ_kstep K HA E15. clear HF HG.
arbQ_env E HA HD.
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
1: { exfalso. assert (E12c : ew Ec 12 = Z_to_bv 64 fsm) by (rewrite HA by lia; exact E12).
     rewrite branch_ne_U, (arbQ_fsm_cond _ fsm E12c Rfsm), EST in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK ARB_SPAN; [arbQ_awr HA E15 Hbo out |].
arbQ_kstep K HA E15. clear HF HG.
arbQ_env E HA HD.
assert (WR : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
pose proof pa_B_ok as (HB0 & HB1 & _).
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (8%bv : bv 5) Qs0.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
rewrite (HA 15%nat) in Qs0 by lia. rewrite E15 in Qs0.
rewrite (HA 2%nat) in Qsp by lia. rewrite Usp in Qsp.
rewrite (HA 3%nat) in Qgp by lia. rewrite E3 in Qgp.
rewrite (HA 4%nat) in Qtp by lia. rewrite E4 in Qtp.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msX) _) ?mdX) _ =>
  eapply (arb_rival_at fq ly S W regs mem md out ly S (ms_regs msX) (ms_mem msX) mdX 0 0 0 0 0 _ HJ HROD) end.
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
intros W2 c2 _ (-> & fq2 & ly2 & S2 & regs2 & mem2 & md2 & -> & FPR & HJ2 & HP2 & Ha02 & HPerm2 & Hkp2).
clear RUN RUNTO BR RET. pose proof (paj_run (fx := fq2) B LAWS) as RUN. pose proof (paj_run_to (fx := fq2) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq2) (PI := PI)) as BR. pose proof (paj_ret_at (fx := fq2) (PI := PI)) as RET.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HsP2 & _).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 - REAC_RIVAL_KIND_OF_STK <= a < spZ regs - 128) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem msX) a)
    by (intros a Ha Hn; exact (arbPA_aview_call (w_H W) (ms_mem msX) mem2 _ _ a Hkp2 Ha Hn));
  assert (PC : forall a, apresent (w_H W) (ms_mem msX) a -> apresent (w_H W) mem2 a)
    by (apply (arbPA_pres_call (w_H W) (ms_mem msX) mem2 _ _ Hkp2); intros a Ha; apply HsP2; rewrite WS; rewrite WR in Ha; lia) end.
lazymatch type of K with arbQ_kept _ _ ?mq ?Zx =>
  pose proof (arbQ_kept_step W mem3 mq mem2 Zx (fun a => spZ regs - 128 - REAC_RIVAL_KIND_OF_STK <= a < spZ regs - 128) Zx K KC
    ltac:(intros a Hq; exact Hq) ltac:(intros a Hq; cbv beta in Hq |- *; rewrite WR in Hq; rewrite WS; lia)) as K2 end.
clear K. rename K2 into K.
assert (HboX : In (bo, No) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); exact Hbo).
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [ | | | apply Forall_nil].
  - eapply region_kept_aview; [rewrite (HA 2%nat) by lia; exact Usp | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia.
  - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia.
  - eapply region_kept_aview; [rewrite (HA 15%nat) by lia; rewrite E15; apply unsigned_lit_small; lia | | exact PC].
    intros a Ha. cbn [YP09.r_lo YP09.r_hi] in Ha. apply KC; rewrite ?WR; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. apply (arb_st_ok_xfx fq fq2) in HS.
lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
  assert (SHOK2 : sh_ok SEGS ARB_BX (arbQ_SH None) Ea (mrestrict (w_H W) mem2)) end.
{ constructor; [|constructor].
  apply (arb_shent ly2 S2 W mem2 md2 _ 15 bo No out 0 32 (proj1 HJ2) HboX);
  [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
  | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 15%nat) by lia; exact E15 | lia] | lia | lia | lia]. }
clear SHOK. rename SHOK2 into SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
  assert (HEIa : img_env VAL A_LIM Ea) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
  assert (HR : ew Ea 516 = getr regs2 10) by reflexivity end.
rewrite Z.eqb_refl in Ha02.
arbPA_env E HA HD HR.
paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbQ_awr HA E15 HboX out |].
arbQ_kstep K HA E15. clear HF HG.
arbPA_env E HA HD HR.
destruct (arbQ_out0_rest _ out pace HO) as [GM0 G10].
psrr_branch_tok RUN BR HS SHOK ARB_SPAN.
- assert (U0 : our = 0).
  { rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite (HA 11%nat) in Hc by lia.
    rewrite E11, Z.add_0_r, unsigned_lit_small in Hc by lia.
    unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia. change (0 mod 2 ^ 64) with 0 in Hc. apply Z.eqb_eq. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbQ_awr HA E15 HboX out |].
  arbQ_kstep K HA E15. clear HF HG.
  arbPA_env E HA HD HR.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno Hns. rewrite (K a Ha) by (cbv beta; lia). apply HK; assumption. }
  arbQ_zc HS HA E15 E33 out 1%nat 0 1 G0. rewrite Z.add_0_r in G0.
  arbQ_zc HS HA E15 E33 out 2%nat 12 0 G12.
  arbQ_zc HS HA E15 E33 out 2%nat 16 pace G16.
  arbPA_zc HS HA E15 out 2%nat 20 0 G20 ltac:(first [cbn [sv_denot]; apply arbQ_u64_mod32 | vm_compute; reflexivity]).
  arbPA_zc HS HA E15 out 2%nat 24 0 G24
    ltac:(cbn [sv_denot]; rewrite HR, Z.add_0_r, Z_to_bv_bv_unsigned, Ha02; apply arbQ_u64_mod32).
  arbPA_zc HS HA E15 out 2%nat 28 0 G28 ltac:(first [cbn [sv_denot]; apply arbQ_u64_mod32 | vm_compute; reflexivity]).
  assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) reac_arbitrate_c.MAC0)).
  { apply (arbQ_garr8_copy _ mem3 _ (out + 4) (out + 4) _ GM0). intros i Hi. cbn in Hi. apply K; [lia | cbv beta; lia]. }
  assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
  { apply (arbQ_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi. apply K; [lia | cbv beta; lia]. }
  eapply (arbQ_ret fq fq2 ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P None regs3 _ _ _ _ ly2 S2 FPR HPRE
    ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ2 HPerm2 KF).
  unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite <- Hb, EST, (proj2 (Z.eqb_eq our 0) U0). cbv iota.
  exact (arb_bytes_garr8 _ out 1 reac_arbitrate_c.MAC0 0 pace 0 0 0 G0 eq_refl GM2 G102 G12 G16 G20 G24 G28).
- assert (U0 : our <> 0).
  { rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite (HA 11%nat) in Hc by lia.
    rewrite E11, Z.add_0_r, unsigned_lit_small in Hc by lia.
    unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia. change (0 mod 2 ^ 64) with 0 in Hc. apply Z.eqb_neq. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ2 SHOK ARB_SPAN; [arbQ_awr HA E15 HboX out |].
  arbQ_kstep K HA E15. clear HF HG.
  arbPA_env E HA HD HR.
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
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA DS___asan_memcpy) (AMEMCPY fq2) W (ms_regs msU) (ms_mem msU)
       REAC_ARBITRATE_STK (spZ regs) [(out, out + 32)] ly S W mem md [] ly2 S2 _ 0 (out + 4) our 6 (-128) _ HJ2).
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
  assert (HfrZ : forall a, 0 <= a < 2 ^ 64 -> ~ ((out + 4 <= a < out + 10) \/ (spZ regs - 128 - ESTACK <= a < spZ regs - 128)) ->
    aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) (ms_mem msU) a).
  { intros a Ha Hz. apply Hfr; [exact Ha | intro; apply Hz; left; lia | intro; apply Hz; right; lia]. }
  assert (GM : garr8 SEGS (mrestrict (w_H W) mem4) (out + 4) (map (fun b0 : byte => bv_unsigned b0) P)).
  { apply (arbQ_garr8_copy _ mem _ our (out + 4) _ GP). intros i Hi. rewrite length_map, LP in Hi.
    rewrite Heff by lia. rewrite (K (our + i)); [| lia | cbv beta; lia]. apply HK; lia. }
  assert (G104 : garr8 SEGS (mrestrict (w_H W) mem4) (out + 10) [0; 0]).
  { apply (arbQ_garr8_copy _ mem3 _ (out + 10) (out + 10) _ G10). intros i Hi. cbn in Hi.
    rewrite HfrZ by (unfold ESTACK; lia). apply K; [lia | cbv beta; lia]. }
  pose proof (arbQ_kept_step _ _ _ _ _ _ (fun a => (out <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs)) K HfrZ
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
    assert (SHOK2 : sh_ok SEGS ARB_BX (arbQ_SH None) Ea (mrestrict (w_H W) mem4)) end.
  { constructor; [|constructor].
    apply (arb_shent ly2 S2 W mem4 md4 _ 15 bo No out 0 32 (proj1 HJ4) HboX);
    [apply arb_U_BX; rewrite ew_havoc_old by lia; rewrite (HA 32%nat) by lia; exact E32
    | apply arb_U_atom; [rewrite ew_havoc_old by lia; rewrite (HA 15%nat) by lia; exact E15 | lia] | lia | lia | lia]. }
  clear SHOK. rename SHOK2 into SHOK.
  lazymatch type of HS with st_ok_pi _ _ ?Ea _ _ =>
    assert (HEIb : img_env VAL A_LIM Ea) by (apply img_env_havoc_hi; [assumption | cbv; lia]) end.
  arbPA_env E HA HD HR.
  pose proof (arbQ_kept_refl W mem4 (fun a => (out <= a < out + 4) \/ (out + 12 <= a < out + 32) \/ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs))) as KM.
  paj_run_tok RUN HS HJ4 SHOK ARB_SPAN; [arbQ_awr HA E15 HboX out |].
  lazymatch goal with HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => pose proof HFr' as HFr2 end.
  arbQ_kstep K2 HA E15. arbQ_kstep KM HA E15. clear HF HG.
  arbPA_env E HA HD HR.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => set (mF := ms_mem msX) in * end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 32) -> ~ (spZ regs - REAC_ARBITRATE_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno Hns. rewrite (K2 a Ha) by (cbv beta; lia). apply HK; assumption. }
  arbQ_zc HS HA E15 E33 out 1%nat 0 1 G0. rewrite Z.add_0_r in G0.
  arbQ_zc HS HA E15 E33 out 2%nat 12 1 G12.
  arbQ_zc HS HA E15 E33 out 2%nat 16 pace G16.
  arbPA_zc HS HA E15 out 2%nat 20 0 G20 ltac:(first [cbn [sv_denot]; apply arbQ_u64_mod32 | vm_compute; reflexivity]).
  arbPA_zc HS HA E15 out 2%nat 24 0 G24
    ltac:(cbn [sv_denot]; rewrite HR, Z.add_0_r, Z_to_bv_bv_unsigned, Ha02; apply arbQ_u64_mod32).
  arbPA_zc HS HA E15 out 2%nat 28 0 G28 ltac:(first [cbn [sv_denot]; apply arbQ_u64_mod32 | vm_compute; reflexivity]).
  assert (GM2 : garr8 SEGS (mrestrict (w_H W) mF) (out + 4) (map (fun b0 : byte => bv_unsigned b0) P)).
  { apply (arbQ_garr8_copy _ mem4 _ (out + 4) (out + 4) _ GM). intros i Hi. rewrite length_map, LP in Hi.
    apply KM; [lia | cbv beta; lia]. }
  assert (G102 : garr8 SEGS (mrestrict (w_H W) mF) (out + 10) [0; 0]).
  { apply (arbQ_garr8_copy _ mem4 _ (out + 10) (out + 10) _ G104). intros i Hi. cbn in Hi. apply KM; [lia | cbv beta; lia]. }
  eapply (arbQ_ret fq fq2 ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P None regs3 _ _ _ _ ly2 S2 FPR HPRE
    ltac:(intros n Hn; rewrite HA by lia; rewrite HE; reflexivity) ltac:(rewrite HD, HE; reflexivity) HS eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ4 HPerm2 KF).
  unfold reac_arbitrate_c.arb_model. cbv zeta. rewrite <- Hb, EST, (proj2 (Z.eqb_neq our 0) U0). cbv iota.
  exact (arb_bytes_garr8 _ out 1 P 1 pace 0 0 0 G0 LP GM2 G102 G12 G16 G20 G24 G28).
Qed.

Lemma arbQ_pa : ARBQ_PA.
Proof.
unfold ARBQ_PA.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P b regs3 mem3 md3 HPRE HINV EST.
destruct b as [j|].
- exact (arbQ_pa_some fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P j regs3 mem3 md3 HPRE HINV EST).
- exact (arbQ_pa_none fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P regs3 mem3 md3 HPRE HINV EST).
Qed.

Lemma arb_segP : ARB_SEGP.
Proof. exact (arbQ_dispatch arbQ_pa arbQ_pb arbQ_pc). Qed.

Lemma arb_loop : forall (k : nat) (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch
    (t our fsm pace now out bt Nt bp Np bo No : Z) (T P : list byte) (i : Z) (b : option Z) (regs3 : bvmap 5 word) mem3 md3,
  Z.to_nat (disco_table_c.n_of T - i) = k ->
  arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P ->
  arb_invL ly S W regs mem md t our fsm pace now out T P i b regs3 mem3 md3 ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + AF_ARB_L)) mem3 (seg_rom SEGS)) md3)
    (treac_arbitrate_post fq regs ly S W mem md t our fsm pace now out T P).
Proof.
induction k as [|k IH]; intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b regs3 mem3 md3 Hk HPRE HL.
- exfalso. pose proof HL as (_ & _ & _ & _ & Hi & _). lia.
- apply (arb_segL fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P i b regs3 mem3 md3 _ HPRE HL).
  + intros regs4 mem4 md4 HL4.
    apply (IH fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P (i + 1) (reac_arbitrate.scanz T P our now (i + 1)) regs4 mem4 md4); [lia | exact HPRE | exact HL4].
  + intros regs4 mem4 md4 HP4. exact (arb_segP fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P _ regs4 mem4 md4 HPRE HP4).
Qed.

Theorem pb_reac_arbitrate : treac_arbitrate_spec.
Proof.
unfold treac_arbitrate_spec.
intros fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P
  HPRE HROD H10 H11 H12 H13 H14 H15 Rt Rour Rfsm Rpace Rnow Rout Hbo Hbo1 Hbo2 Ho4 HT HP.
assert (HA : arb_pre ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P)
  by (repeat (split; [assumption|]); exact HP).
apply (arb_segA fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P _ HA).
- intros regs3 mem3 md3 HL. exact (arb_loop _ fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P 0 None regs3 mem3 md3 eq_refl HA HL).
- intros regs3 mem3 md3 HP3. exact (arb_segP fq ly S W regs mem md ch t our fsm pace now out bt Nt bp Np bo No T P None regs3 mem3 md3 HA HP3).
Qed.

End h.
End f.
End d.
