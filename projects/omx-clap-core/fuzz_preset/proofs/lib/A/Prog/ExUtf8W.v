(* fuzz_preset, both images: the IMAGE-FREE part of the walk of ex_utf8 / put_utf8 (fuzz_preset.c :130-156), shared by
   the image walks (lib/B/Prog/ExUtf8WB.v: image B', #102 pin). Generic over the listing L and its image instance
   PA : PAImg L: the model's four arms (PjGrammar.utf8), the symbolic entry state (atoms 2 sp, 10 o, 11 cp, 32 the
   shadow base; the k bytes at o writable) and its proof u8_entry, the byte-shape lemmas for the stored chunks, the
   per-run post u8_post with its memnorm keep (u8_P / u8_plaw, the memory invariant of YC1fPx's _inv runners), the
   passage to the text's fpostm (u8_to_fpost, bound to the text on the kit's cut 7cdbb61b5fa0 lib/A/PRH_FnReader.v:290-303:
   ledger with most / own carried by S1Ledger.v's prh_ledger_frame, fpostm's memnorm keep, room_live_cf, S' = S), and
   the run-finishing tactics u8_awr / u8_byte. What is NOT here is what computes on a listing: the runs themselves
   (paj_run_tok_x_inv vm_computes over the concrete listing), one file per image.
   WHY THE SPLIT CARRIES TO IMAGE B (measured, WalkS8b): the B bodies are NOT image A's - UBSan adds pointer checks
   (ex_utf8 B 148 instructions against A's 130: a `beqz a0` null check before each first store and `beq a0,-1` /
   `bltu -3,a0` / `bltu -4,a0` overflow checks, each to an `unimp` trap; put_utf8 B 143, the overflow checks only), so
   no A proof is a B proof. But THE A AND B RUN SCRIPTS ARE THE SAME TEXT: the entry facts (4096 <= o, o + k < 2 ^ 47)
   decide every UBSan branch inside the engine, so no case gains a branch. "Parametric in the entry pc" covers the two
   entries WITHIN one image (ex_utf8 / put_utf8 have one body in A), never A to B.
   Form: YCbqG's afn_pre_x / apost_base_x over the allocator relation ARx; every conclusion of the image files is SRr
   (srealizes, YA0n.v). Helpers u8_low_byte_mod .. u8_region_nth are ported from a Theorem Labs lane's put_utf8_xw.v
   (a working branch cfcf4ad0554, handed over by a Theorem Labs lane). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the model: PjGrammar.utf8, its four arms ---- *)
Lemma u8_arm1 : forall cp, 0 <= cp < 128 -> PjGrammar.utf8 cp = [cp].
Proof. intros cp H. unfold PjGrammar.utf8. rewrite (proj2 (Z.ltb_lt _ _) (proj2 H)). reflexivity. Qed.
Lemma u8_arm2 : forall cp, 128 <= cp < 2048 -> PjGrammar.utf8 cp = [192 + cp / 64; 128 + cp mod 64].
Proof.
  intros cp H. unfold PjGrammar.utf8.
  rewrite (proj2 (Z.ltb_ge cp 128) ltac:(lia)), (proj2 (Z.ltb_lt cp 2048) ltac:(lia)). reflexivity.
Qed.
Lemma u8_arm3 : forall cp, 2048 <= cp < 65536 ->
  PjGrammar.utf8 cp = [224 + cp / 4096; 128 + (cp / 64) mod 64; 128 + cp mod 64].
Proof.
  intros cp H. unfold PjGrammar.utf8.
  rewrite (proj2 (Z.ltb_ge cp 128) ltac:(lia)), (proj2 (Z.ltb_ge cp 2048) ltac:(lia)), (proj2 (Z.ltb_lt cp 65536) ltac:(lia)).
  reflexivity.
Qed.

Lemma u8_arm4 : forall cp, 65536 <= cp ->
  PjGrammar.utf8 cp = [240 + cp / 262144; 128 + (cp / 4096) mod 64; 128 + (cp / 64) mod 64; 128 + cp mod 64].
Proof.
  intros cp H. unfold PjGrammar.utf8.
  rewrite (proj2 (Z.ltb_ge cp 128) ltac:(lia)), (proj2 (Z.ltb_ge cp 2048) ltac:(lia)), (proj2 (Z.ltb_ge cp 65536) ltac:(lia)).
  reflexivity.
Qed.

(* ---- the symbolic entry state: atoms 2 sp, 10 o, 11 cp, 32 the shadow base; the k bytes at o writable ---- *)
Definition U8_BX : sv := SOff 32 0.
Definition U8_SPAN : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition u8_regions (k : Z) : smem :=
  [stack_region 16; got_regionP; bcell_regionP 32; YP09.mkRegion (Some 10%nat) 0 k 0 k []].
Definition ss_u8 (eo k lo hi : Z) (cs : list acond) : sstate :=
  mkSS eo sr_atoms (u8_regions k) None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 16) 0); (11%nat, mkAF lo hi 0);
              (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] cs []).
Definition u8_SH (k : Z) : list shent := [mkSHE 10 0 k].

(* ---- image-free helpers, ported from a Theorem Labs lane's put_utf8_xw.v (a working branch cfcf4ad0554,
   handed over by a Theorem Labs lane): a stored chunk read back as a value, the low byte arithmetic ---- *)
Lemma u8_low_byte_mod : forall u n k, 0 <= u -> (k < n)%nat ->
  Z_to_bv 8 (Z.shiftr (u mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) = Z_to_bv 8 (Z.shiftr u (8 * Z.of_nat k)).
Proof.
  intros u n k Hu Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i 8) as [Hl|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma u8_val_of_chunk : forall {fx : YK11.FPState} segs E mem base off (n : N) (e : sv),
  YP09.chunk_ok segs E mem base (YP09.mkChunk off (CVal n e)) -> (Z.of_N n <= 8) ->
  val_mem segs mem (base + off) (N.to_nat n) (U E e mod 2 ^ (8 * Z.of_N n)).
Proof.
  intros fx segs E mem base off n e H Hn k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val c_len cv_len] in H.
  pose proof (N_nat_Z n) as Hnn.
  destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. unfold YP09.byte_of_word in Hb1.
  injection Hb1 as <-. rewrite Hb2. f_equal. unfold U.
  pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Hu. change (bv_modulus 64) with (2 ^ 64) in Hu.
  set (u := bv_unsigned (sv_denot E e)) in *.
  assert (Hm : 0 <= u mod 2 ^ (8 * Z.of_N n) < 2 ^ (8 * Z.of_nat (N.to_nat n))).
  { rewrite Hnn. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
  rewrite (le_byte_small _ _ _ Hm Hk). rewrite <- Hnn. symmetry. apply u8_low_byte_mod; [lia | exact Hk].
Qed.
Lemma u8_field_of_region : forall {fx : YK11.FPState} {segs : list Segment} E m n b cs lo hi wlo whi od (w : N) e,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem segs m (b + od) (N.to_nat w) (U E e mod 2 ^ (8 * Z.of_N w)).
Proof.
  intros fx segs E m n b cs lo hi wlo whi od w e (_ & _ & _ & Hcs) Hn Hc Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
  exact (u8_val_of_chunk segs E m b od w e Hck Hw).
Qed.
Lemma u8_region_nth : forall {fx : YK11.FPState} segs E ss ms i r,
  st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
  intros fx segs E ss ms i r HS Hi. destruct (st_ok_mem_ok segs E ss ms HS) as (_ & Hrs & _).
  exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma u8_low_canon : forall x, zcanon x mod 256 = x mod 256.
Proof.
  intros x. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
  rewrite (Z.mod_eq x 18446744073709551616) by lia.
  replace (x - 18446744073709551616 * (x / 18446744073709551616)) with (x + (- (72057594037927936 * (x / 18446744073709551616))) * 256) by lia.
  apply Z.mod_add. lia.
Qed.
Lemma u8_lor_low : forall x k, 0 <= k <= 8 -> 0 <= x < 2 ^ k -> Z.lor x (2 ^ 64 - 2 ^ k) mod 256 = x + (256 - 2 ^ k).
Proof.
  intros x k Hk Hx.
  assert (H2k : 1 <= 2 ^ k <= 256) by (split; [apply (Z.pow_le_mono_r 2 0 k); lia | apply (Z.pow_le_mono_r 2 k 8); lia]).
  assert (Hand : Z.land x (2 ^ 64 - 2 ^ k) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec i k) as [Hl|Hge].
    - replace (2 ^ 64 - 2 ^ k) with ((2 ^ (64 - k) - 1) * 2 ^ k) by (rewrite Z.mul_sub_distr_r, <- Z.pow_add_r by lia; f_equal; f_equal; lia).
      rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - destruct (Z.eq_dec x 0) as [->|Hnz]; [rewrite Z.bits_0; reflexivity|].
      rewrite (Z.bits_above_log2 x i); [reflexivity | lia |].
      apply (Z.lt_le_trans _ k); [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite <- Z.lxor_lor by exact Hand. rewrite <- Z.add_nocarry_lxor by exact Hand.
  replace (x + (2 ^ 64 - 2 ^ k)) with (x + (256 - 2 ^ k) + 72057594037927935 * 256) by (change (2 ^ 64) with 18446744073709551616; lia).
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma u8_sll_srl : forall cp s, 0 <= cp -> 0 <= s <= 58 ->
  Z.shiftr (Z.shiftl cp s mod 2 ^ 64) 58 = (cp / 2 ^ (58 - s)) mod 64.
Proof.
  intros cp s Hcp Hs. rewrite <- Z.shiftr_div_pow2 by lia. change 64 with (2 ^ 6) at 2.
  apply Z.bits_inj'. intros i Hi. rewrite Z.shiftr_spec by lia.
  destruct (Z_lt_le_dec i 6) as [Hl|Hge].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftl_spec by lia.
    rewrite Z.shiftr_spec by lia. f_equal. lia.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma u8_zc : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.
Lemma u8_land63 : forall s, 0 <= s < 64 -> Z.land s 63 = s.
Proof. intros s Hs. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 6) with 64. lia. Qed.
(* the three byte shapes the engine leaves in the stored chunks *)
Lemma u8_bA : forall E cp s c k r, ew E 11 = Z_to_bv 64 cp -> 0 <= cp < 2 ^ 21 -> 0 <= s < 64 -> 0 <= k <= 8 ->
  c = 2 ^ k -> cp / 2 ^ s < 2 ^ k -> r = cp / 2 ^ s + (256 - c) ->
  U E (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit s)) (SLit (- c))) mod 256 = r.
Proof.
  intros E cp s c k r H11 Hcp Hs Hk Hc Hlt Hr.
  rewrite !U_SAlu, !U_SLit. rewrite (U_atom E 11 cp H11) by lia. cbn [zalu_raw].
  rewrite u8_low_canon. rewrite (u8_zc s) by lia. rewrite u8_land63 by lia. rewrite Z.shiftr_div_pow2 by lia.
  assert (Hq : 0 <= cp / 2 ^ s) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  assert (H2k : 1 <= 2 ^ k <= 256) by (split; [apply (Z.pow_le_mono_r 2 0 k); lia | apply (Z.pow_le_mono_r 2 k 8); lia]).
  rewrite (u8_zc (cp / 2 ^ s)) by lia.
  replace (zcanon (- c)) with (2 ^ 64 - 2 ^ k)
    by (unfold zcanon, M64; subst c; rewrite <- (Z.mod_add (- 2 ^ k) 1 (2 ^ 64)) by lia; rewrite Z.mod_small; lia).
  rewrite u8_lor_low by lia. lia.
Qed.
Lemma u8_bB : forall E cp r, ew E 11 = Z_to_bv 64 cp -> 0 <= cp < 2 ^ 21 -> r = 128 + cp mod 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))) mod 256 = r.
Proof.
  intros E cp r H11 Hcp Hr.
  rewrite !U_SAlu, !U_SLit. rewrite (U_atom E 11 cp H11) by lia. cbn [zalu_raw].
  rewrite u8_low_canon. rewrite (u8_zc 63) by lia.
  change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64.
  pose proof (Z.mod_pos_bound cp 64 ltac:(lia)) as Hm.
  rewrite (u8_zc (cp mod 64)) by lia. change (zcanon (-128)) with 18446744073709551488.
  replace (cp mod 64 + 18446744073709551488) with (cp mod 64 + 128 + 72057594037927935 * 256) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma u8_bC : forall E cp sh r, ew E 11 = Z_to_bv 64 cp -> 0 <= cp < 2 ^ 21 -> 0 <= sh <= 58 ->
  r = 128 + (cp / 2 ^ (58 - sh)) mod 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit sh)) (SLit 58)) (SLit (-128))) mod 256 = r.
Proof.
  intros E cp sh r H11 Hcp Hsh Hr.
  rewrite !U_SAlu, !U_SLit. rewrite (U_atom E 11 cp H11) by lia. cbn [zalu_raw].
  rewrite u8_low_canon. rewrite (u8_zc sh) by lia. rewrite (u8_zc 58) by lia. rewrite !u8_land63 by lia.
  change (zcanon (Z.shiftl cp sh)) with (Z.shiftl cp sh mod 2 ^ 64).
  rewrite u8_sll_srl by lia.
  pose proof (Z.mod_pos_bound (cp / 2 ^ (58 - sh)) 64 ltac:(lia)) as Hm.
  rewrite (u8_zc ((cp / 2 ^ (58 - sh)) mod 64)) by lia. change (zcanon (-128)) with 18446744073709551488.
  replace ((cp / 2 ^ (58 - sh)) mod 64 + 18446744073709551488) with ((cp / 2 ^ (58 - sh)) mod 64 + 128 + 72057594037927935 * 256) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma u8_garr8_cons : forall segs (m : word -> option byte) p v L,
  val_mem segs m p 1 v -> 0 <= v < 256 -> garr8 segs m (p + 1) L -> garr8 segs m p (v :: L).
Proof.
  intros segs m p v L Hv Hr HG j Hj. destruct j as [|j].
  - cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [exact Hv | exact Hr].
  - cbn [nth]. cbn in Hj. destruct (HG j ltac:(lia)) as [Hv' Hr']. split; [|exact Hr'].
    replace (p + Z.of_nat (S j)) with (p + 1 + Z.of_nat j) by lia. exact Hv'.
Qed.


Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation SEGS := (@pa_segs _ L PA).
#[local] Abbreviation VAL := (@pa_val _ L PA).
#[local] Abbreviation BASE := (@pa_val _ L PA A_TEXT).
Definition EU (regs : bvmap 5 word) : env := @Eimg _ L PA (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the image binding of the shadow base (YC1fP.v PALibCore: A_OBJ 0 is its GOT word, A_OBJ 12 its cell) *)
Hypothesis TL : PALibCore (PI := PA) B.
(* image fact: the shadow-base GOT word and the shadow cell lie in the image *)
Hypothesis HOBJ : forall i a, (i = 0 \/ i = 12)%nat -> VAL (A_OBJ i) <= a < VAL (A_OBJ i) + 8 -> in_img SEGS a.
Let HBgot := palc_got_shadow (PI := PA) B TL.
Let HBcell := palc_cell (PI := PA) B TL.

Lemma u8_srlw16 : forall cp, 0 <= cp < 2 ^ 21 -> zalu32 ALU_SRL cp 16 = cp / 65536.
Proof.
  intros cp H. unfold zalu32, zalu_raw, zu32, M32, zcanon, M64.
  rewrite (Z.mod_small cp (2 ^ 32)) by lia. change (Z.land (16 mod 2 ^ 32) 31) with 16.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
  assert (Hq : 0 <= cp / 65536 < 32) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  unfold bv_swrap. change (bv_half_modulus 32) with 2147483648.
  unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  rewrite (Z.mod_small (cp / 65536 + 2147483648) 4294967296) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma u8_srlw16_U : forall E cp, ew E 11 = Z_to_bv 64 cp -> 0 <= cp < 2 ^ 21 ->
  U E (SAluw ALU_SRL (SOff 11 0) (SLit 16)) = cp / 65536.
Proof.
  intros E cp H11 Hcp. unfold U.
  change (sv_denot E (SAluw ALU_SRL (SOff 11 0) (SLit 16)))
    with (sext 64 (alu32 ALU_SRL (low32 (sv_denot E (SOff 11 0))) (low32 (sv_denot E (SLit 16))))).
  assert (Hs : sv_denot E (SOff 11 0) = Z_to_bv 64 cp).
  { apply bv_eq. rewrite denot_SOff, H11, !unsigned_lit_small by lia. rewrite Z.add_0_r.
    unfold zcanon, M64. apply Z.mod_small. lia. }
  rewrite Hs. change (sv_denot E (SLit 16)) with (Z_to_bv 64 16).
  rewrite zalu32_sound, u8_srlw16 by lia. rewrite unsigned_lit_small; [reflexivity|].
  split; [apply Z.div_pos | apply (Z.lt_trans _ 32); [apply Z.div_lt_upper_bound|]]; lia.
Qed.
Lemma u8_c3 : forall regs cp, getr regs 11 = w64 cp -> 2048 <= cp <= 65535 ->
  conds_ok (EU regs) [mkAC BC_EQ (SAluw ALU_SRL (SOff 11 0) (SLit 16)) (SLit 0)].
Proof.
  intros regs cp H11 Hcp. split; [|exact I].
  change (branch_taken BC_EQ (sv_denot (EU regs) (SAluw ALU_SRL (SOff 11 0) (SLit 16))) (sv_denot (EU regs) (SLit 0)) = true).
  assert (E11 : ew (EU regs) 11 = Z_to_bv 64 cp)
    by (unfold EU; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  rewrite branch_eq_U, (u8_srlw16_U _ cp E11) by lia.
  change (U (EU regs) (SLit 0)) with (zcanon 0).
  rewrite (Z.div_small cp 65536) by lia. reflexivity.
Qed.
Lemma u8_c4 : forall regs cp, getr regs 11 = w64 cp -> 65536 <= cp < 2 ^ 21 ->
  conds_ok (EU regs) [mkAC BC_NE (SAluw ALU_SRL (SOff 11 0) (SLit 16)) (SLit 0)].
Proof.
  intros regs cp H11 Hcp. split; [|exact I].
  change (branch_taken BC_NE (sv_denot (EU regs) (SAluw ALU_SRL (SOff 11 0) (SLit 16))) (sv_denot (EU regs) (SLit 0)) = true).
  assert (E11 : ew (EU regs) 11 = Z_to_bv 64 cp)
    by (unfold EU; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  rewrite branch_ne_U, (u8_srlw16_U _ cp E11) by lia.
  change (U (EU regs) (SLit 0)) with (zcanon 0).
  assert (Hq : 1 <= cp / 65536) by (apply (Z.div_le_lower_bound cp 65536 1); lia).
  apply negb_true_iff. apply Z.eqb_neq. unfold zcanon, M64. rewrite Z.mod_0_l by lia. lia.
Qed.

Lemma u8_entry : forall ly S Hp W regs mem md ch STK o cp eo k lo hi cs b m,
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> 16 <= STK ->
  getr regs 10 = w64 o -> getr regs 11 = w64 cp -> lo <= cp <= hi -> 0 <= lo -> hi < 2 ^ 64 ->
  In (b, m) (ablocks B ly S) -> b <= o -> o + k <= b + m -> 0 < k ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF o k ->
  conds_ok (EU regs) cs -> regions_wf (u8_regions k) = true ->
  st_ok_pi SEGS VAL (EU regs) (ss_u8 eo k lo hi cs)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + eo)) mem (seg_rom SEGS))) /\
  sh_ok SEGS U8_BX (u8_SH k) (EU regs) (mrestrict (w_H W) mem).
Proof.
  intros ly S Hp W regs mem md ch STK o cp eo k lo hi cs b m HPRE HSTK H10 H11 Hcp Hlo Hhi Hbb Hbo Hon Hk HRA Hcs Hwf.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hbb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
  assert (HrL : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (palc_got_cell (PI := PA) B TL) as HgcD.
  pose proof (@pa_val_range _ _ PA (A_OBJ 0)) as R0. pose proof (@pa_val_range _ _ PA (A_OBJ 12)) as R12.
  assert (I0 : forall a, VAL (A_OBJ 0) <= a < VAL (A_OBJ 0) + 8 -> in_img SEGS a) by (intros a Ha; apply (HOBJ 0); [left; reflexivity | exact Ha]).
  assert (I12 : forall a, VAL (A_OBJ 12) <= a < VAL (A_OBJ 12) + 8 -> in_img SEGS a) by (intros a Ha; apply (HOBJ 12); [right; reflexivity | exact Ha]).
  pose proof (@pa_segs_low _ _ PA (VAL (A_OBJ 0)) (I0 (VAL (A_OBJ 0)) ltac:(lia))) as L0. pose proof (@pa_segs_low _ _ PA (VAL (A_OBJ 0) + 7) (I0 (VAL (A_OBJ 0) + 7) ltac:(lia))) as L0'.
  pose proof (@pa_segs_low _ _ PA (VAL (A_OBJ 12)) (I12 (VAL (A_OBJ 12)) ltac:(lia))) as L12. pose proof (@pa_segs_low _ _ PA (VAL (A_OBJ 12) + 7) (I12 (VAL (A_OBJ 12) + 7) ltac:(lia))) as L12'.
  assert (D0 : o + k <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= o).
  { destruct (Z_le_gt_dec (o + k) (VAL (A_OBJ 0))); [left; lia|]. destruct (Z_le_gt_dec (VAL (A_OBJ 0) + 8) o); [right; lia|]. exfalso.
    destruct (alx_client_img _ _ _ LAWS ly S Hp W mem md (Z.max o (VAL (A_OBJ 0))) HAR) as [_ Hni];
    [left; exists b, m; split; [exact Hbb | lia] | apply Hni, I0; lia]. }
  assert (D12 : o + k <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= o).
  { destruct (Z_le_gt_dec (o + k) (VAL (A_OBJ 12))); [left; lia|]. destruct (Z_le_gt_dec (VAL (A_OBJ 12) + 8) o); [right; lia|]. exfalso.
    destruct (alx_client_img _ _ _ LAWS ly S Hp W mem md (Z.max o (VAL (A_OBJ 12))) HAR) as [_ Hni];
    [left; exists b, m; split; [exact Hbb | lia] | apply Hni, I12; lia]. }
  unfold kLowMemEnd in *.
  set (E := EU regs) in *.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
    by (intros n Hn; subst E; unfold EU; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 o) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 cp) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold EU; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EU; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  split.
  - rewrite restrict_mkst_fx. unfold ss_u8. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + exact Hwf.
    + unfold u8_regions, stack_region, got_regionP, bcell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
      * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
      * rewrite (VB 10%nat o E10) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
        intros a Ha. apply (apresent_writable SEGS). apply (proj1 (Hbpres (o + a) ltac:(lia))).
    + apply pairwise_disjoint_of_extents. unfold u8_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 10%nat o E10) by lia.
      rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0) by lia.
      rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by lia.
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [|split; [exact Hcs | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E11, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold spZ in *.
      repeat match goal with |- _ /\ _ => split end; try lia.
  - unfold sh_ok, u8_SH. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W) mem E U8_BX 10 o k o 0 k).
    + exact HRA.
    + unfold U8_BX. rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia). reflexivity.
    + rewrite (U_atom E 10 o E10) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* the core post at any of the two entries: back at ra, the journal at window STK and footprint [o, o + |bs|), the
   bytes bs at o, a0 = |bs|, every byte outside the window and the footprint as it was, and memnorm kept *)
Definition u8_post (STK : Z) (regs : bvmap 5 word) ly S Hp (W : world SEGS) mem md (o : Z) (bs : list Z)
  : world SEGS -> config -> Prop :=
  apost_base_x (SK := SK) SEGS B PST ARx STK [(o, o + Z.of_nat (length bs))] regs ly S Hp W mem md
    (fun ly' S' Hp' W' regs' mem' md' =>
       ly' = ly /\ S' = S /\ Hp' = Hp /\ W' = W /\
       getr regs' 10 = w64 (Z.of_nat (length bs)) /\
       garr8 SEGS (mrestrict (w_H W) mem') o bs /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> ~ (o <= a < o + Z.of_nat (length bs)) ->
          aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) /\
       (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem')).
End g.

(* the memory invariant a run carries (YC1fPx's _inv runners): memnorm of the entry memory memc is kept
   (YSRrMemnorm.srr_inv_laws_imp over srr_inv_laws_memnorm_k, as ExUtf8RunB.v exu_P / exu_plaw) *)
Definition u8_P (segs : list Segment) (memc : word -> option byte) : (word -> option byte) -> Prop :=
  fun m => YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs m.
Lemma u8_plaw : forall segs memc, srr_inv_laws segs (u8_P segs memc).
Proof.
  intros segs memc. exact (YSRrMemnorm.srr_inv_laws_imp segs _ memc (YSRrMemnorm.srr_inv_laws_memnorm_k segs)).
Qed.

(* the write permission of a run's regions: the 16-byte frame, the two read-only cells, the k bytes at o (footprint,
   inside the block (b, m)) *)
Ltac u8_awr :=
  lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end;
  lazymatch goal with Usp : bv_unsigned (ew _ 2) = spZ _, Eu10 : bv_unsigned (ew _ 10) = ?o, Hbb : In (?b, ?m) _,
    HrL : ?m <= req_size ?m |- _ =>
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat o); [reflexivity | exact Eu10 | | apply awr_ok_nil];
  cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; left; split;
  [ eexists; split; [left; reflexivity | cbn [fst snd length Z.of_nat Pos.of_succ_nat]; lia]
  | exists b, m; split; [exact Hbb | lia] ]
  end.

(* one stored byte of the run's region 3, read back: val_mem at o + od of the value v the shape lemma gives *)
Ltac u8_byte HR3 Ex o od e v Hv V :=
  pose proof (u8_field_of_region Ex _ 10%nat o _ _ _ _ _ od 1%N e HR3 ltac:(cbn [ew ewset Nat.eqb]; assumption)
    ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
  change (N.to_nat 1) with 1%nat in V; change (2 ^ (8 * Z.of_N 1)) with 256 in V; rewrite Hv in V.

Section t0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation SEGS := (@pa_segs _ L PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* image fact: alloc.c's statics are image bytes *)
Hypothesis HPST : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.
(* the head is at least one shadow granule wide (PRH_Base.v prh_head_wide) *)
Hypothesis HW : prh_head_wide.

(* from the walk's post to the text's (cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) PRH_FnReader.v tput_utf8_specX's post): the ledger survives by
   S1Ledger.v prh_ledger_frame (statics and harness heads off the window and the footprint, the blocks and Hp
   unchanged), memnorm by u8_post's keep, the rest is read off *)
Lemma u8_to_fpost : forall STK regs ly S Hp W mem md ch o u b m Lam peak cnt fail ran most own W' c',
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> 16 <= STK ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> b <= o -> o + Z.of_nat (length (PjGrammar.utf8 u)) <= b + m -> (In b Hp -> b + cf_head <= o) ->
  u8_post (SK := SK) (PA := PA) B prh_pst ARx STK regs ly S Hp W mem md o (PjGrammar.utf8 u) W' c' ->
  fpostm (PA := PA) B ARx SK STK [(o, o + Z.of_nat (length (PjGrammar.utf8 u)))] regs ly S Hp W mem md
    (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       getr regs' 10 = w64 (Z.of_nat (length (PjGrammar.utf8 u))) /\ bytes_at (PA := PA) W' mem' o (PjGrammar.utf8 u) /\
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger (PA := PA) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own) W' c'.
Proof.
  intros STK regs ly S Hp W mem md ch o cp0 b m Lam peak cnt fail ran most own W' c' HPRE HSTK HLG Hbb Hbo Hon Hhd
    (ly' & S' & Hp' & regs' & mem' & md' & k' & Hc & HJ & HP & -> & -> & -> & -> & Ha0 & Hby & Hfr & Hmn).
  pose proof HW as HW8. unfold prh_head_wide in HW8.
  pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & _).
  pose proof asan_consts as (C1 & _ & _ & _ & C5).
  assert (Hm0 : 0 <= m) by lia.
  pose proof (req_size_pos m Hm0) as Rm.
  pose proof (prh_ledger_blocks (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own HLG) as HF.
  (* the bytes the ledger reads (statics, harness heads) are off the stack window and the footprint *)
  assert (KEEP : forall a, (Exists (in_zr a) prh_pst \/ exists ak, In ak Lam /\ fst ak - cf_head <= a < fst ak - cf_head + 8) ->
    aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a).
  { intros a [Hst | (ak & Hak & Ha)].
    - pose proof (HPST a Hst) as Hi. pose proof (@pa_segs_low _ _ PA a Hi) as Hlowa. rewrite C5 in Hlowa.
      apply Hfr; [lia | lia |].
      intros Hoa. destruct (alx_client_img _ _ _ LAWS ly S Hp W mem md a HAR) as [_ Hni];
        [left; exists b, m; split; [exact Hbb | lia] | exact (Hni Hi)].
    - pose proof (proj1 (Forall_forall _ _) HF ak Hak) as (K0 & K1 & K2 & _).
      destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR K1) as (_ & Hh4096 & Hhceil & _).
      assert (Hn0 : 0 <= snd ak + cf_head) by lia.
      pose proof (req_size_pos _ Hn0) as Rh.
      apply Hfr; [lia | lia |].
      intros Hoa.
      destruct (Z.eq_dec b (fst ak - cf_head)) as [Eb | Nb].
      + subst b. specialize (Hhd K2). lia.
      + pose proof (sep_blocks_x _ _ _ LAWS ly S Hp W mem md b m (fst ak - cf_head) (snd ak + cf_head) HAR Hbb K1
          ltac:(intros Heq; injection Heq as Heq _; exact (Nb Heq))) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  exists ly, S, Hp, regs', mem', md', k'. split; [exact Hc|]. split; [exact HJ|]. split; [exact HP|].
  split; [|exact Hmn].
  split; [intros HR; exact HR|].
  split; [exact Ha0|]. split; [exact Hby|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  apply (prh_ledger_frame (PA := PA) B ly S Hp W mem ly S Hp W mem' Lam peak cnt fail ran peak cnt fail ran most own HLG).
  - eapply prh_glob_kept; [eapply prh_ledger_glob; exact HLG |].
    intros a Ha. apply prh_mbyte_of_aview. apply KEEP. left. exact Ha.
  - intros a k i Hin Hi. apply prh_mbyte_of_aview. apply KEEP. right. exists (a, k). split; [exact Hin | cbn [fst snd]; lia].
  - intros a k _ Hin. exact Hin.
  - apply Permutation_refl.
Qed.
End t0.
