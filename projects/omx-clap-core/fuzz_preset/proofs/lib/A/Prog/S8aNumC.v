(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 asan 1be0f53d, twin bff8519b), ex_value piece 5 (ev_number), lane C:
   ev_C_stmt of S8aNumCut.v, the sub-piece CS (+0x8c0, 0x83b64) -> CR (+0x924, 0x83bc8): in->scratch's shadow check,
   __asan_memcpy (scratch, x0 + i1, j - i1), in's shadow check, the scratch byte's 1-byte check and its NUL store,
   strtod (scratch, &end). Listing 0x83b64 .. 0x83bc4 (25 slots) and the report arms 0x83ff8 (+0xd54), 0x84000 (+0xd5c)
   and the slow arm 0x83ea4 .. 0x83eac (+0xc00) (the engine discharges the three ASan checks; no arm is reached).
   Engine: YC80x / YC1fPx runners carrying memnorm (YSRrMemnorm's paj_run_x_inv, paj_run_to_x_inv) over YCbqG's
   ajournal_x at the cut's float state fxc, three runs:
     seg 1  +0x8c0 -> the __asan_memcpy call slot +0x8e4,
     seg 2  +0x8e8 (memcpy's return) -> +0x900 (the address of the NUL byte is in a0),
     seg 3  +0x900 -> the strtod call slot +0x920.
   The calls: YGcallMxmn.aj_intrin_at_xm (OCpy, CPY := aintrin_realizes_xm) and the strtod ROW
   YStrtodRowX.astrtod_realizes_x (ev_C_stmt's premise, at the image I, its site clause strtod_site_x from the caller
   facts ev_strtod_site I of S8aNumCut.v: the GOT view by AR_laws_x's alx_const_cells at the call state and
   srx_got_b_sound, as lib/B/Prog/PvB_ND.v; and the carried memnorm); the journal after strtod (which may write errno)
   by evc_journal_errno below.
   MEMNORM: ev_mid's last conjunct `YAkMemnorm.memnorm segs mem` (YAkMemnorm.memnorm by conversion) is a STATE fact,
   carried from CS to CR: the three runs by YSRrMemnorm's paj_run_x_inv / paj_run_to_x_inv (P := YAkMemnorm.memnorm
   SEGS, laws srr_inv_laws_memnorm_k; seg 3 holds the NUL store), __asan_memcpy by aj_intrin_at_xm's keep, strtod by
   astrtod_realizes_x's post keep (aj_memnorm mem -> aj_memnorm mem'). It is the memnorm premise of each MIDK use,
   strtod_site_x's aj_memnorm at the call, and CR's MID. No memnorm hypothesis.
   Section hypotheses: LAWS (the allocator's AR_laws_x at head length hl), Hent (ex_value's listing offset;
   A_entry_ex_value at PI_prog_A) and MIDK (lane M's ev_mid_keep_stmt). The image facts ev_img_ok and errno-in-image
   are premises of ev_C_stmt itself.
   rule 24: done for the piece (proof-index ex_value ex_number strtod checked_memcpy, index 2026-10-28T04:13:31Z;
   checker R24CheckNum2 "NUM: CONFIRM"): no released file is Required and no released lemma is cited.
   Numerals (brief rule 4): 7364 (DERIVED: ex_value's slot 1841 * 4 in A_prog_listing); 0x8c0 0x8e8 0x900 0x924
   (LENGTH: offsets into ex_value, measured from the internal file ex_value.fuzz_preset.asan.s); 24 32 96 104 112 120 128
   (LENGTH: struct ex field offsets and their extent, the s1-relative spill slots, from the listing); 256 272 32 16
   (LENGTH: ex_value's `addi sp, sp, -256`, its frame with the `andi sp, sp, -32` realignment, the alignments);
   0x7fff7f800000 (DERIVED: the lower bound of alloc_ceiling, asan_consts), 2 ^ 47, 2 ^ 44, 2 ^ 64, 2 ^ 63, 2 ^ 62,
   2 ^ 32, 2 ^ 30 (LENGTH: address-space / shadow-band / text bounds); 4096 16384 (DERIVED: ESTACK, 4 * ESTACK); 8 3
   (LENGTH: the shadow granule and its log); 18446744073709551615 and -1 (WORD: 2 ^ 64 - 1, the engine's negation
   form); register and atom numbers (WORD: RISC-V register numbers; DERIVED: the engine's atom numbering, 240 = A_TEXT,
   32 33 the extra atoms). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallMx YI67.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0a YStrtodRowX YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aNumCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ======== the symbolic states of the three runs (closed terms; vm_compute runs the engine over them) ======== *)

(* ex_value's entry as an offset from the listing's base (DERIVED: slot 1841 * 4) *)
Definition EVC_K0 : Z := 7364.
Definition evc_k (off : Z) : Z := EVC_K0 + off.
(* s8 (atom 24) holds SHADOW_OFF; the shadow band is [SHADOW_OFF, SHADOW_OFF + 2 ^ 44) *)
Definition EVC_Bx : sv := SOff 24 0.
Definition EVC_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the lower bound of alloc_ceiling (asan_consts): every real-stack byte is at or above it *)
Definition EVC_CEIL : Z := 0x7fff7f800000.
Definition EVC_TOP : Z := 2 ^ 47 - 64.
Definition EVC_TOPQ : Z := 2 ^ 47 - 40.
(* the shadow address of atom n + c in the form the instrumented code computes it: ((n + c) >> 3) + s8 *)
Definition shx (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 24 0).

Definition fa_s1 : nat * afact := (9%nat, mkAF EVC_CEIL EVC_TOP 5).
Definition fa_q : nat * afact := (19%nat, mkAF EVC_CEIL EVC_TOPQ 3).
Definition fa_bx : nat * afact := (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
Definition fa_b : nat * afact := (10%nat, mkAF 4096 EVC_TOP 0).

(* seg 1 at +0x8c0: atoms 9 s1, 19 s3 = q, 24 s8, 11 a1 = x0 + i1, 22 s6 = x0 + j, 32 = in->scratch;
   the two spill slots s1 + 96 and s1 + 120 the code writes, in->scratch read *)
Definition r1_a : YP09.region := YP09.mkRegion (Some 9%nat) 96 104 96 104 [].
Definition r1_b : YP09.region := YP09.mkRegion (Some 9%nat) 120 128 120 128 [].
Definition r1_q : YP09.region := YP09.mkRegion (Some 19%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition ss1 : sstate := mkSS (evc_k 0x8c0) sr_atoms [r1_a; r1_b; r1_q] None (mkFacts [fa_s1; fa_q; fa_bx] [] []).
(* in's first 32 bytes (p, end, depth, scratch) are addressable: the 8-byte checks of q + 24 (0x83b78) and q (0x83b8c) *)
Definition SH12 : list shent := [mkSHE 19 0 32].
(* seg 2 at +0x8e8: s10 = shadow (q) in the code's form; 32 = in->p = x0 + i1, 33 = in->scratch *)
Definition r2_q : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 32 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 0))].
Definition ss2 : sstate :=
  mkSS (evc_k 0x8e8) (sr_set sr_atoms 26%bv (shx 19 0)) [r2_q] None (mkFacts [fa_s1; fa_q; fa_bx] [] []).
(* seg 3 at +0x900: a0 (atom 10) = scr + (j - i1), the NUL byte; s1 + 120 holds q + 24; 32 = in->scratch *)
Definition r3_b : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 1 [].
Definition r3_sp : YP09.region := YP09.mkRegion (Some 9%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 19 24))].
Definition r3_q : YP09.region := YP09.mkRegion (Some 19%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition ss3 : sstate :=
  mkSS (evc_k 0x900) sr_atoms [r3_b; r3_sp; r3_q] None (mkFacts [fa_s1; fa_q; fa_bx; fa_b] [] []).
(* the NUL byte is addressable: its 1-byte check (0x83bac, slow arm 0x83ea4) *)
Definition SH3 : list shent := [mkSHE 10 0 1].
(* the registers each cut carries and every run and call keeps (ev_regs, s5, s6, s7, s11) *)
Definition EVC_KL : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Definition EVC_KL26 : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 27%bv].

(* ======== bytes, words, pure arithmetic ======== *)

Lemma evc_byte_eq : forall v (n k : nat), (k < n)%nat -> (n <= 8)%nat ->
  Z_to_bv 8 (YG0f.le_byte v n k) = byte_of_word (Z_to_bv 64 v) (Z.of_nat k).
Proof.
intros v n k Hk Hn. unfold byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64). unfold YG0f.le_byte.
apply Z.bits_inj'. intros j Hj. change 256 with (2 ^ 8). rewrite !YO0a.testbit_mod_pow2 by lia.
destruct (j <? 8) eqn:E; [|reflexivity]. apply Z.ltb_lt in E.
rewrite !Z.shiftr_spec by lia. rewrite !YO0a.testbit_mod_pow2 by lia.
replace (j + 8 * Z.of_nat k <? 8 * Z.of_nat n) with true by (symmetry; apply Z.ltb_lt; nia).
replace (j + 8 * Z.of_nat k <? 64) with true by (symmetry; apply Z.ltb_lt; nia). reflexivity.
Qed.

Lemma evc_skipn_S : forall (x : list Z) i, (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof. induction x as [|h t IH]; intros [|i] Hi; cbn in *; try lia; [reflexivity | apply IH; lia]. Qed.

(* the text strtod reads: every byte of x[i1, j) is a number character (the sign is one) *)
Lemma evc_numch_txt : forall (x : list Z) i1 c j, nth i1 x 0 = c -> (i1 < j <= length x)%nat ->
  Forall (fun z => PjGrammar.numch z = true) (ev_sub x (i1 + ev_sg c) j) ->
  Forall (fun z => PjGrammar.numch z = true) (ev_sub x i1 j).
Proof.
intros x i1 c j Hc Hj H. unfold ev_sg in H. destruct (Z.eqb_spec c 45) as [E|E].
- unfold ev_sub in *. rewrite (evc_skipn_S x i1) by lia.
  replace (j - i1)%nat with (S (j - S i1)) by lia. cbn [firstn]. constructor.
  + rewrite Hc, E. reflexivity.
  + replace (i1 + 1)%nat with (S i1) in H by lia. exact H.
- rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma evc_txt_len : forall (x : list Z) i1 j, (i1 <= j <= length x)%nat ->
  Z.of_nat (length (ev_sub x i1 j)) = Z.of_nat j - Z.of_nat i1.
Proof. intros x i1 j H. unfold ev_sub. rewrite firstn_length, skipn_length, Nat.min_l by lia. lia. Qed.

Lemma evc_sub_canon : forall u v, 0 <= u <= v -> v < 2 ^ 64 ->
  zcanon (zcanon (u * zcanon (-1)) + v) = v - u.
Proof.
intros u v Huv Hv. unfold zcanon, M64. rewrite Z.add_mod_idemp_l by lia.
change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (u * (2 ^ 64 - 1) + v) with ((v - u) + u * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma evc_sub_canon2 : forall u v s, 0 <= u <= v -> v < 2 ^ 64 -> 0 <= s -> s + (v - u) < 2 ^ 64 ->
  zcanon (zcanon (v + zcanon (u * zcanon 18446744073709551615)) + s) = s + (v - u).
Proof.
intros u v s Huv Hv Hs Hsv. unfold zcanon, M64.
change (18446744073709551615 mod 2 ^ 64) with (2 ^ 64 - 1).
replace (u * (2 ^ 64 - 1)) with (- u + u * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. rewrite Z.add_mod_idemp_r by lia. rewrite Z.add_mod_idemp_l by lia.
rewrite Z.mod_small by lia. lia.
Qed.

Lemma evc_U_sub : forall E u v, ew E 11 = Z_to_bv 64 u -> ew E 22 = Z_to_bv 64 v -> 0 <= u <= v -> v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SLit (-1))) (SOff 22 0)) = Z_to_bv 64 (v - u).
Proof.
intros E u v Hu Hv Huv Hv64. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SMd, (U_atom E 11 u Hu), (U_atom E 22 v Hv), U_SLit by lia. cbn [zalu_raw zmd_raw].
apply evc_sub_canon; lia.
Qed.

Lemma evc_U_add : forall E u v s, ew E 32 = Z_to_bv 64 u -> ew E 22 = Z_to_bv 64 v -> ew E 33 = Z_to_bv 64 s ->
  0 <= u <= v -> v < 2 ^ 64 -> 0 <= s -> s + (v - u) < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 22 0) (SMd M_MUL (SOff 32 0) (SLit 18446744073709551615))) (SOff 33 0)) =
  Z_to_bv 64 (s + (v - u)).
Proof.
intros E u v s Hu Hv Hs Huv Hv64 Hs0 Hsv. rewrite denot_lit_U. f_equal.
rewrite !U_SAlu, U_SMd, (U_atom E 32 u Hu), (U_atom E 22 v Hv), (U_atom E 33 s Hs), U_SLit by lia.
cbn [zalu_raw zmd_raw]. apply evc_sub_canon2; lia.
Qed.

Lemma evc_U_shx : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  ew E 24 = Z_to_bv 64 SHADOW_OFF -> sv_denot E (shx n c) = Z_to_bv 64 (shadow_addr (x + c)).
Proof.
intros E n c x Hn Hx Hxc H24. apply bv_eq.
change (bv_unsigned (sv_denot E (shx n c))) with (U E (shx n c)). unfold shx.
rewrite !U_SAlu, (U_atom_off E n x c Hn Hx Hxc), U_SLit, (U_atom E 24 SHADOW_OFF H24) by (unfold SHADOW_OFF; lia).
cbn [zalu_raw]. change (zcanon 3) with 3. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 3) with 8. rewrite Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64, shadow_addr, SHADOW_OFF.
change (bv_modulus 64) with (2 ^ 64).
assert (0 <= (x + c) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small ((x + c) / 8)) by lia. rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma evc_amem_sub : forall p n p' n', amem_range p n -> p <= p' -> p' + n' <= p + n -> amem_range p' n'.
Proof. unfold amem_range. intros. lia. Qed.

Lemma evc_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

Lemma evc_pres : forall r r', aregs_preserved r r' -> forall x : bv 5, acallee_saved (bv_unsigned x) -> getr r' x = getr r x.
Proof. intros r r' H x Hx. rewrite <- (Z_to_bv_bv_unsigned 5 x). exact (H _ Hx). Qed.

Lemma evc_pres_l : forall r r', aregs_preserved r r' -> forall x, In x EVC_KL -> getr r' x = getr r x.
Proof.
intros r r' H x Hx. apply (evc_pres r r' H). unfold acallee_saved.
unfold EVC_KL in Hx. repeat (destruct Hx as [<-|Hx];
  [match goal with |- context [bv_unsigned ?b] => let v := eval vm_compute in (bv_unsigned b) in
     change (bv_unsigned b) with v end; lia|]). destruct Hx.
Qed.

Lemma evc_lin : forall x m, 0 < m -> x mod m = 0 -> exists t, x = m * t.
Proof. intros x m Hm H. exists (x / m). pose proof (Z.div_mod x m ltac:(lia)). lia. Qed.

(* s1, the body's sp: `addi sp, sp, -256; andi sp, sp, -32` from a 16-aligned sp0 *)
Lemma evc_S1 : forall sp0, sp0 mod 16 = 0 ->
  (exists t, (sp0 - 256) - (sp0 - 256) mod 32 = 32 * t) /\
  sp0 - 272 <= (sp0 - 256) - (sp0 - 256) mod 32 <= sp0 - 256.
Proof.
intros sp0 H. pose proof (Z.div_mod (sp0 - 256) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (sp0 - 256) 32 ltac:(lia)) as M1.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
split; [exists ((sp0 - 256) / 32); lia | lia].
Qed.

(* ex_value's stack allowance covers its frame and strtod's window *)
Lemma evc_stk {PI : PrhImg} : forall n, 272 <= pi_frame F_ex_value -> 272 + 16384 <= STK_ex_value n.
Proof.
intros n H. unfold STK_ex_value.
assert (Hm : 16384 <= zmaxl [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; STK_ex_string; STK_ex_word; STK_ex_ws]).
{ unfold zmaxl. cbn [fold_right]. unfold STK_RT_STRTOD, ESTACK. lia. }
assert (Hn1 : 1 <= Z.of_nat (Datatypes.S n)) by lia.
nia.
Qed.

Section mem. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

Lemma evc_chunk_of_val : forall E m base off (w : N) e v, (w <= 8)%N -> sv_denot E e = Z_to_bv 64 v ->
  val_mem segs m (base + off) (N.to_nat w) v -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal w e)).
Proof.
intros E m base off w e v Hw He Hv i Hi. unfold YP09.c_len, YP09.cv_len in Hi. cbn [YP09.c_val YP09.c_off] in *.
exists (byte_of_word (sv_denot E e) i). split; [reflexivity|].
pose proof (Hv (Z.to_nat i) ltac:(lia)) as H. rewrite Z2Nat.id in H by lia. rewrite H.
f_equal. rewrite He. replace i with (Z.of_nat (Z.to_nat i)) at 2 by lia. apply evc_byte_eq; lia.
Qed.

Lemma evc_vm_keep : forall H (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> aview segs H m' (a + Z.of_nat k) = aview segs H m (a + Z.of_nat k)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof. intros H m m' a n v HK HV k Hk. rewrite (mbyte_of_aview segs H H m m' _ (HK k Hk)). exact (HV k Hk). Qed.

Lemma evc_garr8_aview : forall H m p l j, garr8 segs (mrestrict H m) p l -> (j < length l)%nat ->
  aview segs H m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m p l j G Hj. unfold aview. rewrite (garr8_mbyte segs _ p l j G Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (G j Hj)).
Qed.

Lemma evc_mb_move : forall H H' (m m' : word -> option byte) a b v,
  aview segs H' m' a = aview segs H m b -> mbyte segs (mrestrict H m) b = Some v -> mbyte segs (mrestrict H' m') a = Some v.
Proof.
intros H H' m m' a b v HA V. unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte segs (mrestrict H' m') a) as [b'|] eqn:Eb; cbn [option_map] in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

Lemma evc_garr8_move : forall H H' m m' x d l, garr8 segs (mrestrict H m) x l ->
  (forall j, (j < length l)%nat -> aview segs H' m' (d + Z.of_nat j) = aview segs H m (x + Z.of_nat j)) ->
  garr8 segs (mrestrict H' m') d l.
Proof.
intros H H' m m' x d l G HA j Hj. destruct (G j Hj) as [V R]. split; [|exact R].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
exact (evc_mb_move H H' m m' _ _ _ (HA j Hj) V).
Qed.

(* the scratch after the copy and the NUL store: x[i1, i1 + n) ++ [0] *)
Lemma evc_garr8_build : forall H m m' x0 (x : list Z) i1 n scr,
  garr8 segs (mrestrict H m) x0 x -> (i1 + n <= length x)%nat ->
  (forall j, (j < n)%nat -> aview segs H m' (scr + Z.of_nat j) = aview segs H m (x0 + Z.of_nat (i1 + j))) ->
  val_mem segs (mrestrict H m') (scr + Z.of_nat n) 1 0 ->
  garr8 segs (mrestrict H m') scr (firstn n (skipn i1 x) ++ [0]).
Proof.
intros H m m' x0 x i1 n scr G Hn HA HZ j Hj.
rewrite length_app, firstn_length, skipn_length, Nat.min_l in Hj by lia. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j n) as [Hjn|Hjn].
- rewrite app_nth1 by (rewrite firstn_length, skipn_length; lia).
  rewrite nth_firstn, nth_skipn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hjn).
  destruct (G (i1 + j)%nat ltac:(lia)) as [V R]. split; [|exact R].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
  specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
  exact (evc_mb_move H H m m' _ _ _ (HA j Hjn) V).
- assert (j = n) by lia. subst j.
  rewrite app_nth2 by (rewrite firstn_length, skipn_length; lia).
  rewrite firstn_length, skipn_length, Nat.min_l, Nat.sub_diag by lia. cbn [nth]. split; [exact HZ | lia].
Qed.

Lemma evc_aview_of_frame : forall H (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict H m) (mrestrict H m') -> ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview segs H m' a = aview segs H m a.
Proof.
intros H E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
End mem.

(* ======== the journal after strtod (errno may change); the stack struct's shadow ======== *)
Section je. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis ERRIMG : forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a.

(* ajournal_x_after_write (YCbqG.v:298-416) with errno allowed to change as well, Sc / Hpc / own unchanged:
   the errno word is in the image, so below alloc_ceiling and the frame shadows, off every block and frame;
   the image and ly_extra clauses exclude it by their own premise. *)
Lemma evc_journal_errno : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  ARx lyc Sc Hpc Wc memc' mdc' ->
  ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr HJ Heqw Hgr Hsame HW HAR'.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HE : forall a, as_errno B <= a < as_errno B + 4 -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (segs_low a (ERRIMG a Ha))).
assert (HWw : forall a, Wr a ->
~ aowned B lyc Sc a /\
((alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)))))).
{ intros a Ha.
  exact (awr_byte_cases_x (SK := SK) segs B PST ARx LAWS STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k a HJ (HW a Ha)). }
split; [exact HAR'|].
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split.
{ (* above alloc_ceiling, off the stack window *)
  intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [zlia | |].
  - intros HWa.
    destruct (HWw a HWa) as (_ & [[_ Hs'] | [[[_ Hlow] _] | (cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]])]]);
    [exact (Hs Hs') | zlia | zlia | zlia].
  - intros He. pose proof (HE a He). zlia. }
split.
{ (* bytes of a block live at both ends *)
  intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
  destruct (alx_blocks segs B ARx LAWS lyc Sc Hpc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
  apply Heqw; [zlia | |].
  - intros HWa.
    destruct (HWw _ HWa) as (_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]).
    + zlia.
    + exact (Hnf Hfp).
    + assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
      pose proof (sep_blocks_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
    + assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
      pose proof (sep_block_frame_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
      unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in Hd, Hr. zlia.
    + zlia.
  - intros He.
    exact (blk_img_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc p n (p + i) HAR H2 ltac:(zlia) (ERRIMG _ He)). }
split.
{ (* the image, errno excluded by the clause's premise *)
  intros a Hi Hns He Hpst Hsp. rewrite <- (F3 a Hi Hns He Hpst Hsp). pose proof (segs_low a Hi) as Hal'.
  apply Heqw; [zlia | | exact He]. intros HWa.
  destruct (HWw a HWa) as (_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]).
  - zlia.
  - exact (blk_img_x segs B ARx LAWS _ _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
  - assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
    unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img_x segs B ARx LAWS _ _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
  - zlia. }
split.
{ (* the caller's frames and their shadow *)
  intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
  assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. rewrite <- ?Efa in Hr.
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(zlia)) as Hse.
  apply Heqw; [zlia | |].
  - intros HWa.
    destruct (HWw _ HWa) as (_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]).
    + zlia.
    + destruct Hr as [Hr | Hr]; [|zlia].
      pose proof (sep_block_frame_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
    + apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
      assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
      { eapply (sep_frames_pos_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
        rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
      destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc c' p' HAR
        ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity)) as (Hf0' & Hfc' & Hfh').
      pose proof (shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
      pose proof (fs_frame_bytes_nonneg c') as Hnn'.
      destruct Hr' as [[[Hlo0' Hlo'] Hr'] | [[Hlo1' Hhi'] Hr']]; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'.
      * destruct Hr as [Hr | Hr]; [zlia | zlia].
      * destruct Hr as [Hr | Hr]; [zlia |].
        destruct Hd as [Hd | Hd].
        -- pose proof (shadow_mono _ _ Hd). zlia.
        -- pose proof (shadow_mono _ _ Hd). zlia.
  - intros He. pose proof (HE a He) as Hea.
    destruct Hr as [Hr | Hr]; [|zlia].
    exact (frm_img_x segs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos a HAR HinC Hr (ERRIMG _ He)). }
split; [exact Hgone|].
split; [intros a Ha; apply Hgr; apply Hpres, Ha|].
split; [exact Hstatic|]. split; [|exact HQT].
{ (* ly_extra, errno excluded by the clause's premise *)
  intros a HXa He. rewrite <- (F5 a HXa He).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
  assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
  pose proof (alx_extra segs B ARx LAWS lyc Sc Hpc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
  assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; zlia).
  apply Heqw; [exact Ha64 | | exact He]. intros HWa.
  destruct (HWw a HWa) as (_ & [[Hc' Hs'] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] Hr]])]]).
  - apply Xs. rewrite Eslo, Eshi. zlia.
  - exact (Xb b m Hbin Hr).
  - assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
    unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (proj1 (Xf cid pos Hin') Hr).
  - assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
    unfold in_zr in Hr; cbn [fst snd] in Hr. exact (proj2 (Xf cid pos Hin') Hr). }
Qed.

(* the first 32 bytes of a struct on the real stack read shadow 0 (alx_zshadow over the stack range, the first
   element of zero_shadow_ranges B ly, YG0n.v:188-189); 8-aligned q with q + 40 <= ly_stk_hi ly *)
Lemma evc_stk_zs : forall ly S Hp W mem md q,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= q -> q + 40 <= ly_stk_hi ly -> q mod 8 = 0 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 32.
Proof.
intros ly S Hp W mem md q HAR Hlo Hhi Hq x Hx.
pose proof (alx_zshadow segs B ARx LAWS ly S Hp W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  ltac:(hnf; left; reflexivity)) as Hz.
unfold zero_shadow in Hz. cbn [fst snd] in Hz.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(lia)) as Dlo. pose proof (Z.mod_pos_bound (ly_stk_lo ly) 8 ltac:(lia)) as Mlo.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as Dl.
pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as Ml.
specialize (Hz (x / 8 - ly_stk_lo ly / 8) ltac:(lia)).
unfold shadow_of_addr in *.
replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + ly_stk_lo ly / 8 + (x / 8 - ly_stk_lo ly / 8)) by lia.
exact Hz.
Qed.
End je.

(* ======== the registers every cut of the piece carries ======== *)
Section kp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
Definition evc_keep (a : ev_act) (regs : bvmap 5 word) (j : nat) : Prop :=
  ev_regs a regs /\ getr regs 21 = w64 (-1) /\ getr regs 22 = w64 (ea_x0 a + Z.of_nat j) /\
  getr regs 23 = w64 (ea_fr a) /\ getr regs 27 = w64 (ea_fr a + 32).
Lemma evc_keep_tr : forall a r r' j, evc_keep a r j -> (forall x, In x EVC_KL -> getr r' x = getr r x) -> evc_keep a r' j.
Proof.
intros a r r' j ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26) & R21 & R22 & R23 & R27) HK.
unfold evc_keep, ev_regs.
repeat split; (rewrite HK; [assumption | unfold EVC_KL; cbn [In]; intuition]).
Qed.
Lemma evc_keep_tr26 : forall a r r' j, evc_keep a r j -> (forall x, In x EVC_KL26 -> getr r' x = getr r x) ->
  getr r' 26 = w64 (shadow_addr (ea_q a)) -> evc_keep a r' j.
Proof.
intros a r r' j ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26) & R21 & R22 & R23 & R27) HK H26.
unfold evc_keep, ev_regs.
repeat split; try exact H26; (rewrite HK; [assumption | unfold EVC_KL26; cbn [In]; intuition]).
Qed.
Lemma evc_keep_pres : forall a r r' j, evc_keep a r j -> aregs_preserved r r' -> evc_keep a r' j.
Proof. intros a r r' j H HP. apply (evc_keep_tr a r r' j H). exact (evc_pres_l r r' HP). Qed.
End kp.

(* a register of the state after a run whose symbolic value is still atom n of the run's environment: its value
   before the run (Er : ew E n = getr regs r) *)
Ltac rk_goal HS Er :=
  lazymatch goal with |- getr (ms_regs ?m) ?r = _ =>
    let H := fresh "Hrk" in prreg HS r H; rewrite H; apply Er; reflexivity end.
Ltac rk_all HS Er KL :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; unfold KL in Hx; cbn [In] in Hx;
  repeat (destruct Hx as [<-|Hx]; [rk_goal HS Er|]); destruct Hx.

(* ======== the sub-piece ======== *)
Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the allocator's laws (the instance's AR_laws_x) *)
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* image fact: ex_value's entry is slot 1841 (PAImg_prog.v A_entry_ex_value at PI_prog_A) *)
Hypothesis Hent : SIGMA AS_ex_value = BASE + EVC_K0.
(* lane M's statement: ev_mid across the piece's own writes *)
Hypothesis MIDK : forall a, ev_mid_keep_stmt (PA := PA) B ARx SK a.

#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Lemma evc_ew_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (@Eimg _ A_prog_listing PA (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (u5_range r) as Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs extra n r Hn).
Qed.
Lemma evc_ew32 : forall regs w0 rest, ew (@Eimg _ A_prog_listing PA (Ereg regs (w0 :: rest))) 32 = w0.
Proof. intros. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity. Qed.
Lemma evc_ew33 : forall regs w0 w1 rest, ew (@Eimg _ A_prog_listing PA (Ereg regs (w0 :: w1 :: rest))) 33 = w1.
Proof. intros. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity. Qed.

Lemma ev_C_holds : ev_C_stmt (PA := PA) B ARx SK.
Proof.
unfold ev_C_stmt, ev_img_ok. intros HFR ERRIMG SI STR SITE CPY a KRa.
unfold KS. intros fxc W regs mem md ly S Hp k i1 c j HPRE HFX HCS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCS as (HMID & HBASE & HSCAN & HSPAN & Hj & Hjend & R22 & HFSH).
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _).
pose proof HMID as (HJ & HSP & HHp & HBL & HLED & HCUR & HSRC & HWD & HTREE & HSAV & HFLAG & HRL & HRP & HMN0).
(* MID's last conjunct, the memory normal form, as the runs' invariant P := YAkMemnorm.memnorm SEGS (by conversion) *)
assert (HPM : YAkMemnorm.memnorm SEGS mem) by exact HMN0. clear HMN0.
pose proof HBASE as (HREGS & R23 & Hi1 & Hc & Hws & Hskip & Hc34 & Hc91 & Hc123 & Hc102 & Hc110 & Hc116 & V104).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof HSCAN as (R27 & V112 & R21 & R11 & R12).
pose proof HPRE as (HFP & Hfrm & Hcnt & HPa0 & HPa1 & HCUR0 & Hq8 & Hchap & Hspq & Hqd & HFWIN & HSRC0 & HINX & Hlen &
  Hi0 & Hdep & Hdepn & Hdl & HWD0 & HINS & HSX & HSQ & HTR0 & HLED0 & HPmn).
pose proof HFP as (HAFN & _).
pose proof HAFN as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal0 & HSTKn & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & HSTKd & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
pose proof HCUR as (Vp & Ve & Vdep & Vscr & Vdl).
pose proof HWD as (Hscr0 & Hscrc & Hscram & Hscrw & Hscrra & Hscrhv).
pose proof HSRC as (Hxg & Hx4096 & Hxc & Hxam & Hxra & Hxhv).
(* ---- the geometry ---- *)
assert (Esp0 : ea_sp0 a = spZ (ea_regs a)) by reflexivity.
assert (Elen : ea_len a = Z.of_nat (length (ea_x a))) by reflexivity.
destruct (evc_S1 (ea_sp0 a) ltac:(rewrite Esp0; exact Hal0)) as ((tS & EtS) & HS1lo).
change ((ea_sp0 a - 256) - (ea_sp0 a - 256) mod 32) with (ea_S1 a) in EtS, HS1lo.
destruct (evc_lin _ 16 ltac:(lia) Hal0) as (tsp & Etsp).
destruct (evc_lin _ 16 ltac:(lia) Hd16) as (td & Etd).
destruct (evc_lin _ 8 ltac:(lia) Hq8) as (tq & Etq).
clear Hal0 Hd16 Hal Hq8.
pose proof (evc_stk (ea_n a) HFR) as HSTK. change (STK_ex_value (ea_n a)) with (ea_STK a) in HSTK.
assert (Hi1j : (i1 < j <= length (ea_x a))%nat) by lia.
set (nZ := Z.of_nat j - Z.of_nat i1).
set (txt := ev_sub (ea_x a) i1 j).
assert (Htxtlen : Z.of_nat (length txt) = nZ) by (apply evc_txt_len; lia).
assert (Hn32 : 1 <= nZ <= ea_len a) by lia.
(* the scratch block and the text block (at the current state: ablocks unchanged) *)
destruct HINS as (bs & mss & Hbs & Hbs1 & Hbs2 & _).
rewrite <- HBL in Hbs.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md bs mss HAR Hbs) as (_ & Hbs4096 & Hbsc & [Hbsa1 Hbsa2] & _ & _).
assert (Hrs : req_size mss = mss) by (unfold req_size; destruct (Z.eqb_spec mss 0); lia).
rewrite Hrs in Hbsc.
destruct (HINX ltac:(lia)) as (bx & mxx & Hbx & Hbx1 & Hbx2 & _).
rewrite <- HBL in Hbx.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md bx mxx HAR Hbx) as (_ & Hbx4096 & Hbxc & _ & _ & _).
assert (Hrx : req_size mxx = mxx) by (unfold req_size; destruct (Z.eqb_spec mxx 0); lia).
rewrite Hrx in Hbxc.
(* the own frame (1, pos) *)
assert (HinF : In (1, ea_pos a) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFr : frame_addr ly 1 (ea_pos a) = ea_fr a) by (unfold ea_fr, frame_addr; rewrite EF; reflexivity).
assert (Ef1 : fs_frame_bytes 1 = 128) by reflexivity.
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 1 (ea_pos a) HAR HinF) as (Hfr4096 & Hfrc & Hfrapp).
rewrite ?EFr, ?Ef1 in Hfr4096, Hfrc, Hfrapp.
pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md bs mss 1 (ea_pos a) HAR Hbs HinF) as Hsbf.
unfold zdisjoint in Hsbf. cbn [fst snd] in Hsbf. rewrite EFr, Ef1, Hrs in Hsbf.
pose proof (Zle_0_nat i1) as Hi10. pose proof (Zle_0_nat j) as Hj0.
(* ======== seg 1: +0x8c0 -> the __asan_memcpy call slot ======== *)
remember (@Eimg _ A_prog_listing PA (Ereg regs [w64 (ea_scr a)])) as E1 eqn:HE1.
assert (E1r : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs r)
  by (intros n r Hn; subst E1; apply evc_ew_reg; exact Hn).
assert (E1x : ew E1 32 = w64 (ea_scr a)) by (subst E1; apply evc_ew32).
assert (HEI1 : img_env VAL A_LIM E1) by (subst E1; apply Eimg_env).
assert (RO1 : regs_ok E1 sr_atoms regs) by (subst E1; apply regs_ok_Eimg_Ereg).
clear HE1.
assert (U1_9 : bv_unsigned (ew E1 9) = ea_S1 a) by (rewrite (E1r 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E1_19 : ew E1 19 = w64 (ea_q a)) by (rewrite (E1r 19%nat 19%bv eq_refl); exact R19).
assert (E1_24 : ew E1 24 = w64 SHADOW_OFF) by (rewrite (E1r 24%nat 24%bv eq_refl); exact R24).
assert (U1_19 : bv_unsigned (ew E1 19) = ea_q a) by (rewrite E1_19; apply unsigned_lit_small; lia).
assert (U1_24 : bv_unsigned (ew E1 24) = SHADOW_OFF) by (rewrite E1_24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HS1 : st_ok_pi (fx := fxc) SEGS VAL E1 ss1
  (restrict (w_H W) (mkst (fx := fxc) regs (Z_to_bv 64 (BASE + evc_k 0x8c0)) mem (seg_rom SEGS)))).
{ unfold ss1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact RO1.
  - vm_compute. reflexivity.
  - unfold r1_a, r1_b, r1_q. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U1_9, ?U1_19.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (evc_chunk_of_val SEGS E1 _ (ea_q a) 24 8 (SOff 32 0) (ea_scr a)); [lia | | exact Vscr].
      rewrite denot_lit_U. rewrite (U_atom E1 32 (ea_scr a) E1x) by lia. reflexivity.
  - unfold r1_a, r1_b, r1_q. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U1_9, ?U1_19. repeat split; lia.
  - split; [|split; [exact I | exact I]]. unfold fa_s1, fa_q, fa_bx. cbn [f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U1_9, U1_19, U1_24. unfold EVC_CEIL, EVC_TOP, EVC_TOPQ.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    repeat split; lia. }
assert (SHOK1 : sh_ok SEGS EVC_Bx SH12 E1 (mrestrict (w_H W) mem)).
{ unfold sh_ok, SH12. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  unfold EVC_Bx. rewrite !U_SOff, U1_24, U1_19, !Z.add_0_r.
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  split.
  - change (YCbn.rd_of SEGS (mrestrict (w_H W) mem)) with (aview SEGS (w_H W) mem). rewrite Z.sub_0_r.
    apply (evc_stk_zs SEGS B ARx LAWS ly S Hp W mem md (ea_q a) HAR); lia.
  - intros a0 Ha0. unfold SHADOW_OFF. lia. }
pose (RUN := @paj_run_x_inv fxc rc SK A_prog_listing PL_prog_A PA B (@prh_pst PI) ARx _ LAWS (YAkMemnorm.memnorm SEGS)
  (srr_inv_laws_memnorm_k SEGS)).
pose (RUNTO := @paj_run_to_x_inv fxc rc SK A_prog_listing PL_prog_A PA B (@prh_pst PI) ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS)).
unfold ev_cfg, ev_pc. rewrite Hent.
replace (BASE + EVC_K0 + 0x8c0) with (BASE + evc_k 0x8c0) by (unfold evc_k; lia).
pose proof HJ as HJa.
paj_run_tok_x_inv RUN HS1 HJa SHOK1 HPM EVC_Bspan.
{ intros a0 (r & Hin & Ha0). vm_compute in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha0;
    rewrite ?U1_9, ?U1_19 in Ha0; unfold awr_byte; [left; lia | left; lia | lia]. }
(* ---- at the __asan_memcpy call slot +0x8e4 ---- *)
lazymatch type of HS1 with context [restrict _ ?m] => rename m into ms1 end.
clear HF HG.
pmkst HS1.
assert (K1 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_S1 a + 96 <= z < ea_S1 a + 104) -> ~ (ea_S1 a + 120 <= z < ea_S1 a + 128) ->
  aview SEGS (w_H W) (ms_mem ms1) z = aview SEGS (w_H W) mem z).
{ intros z Hz Hn1 Hn2. apply (evc_aview_of_frame SEGS (w_H W) E1 (ss_mem ss1) mem (ms_mem ms1) z HFr); [|exact Hz].
  intros (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | [<- | [<- | []]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U1_9, ?U1_19 in Hr; lia. }
clear HFr.
assert (RK1 : forall x, In x EVC_KL -> getr (ms_regs ms1) x = getr regs x) by (rk_all HS1 E1r EVC_KL).
assert (T11 : getr (ms_regs ms1) 11 = getr regs 11) by rk_goal HS1 E1r.
rewrite R11 in T11.
prreg HS1 (10%bv : bv 5) T10. rewrite E1x in T10.
prreg HS1 (1%bv : bv 5) T1.
pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 12%bv HS1) as T12.
lazymatch type of T12 with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
  change (sr_get (ss_regs ssx) 12%bv) with (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SLit (-1))) (SOff 22 0)) in T12 end.
rewrite (evc_U_sub E1 (ea_x0 a + Z.of_nat i1) (ea_x0 a + Z.of_nat j)) in T12;
  [| rewrite (E1r 11%nat 11%bv eq_refl); exact R11 | rewrite (E1r 22%nat 22%bv eq_refl); exact R22 | lia | lia].
replace (ea_x0 a + Z.of_nat j - (ea_x0 a + Z.of_nat i1)) with nZ in T12 by (unfold nZ; lia).
lazymatch type of HS1 with st_ok _ ?Ex ?ssx _ =>
  let rga := eval vm_compute in (nth 0 (ss_mem ssx) r1_a) in
  let rgb := eval vm_compute in (nth 1 (ss_mem ssx) r1_a) in
  pose proof (st_chunk_val SEGS Ex ssx _ 0 rga 9 96 8 (shx 19 24) (ea_S1 a) (shadow_addr (ea_q a + 24)) HS1
    ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; intuition) U1_9
    (evc_U_shx E1 19 24 (ea_q a) E1_19 ltac:(lia) ltac:(lia) E1_24)
    ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(cbn; lia)) as V96;
  pose proof (st_chunk_val SEGS Ex ssx _ 1 rgb 9 120 8 (SOff 19 24) (ea_S1 a) (ea_q a + 24) HS1
    ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; intuition) U1_9
    ltac:(rewrite denot_lit_U, (U_atom_off E1 19 (ea_q a) 24 E1_19) by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as V120
end.
cbn [ms_mem restrict] in V96, V120. change (N.to_nat 8) with 8%nat in V96, V120.
assert (KW1 : forall z, 0 <= z < 2 ^ 64 -> ~ ev_wz B a z -> aview SEGS (w_H W) (ms_mem ms1) z = aview SEGS (w_H W) mem z).
{ intros z Hz Hnz. apply K1; [exact Hz | |]; intros Hb; apply Hnz; unfold ev_wz; left; unfold STK_RT_STRTOD, ESTACK; lia. }
pose proof (MIDK a ly S Hp W mem md k _ _ _ (ms_mem ms1) _ k HPRE HMID HJa KW1 HPM) as MID1.
pose proof MID1 as (_ & _ & _ & _ & _ & HCUR1 & HSRC1 & HWD1 & _ & _ & _).
pose proof HWD1 as (_ & _ & _ & Hscrw1 & Hscrra1 & Hscrhv1).
pose proof HSRC1 as (Hxg1 & _ & _ & _ & Hxra1 & Hxhv1).
assert (T2 : getr (ms_regs ms1) 2 = w64 (ea_S1 a)) by (rewrite (RK1 2%bv ltac:(cbn; intuition)); exact R2).
(* ---- the __asan_memcpy call (YGcallMxmn.aj_intrin_at_xm, CPY's memnorm keep) ---- *)
eapply SRr_bind.
{ eapply (aj_intrin_at_xm (SK := SK) SEGS B (@prh_pst PI) ARx LAWS (@pa_segs_low _ _ PA) OCpy (SIGMA AS___asan_memcpy)
    (CPY fxc) W (ms_regs ms1) (ms_mem ms1) (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a) (ea_ly a) (ea_S a)
    (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp _ k (ea_scr a) (ea_x0 a + Z.of_nat i1) nZ
    (ea_S1 a - (ea_sp0 a + ea_d a)) _ HJa).
  - exact T10.
  - exact T11.
  - exact T12.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite T2, unsigned_lit_small by lia. lia.
  - replace (ea_S1 a - (ea_sp0 a + ea_d a)) with (16 * (2 * tS - tsp - td)) by lia.
    rewrite Z.mul_comm. apply Z_mod_mult.
  - lia.
  - unfold ESTACK. lia.
  - rewrite (RK1 3%bv ltac:(cbn; intuition)), R3. exact Hgp0.
  - rewrite (RK1 4%bv ltac:(cbn; intuition)), R4. exact Htp0.
  - exact T1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - intros a0 Ha0. split.
    + unfold awr_byte. right; left. split.
      * exists (ea_scr a, ea_scr a + ea_len a + 1). split; [left; reflexivity | cbn [fst snd]; lia].
      * exists bs, mss. split; [exact Hbs | rewrite Hrs; lia].
    + unfold ESTACK. lia.
  - eapply evc_amem_sub; [exact Hscram | lia | lia].
  - eapply range_addressable_sub; [exact Hscrra1 | lia | lia].
  - intros Hn0. eapply evc_hull_sub; [exact (Hscrhv1 ltac:(lia)) | lia | lia | exact Hn0].
  - split; [lia|]. split; [lia|]. split.
    { intros a0 Ha0. split.
      - replace a0 with (ea_x0 a + Z.of_nat (Z.to_nat (a0 - ea_x0 a))) by lia.
        rewrite (evc_garr8_aview SEGS (w_H W) _ _ _ _ Hxg1) by lia. discriminate.
      - unfold spZ, ESTACK. rewrite T2, unsigned_lit_small by lia. lia. }
    split; [lia|]. split; [eapply evc_amem_sub; [exact Hxam | lia | lia]|].
    split; [eapply range_addressable_sub; [exact Hxra1 | lia | lia]|].
    intros Hn0. eapply evc_hull_sub; [exact (Hxhv1 ltac:(lia)) | lia | lia | exact Hn0]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hr2 & Hcopy & Hfr2 & Hpres2 & Hmn2).
cbv beta iota in Hcopy.
pose proof (Hmn2 HPM) as HPM2. clear HPM Hmn2. rename HPM2 into HPM.
(* ---- after __asan_memcpy: its return site +0x8e8 ---- *)
assert (KP0 : evc_keep a regs j) by (split; [exact HREGS | split; [exact R21 | split; [exact R22 | split; [exact R23 | exact R27]]]]).
pose proof (evc_keep_pres a (ms_regs ms1) regs2 j (evc_keep_tr a regs (ms_regs ms1) j KP0 RK1) HP2) as KP2.
assert (K2 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_scr a <= z < ea_scr a + nZ) -> ~ (ea_S1 a - 4096 <= z < ea_S1 a) ->
  aview SEGS (w_H W) mem2 z = aview SEGS (w_H W) (ms_mem ms1) z).
{ intros z Hz H1 H2. apply Hfr2; [exact Hz | exact H1 | intros Hb; apply H2; unfold ESTACK in Hb; lia]. }
clear Hfr2 HS1 SHOK1 RK1 T1 T2 T10 T11 T12 HP2.
set (mem1 := ms_mem ms1) in *. clearbody mem1. clear ms1.
assert (KW2 : forall z, 0 <= z < 2 ^ 64 -> ~ ev_wz B a z -> aview SEGS (w_H W) mem2 z = aview SEGS (w_H W) mem z).
{ intros z Hz Hnz. rewrite (K2 z Hz); [apply KW1; assumption | |];
  intros Hb; apply Hnz; unfold ev_wz; [right; right; right; right; right; left; lia | left; unfold STK_RT_STRTOD, ESTACK; lia]. }
pose proof (MIDK a ly S Hp W mem md k _ _ _ mem2 md2 k HPRE HMID HJ2 KW2 HPM) as MID2.
pose proof MID2 as (_ & _ & _ & _ & _ & HCUR2 & _ & _ & _ & _ & _).
pose proof HCUR2 as (Vp2 & _ & _ & Vscr2 & _).
pose proof HJ2 as (HAR2 & _).
(* ======== seg 2: +0x8e8 -> +0x900 ======== *)
remember (@Eimg _ A_prog_listing PA (Ereg regs2 [w64 (ea_x0 a + Z.of_nat i1); w64 (ea_scr a)])) as E2 eqn:HE2.
assert (E2r : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
  by (intros n r Hn; subst E2; apply evc_ew_reg; exact Hn).
assert (E2x : ew E2 32 = w64 (ea_x0 a + Z.of_nat i1)) by (subst E2; apply evc_ew32).
assert (E2y : ew E2 33 = w64 (ea_scr a)) by (subst E2; apply evc_ew33).
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (RO2 : regs_ok E2 sr_atoms regs2) by (subst E2; apply regs_ok_Eimg_Ereg).
clear HE2.
pose proof KP2 as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q24 & Q25 & Q26) & Q21 & Q22 & Q23 & Q27).
assert (E2_19 : ew E2 19 = w64 (ea_q a)) by (rewrite (E2r 19%nat 19%bv eq_refl); exact Q19).
assert (E2_24 : ew E2 24 = w64 SHADOW_OFF) by (rewrite (E2r 24%nat 24%bv eq_refl); exact Q24).
assert (E2_22 : ew E2 22 = w64 (ea_x0 a + Z.of_nat j)) by (rewrite (E2r 22%nat 22%bv eq_refl); exact Q22).
assert (U2_9 : bv_unsigned (ew E2 9) = ea_S1 a) by (rewrite (E2r 9%nat 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
assert (U2_19 : bv_unsigned (ew E2 19) = ea_q a) by (rewrite E2_19; apply unsigned_lit_small; lia).
assert (U2_24 : bv_unsigned (ew E2 24) = SHADOW_OFF) by (rewrite E2_24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (S2_26 : sv_denot E2 (shx 19 0) = w64 (shadow_addr (ea_q a))).
{ rewrite (evc_U_shx E2 19 0 (ea_q a) E2_19 ltac:(lia) ltac:(lia) E2_24). rewrite Z.add_0_r. reflexivity. }
assert (HS2 : st_ok_pi (fx := fxc) SEGS VAL E2 ss2
  (restrict (w_H W) (mkst (fx := fxc) regs2 (Z_to_bv 64 (BASE + evc_k 0x8e8)) mem2 (seg_rom SEGS)))).
{ unfold ss2. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_rereg; [exact RO2 | reflexivity | rewrite S2_26; exact Q26].
  - vm_compute. reflexivity.
  - unfold r2_q. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U2_19.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
    + apply (evc_chunk_of_val SEGS E2 _ (ea_q a) 0 8 (SOff 32 0) (ea_x0 a + Z.of_nat i1)); [lia | | rewrite Z.add_0_r; exact Vp2].
      rewrite denot_lit_U. rewrite (U_atom E2 32 _ E2x) by lia. reflexivity.
    + apply (evc_chunk_of_val SEGS E2 _ (ea_q a) 24 8 (SOff 33 0) (ea_scr a)); [lia | | exact Vscr2].
      rewrite denot_lit_U. rewrite (U_atom E2 33 _ E2y) by lia. reflexivity.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split; [exact I | exact I]]. unfold fa_s1, fa_q, fa_bx. cbn [f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U2_9, U2_19, U2_24. unfold EVC_CEIL, EVC_TOP, EVC_TOPQ.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    repeat split; lia. }
assert (SHOK2 : sh_ok SEGS EVC_Bx SH12 E2 (mrestrict (w_H W) mem2)).
{ unfold sh_ok, SH12. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  unfold EVC_Bx. rewrite !U_SOff, U2_24, U2_19, !Z.add_0_r.
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  split.
  - change (YCbn.rd_of SEGS (mrestrict (w_H W) mem2)) with (aview SEGS (w_H W) mem2). rewrite Z.sub_0_r.
    apply (evc_stk_zs SEGS B ARx LAWS ly S Hp W mem2 md2 (ea_q a) HAR2); lia.
  - intros z0 Hz0. unfold SHADOW_OFF. lia. }
pose proof HJ2 as HJb.
paj_run_to_tok_x_inv RUNTO HS2 HJb SHOK2 HPM EVC_Bspan (evc_k 0x900).
{ intros z0 (r & Hin & Hz0). vm_compute in Hin. destruct Hin as [<- | []];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hz0; lia. }
(* ---- at +0x900: a0 = the NUL byte's address ---- *)
lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
clear HF HG.
assert (K3 : forall z, 0 <= z < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms2) z = aview SEGS (w_H W) mem2 z).
{ intros z Hz. apply (evc_aview_of_frame SEGS (w_H W) E2 (ss_mem ss2) mem2 (ms_mem ms2) z HFr); [|exact Hz].
  intros (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | []];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
clear HFr.
assert (RK2 : forall x, In x EVC_KL26 -> getr (ms_regs ms2) x = getr regs2 x) by (rk_all HS2 E2r EVC_KL26).
pose proof (st_ok_pi_restrict_reg (w_H W) E2 _ ms2 26%bv HS2) as T26.
lazymatch type of T26 with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
  change (sr_get (ss_regs ssx) 26%bv) with (shx 19 0) in T26 end.
rewrite S2_26 in T26.
pose proof (st_ok_pi_restrict_reg (w_H W) E2 _ ms2 10%bv HS2) as T10b.
lazymatch type of T10b with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
  change (sr_get (ss_regs ssx) 10%bv) with
    (SAlu ALU_ADD (SAlu ALU_ADD (SOff 22 0) (SMd M_MUL (SOff 32 0) (SLit 18446744073709551615))) (SOff 33 0)) in T10b end.
rewrite (evc_U_add E2 (ea_x0 a + Z.of_nat i1) (ea_x0 a + Z.of_nat j) (ea_scr a) E2x E2_22 E2y) in T10b by lia.
replace (ea_scr a + (ea_x0 a + Z.of_nat j - (ea_x0 a + Z.of_nat i1))) with (ea_scr a + nZ) in T10b by (unfold nZ; lia).
pose proof (evc_keep_tr26 a regs2 (ms_regs ms2) j KP2 RK2 T26) as KP3.
assert (KW3 : forall z, 0 <= z < 2 ^ 64 -> ~ ev_wz B a z -> aview SEGS (w_H W) (ms_mem ms2) z = aview SEGS (w_H W) mem z).
{ intros z Hz Hnz. rewrite (K3 z Hz). exact (KW2 z Hz Hnz). }
pose proof (MIDK a ly S Hp W mem md k _ _ _ (ms_mem ms2) _ k HPRE HMID HJb KW3 HPM) as MID3.
pose proof MID3 as (_ & _ & _ & _ & _ & HCUR3 & _ & HWD3 & _ & _ & _).
pose proof HCUR3 as (_ & _ & _ & Vscr3 & _).
pose proof HWD3 as (_ & _ & _ & Hscrw3 & Hscrra3 & _).
pmkst HS2.
clear HS2 SHOK2 RK2 T26 KP2.
set (regs3 := ms_regs ms2) in *. set (mem3 := ms_mem ms2) in *. clearbody regs3 mem3. clear ms2.
(* ======== seg 3: +0x900 -> the strtod call slot +0x920 ======== *)
remember (@Eimg _ A_prog_listing PA (Ereg regs3 [w64 (ea_scr a)])) as E3 eqn:HE3.
assert (E3r : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs3 r)
  by (intros n r Hn; subst E3; apply evc_ew_reg; exact Hn).
assert (E3x : ew E3 32 = w64 (ea_scr a)) by (subst E3; apply evc_ew32).
assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
assert (RO3 : regs_ok E3 sr_atoms regs3) by (subst E3; apply regs_ok_Eimg_Ereg).
clear HE3.
pose proof KP3 as ((P2 & P3 & P4 & P8 & P9 & P18 & P19 & P24 & P25 & P26) & P21 & P22 & P23 & P27).
assert (E3_19 : ew E3 19 = w64 (ea_q a)) by (rewrite (E3r 19%nat 19%bv eq_refl); exact P19).
assert (U3_9 : bv_unsigned (ew E3 9) = ea_S1 a) by (rewrite (E3r 9%nat 9%bv eq_refl), P9; apply unsigned_lit_small; lia).
assert (U3_19 : bv_unsigned (ew E3 19) = ea_q a) by (rewrite E3_19; apply unsigned_lit_small; lia).
assert (U3_24 : bv_unsigned (ew E3 24) = SHADOW_OFF)
  by (rewrite (E3r 24%nat 24%bv eq_refl), P24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U3_10 : bv_unsigned (ew E3 10) = ea_scr a + nZ)
  by (rewrite (E3r 10%nat 10%bv eq_refl), T10b; apply unsigned_lit_small; lia).
assert (V120_3 : val_mem SEGS (rdW W mem3) (ea_S1 a + 120) 8 (ea_q a + 24)).
{ apply (evc_vm_keep SEGS (w_H W) mem1 mem3 _ 8 _); [|exact V120]. intros kk Hkk.
  rewrite (K3 _) by lia. apply K2; lia. }
assert (HS3 : st_ok_pi (fx := fxc) SEGS VAL E3 ss3
  (restrict (w_H W) (mkst (fx := fxc) regs3 (Z_to_bv 64 (BASE + evc_k 0x900)) mem3 (seg_rom SEGS)))).
{ unfold ss3. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact RO3.
  - vm_compute. reflexivity.
  - unfold r3_b, r3_sp, r3_q. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U3_10, ?U3_9, ?U3_19.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. exact (proj1 (Hscrw3 (ea_scr a + nZ + o) ltac:(lia))).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (evc_chunk_of_val SEGS E3 _ (ea_S1 a) 120 8 (SOff 19 24) (ea_q a + 24)); [lia | | exact V120_3].
      rewrite denot_lit_U, (U_atom_off E3 19 (ea_q a) 24 E3_19) by lia. reflexivity.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (evc_chunk_of_val SEGS E3 _ (ea_q a) 24 8 (SOff 32 0) (ea_scr a)); [lia | | exact Vscr3].
      rewrite denot_lit_U. rewrite (U_atom E3 32 _ E3x) by lia. reflexivity.
  - unfold r3_b, r3_sp, r3_q. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U3_10, ?U3_9, ?U3_19. repeat split; lia.
  - split; [|split; [exact I | exact I]]. unfold fa_s1, fa_q, fa_bx, fa_b. cbn [f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U3_9, U3_19, U3_24, U3_10. unfold EVC_CEIL, EVC_TOP, EVC_TOPQ.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    repeat split; lia. }
assert (SHOK3 : sh_ok SEGS EVC_Bx SH3 E3 (mrestrict (w_H W) mem3)).
{ unfold sh_ok, SH3. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  unfold EVC_Bx. rewrite !U_SOff, U3_24, U3_10, !Z.add_0_r.
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  split.
  - change (YCbn.rd_of SEGS (mrestrict (w_H W) mem3)) with (aview SEGS (w_H W) mem3). rewrite Z.sub_0_r.
    eapply range_addressable_sub; [exact Hscrra3 | lia | lia].
  - intros z0 Hz0. unfold amem_range, kLowMemEnd, kHighMemBeg in Hscram. unfold SHADOW_OFF. lia. }
pose proof HJb as HJc.
paj_run_tok_x_inv RUN HS3 HJc SHOK3 HPM EVC_Bspan.
{ intros z0 (r & Hin & Hz0). vm_compute in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hz0;
    rewrite ?U3_10, ?U3_9, ?U3_19 in Hz0; [|lia|lia].
  unfold awr_byte. right; left. split.
  - exists (ea_scr a, ea_scr a + ea_len a + 1). split; [left; reflexivity | cbn [fst snd]; lia].
  - exists bs, mss. split; [exact Hbs | rewrite Hrs; lia]. }
(* ---- at the strtod call slot +0x920 ---- *)
lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms4 end.
clear HF HG.
assert (K4 : forall z, 0 <= z < 2 ^ 64 -> z <> ea_scr a + nZ ->
  aview SEGS (w_H W) (ms_mem ms4) z = aview SEGS (w_H W) mem3 z).
{ intros z Hz Hn. apply (evc_aview_of_frame SEGS (w_H W) E3 (ss_mem ss3) mem3 (ms_mem ms4) z HFr); [|exact Hz].
  intros (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | [<- | [<- | []]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U3_10, ?U3_9, ?U3_19 in Hr; lia. }
clear HFr.
lazymatch type of HS3 with st_ok _ ?Ex ?ssx _ =>
  let rg := eval vm_compute in (nth 0 (ss_mem ssx) r3_b) in
  assert (U4 : bv_unsigned (ew Ex 10) = ea_scr a + nZ) by (cbn [ew ewset Nat.eqb]; exact U3_10);
  pose proof (st_chunk_val SEGS Ex ssx _ 0 rg 10 0 1 (SLit 0) (ea_scr a + nZ) 0 HS3
     ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; intuition) U4 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V4
end.
cbn [ms_mem restrict] in V4. change (N.to_nat 1) with 1%nat in V4. rewrite Z.add_0_r in V4.
assert (RK3 : forall x, In x EVC_KL -> getr (ms_regs ms4) x = getr regs3 x) by (rk_all HS3 E3r EVC_KL).
pose proof (evc_keep_tr a regs3 (ms_regs ms4) j KP3 RK3) as KP4.
prreg HS3 (10%bv : bv 5) T10c. rewrite E3x in T10c.
assert (T11c : getr (ms_regs ms4) 11 = getr regs3 27).
{ prreg HS3 (11%bv : bv 5) Hq11. rewrite Hq11. apply E3r. reflexivity. }
rewrite P27 in T11c.
prreg HS3 (1%bv : bv 5) T1c.
assert (KW4 : forall z, 0 <= z < 2 ^ 64 -> ~ ev_wz B a z -> aview SEGS (w_H W) (ms_mem ms4) z = aview SEGS (w_H W) mem z).
{ intros z Hz Hnz. rewrite (K4 z Hz); [exact (KW3 z Hz Hnz) |].
  intros Hb; apply Hnz; unfold ev_wz. right; right; right; right; right; left; lia. }
pose proof HJc as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
assert (G4 : garr8 SEGS (rdW W (ms_mem ms4)) (ea_scr a) (txt ++ [0])).
{ unfold txt, ev_sub. replace (j - i1)%nat with (Z.to_nat nZ) by lia.
  apply (evc_garr8_build SEGS (w_H W) mem1 (ms_mem ms4) (ea_x0 a) (ea_x a) i1 (Z.to_nat nZ) (ea_scr a) Hxg1).
  - lia.
  - intros jj Hjj. rewrite (K4 (ea_scr a + Z.of_nat jj)) by lia. rewrite (K3 _) by lia.
    rewrite (Hcopy (Z.of_nat jj)) by lia. f_equal. lia.
  - rewrite Z2Nat.id by lia. exact V4. }
assert (HNUM : Forall (fun z => PjGrammar.numch z = true) txt).
{ unfold txt. apply (evc_numch_txt (ea_x a) i1 c j Hc); [lia | exact (proj2 HSPAN)]. }
pmkst HS3.
pose proof KP4 as ((T2c & T3c & T4c & _ & _ & _ & _ & _ & _ & _) & _ & _ & _ & _).
(* ---- the strtod call: the ROW YStrtodRowX.astrtod_realizes_x at the image SI (ev_C_stmt's premise STR), with the
   caller facts ev_strtod_site SI (SITE) and the carried memnorm for its site clause strtod_site_x ---- *)
destruct SITE as (HBOI & HFOI & HGOTV & HGOTC).
assert (HSP4 : spZ (ms_regs ms4) = ea_S1 a) by (unfold spZ; rewrite T2c, unsigned_lit_small by lia; reflexivity).
(* the end cell e = fr + 32: an 8-byte slot of the live fake frame (1, pos) *)
destruct (YStrtodRowX.strtod_end_of_frame SEGS B ARx LAWS ly S Hp W (ms_mem ms4) _ (ms_regs ms4) STK_RT_STRTOD
  1 (ea_pos a) (ea_fr a + 32) HAR4 HinF ltac:(rewrite EFr; lia) ltac:(rewrite EFr, Ef1; lia)
  ltac:(rewrite Eslo; exact Hceil) ltac:(rewrite HSP4, Eslo; unfold STK_RT_STRTOD, ESTACK; lia))
  as (HEND & HE0 & HEW).
(* strtod_site_x's GOT-view clause at the call memory (the SEG_N form of lib/B/Prog/PvB_ND.v): the guard word is one
   of B's const cells (HGOTC), which AR_laws_x field 16 alx_const_cells keeps at the call's ARx state; its eight image
   bytes hold the same value (HGOTV, srx_got_b) *)
assert (HGOT : forall z, YStrtodRowX.si_got_guard SI <= z < YStrtodRowX.si_got_guard SI + 8 ->
  aview SEGS (w_H W) (ms_mem ms4) z = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 z))).
{ intros z Hz.
  pose proof (alx_const_cells SEGS B ARx LAWS _ _ _ _ _ _ HAR4) as HC.
  rewrite Forall_forall in HC. specialize (HC _ (HGOTC ly)).
  unfold YG0f.cell_holds in HC. cbn [c_at c_val c_w z8 c8 aeval] in HC.
  replace z with (YStrtodRowX.si_got_guard SI + Z.of_nat (Z.to_nat (z - YStrtodRowX.si_got_guard SI))) by lia.
  assert (Hg8 : (Z.to_nat (z - YStrtodRowX.si_got_guard SI) < 8)%nat) by lia.
  set (g8 := Z.to_nat (z - YStrtodRowX.si_got_guard SI)) in *. clearbody g8. clear Hz.
  rewrite (HC g8 Hg8), (YStrtodRowX.srx_got_b_sound SEGS _ _ g8 HGOTV Hg8). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold YG0f.le_byte. rewrite Zmod_mod. reflexivity. }
eapply SRr_bind.
{ eapply (STR fxc ly S Hp W (ms_regs ms4) (ms_mem ms4) _ (ea_scr a) (ea_fr a + 32) txt).
  - unfold ecall_pre_x. split; [exact HAR4|].
    split; [rewrite T1c; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]|].
    unfold spZ. rewrite T2c, unsigned_lit_small by lia.
    split; [lia|]. split; [rewrite Eslo; unfold ESTACK; lia|]. split; [rewrite Eshi; lia|].
    split; [intros z0 Hz0; apply Hpres4; unfold ESTACK in Hz0; lia|].
    split; [rewrite T3c; exact Hgp0 | rewrite T4c; exact Htp0].
  - rewrite HSP4, Eslo. unfold STK_RT_STRTOD, ESTACK. lia.
  - intros z0 Hz0. rewrite HSP4 in Hz0. apply Hpres4. unfold STK_RT_STRTOD, ESTACK in Hz0. lia.
  - rewrite Eslo. exact Hceil.
  - rewrite Eshi. exact H47.
  - exact T10c.
  - exact T11c.
  - exact G4.
  - unfold ev_txt_ok. split; [exact HNUM | rewrite Htxtlen; lia].
  - lia.
  - rewrite Htxtlen. lia.
  - left. rewrite HSP4, Htxtlen. unfold STK_RT_STRTOD, ESTACK. lia.
  - exact HEND.
  - exact HE0.
  - exact HEW.
  - rewrite Htxtlen. lia.
  - exact (proj1 HFX).
  - unfold YStrtodRowX.strtod_site_x. rewrite Htxtlen.
    split.
    { destruct (HBOI ly S Hp W mem md bs mss HAR Hbs) as [Hb | Hb]; [left; rewrite Hrs in Hb | right]; lia. }
    split.
    { pose proof (HFOI ly S Hp W mem md 1 (ea_pos a) HAR HinF) as Hg. rewrite EFr in Hg. lia. }
    split; [lia|].
    split; [exact HGOT|].
    (* the memory normal form at the call memory, carried from CS (YAkMemnorm.memnorm, by conversion) *)
    exact HPM. }
(* ---- strtod's return site +0x924 = CR: the post's facts by name ---- *)
cbv beta. intros W5 c5 _ (-> & fx' & regs5 & mem5 & md5 & bits & cn & -> & HSTR_frm & HSTR_fk & HSTR_fa0 &
  HSTR_model & HSTR_cn & HSTR_AR & HSTR_P & HSTR_same & HSTR_end & HSTR_frame & HSTR_win & HSTR_pres & HSTR_mn).
(* strtod's post keep: the memory normal form at its return memory *)
pose proof (HSTR_mn HPM) as HPM5. clear HSTR_mn.
assert (K5 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_fr a + 32 <= z < ea_fr a + 40) -> ~ (as_errno B <= z < as_errno B + 4) ->
  ~ (ea_S1 a - 16384 <= z < ea_S1 a) -> aview SEGS (w_H W) mem5 z = aview SEGS (w_H W) (ms_mem ms4) z).
{ intros z Hz H1 H2 H3. apply HSTR_frame; [exact Hz | intros Hb; apply H1; lia | | exact H2].
  rewrite HSP4. unfold STK_RT_STRTOD, ESTACK. intros Hb; apply H3; lia. }
assert (HJ5 : ajournal_x (SK := SK) SEGS B (@prh_pst PI) ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
  (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem5 md5 k).
{ eapply (evc_journal_errno (SK := SK) SEGS B (@prh_pst PI) ARx LAWS (@pa_segs_low _ _ PA) ERRIMG)
    with (Wr := fun z => (ea_fr a + 32 <= z < ea_fr a + 40) \/ (ea_S1 a - 16384 <= z < ea_S1 a)).
  - exact HJc.
  - intros z Hz Hn Hne. apply K5;
      [exact Hz | intros Hb; apply Hn; left; exact Hb | exact Hne | intros Hb; apply Hn; right; exact Hb].
  - exact HSTR_pres.
  - exact HSTR_same.
  - intros z [Hb | Hb]; unfold awr_byte.
    + right; right; right. exists 1, (ea_pos a). split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EFr, Ef1. lia.
    + left. lia.
  - exact HSTR_AR. }
assert (KW5 : forall z, 0 <= z < 2 ^ 64 -> ~ ev_wz B a z -> aview SEGS (w_H W) mem5 z = aview SEGS (w_H W) mem z).
{ intros z Hz Hnz. rewrite (K5 z Hz); [exact (KW4 z Hz Hnz) | | |]; intros Hb; apply Hnz; unfold ev_wz.
  - right; left; lia.
  - right; right; right; right; right; right; exact Hb.
  - left; unfold STK_RT_STRTOD, ESTACK; lia. }
pose proof (MIDK a ly S Hp W mem md k _ _ _ mem5 md5 k HPRE HMID HJ5 KW5 HPM5) as MID5.
pose proof (evc_keep_pres a (ms_regs ms4) regs5 j KP4 HSTR_P) as KP5.
pose proof KP5 as (KR5 & S21 & S22 & S23 & S27).
pose proof (@pa_segs_low _ _ PA (as_errno B) (ERRIMG (as_errno B) ltac:(lia))) as He0.
pose proof (@pa_segs_low _ _ PA (as_errno B + 3) (ERRIMG (as_errno B + 3) ltac:(lia))) as He3.
unfold kLowMemEnd in He0, He3.
assert (KS15 : forall z, ea_S1 a <= z < ea_S1 a + 128 -> aview SEGS (w_H W) mem5 z = aview SEGS (w_H W) mem1 z).
{ intros z Hz. rewrite (K5 z) by lia. rewrite (K4 z) by lia. rewrite (K3 z) by lia. apply K2; lia. }
assert (V104_5 : val_mem SEGS (rdW W mem5) (ea_S1 a + 104) 8 (ea_v a)).
{ apply (evc_vm_keep SEGS (w_H W) mem mem5 _ 8 _); [|exact V104]. intros kk Hkk.
  rewrite (KS15 _) by lia. apply K1; lia. }
assert (V112_5 : val_mem SEGS (rdW W mem5) (ea_S1 a + 112) 8 (ea_fr a + 64)).
{ apply (evc_vm_keep SEGS (w_H W) mem mem5 _ 8 _); [|exact V112]. intros kk Hkk.
  rewrite (KS15 _) by lia. apply K1; lia. }
assert (V120_5 : val_mem SEGS (rdW W mem5) (ea_S1 a + 120) 8 (ea_q a + 24)).
{ apply (evc_vm_keep SEGS (w_H W) mem1 mem5 _ 8 _); [|exact V120]. intros kk Hkk. apply KS15. lia. }
assert (V96_5 : val_mem SEGS (rdW W mem5) (ea_S1 a + 96) 8 (shadow_addr (ea_q a + 24))).
{ apply (evc_vm_keep SEGS (w_H W) mem1 mem5 _ 8 _); [|exact V96]. intros kk Hkk. apply KS15. lia. }
assert (KALL : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_S1 a - 16384 <= z < ea_S1 a + 128) ->
  ~ (ea_scr a <= z < ea_scr a + ea_len a + 1) -> ~ (ea_fr a + 32 <= z < ea_fr a + 40) ->
  ~ (as_errno B <= z < as_errno B + 4) -> aview SEGS (w_H W) mem5 z = aview SEGS (w_H W) mem z).
{ intros z Hz H1 H2 H3 H4. rewrite (K5 z Hz H3 H4) by lia. rewrite (K4 z) by lia. rewrite (K3 z) by lia.
  rewrite (K2 z) by lia. apply K1; lia. }
assert (FSH5 : aview SEGS (w_H W) mem5 (shadow_addr (ea_fr a) + 4) = Some 0 /\
  aview SEGS (w_H W) mem5 (shadow_addr (ea_fr a) + 8) = Some 0).
{ destruct HFSH as [FS4 FS8]. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfrapp, Hbsa2.
  split; [rewrite KALL; [exact FS4 | unfold shadow_addr, SHADOW_OFF; lia ..] |
          rewrite KALL; [exact FS8 | unfold shadow_addr, SHADOW_OFF; lia ..]]. }
assert (G5 : garr8 SEGS (rdW W mem5) (ea_scr a) (txt ++ [0])).
{ apply (evc_garr8_move SEGS (w_H W) (w_H W) (ms_mem ms4) mem5 (ea_scr a) (ea_scr a) _ G4).
  intros jj Hjj. rewrite length_app in Hjj. cbn [length] in Hjj.
  apply K5; [lia | lia | | lia].
  intros He. exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md bs mss (ea_scr a + Z.of_nat jj) HAR Hbs
    ltac:(rewrite Hrs; lia) (ERRIMG _ He)). }
lazymatch goal with |- SRr _ _ ?cc _ => replace cc with (ev_cfg (PA := PA) fx' regs5 0x924 mem5 md5) end.
2:{ unfold ev_cfg, ev_pc, w64, raZ. rewrite Hent, T1c, unsigned_lit_small by lia.
    replace (BASE + EVC_K0 + 0x924) with (BASE + 9704) by (unfold EVC_K0; lia). reflexivity. }
refine (KRa fx' W regs5 mem5 md5 ly S Hp k i1 c j bits cn HPRE _ _).
- split; [exact HSTR_frm|]. intros r Hr. rewrite (HSTR_fk r Hr). exact (proj2 HFX r Hr).
- unfold ev_CR. cbv zeta.
  split; [exact MID5|].
  split; [exact (conj KR5 (conj S23 (conj Hi1 (conj Hc (conj Hws (conj Hskip (conj Hc34 (conj Hc91 (conj Hc123
    (conj Hc102 (conj Hc110 (conj Hc116 V104_5))))))))))))|].
  split; [exact S27|]. split; [exact V112_5|]. split; [exact S21|]. split; [exact V120_5|]. split; [exact V96_5|].
  split; [exact HSPAN|]. split; [exact Hj|]. split; [exact Hjend|]. split; [exact S22|].
  split; [exact G5|]. split; [exact HSTR_model|]. split; [exact HSTR_cn|].
  split; [exact HSTR_end|]. split; [exact HSTR_fa0 | exact FSH5].
Qed.
End C.
