(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 338 of its 381 lines of code are new or changed and 247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd for reac-pw/fuzz_rate's
   image A: the run is the first run of the piece "write + record" (J 0x81e00 -> __asan_memcpy 0x51860) and its
   statement is lib/A/RtPgW8Kit.v's rw8_runA_stmt (post RtPgSteps.rts_post); the start state adds the frame for
   locals (e's type and size at F + 0xf0 / F + 0xf4, read through s3 = F + 0xe0) and two capacity conditions; the
   eight bytes written are read back as e->size and e->type (the second word carries the engine's sign extension). *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses from the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): run A of the walk piece "write + record" of
   LLVMFuzzerTestOneInput (0x80714), J 0x81e00 -> __asan_memcpy 0x51860 (pod.h:200-201, pod_put32 of e->size at
   pp + len and of e->type at pp + len + 4, the two `pp->len += 4`, and the arguments of the body copy).
   Proves no function (kind: segment lemma).

   THE RUN. One token-engine run (lib/Reusable/YCbn.v) from 0x81e00 to the memcpy entry; the engine steps the `jal`,
   so ra = 0x81f44. The nine instrumented checks are on the first block's bytes, covered by the shadow entries
   (27, 0x4000, 0x4d18) and (33, 0, 16) of RtPgW8Kit.rw8_shent_blk, so the run leaves no shadow obligation. The two
   capacity tests of pod.h:177 compare len - 0x3ffd (an atom with a negative offset, whose unsigned range the engine
   does not know) with -0x4001; the start state carries them as conditions, proved by rw8a_cond from 0 <= len.
   Atoms: 9 = R (s1), 19 = F + 0xe0 (s3), 27 = pp (s11), 32 = the shadow offset, 33 = pp + len, 34 = len, 35 = sz,
   36 = ty. The engine reads e->size by `lw` with the unsigned atom 35 (its range fits in 31 bits) and e->type with
   SExt true 32 of atom 36; rw8a_sext and rw8a_byte_sh give the low four bytes of either. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgSteps RtPgW8Kit.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the start state at J 0x81e00 ======================================== *)
(* atoms 32 = the shadow offset, 33 = pp + len, 34 = len, 35 = sz, 36 = ty *)
Definition rw8a_extra (pp len sz ty : Z) : list word := [w64 RW8_SB; w64 (pp + len); w64 len; w64 sz; w64 ty].
(* sp = s1 = R, s2 = the shadow offset, s6 = the shadow address of pp->len, s7 = &pp->len, s10 = -0x4001 *)
Definition rw8a_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((18%bv : bv 5), rw8_Bx); ((22%bv : bv 5), rw8_sh 27 0x4000);
   ((23%bv : bv 5), SOff 27 0x4000); ((26%bv : bv 5), SLit 18446744073709535231)].
(* the real frame's cells, read only: &e->body (F + 0xf8), -0x3ffd, &e->type (F + 0xf0) *)
Definition rw8a_rR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x108 0x140 0 0
   [YP09.mkChunk 0x108 (CVal 8 (SOff 19 0x18));
    YP09.mkChunk 0x130 (CVal 8 (SLit 18446744073709535235));
    YP09.mkChunk 0x138 (CVal 8 (SOff 19 0x10))].
(* pp->len *)
Definition rw8a_rLen : YP09.region :=
  YP09.mkRegion (Some 27%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 (SOff 34 0))].
(* the eight bytes the two puts write *)
Definition rw8a_rAt : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 8 [].
(* e's type and size, read only *)
Definition rw8a_rE : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0x10 0x18 0 0
   [YP09.mkChunk 0x10 (CVal 4 (SOff 36 0)); YP09.mkChunk 0x14 (CVal 4 (SOff 35 0))].
Definition rw8a_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4);
           (19%nat, mkAF 4320 140737479966720 4);
           (27%nat, mkAF 4096 140737479966720 4);
           (32%nat, mkAF RW8_SB RW8_SB 0);
           (33%nat, mkAF 4096 140737479966720 3);
           (34%nat, mkAF 32 5384 3);
           (35%nat, mkAF 0 45 0);
           (36%nat, mkAF 0 4294967295 0)]
   [mkAC BC_GEU (SOff 34 (-16381)) (SLit 18446744073709535231);
    mkAC BC_GEU (SOff 34 (-16377)) (SLit 18446744073709535231)]
   [(SAlu ALU_ADD (SOff 27 0) (SOff 34 0), SOff 33 0)].
Definition rw8a_ss : sstate :=
  mkSS 0x81e00 (rw8_sr rw8a_ov) [rw8a_rR; rw8a_rLen; rw8a_rAt; rw8a_rE] None rw8a_facts.
Definition rw8a_SH : list shent := [mkSHE 27 0x4000 0x4d18; mkSHE 33 0 16].

(* ======================================== arithmetic ======================================== *)
(* a capacity test of a put: len + c is not below -0x4001 unsigned *)
Lemma rw8a_cond : forall {fx : YK11.FPState} E (c L : Z), bv_unsigned (ew E 34) = L -> 0 <= L ->
-16385 <= L + c -> L + c < 0 ->
acond_ok E (mkAC BC_GEU (SOff 34 c) (SLit 18446744073709535231)).
Proof.
intros fx E c L H34 HL Hc1 Hc2. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken sv_denot].
rewrite bv_ltu_unsigned, !unsigned_lit, H34.
rewrite (rw8_zc (L + c) (-1) (L + c + 18446744073709551616)) by lia.
rewrite (rw8_zc 18446744073709535231 0 18446744073709535231) by lia.
apply negb_true_iff, Z.ltb_ge. lia.
Qed.
Lemma rw8a_al8 : forall p a, p mod 16 = 0 -> a mod 8 = 0 -> (p + a) mod 8 = 0.
Proof.
intros p a Hp Ha.
assert (Hp8 : p mod 8 = 0).
{ rewrite (Z.div_mod p 16) by lia. rewrite Hp, Z.add_0_r.
  replace (16 * (p / 16)) with ((2 * (p / 16)) * 8) by lia. apply Z.mod_mul. lia. }
rewrite Z.add_mod by lia. rewrite Hp8, Ha. reflexivity.
Qed.
Lemma rw8a_al16 : forall F, F mod 32 = 0 -> (F + 0xe0) mod 16 = 0.
Proof.
intros F H. pose proof (Z.div_mod F 32 ltac:(lia)) as E. rewrite H, Z.add_0_r in E. rewrite E.
replace (32 * (F / 32) + 0xe0) with ((2 * (F / 32) + 14) * 16) by ring. apply Z_mod_mult.
Qed.
(* a byte of a 32-bit value is the same byte of any value congruent to it mod 2^32 (for `sext32 ty`: byte j of
   (sext32 ty) mod 2^64 is byte j of ty, j < 4) *)
Lemma rw8a_byte_sh : forall X y j, 0 <= j -> j + 8 <= 32 -> X mod 2 ^ 32 = y mod 2 ^ 32 ->
Z.shiftr X j mod 256 = Z.shiftr y j mod 256.
Proof.
intros X y j Hj Hj8 Hm. change 256 with (2 ^ 8).
rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.shiftr_spec by lia.
destruct (Z.ltb_spec n 8) as [Hl|Hg].
- rewrite Z.ones_spec_low by lia. rewrite !andb_true_r.
  rewrite <- (Z.mod_pow2_bits_low X 32 (n + j)) by lia. rewrite <- (Z.mod_pow2_bits_low y 32 (n + j)) by lia.
  rewrite Hm. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite !andb_false_r. reflexivity.
Qed.

Section u. Context {fx : YK11.FPState}.
Lemma rw8a_srl : forall E e k, 0 <= k < 64 -> U E (SAlu ALU_SRL e (SLit k)) = Z.shiftr (U E e) k.
Proof.
intros E e k Hk. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id k) by (unfold M64; lia).
replace (Z.land k 63) with k
  by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 6) with 64; lia).
pose proof (U_range E e) as Hr. apply zcanon_id. rewrite Z.shiftr_div_pow2 by lia.
split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | ].
apply (Z.le_lt_trans _ (U E e)); [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|] | lia].
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). nia.
Qed.
Lemma rw8a_sext : forall E e, U E (SExt true 32 e) mod 2 ^ 32 = U E e mod 2 ^ 32.
Proof.
intros E e. rewrite U_SExt. change (Z.of_N 32) with 32. unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
set (z := U E e mod 2 ^ 32).
set (w := (z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31).
assert (Hw : w mod 2 ^ 32 = z mod 2 ^ 32).
{ unfold w. rewrite (Z.mod_eq (z + 2 ^ 31) (2 ^ 32)) by lia.
  replace (z + 2 ^ 31 - 2 ^ 32 * ((z + 2 ^ 31) / 2 ^ 32) - 2 ^ 31) with (z + (- ((z + 2 ^ 31) / 2 ^ 32)) * 2 ^ 32) by ring.
  apply Z.mod_add. lia. }
rewrite (Z.mod_eq w (2 ^ 64)) by lia.
replace (w - 2 ^ 64 * (w / 2 ^ 64)) with (w + (- (w / 2 ^ 64) * 2 ^ 32) * 2 ^ 32) by ring.
rewrite Z.mod_add by lia. rewrite Hw. unfold z. apply Z.mod_mod. lia.
Qed.
(* the byte a one-byte chunk of a final region holds, as aview reads it *)
Lemma rw8a_aview1 : forall E H mem base off e v,
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk off (CVal 1 e)) -> U E e mod 256 = v ->
aview rsegs H mem (base + off) = Some v.
Proof.
intros E H mem base off e v C Hv. unfold aview. rewrite (rw8_mbyte_chunk1 E (mrestrict H mem) base off e C).
cbn [option_map]. f_equal. rewrite rtm_unsigned_byte. exact Hv.
Qed.
(* four one-byte chunks at o .. o + 3 hold the little-endian bytes of x *)
Lemma rw8a_word4 : forall E H mem base o x e0 e1 e2 e3,
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk o (CVal 1 e0)) ->
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk (o + 1) (CVal 1 e1)) ->
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk (o + 2) (CVal 1 e2)) ->
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk (o + 3) (CVal 1 e3)) ->
U E e0 mod 256 = x mod 256 -> U E e1 mod 256 = Z.shiftr x 8 mod 256 ->
U E e2 mod 256 = Z.shiftr x 16 mod 256 -> U E e3 mod 256 = Z.shiftr x 24 mod 256 ->
rtm_bytes rsegs H mem (base + o) (Z_to_le_bytes 4 x).
Proof.
intros E H mem base o x e0 e1 e2 e3 C0 C1 C2 C3 V0 V1 V2 V3.
apply rtm_bytes_aview. intros i Hi. rewrite length_Z_to_le_bytes in Hi.
rewrite rtm_nth_le_bytes by exact Hi. rewrite rtm_unsigned_byte.
destruct i as [|[|[|[|i]]]].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
  exact (rw8a_aview1 E H mem base o e0 _ C0 V0).
- change (8 * Z.of_nat 1) with 8. change (Z.of_nat 1) with 1. rewrite <- Z.add_assoc.
  exact (rw8a_aview1 E H mem base (o + 1) e1 _ C1 V1).
- change (8 * Z.of_nat 2) with 16. change (Z.of_nat 2) with 2. rewrite <- Z.add_assoc.
  exact (rw8a_aview1 E H mem base (o + 2) e2 _ C2 V2).
- change (8 * Z.of_nat 3) with 24. change (Z.of_nat 3) with 3. rewrite <- Z.add_assoc.
  exact (rw8a_aview1 E H mem base (o + 3) e3 _ C3 V3).
- lia.
Qed.
End u.

(* ======================================== run A ======================================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma rw8_runA : rw8_runA_stmt B MT.
Proof using MTL LAWS.
unfold rw8_runA_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos len sz ty rl
  HJ HG Hpp Hfresh H2 H9 H18 H19 H22 H23 H24 H26 H27 V108 V130 V138 Vlen Vty Vsz Hrl
  Hl0 Hl1 Hl8 Hsz Hty.
pose proof rw8_wx as Hwx. pose proof rw8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold rw8_geo in HG. destruct HG as (HR16 & HRlo & HRhi & HRhb & Hown & HF & HFapp & HF32).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
assert (Hm1 : (- 0x4001) mod 2 ^ 64 = 18446744073709535231) by reflexivity.
assert (Hm2 : (- 0x3ffd) mod 2 ^ 64 = 18446744073709535235) by reflexivity.
rewrite Hm2 in V130. rewrite Hm1 in H26.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
assert (HFin : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (sep_block_frame rsegs B LAWS lyc Sc W memc mdc pp Layout.PP_SIZE 3 pos HAR Hpp HFin) as HpF.
rewrite <- HF in HpF. unfold zdisjoint in HpF. cbn [fst snd] in HpF. change (fs_frame_bytes 3) with 512 in HpF.
rewrite Hrq, HPS in Hpceil, Hppres, HpF. rewrite HPS in Hpp, Hfresh.
destruct (rts_fbounds F HF32 HFapp) as (HF0 & HFc & _).
set (E := Ereg regs (rw8a_extra pp len sz ty)).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = w64 (F + 0xe0)) by (subst E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E24 : ew E 24 = w64 rl) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E27 : ew E 27 = w64 pp) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 RW8_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (pp + len)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 len) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 sz) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 ty) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (HE : E = Ereg regs (rw8a_extra pp len sz ty)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs rw8_Bx rw8a_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (rw8_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 27 0x4000 0x4d18 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (rw8_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0 16 (pp + len)); try assumption;
    try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = F + 0xe0) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = RW8_SB) by (rewrite E32; apply unsigned_lit_small; unfold RW8_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp + len) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = len) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = sz) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = ty) by (rewrite E36; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (rw8_sr rw8a_ov) regs).
{ apply (rw8_regs_ok E regs (rw8a_extra pp len sz ty)); [exact HE|]. unfold rw8a_ov.
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rw8_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold rw8_Bx. rewrite (rw8_den_off E 32 RW8_SB 0 E32) by (unfold RW8_SB; lia).
    rewrite Z.add_0_r, H18. reflexivity. }
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rw8_den_sh E 27 pp 0x4000 E27 E32) by lia. rewrite H22. reflexivity. }
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rw8_den_off E 27 pp 0x4000 E27) by lia. rewrite H23. reflexivity. }
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd sv_denot]. rewrite H26. reflexivity. }
  apply Forall_nil. }
assert (Hal33 : (pp + len) mod 8 = 0) by (apply rw8a_al8; assumption).
assert (Hal19 : (F + 0xe0) mod 16 = 0) by (apply rw8a_al16; exact HF32).
assert (HFK : facts_ok E rw8a_facts).
{ split; [| split].
  - cbn [rw8a_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, U27, U32, U33, U34, U35, U36.
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
                        | (change (2 ^ 4) with 16; assumption) | (change (2 ^ 3) with 8; assumption) ].
  - cbn [rw8a_facts f_conds conds_ok].
    refine (conj _ (conj _ I)); apply (rw8a_cond E _ len U34); lia.
  - cbn [rw8a_facts f_alias alias_ok]. split; [|exact I].
    rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 27 pp E27), (U_atom E 34 len E34), (U_atom E 33 (pp + len) E33) by lia.
    apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok rsegs E rw8a_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81e00) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold rw8a_ss. apply (rw8_entry _ _ regs (rw8a_extra pp len sz ty) E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - unfold rw8a_rR, rw8a_rLen, rw8a_rAt, rw8a_rE.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + apply (rtm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val rsegs E _ R 0x108 8 (SOff 19 0x18) (F + 0xf8));
          [ rewrite (rw8_den_off E 19 (F + 0xe0) 0x18 E19) by lia; unfold w64; f_equal; lia
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V108 ].
      * apply (chunk_ok_val rsegs E _ R 0x130 8 (SLit 18446744073709535235) 18446744073709535235);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V130 ].
      * apply (chunk_ok_val rsegs E _ R 0x138 8 (SOff 19 0x10) (F + 0xf0));
          [ rewrite (rw8_den_off E 19 (F + 0xe0) 0x10 E19) by lia; unfold w64; f_equal; lia
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V138 ].
    + apply (rtm_rw_region rsegs E (w_H W) memc 27 pp);
        [ exact U27 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 34 0) len);
        [ rewrite (rw8_den_off E 34 len 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (rtm_rw_region rsegs E (w_H W) memc 33 (pp + len));
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + len + o) ltac:(lia))) | apply Forall_nil ].
    + apply (rtm_ro_region rsegs E (w_H W) memc 19 (F + 0xe0)); [exact U19 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs E _ (F + 0xe0) 0x10 4 (SOff 36 0) ty);
          [ rewrite (rw8_den_off E 36 ty 0 E36) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 4) with 32; lia | lia
          | replace (F + 0xe0 + 0x10) with (F + 0xf0) by lia; exact Vty ].
      * apply (chunk_ok_val rsegs E _ (F + 0xe0) 0x14 4 (SOff 35 0) sz);
          [ rewrite (rw8_den_off E 35 sz 0 E35) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 4) with 32; lia | lia
          | replace (F + 0xe0 + 0x14) with (F + 0xf4) by lia; exact Vsz ].
  - unfold rw8a_rR, rw8a_rLen, rw8a_rAt, rw8a_rE; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [r_base r_lo r_hi base_val]; rewrite U9, U27, U33, U19; repeat split; try exact I; lia.
  - exact HFK. }
unfold cfg_at; change (w64 RW8_J) with (Z_to_bv 64 0x81e00).
aj_run_to_tok rw8_tbl_ok HS HJ Hsh rw8_Bspan 0x51860.
(* the write windows: pp->len and the eight bytes at pp + len, both in the fresh first block *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 27%nat pp);
    [ reflexivity | exact U27
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rt_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (pp + len));
    [ reflexivity | exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rt_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ]).
(* the state at the memcpy entry *)
all: apply SRr_ret.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 37 E Ef)
    by (first [apply env_agree_refl | apply env_agree_ewset2
              | (pose proof (env_agree_refl 37 E) as HAE0; env_agree_chain HAE0)]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & (_ & HM & _) & _);
  cbn [ms_regs restrict] in HRf;
  unfold rts_post; cbv beta; exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (rw8_regs_kept E Ef 37 (rw8_sr rw8a_ov) (ss_regs ssf) regs (ms_regs msf) rw8_clobA HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [let rec kio := first [apply same_io_refl | apply rw8_same_io_wvb
                                | eapply same_io_trans; [| apply rw8_same_io_wvb]; kio] in kio|];
  split; [apply mo_le_refl; assumption|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; cbv beta in Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (rw8_kept_run E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U19, ?U27, ?U33 in Hb;
       first [lia | (apply Hn; left; lia) | (apply Hn; right; lia)] | ]);
    destruct Hr
  |];
  cbv beta;
  assert (G35 : ew Ef 35 = Z_to_bv 64 sz) by (transitivity (ew E 35); [apply (proj1 HA); lia | exact E35]);
  assert (G36 : ew Ef 36 = Z_to_bv 64 ty) by (transitivity (ew E 36); [apply (proj1 HA); lia | exact E36]);
  assert (F27 : ew Ef 27 = ew E 27) by (apply (proj1 HA); lia);
  assert (F33 : ew Ef 33 = ew E 33) by (apply (proj1 HA); lia);
  split; [rewrite (rw8_reg_val E Ef 37 _ _ 1%bv (SLit 532292) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (rw8_reg_val E Ef 37 _ _ 10%bv (SOff 33 8) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          exact (rw8_den_off E 33 (pp + len) 8 E33 ltac:(lia) ltac:(lia))|];
  split; [rewrite (rw8_reg_val E Ef 37 _ _ 11%bv (SOff 19 24) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (rw8_den_off E 19 (F + 0xe0) 24 E19) by lia; unfold w64; f_equal; lia|];
  split; [rewrite (rw8_reg_val E Ef 37 _ _ 12%bv (SOff 35 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (rw8_den_off E 35 sz 0 E35) by lia; rewrite Z.add_0_r; reflexivity|];
  split; [rewrite (rw8_reg_val E Ef 37 _ _ 24%bv (SOff 35 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (rw8_den_off E 35 sz 0 E35) by lia; rewrite Z.add_0_r; reflexivity|];
  split; [rewrite (rw8_reg_val E Ef 37 _ _ 26%bv (SOff 24 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (rw8_den_off E 24 rl 0 E24) by lia; rewrite Z.add_0_r; reflexivity|];
  cbn [ss_mem restrict ms_mem] in HM;
  let Rr := fresh "Rr" in let Rl := fresh "Rl" in let Ra := fresh "Ra" in
  apply Forall_cons_iff in HM as [Rr HM]; apply Forall_cons_iff in HM as [Rl HM];
  apply Forall_cons_iff in HM as [Ra _];
  let Cl := fresh "Cl" in let Ca := fresh "Ca" in
  destruct Rl as (_ & _ & _ & Cl); destruct Ra as (_ & _ & _ & Ca);
  cbn [r_chunks r_base base_val] in Cl, Ca; try rewrite F27 in Cl; rewrite U27 in Cl;
  try rewrite F33 in Ca; rewrite U33 in Ca;
  rewrite Forall_forall in Cl, Ca;
  split;
  [ apply (val_of_chunk_ok rsegs Ef _ pp 0x4000 8 (SOff 34 8) (len + 8));
    [ apply Cl; cbn [In]; repeat (first [left; reflexivity | right])
    | try rewrite (sv_denot_agree 37 E Ef (SOff 34 8) HA eq_refl);
      exact (rw8_den_off E 34 len 8 E34 ltac:(lia) ltac:(lia))
    | change (8 * Z.of_N 8) with 64; lia | lia ]
  |];
  assert (Usz : U Ef (SOff 35 0) = sz) by (apply (U_atom Ef 35 sz G35); lia);
  assert (Uty : U Ef (SExt true 32 (SOff 36 0)) mod 2 ^ 32 = ty mod 2 ^ 32)
    by (rewrite rw8a_sext, (U_atom Ef 36 ty G36) by lia; reflexivity);
  apply rtm_bytes_app; rewrite length_Z_to_le_bytes; split;
  [ rewrite <- (Z.add_0_r (pp + len));
    apply (rw8a_word4 Ef (w_H W) (ms_mem msf) (pp + len) 0 sz (SOff 35 0) (SAlu ALU_SRL (SOff 35 0) (SLit 8))
             (SAlu ALU_SRL (SOff 35 0) (SLit 16)) (SAlu ALU_SRL (SOff 35 0) (SLit 24)));
    [ apply Ca; cbn [In]; repeat (first [left; reflexivity | right])
    | apply Ca; cbn [In]; repeat (first [left; reflexivity | right])
    | apply Ca; cbn [In]; repeat (first [left; reflexivity | right])
    | apply Ca; cbn [In]; repeat (first [left; reflexivity | right])
    | rewrite Usz; reflexivity
    | rewrite rw8a_srl, Usz by lia; reflexivity
    | rewrite rw8a_srl, Usz by lia; reflexivity
    | rewrite rw8a_srl, Usz by lia; reflexivity ]
  | change (Z.of_nat 4) with 4;
    apply (rw8a_word4 Ef (w_H W) (ms_mem msf) (pp + len) 4 ty (SExt true 32 (SOff 36 0))
             (SAlu ALU_SRL (SExt true 32 (SOff 36 0)) (SLit 8))
             (SAlu ALU_SRL (SExt true 32 (SOff 36 0)) (SLit 16))
             (SAlu ALU_SRL (SExt true 32 (SOff 36 0)) (SLit 24)));
    [ apply Ca; cbn [In]; repeat (first [left; reflexivity | right])
    | apply Ca; cbn [In]; repeat (first [left; reflexivity | right])
    | apply Ca; cbn [In]; repeat (first [left; reflexivity | right])
    | apply Ca; cbn [In]; repeat (first [left; reflexivity | right])
    | rewrite <- (Z.shiftr_0_r (U Ef (SExt true 32 (SOff 36 0)))), <- (Z.shiftr_0_r ty);
      apply rw8a_byte_sh; [lia | lia | exact Uty]
    | rewrite rw8a_srl by lia; apply rw8a_byte_sh; [lia | lia | exact Uty]
    | rewrite rw8a_srl by lia; apply rw8a_byte_sh; [lia | lia | exact Uty]
    | rewrite rw8a_srl by lia; apply rw8a_byte_sh; [lia | lia | exact Uty] ] ]
  end.
Qed.
End a.

Print Assumptions rw8_runA.
