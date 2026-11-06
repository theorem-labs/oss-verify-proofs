(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first half of a round of the split loop of LLVMFuzzerTestOneInput's inlined words_of on the ASan+UBSan image B (plugin-hostd/fuzz_command, 0x868e4 .. 0x8698c: the *t test, the strspn wrapper call, its UBSan pointer-overflow test, the exit when only separators are left, w.n + 1 and &w.v[n] behind their UBSan tests, the 8-byte check and the store of the word's address, the strcspn wrapper call), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s45.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (a symbolic seed at a point of the function and the runs from it) and A/ACh2.v:122-290 (a call and back, with the facts carried over it). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_s45.v, with its module paths and module names changed; 1255 of its 1366 lines of code are new or changed and 1010 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the walk
   of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0): segment S15, from the cut K85d04 (0x85d04,
   turn i of the inlined m_declared, v built) to K85b0c (i + 1) or K85e50. Its statement is lt_seg_S15_stmt of
   LLVMFuzzerTestOneInput_defs.v; the inner points S23_L / S23_N / S23_J, the support lemmas and the pieces J and D
   are in LLVMFuzzerTestOneInput_s23k.v. This file holds piece N (0x85dac: the -1 exit or __asan_memcpy of v to
   mt[mn]), piece L (one turn of the dup loop 0x85d30, with the strcmp interceptor), the loop by downward induction
   and the segment lemma lt_seg_S15.

   Section hypotheses: ASTRCMP (RtString.astrcmp_realizes at the strcmp trampoline, the image-B wrapper owner's lib/B/Rt/RtString.v,
   row 17 of the interceptor interface), AMEMCPY (the kit's YG0d.aintrin_realizes OCpy at __asan_memcpy), TL (PALib:
   the errno cell aj_art_at needs). lt_img crosses both calls by the memory agreement on image bytes (both posts keep
   every byte outside the scratch window below s1 and the copy's destination), so no image-record hypothesis is
   taken. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YK06 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaArt PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_s23k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================== piece N (0x85dac) ==================================
reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256
   c3796c0b38f3), the walk of LLVMFuzzerTestOneInput (0x84dc0), segment S15, piece N: from the inner point 0x85dac
   (LLVMFuzzerTestOneInput_s23k.v S23_N_stmt i: no entry of the table is (par, vid), a1 = mn, s8 = m) to
     - 0x85b58 (S23_J_stmt i) when mn < cap: 0x85dac .. 0x85de8 (the test mn >= cap not taken; UBSan's tests of
       mt + 20 mn: the null test 0x85dc4 decided by the ranges of mn and mt, the overflow test 0x85de0 split and its
       trap side refuted), __asan_memcpy(mt + 20 mn, v, 20) at 0x85dec, then 0x85df0 .. 0x85e14 (added + 1 with
       UBSan's signed-overflow test 0x85df8 decided by the range of added, mn + 1, a6 and s8 reloaded, j 0x85b58);
     - 0x85e50 (LT_K85e50) when mn >= cap: 0x85fd8 .. 0x85ff4 (v out of scope: SH(FR) + 4 .. 6 := 0xf8, 112(s1) :=
       -1, j 0x85e50).
   The case split is logical (mn < cap or not); each side has its own seed whose condition decides `bge a1,a0`
   (0x85db0) inside the run. *)

(* ---- the seed at 0x85dac ----
   Atoms: 0 .. 31 the registers (a1 = mn, s8 = m, a6 = SHADOW_OFF), 32 = cap, 33 = v = FR + 32, 34 = added,
   35 = mt, 36 = SH(FR). The s1 region holds the slots the stretch reads (40 cap, 64 &v, 112 added, 120 mt,
   128 mn, 184 SH(FR), 192 m, 200 the shadow base) and is writable at 112 .. 136 (added, mn). The side mn >= cap
   adds a region at SH(FR) writable at 4 .. 7 (v's three shadow bytes). No instrumented check lies in the stretch:
   the shadow table is empty and the span (0, 0) is apart from every write window. *)
Definition s23n_SB : Z * Z := (0, 0).
Definition s23n_x : sv := SLit SHADOW_OFF.
Definition s23n_s1 : YP09.region := YP09.mkRegion (Some 9%nat) 40 208 112 136
  [YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 64 (CVal 8 (SOff 33 0));
   YP09.mkChunk 112 (CVal 8 (SOff 34 0)); YP09.mkChunk 120 (CVal 8 (SOff 35 0));
   YP09.mkChunk 128 (CVal 8 (SOff 11 0)); YP09.mkChunk 184 (CVal 8 (SOff 36 0));
   YP09.mkChunk 192 (CVal 8 (SOff 24 0)); YP09.mkChunk 200 (CVal 8 (SOff 16 0))].
Definition s23n_sh : YP09.region := YP09.mkRegion (Some 36%nat) 4 7 4 7 [].
Definition s23n_atoms : list (nat * afact) :=
  [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0); (11%nat, mkAF 0 39 0); (32%nat, mkAF 0 39 0);
   (34%nat, mkAF 0 31 0); (35%nat, mkAF 4096 (2 ^ 47) 0);
   (36%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 0)].
Definition s23n_ss (cs : list acond) : sstate := mkSS LO_DAC sr_atoms [s23n_s1] None (mkFacts s23n_atoms cs []).
Definition s23n_ssA : sstate :=
  mkSS LO_DAC sr_atoms [s23n_sh; s23n_s1] None (mkFacts s23n_atoms [mkAC BC_GE (SOff 11 0) (SOff 32 0)] []).
Definition s23n_ext (cap v ad mt sh : Z) : list word :=
  [Z_to_bv 64 cap; Z_to_bv 64 v; Z_to_bv 64 ad; Z_to_bv 64 mt; Z_to_bv 64 sh].

(* the frame's shadow with v in scope and out of scope differ in v's three bytes only *)
Lemma s23n_fsh_NV_N : forall j, (j < 36)%nat -> j <> 4%nat -> j <> 5%nat -> j <> 6%nat ->
  nth j (lt_fsh LFO_NV) 0 = nth j (lt_fsh LFO_N) 0.
Proof.
intros j Hj H4 H5 H6.
do 36 (destruct j as [|j]; [first [reflexivity | exfalso; lia] |]). lia.
Qed.
Lemma s23n_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. Qed.
Ltac s23n_in := solve [repeat (first [left; reflexivity | right])].
(* an address of an application range *)
Lemma s23n_app_in : forall {rc : YM05.RunCeil} lo len a, in_app lo len -> lo <= a < lo + len ->
  a < kLowShadowBeg \/ kHighMemBeg <= a.
Proof. intros rc lo len a [H0 [HL | [HH HC]]] Ha; [left | right]; lia. Qed.

(* a shadow address of the frame's 64 shadow bytes is not an application address *)
Lemma s23n_app_not_sh : forall {rc : YM05.RunCeil} a FR j0 j1,
  (a < kLowShadowBeg \/ kHighMemBeg <= a) -> 4096 <= FR -> FR + 512 <= alloc_ceiling -> 0 <= j0 -> j1 <= 64 ->
  ~ (shadow_addr FR + j0 <= a < shadow_addr FR + j1).
Proof.
intros rc a FR j0 j1 Ha H1 H2 H3 H4 Hc.
pose proof asan_consts as ((C1 & C1') & _).
pose proof (Z.div_le_mono 4096 FR 8 ltac:(lia) H1) as D1. change (4096 / 8) with 512 in D1.
pose proof (Z.div_le_mono FR 0x7fffff800000 8 ltac:(lia) ltac:(lia)) as D2.
change (0x7fffff800000 / 8) with 17592184995840 in D2.
unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* the 20 bytes of v (FR + 32 .. FR + 52) are addressable when its shadow bytes are 00 00 04 *)
Lemma s23n_v_addr : forall (rd : reader) FR, FR mod 32 = 0 ->
  rd (shadow_addr FR + 4) = Some 0 -> rd (shadow_addr FR + 5) = Some 0 -> rd (shadow_addr FR + 6) = Some 4 ->
  range_addressable rd SHADOW_OFF (FR + 32) 20.
Proof.
intros rd FR H32 S4 S5 S6 y Hy. unfold shadow_of_addr.
destruct (Z_lt_ge_dec y (FR + 40)) as [L1 | L1].
- exists 0. split; [|left; reflexivity].
  replace (SHADOW_OFF + y / 8) with (shadow_addr FR + 4) by (unfold shadow_addr; lia). exact S4.
- destruct (Z_lt_ge_dec y (FR + 48)) as [L2 | L2].
  + exists 0. split; [|left; reflexivity].
    replace (SHADOW_OFF + y / 8) with (shadow_addr FR + 5) by (unfold shadow_addr; lia). exact S5.
  + exists 4. split.
    * replace (SHADOW_OFF + y / 8) with (shadow_addr FR + 6) by (unfold shadow_addr; lia). exact S6.
    * right. split; lia.
Qed.

(* the shadow hull of v lies inside the frame's 64 shadow bytes *)
Lemma s23n_v_hull : forall FR s, FR mod 32 = 0 ->
  shadow_addr (FR + 32) / 8 * 8 <= s < shadow_addr (FR + 32 + 20 - 1) / 8 * 8 + 8 ->
  shadow_addr FR <= s < shadow_addr FR + 64.
Proof. intros FR s H32 Hs. unfold shadow_addr, SHADOW_OFF in *. lia. Qed.

(* UBSan's overflow test of mt + 20 mn (0x85dc8 .. 0x85de0) through the engine's term: the value tested is 1 *)
Lemma s23n_U_dest : forall E mn mt, ew E 11 = Z_to_bv 64 mn -> ew E 35 = Z_to_bv 64 mt -> 0 <= mn <= 39 ->
  0 <= mt < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SLit 20)) (SOff 35 0)) = mt + 20 * mn.
Proof.
intros E mn mt H11 H35 Hmn Hmt.
rewrite U_SAlu, U_SMd, U_SLit, (U_atom E 11 mn H11 ltac:(lia)), (U_atom E 35 mt H35 ltac:(lia)).
cbn [zalu_raw zmd_raw]. rewrite (zcanon_small 20) by lia. rewrite (zcanon_small (mn * 20)) by lia.
rewrite zcanon_small by lia. lia.
Qed.
Lemma s23n_U_trap37 : forall E mn mt, ew E 11 = Z_to_bv 64 mn -> ew E 35 = Z_to_bv 64 mt -> 0 <= mn <= 39 ->
  0 <= mt < 2 ^ 47 ->
  U E (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SLit 20)) (SOff 35 0))
    (SOff 35 0)) (SLit 0)) (SLit 1)) = 1.
Proof.
intros E mn mt H11 H35 Hmn Hmt.
rewrite U_SAlu. rewrite (U_SAlu E ALU_XOR). rewrite (U_SAlu E ALU_SLTU).
rewrite (s23n_U_dest E mn mt H11 H35 Hmn Hmt), (U_atom E 35 mt H35 ltac:(lia)), !U_SLit.
cbn [zalu_raw]. destruct (mt + 20 * mn <? mt) eqn:Hlt; [apply Z.ltb_lt in Hlt; lia|]. reflexivity.
Qed.
(* the signed compare of two small atoms *)
Lemma s23n_lts : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  bv_lts (sv_denot E (SOff a 0)) (sv_denot E (SOff b 0)) = (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite bv_lts_signed.
assert (Ua : bv_unsigned (sv_denot E (SOff a 0)) = x) by exact (U_atom E a x Ha ltac:(lia)).
assert (Ub : bv_unsigned (sv_denot E (SOff b 0)) = y) by exact (U_atom E b y Hb ltac:(lia)).
rewrite (signed_of_small (sv_denot E (SOff a 0))) by (rewrite Ua; unfold half64; lia).
rewrite (signed_of_small (sv_denot E (SOff b 0))) by (rewrite Ub; unfold half64; lia).
rewrite Ua, Ub. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition s23n_E (regs : bvmap 5 word) (cap v ad mt sh : Z) : env := Eimg (Ereg regs (s23n_ext cap v ad mt sh)).
Lemma s23n_E_lo : forall regs cap v ad mt sh n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (s23n_E regs cap v ad mt sh) n = getr regs r.
Proof.
intros regs cap v ad mt sh n r Hr. pose proof (u5_range r) as R5. unfold s23n_E.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr.
Qed.
Lemma s23n_E_x : forall regs cap v ad mt sh j, (j < 5)%nat ->
  ew (s23n_E regs cap v ad mt sh) (32 + j) = nth j (s23n_ext cap v ad mt sh) (Z_to_bv 64 0).
Proof. intros regs cap v ad mt sh j Hj. unfold s23n_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma s23n_E_agree : forall regs cap v ad mt sh, env_agree 32 (Ereg regs (s23n_ext cap v ad mt sh)) (s23n_E regs cap v ad mt sh).
Proof.
intros regs cap v ad mt sh.
split; [intros n Hn; unfold s23n_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
Qed.

(* a word chunk of a region of the state, read back *)
Lemma s23n_chunk_word : forall (W : world SEGS) E ss ms (j : nat) rg (n : nat) base off e v,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) j = Some rg -> YP09.r_base rg = Some n ->
  bv_unsigned (ew E n) = base -> In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks rg) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (rdW W (ms_mem ms)) (base + off) = Some v.
Proof.
intros W E ss ms j rg n base off e v HS Hj Hb Hbase Hc He Hv. pose proof (nth_error_In _ _ Hj) as Hin.
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
pose proof (mem_ok_region SEGS _ _ _ _ HM Hin) as HR.
pose proof (region_ok_chunk SEGS _ _ _ _ HR Hc) as HC. rewrite Hb in HC. cbn [base_val] in HC. rewrite Hbase in HC.
apply rdword_of_val_mem; [|exact Hv].
exact (val_of_chunk_ok SEGS E _ base off 8 e v HC He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
  ltac:(cbn; lia)).
Qed.
(* a one-byte literal chunk of a region of the state, read back *)
Lemma s23n_chunk_byte : forall (W : world SEGS) E ss ms (j : nat) rg (n : nat) base off z,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) j = Some rg -> YP09.r_base rg = Some n ->
  bv_unsigned (ew E n) = base -> In (YP09.mkChunk off (CVal 1 (SLit z))) (YP09.r_chunks rg) ->
  rdW W (ms_mem ms) (base + off) = Some (z mod 2 ^ 64 mod 256).
Proof.
intros W E ss ms j rg n base off z HS Hj Hb Hbase Hc. pose proof (nth_error_In _ _ Hj) as Hin.
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
pose proof (mem_ok_region SEGS _ _ _ _ HM Hin) as HR.
pose proof (region_ok_chunk SEGS _ _ _ _ HR Hc) as HC. rewrite Hb in HC. cbn [base_val] in HC. rewrite Hbase in HC.
destruct (HC 0 ltac:(cbn; lia)) as (bb & Hbb & Hm). cbn [cbyte YP09.c_off YP09.c_val] in Hbb, Hm.
injection Hbb as <-. rewrite Z.add_0_r in Hm. unfold aview. rewrite Hm. reflexivity.
Qed.
(* a slot outside the windows a stretch wrote *)
Lemma s23n_slot_kept : forall (rd rd' : reader) s1 o v (Zs : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> rd' a = rd a) ->
  (forall k, 0 <= k < 8 -> 0 <= s1 + o + k < 2 ^ 64 /\ ~ Zs (s1 + o + k)) ->
  rdword rd (s1 + o) = Some v -> rdword rd' (s1 + o) = Some v.
Proof.
intros rd rd' s1 o v Zs HK HZ H. rewrite <- H. apply rdword_ext. intros k Hk.
destruct (HZ k Hk) as [H1 H2]. exact (HK _ H1 H2).
Qed.

(* the region at s1 at the seed *)
Lemma s23n_s1_ok : forall E (W : world SEGS) mem s1 cap v ad mt sh mn m,
  bv_unsigned (ew E 9) = s1 -> ew E 32 = Z_to_bv 64 cap -> ew E 33 = Z_to_bv 64 v -> ew E 34 = Z_to_bv 64 ad ->
  ew E 35 = Z_to_bv 64 mt -> ew E 36 = Z_to_bv 64 sh -> ew E 11 = Z_to_bv 64 mn -> ew E 24 = Z_to_bv 64 m ->
  ew E 16 = Z_to_bv 64 SHADOW_OFF ->
  0 <= s1 -> s1 + 208 <= 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= ad < 2 ^ 64 -> 0 <= mt < 2 ^ 64 ->
  0 <= sh < 2 ^ 64 -> 0 <= mn < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  (forall o, 112 <= o < 136 -> apresent (w_H W) mem (s1 + o)) ->
  rdword (rdW W mem) (s1 + 40) = Some cap -> rdword (rdW W mem) (s1 + 64) = Some v ->
  rdword (rdW W mem) (s1 + 112) = Some ad -> rdword (rdW W mem) (s1 + 120) = Some mt ->
  rdword (rdW W mem) (s1 + 128) = Some mn -> rdword (rdW W mem) (s1 + 184) = Some sh ->
  rdword (rdW W mem) (s1 + 192) = Some m -> rdword (rdW W mem) (s1 + 200) = Some SHADOW_OFF ->
  region_ok SEGS E (mrestrict (w_H W) mem) s23n_s1.
Proof.
intros E W mem s1 cap v ad mt sh mn m U9 E32 E33 E34 E35 E36 E11 E24 E16 H0 H1 Rc Rv Ra Rmt Rsh Rmn Rm Hpres
  G40 G64 G112 G120 G128 G184 G192 G200.
unfold region_ok, s23n_s1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U9. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS E _ s1 40 8 (SOff 32 0) cap);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact (val_mem_of_rdword SEGS _ _ _ _ G40)].
- apply (chunk_ok_val SEGS E _ s1 64 8 (SOff 33 0) v);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact (val_mem_of_rdword SEGS _ _ _ _ G64)].
- apply (chunk_ok_val SEGS E _ s1 112 8 (SOff 34 0) ad);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact (val_mem_of_rdword SEGS _ _ _ _ G112)].
- apply (chunk_ok_val SEGS E _ s1 120 8 (SOff 35 0) mt);
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact (val_mem_of_rdword SEGS _ _ _ _ G120)].
- apply (chunk_ok_val SEGS E _ s1 128 8 (SOff 11 0) mn);
    [cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact (val_mem_of_rdword SEGS _ _ _ _ G128)].
- apply (chunk_ok_val SEGS E _ s1 184 8 (SOff 36 0) sh);
    [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact (val_mem_of_rdword SEGS _ _ _ _ G184)].
- apply (chunk_ok_val SEGS E _ s1 192 8 (SOff 24 0) m);
    [cbn [sv_denot]; rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact (val_mem_of_rdword SEGS _ _ _ _ G192)].
- apply (chunk_ok_val SEGS E _ s1 200 8 (SOff 16 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E16, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | zside
    | exact (val_mem_of_rdword SEGS _ _ _ _ G200)].
Qed.

(* the seed at 0x85dac, with the conditions cs *)
Lemma s23n_seed : forall (W : world SEGS) regs mem (cs : list acond) s1 cap v ad mt sh mn m,
  getr regs 9 = w64 s1 -> getr regs 11 = w64 mn -> getr regs 24 = w64 m -> getr regs 16 = w64 SHADOW_OFF ->
  0x7fff7f800000 <= s1 <= 2 ^ 47 -> 0 <= cap <= 39 -> 0 <= mn <= 39 -> 0 <= ad <= 31 -> 4096 <= mt <= 2 ^ 47 ->
  SHADOW_OFF + 512 <= sh <= SHADOW_OFF + 2 ^ 44 -> 0 <= v < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  conds_ok (s23n_E regs cap v ad mt sh) cs ->
  (forall o, 112 <= o < 136 -> apresent (w_H W) mem (s1 + o)) ->
  rdword (rdW W mem) (s1 + 40) = Some cap -> rdword (rdW W mem) (s1 + 64) = Some v ->
  rdword (rdW W mem) (s1 + 112) = Some ad -> rdword (rdW W mem) (s1 + 120) = Some mt ->
  rdword (rdW W mem) (s1 + 128) = Some mn -> rdword (rdW W mem) (s1 + 184) = Some sh ->
  rdword (rdW W mem) (s1 + 192) = Some m -> rdword (rdW W mem) (s1 + 200) = Some SHADOW_OFF ->
  st_ok_pi SEGS VAL (s23n_E regs cap v ad mt sh) (s23n_ss cs)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_DAC)) mem (seg_rom SEGS))).
Proof.
intros W regs mem cs s1 cap v ad mt sh mn m R9 R11 R24 R16 Hs1 Hcap Hmn Had Hmt Hsh Hv Hm Hcs Hpres
  G40 G64 G112 G120 G128 G184 G192 G200.
set (E := s23n_E regs cap v ad mt sh).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (subst E; rewrite (s23n_E_lo regs cap v ad mt sh 9 9%bv eq_refl); exact R9).
assert (E11 : ew E 11 = Z_to_bv 64 mn) by (subst E; rewrite (s23n_E_lo regs cap v ad mt sh 11 11%bv eq_refl); exact R11).
assert (E24 : ew E 24 = Z_to_bv 64 m) by (subst E; rewrite (s23n_E_lo regs cap v ad mt sh 24 24%bv eq_refl); exact R24).
assert (E16 : ew E 16 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (s23n_E_lo regs cap v ad mt sh 16 16%bv eq_refl); exact R16).
assert (E32 : ew E 32 = Z_to_bv 64 cap) by (subst E; exact (s23n_E_x regs cap v ad mt sh 0 ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 v) by (subst E; exact (s23n_E_x regs cap v ad mt sh 1 ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 ad) by (subst E; exact (s23n_E_x regs cap v ad mt sh 2 ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 mt) by (subst E; exact (s23n_E_x regs cap v ad mt sh 3 ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 sh) by (subst E; exact (s23n_E_x regs cap v ad mt sh 4 ltac:(lia))).
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = mn) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = cap) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = ad) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = mt) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = sh) by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
unfold s23n_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s23n_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  apply (s23n_s1_ok E W mem s1 cap v ad mt sh mn m U9 E32 E33 E34 E35 E36 E11 E24 E16); try lia;
    first [exact Hpres | assumption | unfold SHADOW_OFF in *; lia].
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact Hcs | exact I]].
  cbn [s23n_atoms f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U11, U32, U34, U35, U36. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the memory-checking runtime's memcpy entry (LLVMFuzzerTestOneInput_c.v), at every FP state *)
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA SS___asan_memcpy).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS. Let BR := paj_branch (PI := PI).

(* the write window of the s1 region (112 .. 136), an s1 slot of the frame below SP0 *)
Ltac s23n_awr1 cx U WS :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end;
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
    [reflexivity | rewrite U; ring | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil].
(* what a run with only the s1 region's window left alone *)
Ltac s23n_keepW K s1 U :=
  lazymatch goal with Hfr : frame_of _ _ (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 112 <= a < s1 + 136) -> rdW W m2 a = rdW W m1 a)
    by (intros a Ha Hna; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => s1 + 112 <= a < s1 + 136) Hfr);
        [ intros b wlo whi a' Hin Hrr; vm_compute in Hin; destruct Hin as [Hq0 | []]; injection Hq0 as <- <- <-;
          cbn [base_val] in Hrr; rewrite U in Hrr; lia
        | exact Ha | exact Hna ])
  end.

Lemma s23_N : forall i, S23_J_stmt B MT i -> LTA_K85e50 B MT -> S23_N_stmt B MT i.
Proof.
intros i HJS HE50. unfold S23_N_stmt.
intros cx ly S W regs mem md k acc c m tab mt par vid HB HFRM HBODY HREGS HDUP HSL HTABS HPAR HVID R11 R24.
pose proof (s23_facts B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid HB HBODY) as
  (HAR & HinF & EFA & Hfr32 & Hfr4096 & Hfrceil & Hfrpres & Hsh & Hs1al & Hs1 & Hsp0al & Hsp0 & Hstkpres &
   Hcap & Hmtn & Htabn & Hlen & Hmt16 & Hmt4096 & Hmtceil & Htab16 & Htab4096 & Htabceil & Hm16 & Hm4096 & Hmceil &
   Hc16 & Hc4096 & Hcceil & HmtIn & HmtN0 & Hmtpres & HmtFR & HmtTab & HmtM & HmtC).
pose proof HBODY as (HCORE & Hhc & Hhm & Hhtab & Hhmt & Hi & Hign & Hsplit & Had & Hcm).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & HSB & HSH & H184).
pose proof HREGS as (R16 & R20 & R21 & R22 & R26 & R27).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as ((C1 & C1') & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
rewrite WS in Hsp0.
(* the model: i < m->n <= 32, the name of seg[i] and its split *)
pose proof Hcm as [Hrc Hmc].
destruct (s23_mconf_n B MT (rdW W mem) m (seg_spec.seg_mc (x_run cx)) Hmc) as [_ Hnseg].
assert (Hi32 : (i < 32)%nat) by (unfold x_mcF in Hi; lia).
destruct (s23_name_facts B MT (rdW W mem) cx m i Hmc Hi) as [Hnz Hnl].
destruct (s23_split_facts _ par vid Hnz Hnl Hsplit) as (Hpnz & Hpl & Hvid).
(* m_declared's step at seg[i] (no duplicate): appended when mn < cap, failed when mn >= cap *)
assert (HDS : Z.of_nat (length (snd (x_decl cx i))) < x_cap cx ->
  x_decl cx (Datatypes.S i) = (fst (x_decl cx i) + 1, snd (x_decl cx i) ++ [(par, vid)])).
{ intros Hlt0. rewrite (@s23_decl_S fx rc SK PI cx i par vid Hi Hign Hsplit ltac:(lia)), HDUP.
  destruct (x_cap cx <=? Z.of_nat (length (snd (x_decl cx i)))) eqn:E0; [apply Z.leb_le in E0; lia | reflexivity]. }
set (t := snd (x_decl cx i)) in *.
set (ad := fst (x_decl cx i)) in *.
set (mn := Z.of_nat (length t)) in *.
assert (Hmn : 0 <= mn <= 39) by (subst mn; lia).
assert (Had' : 0 <= ad <= 31) by lia.
(* the frame, its shadow and the blocks: where they lie *)
destruct (al_frames _ _ LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (_ & HFapp & _ & HFsp).
rewrite EFA in HFapp, HFsp. rewrite <- Hsh in HFsp.
change (fs_frame_bytes LT_FCLS) with 512 in HFapp. change (fs_frame_bytes LT_FCLS / 8) with 64 in HFsp.
destruct (al_blocks _ _ LAWS ly S W mem md mt (x_mtn cx) HAR HmtIn) as (_ & _ & _ & HMTapp & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md tab (x_tabn cx)) as (_ & _ & _ & HTBapp & _ & _ & _);
  [exact HAR | exact (proj1 Hhtab) |].
assert (Hmtn0 : 0 < x_mtn cx) by lia.
assert (Htabn0 : 0 < x_tabn cx) by lia.
rewrite (s23n_req _ Hmtn0) in HMTapp. rewrite (s23n_req _ Htabn0) in HTBapp.
assert (Hshv : x_sh cx = SHADOW_OFF + x_fr cx / 8) by (rewrite Hsh; reflexivity).
assert (Hshr : SHADOW_OFF + 512 <= x_sh cx <= SHADOW_OFF + 2 ^ 44).
{ rewrite Hshv. pose proof (Z.div_le_mono 4096 (x_fr cx) 8 ltac:(lia) Hfr4096) as D1.
  change (4096 / 8) with 512 in D1.
  pose proof (Z.div_le_mono (x_fr cx) 0x7fffff800000 8 ltac:(lia) ltac:(lia)) as D2.
  change (0x7fffff800000 / 8) with 17592184995840 in D2. lia. }
assert (Hs1r : 0x7fff7f800000 <= x_s1 cx <= 2 ^ 47) by lia.
(* the slots the stretch reads *)
assert (G40 : rdword (rdW W mem) (x_s1 cx + 40) = Some (x_cap cx))
  by (apply HSL; apply in_or_app; left; unfold LT_LV; repeat (first [left; reflexivity | right])).
assert (G64 : rdword (rdW W mem) (x_s1 cx + 64) = Some (x_fr cx + 32))
  by (apply HSL; apply in_or_app; left; unfold LT_LV; repeat (first [left; reflexivity | right])).
assert (G192 : rdword (rdW W mem) (x_s1 cx + 192) = Some m)
  by (apply HSL; apply in_or_app; left; unfold LT_LV; repeat (first [left; reflexivity | right])).
assert (G112 : rdword (rdW W mem) (x_s1 cx + 112) = Some ad)
  by (apply HSL; apply in_or_app; right; unfold LT_LD; repeat (first [left; reflexivity | right])).
assert (G120 : rdword (rdW W mem) (x_s1 cx + 120) = Some mt)
  by (apply HSL; apply in_or_app; right; unfold LT_LD; repeat (first [left; reflexivity | right])).
assert (G128 : rdword (rdW W mem) (x_s1 cx + 128) = Some mn)
  by (apply HSL; apply in_or_app; right; unfold LT_LD; repeat (first [left; reflexivity | right])).
assert (Hpres1 : forall o, 112 <= o < 136 -> apresent (w_H W) mem (x_s1 cx + o)) by (intros o Ho; apply Hstkpres; lia).
unfold cfg_at, w64.
destruct (Z_lt_ge_dec mn (x_cap cx)) as [Hlt | Hge].
- (* ======== mn < cap: the memcpy of v to mt[mn], added + 1, mn + 1, to 0x85b58 ======== *)
  set (E := s23n_E regs (x_cap cx) (x_fr cx + 32) ad mt (x_sh cx)).
  assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hr; subst E; apply s23n_E_lo; exact Hr).
  assert (E11 : ew E 11 = Z_to_bv 64 mn) by (rewrite (EL 11%nat 11%bv eq_refl); exact R11).
  assert (E32 : ew E 32 = Z_to_bv 64 (x_cap cx)) by (subst E; exact (s23n_E_x _ _ _ _ _ _ 0 ltac:(lia))).
  assert (HCS : conds_ok E [mkAC BC_LT (SOff 11 0) (SOff 32 0)]).
  { split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
    rewrite (s23n_lts E 11 32 mn (x_cap cx) E11 E32 ltac:(lia) ltac:(lia)). apply Z.ltb_lt. lia. }
  pose proof (s23n_seed W regs mem _ (x_s1 cx) (x_cap cx) (x_fr cx + 32) ad mt (x_sh cx) mn m R9 R11 R24 R16
    Hs1r ltac:(lia) Hmn Had' ltac:(lia) Hshr ltac:(lia) ltac:(unfold seg_spec.SEG_M_SIZE in *; lia) HCS Hpres1
    G40 G64 G112 G120 G128 H184 G192 HSB) as HS.
  fold E in HS.
  assert (E2 : ew E 2 = getr regs 2) by exact (EL 2%nat 2%bv eq_refl).
  assert (E3 : ew E 3 = getr regs 3) by exact (EL 3%nat 3%bv eq_refl).
  assert (E4 : ew E 4 = getr regs 4) by exact (EL 4%nat 4%bv eq_refl).
  assert (U9 : bv_unsigned (ew E 9) = x_s1 cx) by (rewrite (EL 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (E33 : ew E 33 = Z_to_bv 64 (x_fr cx + 32)) by (subst E; exact (s23n_E_x _ _ _ _ _ _ 1 ltac:(lia))).
  assert (E34 : ew E 34 = Z_to_bv 64 ad) by (subst E; exact (s23n_E_x _ _ _ _ _ _ 2 ltac:(lia))).
  assert (E35 : ew E 35 = Z_to_bv 64 mt) by (subst E; exact (s23n_E_x _ _ _ _ _ _ 3 ltac:(lia))).
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold s23n_E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (s23n_ext (x_cap cx) (x_fr cx + 32) ad mt (x_sh cx))) E) by (subst E; apply s23n_E_agree).
  assert (SHOK : sh_ok SEGS s23n_x [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
  clearbody E. clear EL.
  (* ---- 0x85dac .. 0x85de0: the test mn >= cap (not taken), a0 = 20 mn + mt, UBSan's null test (decided),
     the overflow test of mt + 20 mn: the run stops at its branch ---- *)
  paj_run_tok RUN HS HJ SHOK s23n_SB.
  { s23n_awr1 cx U9 WS. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv1 := d) in *; clearbody mdv1 end.
  s23n_keepW K1 (x_s1 cx) U9.
  clear HF HFr HG.
  (* the trap side (0x85ff8): mt + 20 mn would wrap or mn < 0; neither *)
  psrr_branch_tok RUN BR HS SHOK s23n_SB.
  { exfalso. rewrite branch_eq_U, (s23n_U_trap37 E mn mt E11 E35 ltac:(lia) ltac:(lia)), U_SLit in Hc.
    rewrite (zcanon_small 0) in Hc by lia. discriminate Hc. }
  clear Hc.
  (* ---- 0x85de4 .. 0x85dec: a2 = 20, a1 = v, jal __asan_memcpy ---- *)
  paj_run_tok RUN HS HJ SHOK s23n_SB.
  { s23n_awr1 cx U9 WS. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  s23n_keepW K2 (x_s1 cx) U9.
  clear HF HFr HG.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
  lazymatch type of HS with st_ok _ _ ?ssc (restrict _ ?msc) =>
    pose proof (st_ok_restrict_reg SEGS (w_H W) E ssc msc 10%bv HS) as P10;
    let e := eval vm_compute in (sr_get (ss_regs ssc) 10%bv) in change (sr_get (ss_regs ssc) 10%bv) with e in P10
  end.
  cbn [ms_regs restrict] in P10.
  rewrite (denot_lit_U E), (s23n_U_dest E mn mt E11 E35 ltac:(lia) ltac:(lia)) in P10.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?mdT) _ =>
    set (rT0 := rT) in *; set (mT0 := mT) in *; set (mdT0 := mdT) in * end.
  assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 112 <= a < x_s1 cx + 136) -> rdW W mT0 a = rdW W mem a).
  { intros a Ha Hna. rewrite (K2 a Ha Hna). exact (K1 a Ha Hna). }
  clear K1 K2.
  assert (HspT : spZ rT0 = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
  { unfold spZ. rewrite P2, E2, R2. unfold w64. rewrite unsigned_lit_small by lia. ring. }
  assert (P3' : getr rT0 3 = w64 (as_gp B)) by (rewrite P3, E3, R3; exact Hgp).
  assert (P4' : getr rT0 4 = w64 (as_tp B)) by (rewrite P4, E4, R4; exact Htp).
  assert (P11' : getr rT0 11 = w64 (x_fr cx + 32)) by (rewrite P11, E33; reflexivity).
  assert (HraT : YK0s.ret_ok (Z_to_bv 64 (BASE + 4144))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
  pose proof (proj1 HJ) as HART.
  (* ---- __asan_memcpy(mt + 20 mn, v, 20) ---- *)
  eapply SRr_bind.
  { apply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA SS___asan_memcpy) (AMEMCPY fx) W rT0 mT0
      STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
      [(LT_FCLS, x_fpos cx)] ly S mdT0 k (mt + 20 * mn) (x_fr cx + 32) 20 (x_s1 cx - x_sp0 cx)
      (Z_to_bv 64 (BASE + 4144)) HJ P10 P11' P12 ltac:(lia) ltac:(lia) ltac:(lia) HspT ltac:(lia) ltac:(lia)
      ltac:(rewrite Hes, WS; lia) P3' P4' P1 HraT).
    - intros a Ha. split.
      + right; right; left. exists mt, (x_mtn cx). split; [exact HmtIn|].
        split; [exact HmtN0 | rewrite (s23n_req _ Hmtn0); lia].
      + rewrite Hes. lia.
    - intros a Ha HFP _. exfalso. destruct HFP as (r0 & Hr0 & Hlo & Hhi). cbn [ltoi_PG In] in Hr0.
      destruct Hr0 as [<- | []]. cbn [fst snd] in Hlo, Hhi.
      pose proof (blk_off_imgP B ly S W mem md mt (x_mtn cx) HAR HmtIn) as Hoff. unfold off_img in Hoff.
      rewrite (s23n_req _ Hmtn0) in Hoff. unfold longlA, A_LONGL, LONGL_N in *. lia.
    - exact (amem_range_of_block SEGS B LAWS ly S W mem md mt (x_mtn cx) (mt + 20 * mn) 20 HAR HmtIn
        ltac:(lia) ltac:(rewrite (s23n_req _ Hmtn0); lia)).
    - exact (range_addressable_of_block SEGS B LAWS ly S W mT0 mdT0 mt (x_mtn cx) (mt + 20 * mn) 20 HART HmtIn
        ltac:(lia) ltac:(rewrite (s23n_req _ Hmtn0); lia)).
    - intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mT0 mdT0 mt (x_mtn cx) (mt + 20 * mn) 20 HART
        HmtIn ltac:(lia) ltac:(rewrite (s23n_req _ Hmtn0); lia) Hpos).
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - rewrite KT; [| lia | lia]. apply (aview_some_of_apresent SEGS). apply Hfrpres. lia.
        - rewrite HspT, Hes. lia. }
      split; [lia|]. split.
      { unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
        unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia. }
      split.
      { apply s23n_v_addr; [exact Hfr32 | | |]; rewrite <- Hsh; rewrite KT; unfold SHADOW_OFF in Hshr; try lia.
        - exact (HSH 4%nat ltac:(rewrite lt_fsh_len; lia)).
        - exact (HSH 5%nat ltac:(rewrite lt_fsh_len; lia)).
        - exact (HSH 6%nat ltac:(rewrite lt_fsh_len; lia)). }
      intros _ s Hs. pose proof (s23n_v_hull (x_fr cx) s Hfr32 Hs) as Hs'. rewrite <- Hsh in Hs'.
      rewrite KT; unfold SHADOW_OFF in Hshr; [| lia | lia].
      apply (aview_some_of_apresent SEGS). replace s with (x_sh cx + (s - x_sh cx)) by lia.
      exact (proj1 (HFsp (s - x_sh cx) ltac:(lia))). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HCPY & HKC & _ & _).
  (* ---- back at 0x85df0: the s1 region kept, the clobbered registers fresh atoms from 40 ---- *)
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
  match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U9; intros a Ha.
    - apply (mbyte_of_aview SEGS). apply HKC; [lia | lia | rewrite Hes; lia].
    - intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite WS. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 40 (map (getr regs2) CLOB)) as Ea eqn:HEa.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall n, (n < 40)%nat -> ew Ea n = ew E n)
    by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
  assert (HAEa : env_agree 32 (Ereg regs (s23n_ext (x_cap cx) (x_fr cx + 32) ad mt (x_sh cx))) Ea).
  { destruct HAE as [HA1 HA2]. split; [intros n Hn; rewrite OLDa by lia; exact (HA1 n Hn) | rewrite HEa; exact HA2]. }
  assert (U9a : bv_unsigned (ew Ea 9) = x_s1 cx) by (rewrite OLDa by lia; exact U9).
  assert (SHOKa : sh_ok SEGS s23n_x [] Ea (mrestrict (w_H W) mem2)) by (unfold sh_ok; apply Forall_nil).
  assert (E11a : ew Ea 11 = Z_to_bv 64 mn) by (rewrite OLDa by lia; exact E11).
  assert (E34a : ew Ea 34 = Z_to_bv 64 ad) by (rewrite OLDa by lia; exact E34).
  assert (E35a : ew Ea 35 = Z_to_bv 64 mt) by (rewrite OLDa by lia; exact E35).
  clear HEa.
  (* ---- 0x85df0 .. 0x85e14: added + 1 (UBSan's test decided), mn + 1, a6 and s8 reloaded, j 0x85b58 ---- *)
  paj_run_to_tok RUNTO HS HJ2 SHOKa s23n_SB LO_B58.
  { s23n_awr1 cx U9a WS. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv4 := d) in *; clearbody mdv4 end.
  s23n_keepW K4 (x_s1 cx) U9a.
  clear HF HFr HG.
  try rename ms into ms_old.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into ms end.
  (* the slots the stretch wrote *)
  assert (W112 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 112) = Some (ad + 1))
    by exact (s23n_chunk_word W Ea _ ms 0 _ 9 (x_s1 cx) 112 (SOff 34 1) (ad + 1) HS eq_refl eq_refl U9a
      ltac:(vm_compute; s23n_in) ltac:(cbn [sv_denot]; rewrite E34a, unsigned_lit_small by lia; reflexivity)
      ltac:(lia)).
  assert (W120 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 120) = Some mt)
    by exact (s23n_chunk_word W Ea _ ms 0 _ 9 (x_s1 cx) 120 (SOff 35 0) mt HS eq_refl eq_refl U9a
      ltac:(vm_compute; s23n_in) ltac:(cbn [sv_denot]; rewrite E35a, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(lia)).
  assert (W128 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 128) = Some (mn + 1))
    by exact (s23n_chunk_word W Ea _ ms 0 _ 9 (x_s1 cx) 128 (SOff 11 1) (mn + 1) HS eq_refl eq_refl U9a
      ltac:(vm_compute; s23n_in) ltac:(cbn [sv_denot]; rewrite E11a, unsigned_lit_small by lia; reflexivity)
      ltac:(lia)).
  (* the registers the stretches kept *)
  pose proof (regs_kept_of_st_ok_pi Ea _ _ regs (s23n_ext (x_cap cx) (x_fr cx + 32) ad mt (x_sh cx))
    [2; 3; 4; 8; 9; 16; 20; 21; 22; 24; 26; 27]%bv HS HAEa ltac:(vm_compute; reflexivity)) as HKR0.
  cbn [ms_regs restrict] in HKR0.
  assert (HKR : forall r : bv 5, In r [2; 3; 4; 8; 9; 16; 20; 21; 22; 24; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. exact (HKR0 r Hr). }
  pmkst HS.
  (* the memory: v copied to mt[mn]; the rest differs from the cut's only in the slots 112 .. 136, the copy and
     the runtime's window below s1 *)
  assert (KALL : forall a, 0 <= a < 2 ^ 64 ->
    ~ (x_s1 cx + 112 <= a < x_s1 cx + 136 \/ mt + 20 * mn <= a < mt + 20 * mn + 20 \/ x_s1 cx - 4096 <= a < x_s1 cx) ->
    rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha Hna. rewrite (K4 a Ha ltac:(tauto)). rewrite (HKC a Ha ltac:(tauto) ltac:(rewrite Hes; lia)).
    exact (KT a Ha ltac:(tauto)). }
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ s23_win cx mt a -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha Hw. apply KALL; [exact Ha|]. intros [H1 | [H1 | H1]]; apply Hw; unfold s23_win, ESTACK.
    - right; left. exact H1.
    - right; right; right. lia.
    - left. lia. }
  assert (HSH' : sa_zs (rdW W (ms_mem ms)) (x_sh cx) (lt_fsh LFO_NV)).
  { intros j Hj. pose proof Hj as Hj'. rewrite lt_fsh_len in Hj'. rewrite KALL.
    - exact (HSH j Hj).
    - unfold SHADOW_OFF in Hshr. lia.
    - intros [H1 | [H1 | H1]]; [unfold SHADOW_OFF in Hshr; lia | | unfold SHADOW_OFF in Hshr; lia].
      apply (s23n_app_not_sh (x_sh cx + Z.of_nat j) (x_fr cx) 0 36
        (s23n_app_in _ _ (x_sh cx + Z.of_nat j) HMTapp ltac:(lia))
        Hfr4096 Hfrceil ltac:(lia) ltac:(lia)). rewrite <- Hsh. lia. }
  pose proof (s23_body_kept B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid (ms_regs ms) (ms_mem ms) mdv4
    LFO_NV HB HBODY HJ2 (HKR 2%bv ltac:(s23n_in)) (HKR 3%bv ltac:(s23n_in)) (HKR 4%bv ltac:(s23n_in)) (HKR 8%bv ltac:(s23n_in))
    (HKR 9%bv ltac:(s23n_in)) KW HSH') as HBODY'.
  pose proof (HDS Hlt) as HDS'. fold t ad in HDS'.
  refine (HJS cx ly S W (ms_regs ms) (ms_mem ms) mdv4 k acc c m tab mt par vid HB HFRM HBODY' _ _ _ _ _).
  + split; [rewrite (HKR 16%bv ltac:(s23n_in)); exact R16|]. split; [rewrite (HKR 20%bv ltac:(s23n_in)); exact R20|].
    split; [rewrite (HKR 21%bv ltac:(s23n_in)); exact R21|]. split; [rewrite (HKR 22%bv ltac:(s23n_in)); exact R22|].
    split; [rewrite (HKR 26%bv ltac:(s23n_in)); exact R26|]. rewrite (HKR 27%bv ltac:(s23n_in)); exact R27.
  + rewrite HDS'. cbn [fst]. lia.
  + intros o w Hin. unfold LT_LV, LT_LD in Hin. rewrite HDS' in Hin. cbn [fst snd app In] in Hin.
    destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]]]]]]]]]]]]]]]];
      injection Hq as <- <-.
    13: exact W112.
    13: exact W120.
    13: { replace (Z.of_nat (length (t ++ [(par, vid)]))) with (mn + 1)
            by (unfold mn; rewrite length_app; cbn [length]; lia). exact W128. }
    all: apply (s23n_slot_kept (rdW W mem) (rdW W (ms_mem ms)) (x_s1 cx) _ _ _ KALL);
      [ intros kk Hkk; split; [lia | intros [H1 | [H1 | H1]]; lia]
      | apply HSL; apply in_or_app; first [left; unfold LT_LV; s23n_in | right; unfold LT_LD; s23n_in] ].
  + rewrite HDS'. cbn [snd].
    pose proof (s23_tabs_kept B MT cx (rdW W mem) (rdW W (ms_mem ms)) tab mt t) as HTK.
    destruct (HTK) as (Hc0 & Hrt & Hg & Hn & _ & _); [| | | exact HTABS |].
    { intros a Ha. apply KALL; [lia|]. intros [H1 | [H1 | H1]]; lia. }
    { intros a Ha. unfold FO_N in Ha. apply KALL; [lia|]. intros [H1 | [H1 | H1]]; lia. }
    { intros a Ha. apply KALL; [lia|]. intros [H1 | [H1 | H1]]; unfold mn in *; lia. }
    split; [exact Hc0|]. split; [exact Hrt|]. split; [exact Hg|]. split; [exact Hn|].
    split; [|rewrite length_app; cbn [length]; unfold mn in Hlt; lia].
    apply (s23_mtab_app B MT (rdW W mem) (rdW W (ms_mem ms)) mt t (x_fr cx + 32) par vid).
    * destruct HTABS as (_ & _ & _ & _ & HMT & _). exact HMT.
    * intros a Ha. apply KALL; [lia|]. intros [H1 | [H1 | H1]]; unfold mn in *; lia.
    * intros j Hj. rewrite K4; [| lia | lia].
      change (mt + 20 * Z.of_nat (length t) + j) with (mt + 20 * mn + j). rewrite (HCPY j Hj).
      apply KT; lia.
    * intros j Hj. destruct (rdW W mem (x_fr cx + 32 + j)) as [z|] eqn:Ez.
      -- exists z. split; [reflexivity|]. destruct (aview_byte SEGS _ _ _ _ Ez) as (_ & _ & _ & Rz). exact Rz.
      -- exfalso. apply (aview_some_of_apresent SEGS (w_H W) mem (x_fr cx + 32 + j)); [apply Hfrpres; lia | exact Ez].
    * exact HPAR.
    * lia.
    * replace (x_fr cx + 32 + 16) with (x_fr cx + FO_VID) by (unfold FO_VID; lia). exact HVID.
    * lia.
  + rewrite (HKR 24%bv ltac:(s23n_in)). exact R24.
- (* ======== mn >= cap: v out of scope, 112(s1) := -1, to K85e50 ======== *)
  set (E := s23n_E regs (x_cap cx) (x_fr cx + 32) ad mt (x_sh cx)).
  assert (E11 : ew E 11 = Z_to_bv 64 mn) by (subst E; rewrite (s23n_E_lo _ _ _ _ _ _ 11 11%bv eq_refl); exact R11).
  assert (E32 : ew E 32 = Z_to_bv 64 (x_cap cx)) by (subst E; exact (s23n_E_x _ _ _ _ _ _ 0 ltac:(lia))).
  assert (HCS : conds_ok E [mkAC BC_GE (SOff 11 0) (SOff 32 0)]).
  { split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
    rewrite (s23n_lts E 11 32 mn (x_cap cx) E11 E32 ltac:(lia) ltac:(lia)).
    apply negb_true_iff, Z.ltb_ge. lia. }
  pose proof (s23n_seed W regs mem _ (x_s1 cx) (x_cap cx) (x_fr cx + 32) ad mt (x_sh cx) mn m R9 R11 R24 R16
    Hs1r ltac:(lia) Hmn Had' ltac:(lia) Hshr ltac:(lia) ltac:(unfold seg_spec.SEG_M_SIZE in *; lia) HCS Hpres1
    G40 G64 G112 G120 G128 H184 G192 HSB)
    as HS0.
  fold E in HS0.
  assert (E9 : ew E 9 = getr regs 9) by (subst E; apply (s23n_E_lo _ _ _ _ _ _ 9 9%bv eq_refl)).
  assert (U9 : bv_unsigned (ew E 9) = x_s1 cx) by (rewrite E9, R9; apply unsigned_lit_small; lia).
  assert (E36 : ew E 36 = Z_to_bv 64 (x_sh cx)) by (subst E; exact (s23n_E_x _ _ _ _ _ _ 4 ltac:(lia))).
  assert (U36 : bv_unsigned (ew E 36) = x_sh cx) by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  assert (E35 : ew E 35 = Z_to_bv 64 mt) by (subst E; exact (s23n_E_x _ _ _ _ _ _ 3 ltac:(lia))).
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold s23n_E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (s23n_ext (x_cap cx) (x_fr cx + 32) ad mt (x_sh cx))) E) by (subst E; apply s23n_E_agree).
  assert (HS : st_ok_pi SEGS VAL E s23n_ssA (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_DAC)) mem (seg_rom SEGS)))).
  { refine (st_ok_pi_add_region E _ _ s23n_sh HS0 eq_refl _ _).
    - cbn [ms_mem restrict mkst]. try rewrite restrict_mkst_fx. cbn [ms_mem].
      unfold region_ok, s23n_sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U36. unfold SHADOW_OFF in Hshr. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (HFsp o ltac:(lia))) | apply Forall_nil].
    - unfold s23n_ss. cbn [ss_mem all_disjoint]. split; [|exact I]. unfold extent_disjoint, s23n_sh, s23n_s1.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U36, U9. left. unfold SHADOW_OFF in Hshr. lia. }
  clear HS0.
  assert (SHOK : sh_ok SEGS s23n_x [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
  clearbody E.
  paj_run_to_tok RUNTO HS HJ SHOK s23n_SB LO_K85e50.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
    eapply awr_ok_cons_gen with (n := 36%nat) (b := x_sh cx); [reflexivity | exact U36 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
      exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
      rewrite EFA, <- Hsh. change (fs_frame_bytes LT_FCLS / 8) with 64. lia. }
    eapply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
      [reflexivity | rewrite U9; ring | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  (* the stretch wrote v's shadow bytes and 112(s1) only *)
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 112 <= a < x_s1 cx + 136 \/ x_sh cx + 4 <= a < x_sh cx + 7) ->
    rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha Hna.
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _
      (fun a => x_s1 cx + 112 <= a < x_s1 cx + 136 \/ x_sh cx + 4 <= a < x_sh cx + 7) HFr); [|exact Ha | exact Hna].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    destruct Hin as [Hq0 | [Hq0 | []]]; injection Hq0 as <- <- <-; cbn [base_val] in Hrr;
      [rewrite U36 in Hrr; right; lia | rewrite U9 in Hrr; left; lia]. }
  clear HF HFr HG.
  (* the bytes and slots the stretch wrote *)
  assert (B4 : rdW W (ms_mem ms) (x_sh cx + 4) = Some 248)
    by exact (s23n_chunk_byte W E _ ms 0 _ 36 (x_sh cx) 4 18446744073709551608 HS eq_refl eq_refl U36
      ltac:(vm_compute; s23n_in)).
  assert (B5 : rdW W (ms_mem ms) (x_sh cx + 5) = Some 248)
    by exact (s23n_chunk_byte W E _ ms 0 _ 36 (x_sh cx) 5 18446744073709551608 HS eq_refl eq_refl U36
      ltac:(vm_compute; s23n_in)).
  assert (B6 : rdW W (ms_mem ms) (x_sh cx + 6) = Some 248)
    by exact (s23n_chunk_byte W E _ ms 0 _ 36 (x_sh cx) 6 18446744073709551608 HS eq_refl eq_refl U36
      ltac:(vm_compute; s23n_in)).
  assert (W112 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 112) = Some 18446744073709551615)
    by exact (s23n_chunk_word W E _ ms 1 _ 9 (x_s1 cx) 112 (SLit 18446744073709551615) 18446744073709551615 HS
      eq_refl eq_refl U9 ltac:(vm_compute; s23n_in) eq_refl ltac:(lia)).
  assert (W120 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 120) = Some mt)
    by exact (s23n_chunk_word W E _ ms 1 _ 9 (x_s1 cx) 120 (SOff 35 0) mt HS eq_refl eq_refl U9
      ltac:(vm_compute; s23n_in) ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(lia)).
  assert (W128 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 128) = Some mn)
    by exact (s23n_chunk_word W E _ ms 1 _ 9 (x_s1 cx) 128 (SOff 11 0) mn HS eq_refl eq_refl U9
      ltac:(vm_compute; s23n_in) ltac:(cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(lia)).
  (* the registers the stretch kept *)
  pose proof (regs_kept_of_st_ok_pi E _ _ regs (s23n_ext (x_cap cx) (x_fr cx + 32) ad mt (x_sh cx))
    [2; 3; 4; 8; 9; 24]%bv HS HAE ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  pmkst HS.
  (* m_declared failed at seg[i]: (-1, t) *)
  pose proof (@s23_decl_fail fx rc SK PI cx i par vid Hi Hign Hsplit ltac:(change (0 <= ad); lia) HDUP
    ltac:(change (x_cap cx <= mn); lia)) as HMD.
  (* the body at the new state, v out of scope *)
  assert (HSH' : sa_zs (rdW W (ms_mem ms)) (x_sh cx) (lt_fsh LFO_N)).
  { intros j Hj. rewrite lt_fsh_len in Hj.
    destruct (Nat.eq_dec j 4) as [-> | J4]; [exact B4|].
    destruct (Nat.eq_dec j 5) as [-> | J5]; [exact B5|].
    destruct (Nat.eq_dec j 6) as [-> | J6]; [exact B6|].
    rewrite KA.
    - rewrite (HSH j ltac:(rewrite lt_fsh_len; lia)). f_equal. apply s23n_fsh_NV_N; assumption.
    - unfold SHADOW_OFF in Hshr. lia.
    - intros [H1 | H1]; [unfold SHADOW_OFF in Hshr; lia | lia]. }
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ s23_win cx mt a -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha Hw. apply KA; [exact Ha|]. intros [H1 | H1]; apply Hw; unfold s23_win; [right; left | right; right; left];
    exact H1. }
  pose proof (s23_body_kept B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid (ms_regs ms) (ms_mem ms) mdv
    LFO_N HB HBODY HJ (HKR 2%bv ltac:(s23n_in)) (HKR 3%bv ltac:(s23n_in)) (HKR 4%bv ltac:(s23n_in)) (HKR 8%bv ltac:(s23n_in))
    (HKR 9%bv ltac:(s23n_in)) KW HSH') as HBODY'.
  pose proof HBODY' as (HCORE' & Hhc' & Hhm' & Hhtab' & Hhmt' & _ & _ & _ & _ & Hcm').
  refine (HE50 fx cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m tab mt HB HFRM HCORE' Hhc' Hhm' Hhtab' Hhmt'
    _ _ Hcm' _).
  + rewrite (HKR 24%bv ltac:(s23n_in)). exact R24.
  + rewrite HMD. intros o w Hin. cbn [fst snd In] in Hin.
    destruct Hin as [Hq | [Hq | [Hq | [Hq | [Hq | [Hq | [Hq | [Hq | [Hq | []]]]]]]]]]; injection Hq as <- <-;
      [ | | | | | rewrite W112; reflexivity | exact W120 | exact W128 | ];
      (apply (s23n_slot_kept (rdW W mem) (rdW W (ms_mem ms)) (x_s1 cx) _ _ _ KA);
       [intros kk Hkk; split; [lia | intros [H1 | H1]; unfold SHADOW_OFF in Hshr; lia]
       | apply HSL; apply in_or_app; first [left; unfold LT_LV; s23n_in | right; unfold LT_LD; s23n_in]]).
  + rewrite HMD. cbn [snd].
    apply (s23_tabs_kept B MT cx (rdW W mem) (rdW W (ms_mem ms)) tab mt t); [| | | exact HTABS].
    * intros a Ha. apply KA; [lia|]. intros [H1 | H1]; [lia|].
      rewrite Hsh in H1. exact (s23n_app_not_sh a (x_fr cx) 4 7 (s23n_app_in _ _ a HTBapp Ha) Hfr4096 Hfrceil
        ltac:(lia) ltac:(lia) H1).
    * intros a Ha. apply KA; [unfold FO_N in Ha; lia|]. intros [H1 | H1]; [unfold FO_N in Ha; lia|].
      rewrite Hsh in H1. exact (s23n_app_not_sh a (x_fr cx) 4 7 (s23n_app_in _ _ a HFapp ltac:(unfold FO_N in Ha; lia))
        Hfr4096 Hfrceil ltac:(lia) ltac:(lia) H1).
    * intros a Ha. apply KA; [lia|]. intros [H1 | H1]; [lia|].
      rewrite Hsh in H1. exact (s23n_app_not_sh a (x_fr cx) 4 7 (s23n_app_in _ _ a HMTapp ltac:(lia)) Hfr4096 Hfrceil
        ltac:(lia) ltac:(lia) H1).
Qed.

End e.
End f.
End d.

(* ================================== piece L (0x85d30) ==================================
reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256
   c3796c0b38f3): one turn of the dup loop of m_declared's inlined turn i in the test harness's entry function
   LLVMFuzzerTestOneInput (0x84dc0), segment S15: s23_L, the inner cut S23_L_stmt i q (0x85d30, LLVMFuzzerTestOneInput_s23k.v)
   from S23_L_stmt i (q + 1), S23_J_stmt i and S23_N_stmt i.

   The code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s, 0x85d30 .. 0x85da8):
     0x85d30 .. 0x85d3c  ld a0,152(s1) (~MT); bltu a0,s8 (UBSan trap 34: MT + 20 q wraps): decided in the run by the
                         ranges of the slot's atom (>= 2^64 - 1 - 2^47) and of s8 = 20 q (<= 780); ld a0,160(s1) = 1;
                         beqz (trap 35): decided by the literal
     0x85d40 .. 0x85d4c  the 4-byte check of mt[q].vid at s3 = MT + 16 + 20 q (check 34): a token whose obligation is
                         discharged by mt's live block (range_addressable_of_block); its slow block 0x85d90 is the
                         token's, its report edge 0x8611c is never taken
     0x85d50 .. 0x85d58  lw a0,16(s7) (the vid of mt[q], sign-extended), sext.w a1,s5 (vid), bne: split
       vids differ       0x85d74 a0 := 0, to the latch 0x85d78
       vids agree        0x85d5c .. 0x85d64 a0 := s7 = &mt[q], a1 := 64(s1) = v, the strcmp interceptor
                         (RtString.astrcmp_realizes through PaArt.v's aj_art_at); back at 0x85d68: a6 := 200(s1),
                         seqz a0 (strcmp's answer is 0 exactly when the two parents agree), to the latch
     0x85d78 .. 0x85d88  s2 |= a0, s7, s8, s3 += 20, bne s9,s8: split
       q + 1 < mn        back to the head 0x85d30: S23_L_stmt i (q + 1)
       q + 1 = mn        0x85d8c j 0x85da0; s8 := 192(s1) = m, a1 := 128(s1) = mn, bnez s2: split
         a duplicate     0x85b58: S23_J_stmt i (m_declared's turn keeps its table, s23_decl_S)
         none            0x85dac: S23_N_stmt i
   No UBSan trap edge and no error-path call is reached. The inner point s23l_X_stmt i q is the latch 0x85d78
   (LO_D78), stated as S23_L_stmt i q with a0 = whether mt[q] is (par, vid). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YK06 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB LLVMFuzzerTestOneInput_defs.

(* 0x85d78 `or s2,a0,s2`: the latch of the dup loop's turn q (offset from BASE = 0x84dc0) *)
Definition LO_D78 : Z := 0xfb8.
(* whether the entry q of the table is (par, vid): the code's test (the vids first, then strcmp) *)
Definition s23l_hit (t : list (list Z * Z)) (q : nat) (par : list Z) (vid : Z) : bool :=
  (snd (nth q t ([], 0)) =? vid) && (SegModel.strcmp (fst (nth q t ([], 0))) par =? 0).

(* lw's sign extension of an unsigned 32-bit table vid, compared with a vid in [1, 4094] *)
Lemma s23l_sext_eq : forall v x, 0 <= v < 2 ^ 32 -> 1 <= x <= 4094 ->
  (zcanon (bv_swrap 32 (v mod 2 ^ Z.of_N 32)) =? x) = (v =? x).
Proof.
intros v x Hv Hx. change (Z.of_N 32) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, zcanon, M64. change (Z.of_N 32) with 32. change (2 ^ 32 / 2) with (2 ^ 31).
destruct (Z.ltb_spec v (2 ^ 31)) as [Hl|Hl].
- rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
  rewrite Z.mod_small by lia. reflexivity.
- replace (v + 2 ^ 31) with ((v - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (v - 2 ^ 31) (2 ^ 32)) by lia.
  replace (v - 2 ^ 31 - 2 ^ 31) with ((v + 2 ^ 64 - 2 ^ 32) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia. destruct (Z.eqb_spec (v + 2 ^ 64 - 2 ^ 32) x); destruct (Z.eqb_spec v x); lia.
Qed.

(* strcmp's answer, through seqz, is the model's equality test of the two parents *)
Lemma s23l_hit_eq : forall (r : word) a p,
  (r = w64 0 <-> seg_spec.zb a = seg_spec.zb p) -> seg_spec.zs (seg_spec.zb a) = a -> seg_spec.zs (seg_spec.zb p) = p ->
  ~ In 0 a -> ~ In 0 p -> (if bv_unsigned r <? 1 then 1 else 0) = seg_spec.b2z (SegModel.strcmp a p =? 0).
Proof.
intros r a p HQ Za Zp Ha Hp. pose proof (bv_unsigned_in_range 64 r) as Rr. change (bv_modulus 64) with (2 ^ 64) in Rr.
destruct (SegModel.strcmp a p =? 0) eqn:Es.
- apply (s23_strcmp0 a p Ha Hp) in Es. subst p. rewrite (proj2 HQ eq_refl). reflexivity.
- assert (Hne : r <> w64 0).
  { intros Hr. apply HQ in Hr. assert (a = p) by (rewrite <- Za, <- Zp, Hr; reflexivity). subst p.
    rewrite (proj2 (s23_strcmp0 a a Ha Ha) eq_refl) in Es. discriminate. }
  destruct (Z.ltb_spec (bv_unsigned r) 1) as [Hl|Hl]; [|reflexivity].
  exfalso. apply Hne. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Section f. Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).  #[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA s := (@pa_sigma _ seg_listing PI s).  #[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ---- the fresh symbolic seat of a stretch: every register its own atom, atoms 32.. given ---- *)
Definition s23l_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (Ereg regs extra).
Lemma s23l_E_reg : forall regs extra n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s23l_E regs extra) n = getr regs rr.
Proof.
intros regs extra n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold s23l_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma s23l_E_extra : forall regs extra j, (j < 8)%nat -> ew (s23l_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. unfold s23l_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma s23l_E_img : forall regs extra, img_env VAL A_LIM (s23l_E regs extra).
Proof. intros regs extra. unfold s23l_E. apply Eimg_env. Qed.
Lemma s23l_E_agree : forall regs extra, env_agree 32 (Ereg regs extra) (s23l_E regs extra).
Proof. intros regs extra. split; [intros n Hn; unfold s23l_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.
Lemma s23l_seat : forall (W : world SEGS) (regs : bvmap 5 word) mem pc extra rs ats,
  regions_wf rs = true ->
  Forall (region_ok SEGS (s23l_E regs extra) (mrestrict (w_H W) mem)) rs ->
  pairwise_disjoint (s23l_E regs extra) rs ->
  atoms_ok (s23l_E regs extra) ats ->
  st_ok_pi SEGS VAL (s23l_E regs extra) (mkSS pc sr_atoms rs None (mkFacts ats [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc extra rs ats Hwf Hrs Hpd Hat.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s23l_E. apply regs_ok_Eimg_Ereg.
- exact Hwf.
- exact Hrs.
- exact Hpd.
- split; [exact Hat | split; exact I].
Qed.
Lemma s23l_afact : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi Hn Hv Hl. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hn, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
(* a chunk of a region: an 8-byte word, or the 4 bytes of an unsigned value *)
Lemma s23l_chunk8 : forall (W : world SEGS) mem E base off e v,
  rdword (rdW W mem) (base + off) = Some v -> 0 <= v < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros W mem E base off e v Hw Hv He.
apply (chunk_ok_val SEGS E _ base off 8 e v); [exact He | cbn; lia | cbn; lia |].
exact (val_mem_of_rdword SEGS (w_H W) mem _ v Hw).
Qed.
Lemma s23l_val_mem : forall (W : world SEGS) mem a n v,
  sa_val (rdW W mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v H k Hk. specialize (H k Hk). unfold aview in H.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in H; [|discriminate].
injection H as H. f_equal. change (YO0f.le_byte v n k) with (le_byte v n k). rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma s23l_chunk4 : forall (W : world SEGS) mem E base off e v,
  sa_val (rdW W mem) (base + off) 4 v -> 0 <= v < 2 ^ 32 -> sv_denot E e = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 4 e)).
Proof.
intros W mem E base off e v Hw Hv He.
apply (chunk_ok_val SEGS E _ base off 4 e v); [exact He | cbn; lia | cbn; lia |].
exact (s23l_val_mem W mem _ 4 v Hw).
Qed.
(* a register the run left as its own atom, and a register the run computed *)
Lemma s23l_reg_keep : forall (regs regs0 : bvmap 5 word) (rr : bv 5) E (n : nat),
  getr regs rr = sv_denot E (SOff n 0) -> ew E n = getr regs0 rr -> getr regs rr = getr regs0 rr.
Proof. intros regs regs0 rr E n H Hn. rewrite H. cbn [sv_denot]. rewrite Hn, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma s23l_reg_U : forall (regs : bvmap 5 word) (rr : bv 5) E e v,
  getr regs rr = sv_denot E e -> U E e = v -> getr regs rr = w64 v.
Proof. intros regs rr E e v H HU. rewrite H. unfold w64. rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* a run that writes nothing leaves every byte a reader sees *)
Lemma s23l_ro_kept : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> rs_read_only rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros E rs H m m' HF Hro a. unfold aview. rewrite (frame_of_read_only E rs _ _ Hro HF). reflexivity. Qed.
Lemma s23l_zs_kept : forall (rd rd' : reader) a l, (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) ->
  sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l HK H j Hj. rewrite HK by lia. exact (H j Hj). Qed.
Ltac s23l_prraw HS r P :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as P;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in P;
    cbn [ms_regs restrict mkst] in P
  end.
Ltac s23l_vreg HS r := let P := fresh "P" in s23l_prraw HS r P; apply (s23l_reg_U _ _ _ _ _ P).
(* v = FR + 32 at LFO_NV: its first 16 bytes are addressable (shadow 00 00 at SH(FR) + 4, + 5) and the shadow words
   around them are mapped (the frame's 36 shadow bytes) *)
Lemma s23l_v_read : forall (rd : reader) fr n,
  fr mod 32 = 0 -> 0 <= fr -> sa_zs rd (shadow_addr fr) (lt_fsh LFO_NV) -> 0 < n <= 16 ->
  range_addressable rd SHADOW_OFF (fr + 32) n /\ shadow_hull_vis rd (fr + 32) n.
Proof.
intros rd fr n H32 H0 HZ Hn.
apply Z.mod_divide in H32; [|lia]. destruct H32 as [w Hw].
assert (Hsh : shadow_addr fr = 2147450880 + 4 * w).
{ unfold shadow_addr, SHADOW_OFF. rewrite Hw. replace (w * 32) with ((4 * w) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (HB : forall j, 0 <= j < 36 -> rd (shadow_addr fr + j) = Some (nth (Z.to_nat j) (lt_fsh LFO_NV) 0)).
{ intros j Hj. rewrite <- (Z2Nat.id j) at 1 by lia. apply HZ. rewrite lt_fsh_len. lia. }
assert (Hd : forall x, fr + 32 <= x < fr + 48 -> shadow_of_addr SHADOW_OFF x = shadow_addr fr + 4 + (x - fr - 32) / 8).
{ intros x Hx. unfold shadow_of_addr. rewrite Hsh. unfold SHADOW_OFF.
  replace x with ((4 * w + 4) * 8 + (x - fr - 32)) by lia. rewrite Z.div_add_l by lia.
  replace ((4 * w + 4) * 8 + (x - fr - 32) - fr - 32) with (x - fr - 32) by lia. lia. }
split.
- intros x Hx. rewrite (Hd x ltac:(lia)). exists 0. split; [|left; reflexivity].
  assert (Hq : (x - fr - 32) / 8 = 0 \/ (x - fr - 32) / 8 = 1).
  { pose proof (Z.div_pos (x - fr - 32) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (x - fr - 32) 8 2 ltac:(lia) ltac:(lia)). lia. }
  destruct Hq as [Hq | Hq]; rewrite Hq.
  + rewrite Z.add_0_r, (HB 4) by lia. reflexivity.
  + replace (shadow_addr fr + 4 + 1) with (shadow_addr fr + 5) by lia. rewrite (HB 5) by lia. reflexivity.
- intros s Hs.
  assert (A1 : shadow_addr (fr + 32) = 2147450880 + 4 * w + 4).
  { unfold shadow_addr, SHADOW_OFF. rewrite Hw. replace (w * 32 + 32) with ((4 * w + 4) * 8) by ring. rewrite Z.div_mul by lia. lia. }
  assert (A2 : shadow_addr (fr + 32 + n - 1) = 2147450880 + 4 * w + 4 + (n - 1) / 8).
  { unfold shadow_addr, SHADOW_OFF. rewrite Hw. replace (w * 32 + 32 + n - 1) with ((4 * w + 4) * 8 + (n - 1)) by ring.
    rewrite Z.div_add_l by lia. lia. }
  rewrite A1, A2 in Hs.
  assert (Hq : (n - 1) / 8 = 0 \/ (n - 1) / 8 = 1).
  { pose proof (Z.div_pos (n - 1) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (n - 1) 8 2 ltac:(lia) ltac:(lia)). lia. }
  pose proof (Z.div_mod (2147450880 + 4 * w + 4) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (2147450880 + 4 * w + 4) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (2147450880 + 4 * w + 4 + (n - 1) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (2147450880 + 4 * w + 4 + (n - 1) / 8) 8 ltac:(lia)) as M2.
  replace s with (shadow_addr fr + (s - shadow_addr fr)) by lia. rewrite HB by lia. discriminate.
Qed.

Section e. Variable B : asyms. Variable MT : ameter_ops.
Hypothesis TL : PALib B.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @RtString.astrcmp_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strcmp).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS. Let BR := paj_branch (PI := PI). Let errno_low := pal_env B TL.

(* the slots of the m_declared loop lie at 16(s1) .. 216(s1) *)
Lemma s23l_slots_range : forall cx c m tab mt i o v, In (o, v) (LT_LV cx c m ++ LT_LD cx m tab mt i) -> 16 <= o <= 216.
Proof.
intros cx c m tab mt i o v Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; cbn [LT_LV LT_LD In] in Hin;
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as Ho _; subst o; lia|]); destruct Hin.
Qed.
(* v's parent: NUL-free, under 15 bytes; vid in [1, 4094] *)
Lemma s23l_par_facts : forall cx ly S W regs mem md k acc o c m tab mt i par vid,
  s23_body B MT cx ly S W regs mem md k acc o c m tab mt i par vid ->
  ~ In 0 par /\ (length par < 15)%nat /\ 1 <= vid <= 4094.
Proof.
intros cx ly S W regs mem md k acc o c m tab mt i par vid HBD.
destruct HBD as (_ & _ & _ & _ & _ & Hi & _ & Hsp & _ & (_ & Hmc)).
destruct (s23_name_facts B MT (rdW W mem) cx m i Hmc Hi) as [Hn0 Hn16].
exact (s23_split_facts _ par vid Hn0 Hn16 Hsp).
Qed.
(* the facts of a point of the dup loop carried to a later state of the same turn: the journal at the new memory,
   the registers sp gp tp s0 s1 s4 s5 s6 s10 s11 kept, a6 the shadow base, and every byte outside the runtime's
   scratch below s1 kept *)
Lemma s23l_carry : forall cx ly S W regs mem md k acc c m tab mt i par vid regs' mem' md',
  lt_base B MT cx ->
  s23_body B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid ->
  s23_regs regs m i vid ->
  lt_slots cx (rdW W mem) (LT_LV cx c m ++ LT_LD cx m tab mt i) ->
  lt_tabs cx (rdW W mem) tab mt (snd (x_decl cx i)) ->
  sa_strz (rdW W mem) (x_fr cx + FO_V) par -> sa_val (rdW W mem) (x_fr cx + FO_VID) 4 vid ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall r, In r [2; 3; 4; 8; 9; 20; 21; 22; 26; 27]%bv -> getr regs' r = getr regs r) ->
  getr regs' 16 = w64 SHADOW_OFF ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - 2 * ESTACK <= a < x_s1 cx) -> rdW W mem' a = rdW W mem a) ->
  s23_body B MT cx ly S W regs' mem' md' k acc LFO_NV c m tab mt i par vid /\ s23_regs regs' m i vid /\
  lt_slots cx (rdW W mem') (LT_LV cx c m ++ LT_LD cx m tab mt i) /\
  lt_tabs cx (rdW W mem') tab mt (snd (x_decl cx i)) /\
  sa_strz (rdW W mem') (x_fr cx + FO_V) par /\ sa_val (rdW W mem') (x_fr cx + FO_VID) 4 vid.
Proof.
intros cx ly S W regs mem md k acc c m tab mt i par vid regs' mem' md' HB0 HBD HRG HSL HTB Hv Hvid HJ' HR R16 HK.
pose proof (s23_facts B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid HB0 HBD) as
  (HAR & Hfin & Hfa & Hfr32 & Hfr4096 & Hfrceil & Hfrpres & Hsh & Hs132 & Hs1b & Hsp016 & Hsp0 & Hstk & Hcap & Hmtn &
   Htabn & Hmn & Hmt16 & Hmt4096 & Hmtceil & Htab16 & Htab4096 & Htabceil & _).
pose proof (s23l_par_facts cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid HBD) as (Hp0 & Hp15 & Hvr).
pose proof HBD as ((HFR & _) & _). pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSH & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. rewrite HSTK in Hsp0.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsh0 : 0 <= x_sh cx) by (rewrite Hsh; unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8); lia).
assert (Hsh1 : x_sh cx + 36 <= alloc_ceiling).
{ rewrite Hsh. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_le_upper_bound (x_fr cx) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
assert (KL : forall a, 0 <= a < alloc_ceiling -> rdW W mem' a = rdW W mem a) by (intros a Ha; apply HK; lia).
assert (KS : forall a, x_s1 cx <= a < x_s1 cx + 352 -> rdW W mem' a = rdW W mem a) by (intros a Ha; apply HK; lia).
unfold s23_regs in HRG |- *. destruct HRG as (_ & R20 & R21 & R22 & R26 & R27).
assert (HFSH' : sa_zs (rdW W mem') (x_sh cx) (lt_fsh LFO_NV)).
{ apply (s23l_zs_kept (rdW W mem)); [|exact HFSH]. rewrite lt_fsh_len. intros x Hx. apply KL. lia. }
split; [|split; [|split; [|split; [|split]]]].
- apply (s23_body_kept B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid regs' mem' md' LFO_NV HB0 HBD HJ');
    [apply HR; cbn; tauto | apply HR; cbn; tauto | apply HR; cbn; tauto | apply HR; cbn; tauto | apply HR; cbn; tauto | | exact HFSH'].
  intros a Ha Hw. apply HK; [exact Ha|]. intros Hn. apply Hw. left. exact Hn.
- split; [exact R16|].
  rewrite (HR 20%bv), (HR 21%bv), (HR 22%bv), (HR 26%bv), (HR 27%bv) by (cbn; tauto).
  split; [exact R20|]. split; [exact R21|]. split; [exact R22|]. split; [exact R26 | exact R27].
- apply (s23_slots_kept B MT cx (rdW W mem)); [|exact HSL].
  intros o v Hin a Ha. pose proof (s23l_slots_range cx c m tab mt i o v Hin). apply KS. lia.
- apply (s23_tabs_kept B MT cx (rdW W mem)); [| | |exact HTB].
  + intros a Ha. apply KL. unfold seg_spec.RVLAN_SIZE in *. lia.
  + intros a Ha. apply KL. unfold FO_N in Ha. lia.
  + intros a Ha. apply KL. lia.
- apply (s23_strz_kept B MT (rdW W mem)); [|exact Hv]. intros a Ha. apply KL. unfold FO_V in Ha. lia.
- apply (s23_val_kept B MT (rdW W mem)); [|exact Hvid]. intros a Ha. apply KL. unfold FO_VID in Ha. lia.
Qed.

(* the strcmp interceptor call: PaArt.v's aj_art_at over the contract RtString.astrcmp_realizes (as fuzz_command's
   aj_strspn_at_loc, LLVMFuzzerTestOneInput_s45.v:370-401), errno untouched (Eb = False) *)
Lemma s23l_strcmp_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  astr_at SEGS W memT x sx -> astr_at SEGS W memT y sy ->
  aread_ok SEGS (2 * ESTACK) W regsT memT x (astr_len sx + 1) ->
  aread_ok SEGS (2 * ESTACK) W regsT memT y (astr_len sy + 1) ->
  atail_vis SEGS W memT (x + astr_len sx) -> atail_vis SEGS W memT (y + astr_len sy) ->
  rt_rom_view SEGS B W memT ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_strcmp)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
  aregs_preserved regsT regs2 /\ (getr regs2 10 = w64 0 <-> sx = sy) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> ~ False ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy o raw
  HJ Ha0 Ha1 Hx Hy Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hrx Hry Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
apply (aj_art_at (fx := fx) SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
  (SIGMA SS___interceptor_trampoline_strcmp) W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
  (fun regs2 _ => getr regs2 10 = w64 0 <-> sx = sy)
  HJ Hsp Hal Hneg ltac:(lia) Hbud Hra (fun a F => False_ind _ F)).
apply (ASTRCMP fx lyc Sc W regsT memT mdc x y sx sy); try assumption.
apply (ecall_pre_stk_at SEGS B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg
  ltac:(lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp].
Qed.
(* the callee-saved registers across a runtime call *)
Lemma s23l_pres_keep : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr.
assert (Hc : acallee_saved (bv_unsigned r)).
{ cbn [In] in Hr. unfold acallee_saved.
  repeat (destruct Hr as [Hr | Hr];
    [ subst r; lazymatch goal with |- context [bv_unsigned ?rr] =>
        let z := eval vm_compute in (bv_unsigned rr) in change (bv_unsigned rr) with z end; lia |]).
  destruct Hr. }
rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hc).
Qed.

(* the latch 0x85d78 of turn q: S23_L_stmt's premises and a0 = whether mt[q] is (par, vid) *)
Definition s23l_X_stmt (i q : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (par : list Z) (vid : Z),
  lt_base B MT cx -> sa_frm0 ->
  s23_body B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid ->
  s23_regs regs m i vid ->
  (q < length (snd (x_decl cx i)))%nat ->
  lt_slots cx (rdW W mem) (LT_LV cx c m ++ LT_LD cx m tab mt i) ->
  lt_tabs cx (rdW W mem) tab mt (snd (x_decl cx i)) ->
  sa_strz (rdW W mem) (x_fr cx + FO_V) par -> sa_val (rdW W mem) (x_fr cx + FO_VID) 4 vid ->
  getr regs 10 = w64 (seg_spec.b2z (s23l_hit (snd (x_decl cx i)) q par vid)) ->
  getr regs 18 = w64 (seg_spec.b2z (s23_dup (firstn q (snd (x_decl cx i))) par vid)) ->
  getr regs 19 = w64 (mt + 16 + 20 * Z.of_nat q) -> getr regs 23 = w64 (mt + 20 * Z.of_nat q) ->
  getr regs 24 = w64 (20 * Z.of_nat q) ->
  getr regs 25 = w64 (20 * Z.of_nat (length (snd (x_decl cx i)))) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_D78) regs mem md) (lt_post B MT cx).

(* the latch: s2 |= a0, the increments, the loop test, and after the loop the test of s2 *)
Lemma s23l_latch : forall i q, S23_L_stmt B MT i (Datatypes.S q) -> S23_J_stmt B MT i -> S23_N_stmt B MT i -> s23l_X_stmt i q.
Proof.
intros i q HL HJn HN. unfold s23l_X_stmt.
intros cx ly S W regs mem md k acc c m tab mt par vid HB0 Hfrm HBD HRG Hq HSL HTB Hv Hvid R10 R18 R19 R23 R24 R25.
pose proof (s23_facts B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid HB0 HBD) as
  (HAR & Hfin & Hfa & Hfr32 & Hfr4096 & Hfrceil & Hfrpres & Hsh & Hs132 & Hs1b & Hsp016 & Hsp0 & Hstk & Hcap & Hmtn &
   Htabn & Hmn & Hmt16 & Hmt4096 & Hmtceil & _ & _ & _ & Hm16 & Hm4096 & Hmceil & _ & _ & _ & Hmtin & Hmtn0 & Hmtpres & Hmtfr & _).
pose proof HBD as ((HFR & HIMG & HBL & HBUD) & _).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & _ & _ & _ & _ & _ & H200 & HFSH & H184).
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_value as [[CMIN CMAX] _].
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. rewrite HSTK in Hsp0, Hstk. unfold seg_spec.SEG_M_SIZE in Hmceil.
assert (Hes : ESTACK = 4096) by reflexivity.
set (t := snd (x_decl cx i)) in *.
assert (S192 : rdword (rdW W mem) (x_s1 cx + 192) = Some m) by (apply HSL; apply in_or_app; left; cbn [LT_LV In]; repeat (first [left; reflexivity | right])).
assert (S128 : rdword (rdW W mem) (x_s1 cx + 128) = Some (Z.of_nat (length t))) by (apply HSL; apply in_or_app; right; cbn [LT_LD In]; repeat (first [left; reflexivity | right])).
assert (Hb01 : forall b, 0 <= seg_spec.b2z b <= 1) by (intros [|]; cbn; lia).
pose proof (Hb01 (s23l_hit t q par vid)) as Hh01. pose proof (Hb01 (s23_dup (firstn q t) par vid)) as Hd01.
pose proof HBD as (_ & _ & _ & _ & _ & Hi & Hig & Hsp & Hd0 & _).
(* the seat at 0x85d78: every register its own atom; atom 32 = m (192(s1)), 33 = mn (128(s1)); a0, s2 in [0, 1],
   s8 = 20 q, s9 = 20 mn *)
set (XC := [w64 m; w64 (Z.of_nat (length t))]).
pose proof (s23l_E_img regs XC) as HEI. pose proof (s23l_E_agree regs XC) as HAE.
pose proof (s23l_E_reg regs XC) as EEo.
assert (E32 : ew (s23l_E regs XC) 32 = w64 m) by exact (s23l_E_extra regs _ 0 ltac:(lia)).
assert (E33 : ew (s23l_E regs XC) 33 = w64 (Z.of_nat (length t))) by exact (s23l_E_extra regs _ 1 ltac:(lia)).
remember (s23l_E regs XC) as E eqn:HE0.
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E10 : ew E 10 = w64 (seg_spec.b2z (s23l_hit t q par vid))) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (E18 : ew E 18 = w64 (seg_spec.b2z (s23_dup (firstn q t) par vid))) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 (mt + 16 + 20 * Z.of_nat q)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E23 : ew E 23 = w64 (mt + 20 * Z.of_nat q)) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = w64 (20 * Z.of_nat q)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 (20 * Z.of_nat (length t))) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
set (rsC := [YP09.mkRegion (Some 9%nat) 128 200 0 0 [YP09.mkChunk 128 (CVal 8 (SOff 33 0)); YP09.mkChunk 192 (CVal 8 (SOff 32 0))]]).
set (atC := [(10%nat, mkAF 0 1 0); (18%nat, mkAF 0 1 0); (24%nat, mkAF 0 780 0); (25%nat, mkAF 20 800 0)]).
assert (HRS : Forall (region_ok SEGS E (mrestrict (w_H W) mem)) rsC).
{ constructor; [|constructor]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  + apply (s23l_chunk8 W mem E _ 128 _ _ S128); [lia | cbn [sv_denot]; rewrite E33, Z.add_0_r; apply Z_to_bv_bv_unsigned].
  + apply (s23l_chunk8 W mem E _ 192 _ _ S192); [lia | cbn [sv_denot]; rewrite E32, Z.add_0_r; apply Z_to_bv_bv_unsigned]. }
assert (HPD : pairwise_disjoint E rsC) by (apply pairwise_disjoint_of_extents; cbn; tauto).
assert (HAT : atoms_ok E atC).
{ cbn [atC atoms_ok]. split; [apply (s23l_afact E 10 _ _ _ E10); pose proof (Hb01 (s23l_hit t q par vid)); lia|].
  split; [apply (s23l_afact E 18 _ _ _ E18); pose proof (Hb01 (s23_dup (firstn q t) par vid)); lia|].
  split; [apply (s23l_afact E 24 _ _ _ E24); lia|].
  split; [apply (s23l_afact E 25 _ _ _ E25); lia|]. exact I. }
pose proof (s23l_seat W regs mem LO_D78 XC rsC atC eq_refl) as HS. rewrite <- HE0 in HS. specialize (HS HRS HPD HAT).
assert (SHOK : sh_ok SEGS (SOff 16 0) [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold cfg_at, w64.
unfold rsC, atC in HS. clear HRS HPD HAT rsC atC.
(* 0x85d78 .. 0x85d88: s2 |= a0, s7, s8, s3 += 20; the run stops at bne s9,s8 *)
paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
rename ms into ms1.
pose proof (s23l_ro_kept E _ _ _ _ HFr eq_refl) as K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- (* s9 <> s8 + 20: q + 1 < mn, back to the loop's head 0x85d30 *)
  rewrite branch_ne_U, (U_atom E 25 _ E25), (U_atom_off E 24 _ 20 E24) in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hq1 : (Datatypes.S q < length t)%nat) by lia.
  paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) LO_D30.
  { cbn [ss_mem add_cond]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  rename ms into ms2.
  pose proof (s23l_ro_kept E _ _ _ _ HFr eq_refl) as K2. clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi E _ _ regs XC [2; 3; 4; 8; 9; 16; 20; 21; 22; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as RK.
  cbn [ms_regs restrict] in RK.
  destruct (s23l_carry cx ly S W regs mem md k acc c m tab mt i par vid (ms_regs ms2) (ms_mem ms2) md2 HB0 HBD HRG HSL HTB Hv Hvid HJ)
    as (HBD' & HRG' & HSL' & HTB' & Hv' & Hvid').
  { intros r Hr. apply RK. cbn [In] in Hr |- *. tauto. }
  { rewrite (RK 16%bv) by (cbn; tauto). exact (proj1 HRG). }
  { intros a _ _. rewrite K2. apply K1. }
  pmkst HS.
  apply (HL cx ly S W (ms_regs ms2) (ms_mem ms2) md2 k acc c m tab mt par vid HB0 Hfrm HBD' HRG' Hq1 HSL' HTB' Hv' Hvid').
  + s23l_vreg HS (18%bv : bv 5). fold t.
    rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 10 _ E10), (U_atom E 18 _ E18) by lia.
    rewrite (s23_dup_firstn_S t q par vid Hq). fold (s23l_hit t q par vid).
    destruct (s23_dup (firstn q t) par vid), (s23l_hit t q par vid); reflexivity.
  + s23l_vreg HS (19%bv : bv 5). rewrite (U_atom_off E 19 _ 20 E19) by lia. lia.
  + s23l_vreg HS (23%bv : bv 5). rewrite (U_atom_off E 23 _ 20 E23) by lia. lia.
  + s23l_vreg HS (24%bv : bv 5). rewrite (U_atom_off E 24 _ 20 E24) by lia. lia.
  + rewrite (RK 25%bv) by (cbn; tauto). exact R25.
- (* s9 = s8 + 20: q + 1 = mn, the loop is done; j 0x85da0, s8 := m, a1 := mn, bnez s2 *)
  rewrite branch_ne_U, (U_atom E 25 _ E25), (U_atom_off E 24 _ 20 E24) in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hqn : Datatypes.S q = length t) by lia.
  paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  { cbn [ss_mem add_cond]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  rename ms into ms2.
  pose proof (s23l_ro_kept E _ _ _ _ HFr eq_refl) as K2. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  + (* s2 <> 0: an entry of the table is (par, vid); to the join 0x85b58 *)
    rewrite branch_ne_U, U_SAlu, U_SLit in Hc0. cbn [zalu_raw] in Hc0.
    rewrite (U_atom E 10 _ E10), (U_atom E 18 _ E18) in Hc0 by lia.
    assert (Hdup : s23_dup t par vid = true).
    { rewrite <- (firstn_all t), <- Hqn, (s23_dup_firstn_S t q par vid Hq). fold (s23l_hit t q par vid).
      destruct (s23_dup (firstn q t) par vid), (s23l_hit t q par vid); cbn in Hc0 |- *; first [reflexivity | discriminate]. }
    assert (Hdecl : x_decl cx (Datatypes.S i) = x_decl cx i)
      by (rewrite (s23_decl_S cx i par vid Hi Hig Hsp ltac:(lia)); fold t; rewrite Hdup; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) LO_B58.
    { cbn [ss_mem add_cond]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md3 := d) in *; clearbody md3 end.
    rename ms into ms3.
    pose proof (s23l_ro_kept E _ _ _ _ HFr eq_refl) as K3. clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi E _ _ regs XC [2; 3; 4; 8; 9; 16; 20; 21; 22; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as RK.
    cbn [ms_regs restrict] in RK.
    destruct (s23l_carry cx ly S W regs mem md k acc c m tab mt i par vid (ms_regs ms3) (ms_mem ms3) md3 HB0 HBD HRG HSL HTB Hv Hvid HJ)
      as (HBD' & HRG' & HSL' & HTB' & Hv' & Hvid').
    { intros r Hr. apply RK. cbn [In] in Hr |- *. tauto. }
    { rewrite (RK 16%bv) by (cbn; tauto). exact (proj1 HRG). }
    { intros a _ _. rewrite K3, K2. apply K1. }
    pmkst HS.
    apply (HJn cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k acc c m tab mt par vid HB0 Hfrm HBD' HRG').
    * rewrite Hdecl. lia.
    * replace (LT_LD cx m tab mt (Datatypes.S i)) with (LT_LD cx m tab mt i) by (unfold LT_LD; rewrite Hdecl; reflexivity). exact HSL'.
    * rewrite Hdecl. exact HTB'.
    * s23l_vreg HS (24%bv : bv 5). apply (U_atom E 32 m E32). lia.
  + (* s2 = 0: no entry is (par, vid); to the capacity test 0x85dac *)
    rewrite branch_ne_U, U_SAlu, U_SLit in Hc0. cbn [zalu_raw] in Hc0.
    rewrite (U_atom E 10 _ E10), (U_atom E 18 _ E18) in Hc0 by lia.
    assert (Hdup : s23_dup t par vid = false).
    { rewrite <- (firstn_all t), <- Hqn, (s23_dup_firstn_S t q par vid Hq). fold (s23l_hit t q par vid).
      destruct (s23_dup (firstn q t) par vid), (s23l_hit t q par vid); cbn in Hc0 |- *; first [reflexivity | discriminate]. }
    paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) LO_DAC.
    { cbn [ss_mem add_cond]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md3 := d) in *; clearbody md3 end.
    rename ms into ms3.
    pose proof (s23l_ro_kept E _ _ _ _ HFr eq_refl) as K3. clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi E _ _ regs XC [2; 3; 4; 8; 9; 16; 20; 21; 22; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as RK.
    cbn [ms_regs restrict] in RK.
    destruct (s23l_carry cx ly S W regs mem md k acc c m tab mt i par vid (ms_regs ms3) (ms_mem ms3) md3 HB0 HBD HRG HSL HTB Hv Hvid HJ)
      as (HBD' & HRG' & HSL' & HTB' & Hv' & Hvid').
    { intros r Hr. apply RK. cbn [In] in Hr |- *. tauto. }
    { rewrite (RK 16%bv) by (cbn; tauto). exact (proj1 HRG). }
    { intros a _ _. rewrite K3, K2. apply K1. }
    pmkst HS.
    apply (HN cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k acc c m tab mt par vid HB0 Hfrm HBD' HRG' Hdup HSL' HTB' Hv' Hvid').
    * s23l_vreg HS (11%bv : bv 5). apply (U_atom E 33 _ E33). lia.
    * s23l_vreg HS (24%bv : bv 5). apply (U_atom E 32 m E32). lia.
Qed.

(* one turn of the dup loop, from its head 0x85d30 to the latch *)
Lemma s23_L : forall i q, S23_L_stmt B MT i (Datatypes.S q) -> S23_J_stmt B MT i -> S23_N_stmt B MT i ->
  S23_L_stmt B MT i q.
Proof.
intros i q HL HJn HN. pose proof (s23l_latch i q HL HJn HN) as HX. clear HL HJn HN. unfold S23_L_stmt.
intros cx ly S W regs mem md k acc c m tab mt par vid HB0 Hfrm HBD HRG Hq HSL HTB Hv Hvid R18 R19 R23 R24 R25.
pose proof (s23_facts B MT cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid HB0 HBD) as
  (HAR & Hfin & Hfa & Hfr32 & Hfr4096 & Hfrceil & Hfrpres & Hsh & Hs132 & Hs1b & Hsp016 & Hsp0 & Hstk & Hcap & Hmtn &
   Htabn & Hmn & Hmt16 & Hmt4096 & Hmtceil & _ & _ & _ & Hm16 & Hm4096 & Hmceil & _ & _ & _ & Hmtin & Hmtn0 & Hmtpres & Hmtfr & _).
pose proof HBD as ((HFR & HIMG & HBL & HBUD) & _).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & _ & _ & _ & _ & _ & H200 & HFSH & H184).
pose proof HRG as (R16 & R20 & R21 & R22 & R26 & R27).
pose proof (s23l_par_facts cx ly S W regs mem md k acc LFO_NV c m tab mt i par vid HBD) as (Hp0 & Hp15 & Hvr).
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_value as [[CMIN CMAX] _].
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. rewrite HSTK in Hsp0, Hstk. unfold seg_spec.SEG_M_SIZE in Hmceil.
assert (Hes : ESTACK = 4096) by reflexivity.
set (t := snd (x_decl cx i)) in *.
pose proof HTB as (_ & _ & _ & _ & HMT & _).
destruct (s23_mtab_entry B MT (rdW W mem) mt t q HMT Hq) as (Hez & Hel & Hev & Hevr & Hepres).
set (e := nth q t ([], 0)) in *.
assert (Rmt : req_size (x_mtn cx) = x_mtn cx) by (unfold req_size; rewrite Hmtn; destruct (Z.eqb_spec (20 * (x_cap cx + 1)) 0); lia).
assert (S64 : rdword (rdW W mem) (x_s1 cx + 64) = Some (x_fr cx + FO_V)) by (apply HSL; apply in_or_app; left; cbn [LT_LV In]; repeat (first [left; reflexivity | right])).
assert (S152 : rdword (rdW W mem) (x_s1 cx + 152) = Some (lt_not mt)) by (apply HSL; apply in_or_app; right; cbn [LT_LD In]; repeat (first [left; reflexivity | right])).
assert (S160 : rdword (rdW W mem) (x_s1 cx + 160) = Some 1) by (apply HSL; apply in_or_app; right; cbn [LT_LD In]; repeat (first [left; reflexivity | right])).
(* the seat at 0x85d30: every register its own atom; atom 32 = ~MT (152(s1)), 33 = v = FR + 32 (64(s1)), 34 = the vid
   of mt[q] (4 bytes at MT + 20 q + 16); the shadow base a6, s3, s5, s8 and atoms 32, 34 with their ranges *)
set (XA := [w64 (lt_not mt); w64 (x_fr cx + FO_V); w64 (snd e)]).
pose proof (s23l_E_img regs XA) as HEI. pose proof (s23l_E_agree regs XA) as HAE.
pose proof (s23l_E_reg regs XA) as EEo.
assert (E32 : ew (s23l_E regs XA) 32 = w64 (lt_not mt)) by exact (s23l_E_extra regs _ 0 ltac:(lia)).
assert (E33 : ew (s23l_E regs XA) 33 = w64 (x_fr cx + FO_V)) by exact (s23l_E_extra regs _ 1 ltac:(lia)).
assert (E34 : ew (s23l_E regs XA) 34 = w64 (snd e)) by exact (s23l_E_extra regs _ 2 ltac:(lia)).
remember (s23l_E regs XA) as E eqn:HE0.
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E16 : ew E 16 = w64 SHADOW_OFF) by (rewrite (EEo 16%nat 16%bv eq_refl); exact R16).
assert (E19 : ew E 19 = w64 (mt + 16 + 20 * Z.of_nat q)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E21 : ew E 21 = w64 vid) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E23 : ew E 23 = w64 (mt + 20 * Z.of_nat q)) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = w64 (20 * Z.of_nat q)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
set (rsA := [YP09.mkRegion (Some 9%nat) 64 168 0 0 [YP09.mkChunk 64 (CVal 8 (SOff 33 0)); YP09.mkChunk 152 (CVal 8 (SOff 32 0)); YP09.mkChunk 160 (CVal 8 (SLit 1))];
             YP09.mkRegion (Some 23%nat) 16 20 0 0 [YP09.mkChunk 16 (CVal 4 (SOff 34 0))]]).
set (atA := [(16%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, mkAF 4096 (2 ^ 47 - 16) 0); (21%nat, mkAF 1 4094 0);
             (24%nat, mkAF 0 780 0); (32%nat, mkAF (2 ^ 64 - 1 - 2 ^ 47) (2 ^ 64 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0)]).
assert (HRS : Forall (region_ok SEGS E (mrestrict (w_H W) mem)) rsA).
{ constructor; [|constructor; [|constructor]]; unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  - rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (s23l_chunk8 W mem E _ 64 _ _ S64); [unfold FO_V; lia | cbn [sv_denot]; rewrite E33, Z.add_0_r; apply Z_to_bv_bv_unsigned].
    + apply (s23l_chunk8 W mem E _ 152 _ _ S152); [unfold lt_not; lia | cbn [sv_denot]; rewrite E32, Z.add_0_r; apply Z_to_bv_bv_unsigned].
    + apply (s23l_chunk8 W mem E _ 160 _ _ S160); [lia | reflexivity].
  - rewrite E23. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (s23l_chunk4 W mem E _ 16 _ _ Hev); [lia | cbn [sv_denot]; rewrite E34, Z.add_0_r; apply Z_to_bv_bv_unsigned]. }
assert (HPD : pairwise_disjoint E rsA).
{ apply pairwise_disjoint_of_extents. unfold rsA, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E23. unfold w64. rewrite !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
assert (HAT : atoms_ok E atA).
{ cbn [atA atoms_ok].
  split; [apply (s23l_afact E 16 _ _ _ E16); unfold SHADOW_OFF; lia|].
  split; [apply (s23l_afact E 19 _ _ _ E19); lia|].
  split; [apply (s23l_afact E 21 _ _ _ E21); lia|].
  split; [apply (s23l_afact E 24 _ _ _ E24); lia|].
  split; [apply (s23l_afact E 32 _ _ _ E32); unfold lt_not; lia|].
  split; [apply (s23l_afact E 34 _ _ _ E34); lia|]. exact I. }
pose proof (s23l_seat W regs mem LO_D30 XA rsA atA eq_refl) as HS. rewrite <- HE0 in HS. specialize (HS HRS HPD HAT).
assert (SHOK : sh_ok SEGS (SOff 16 0) [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold rsA, atA in HS. clear HRS HPD HAT rsA atA.
unfold cfg_at, w64.
(* 0x85d30 .. 0x85d58: both UBSan trap branches are decided inside the run (bltu ~MT, s8 at 0x85d34 by the ranges of
   atom 32 >= 2^64 - 1 - 2^47 and of s8 <= 780; beqz 160(s1) at 0x85d3c by the literal 1); the 4-byte check of s3 is a
   token whose obligation is the first goal; the run stops at bne a0,a1 (0x85d58) *)
paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ (* the 4-byte check of mt[q].vid (s3): inside mt's block *)
  cbn [ms_mem mkst].
  apply (obl_of_range SEGS (w_H W) mem E (SOff 16 0) _ 4 mt (x_mtn cx));
    [exact (range_addressable_of_block SEGS B LAWS ly S W mem md mt (x_mtn cx) mt (x_mtn cx) HAR Hmtin ltac:(lia) ltac:(lia))
    | apply (U_atom E 16 _ E16); unfold SHADOW_OFF; lia
    | rewrite (U_atom E 19 _ E19) by lia; lia
    | rewrite (U_atom E 19 _ E19) by lia; lia]. }
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
rename ms into ms1.
pose proof (s23l_ro_kept E _ _ _ _ HFr eq_refl) as K1. clear HF HFr HG.
assert (HAE1 : env_agree 32 (Ereg regs XA) (ewset (ewset E 1024 w) 1025 w0)).
{ destruct HAE as [HA1 HA2]. split; [intros n Hn; cbn [ew ewset]; destruct (Nat.eqb_spec n 1025); [lia|]; destruct (Nat.eqb_spec n 1024); [lia|]; exact (HA1 n Hn) | cbn [ed ewset]; exact HA2]. }
set (E1 := ewset (ewset E 1024 w) 1025 w0) in *.
assert (EO1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n)
  by (intros n Hn; unfold E1; cbn [ew ewset]; destruct (Nat.eqb_spec n 1025); [lia|]; destruct (Nat.eqb_spec n 1024); [lia|]; reflexivity).
clearbody E1.
psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- (* the vids differ: 0x85d74 a0 := 0, to the latch *)
  rewrite branch_ne_U, U_SExt, (U_atom E1 34 _ ltac:(rewrite EO1 by lia; exact E34)), (U_atom E1 21 _ ltac:(rewrite EO1 by lia; exact E21)) in Hc by lia.
  rewrite (s23l_sext_eq (snd e) vid Hevr Hvr) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) LO_D78.
  { cbn [ss_mem add_cond]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  rename ms into ms2.
  pose proof (s23l_ro_kept _ _ _ _ _ HFr eq_refl) as K2. clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi E1 _ _ regs XA [2; 3; 4; 8; 9; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE1 ltac:(vm_compute; reflexivity)) as RK.
  cbn [ms_regs restrict] in RK.
  destruct (s23l_carry cx ly S W regs mem md k acc c m tab mt i par vid (ms_regs ms2) (ms_mem ms2) md2 HB0 HBD HRG HSL HTB Hv Hvid HJ)
    as (HBD' & HRG' & HSL' & HTB' & Hv' & Hvid').
  { intros r Hr. apply RK. cbn [In] in Hr |- *. tauto. }
  { rewrite (RK 16%bv) by (cbn; tauto). exact R16. }
  { intros a _ _. rewrite K2. apply K1. }
  pmkst HS.
  apply (HX cx ly S W (ms_regs ms2) (ms_mem ms2) md2 k acc c m tab mt par vid HB0 Hfrm HBD' HRG' Hq HSL' HTB' Hv' Hvid').
  + s23l_vreg HS (10%bv : bv 5). rewrite U_lit by lia. unfold s23l_hit. fold t. fold e. apply Z.eqb_neq in Hc. rewrite Hc. reflexivity.
  + rewrite (RK 18%bv) by (cbn; tauto). exact R18.
  + rewrite (RK 19%bv) by (cbn; tauto). exact R19.
  + rewrite (RK 23%bv) by (cbn; tauto). exact R23.
  + rewrite (RK 24%bv) by (cbn; tauto). exact R24.
  + rewrite (RK 25%bv) by (cbn; tauto). exact R25.
- (* the vids agree: a0 := s7 = &mt[q], a1 := v, the strcmp call 0x85d64 *)
  rewrite branch_ne_U, U_SExt, (U_atom E1 34 _ ltac:(rewrite EO1 by lia; exact E34)), (U_atom E1 21 _ ltac:(rewrite EO1 by lia; exact E21)) in Hc by lia.
  rewrite (s23l_sext_eq (snd e) vid Hevr Hvr) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  { cbn [ss_mem add_cond]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  rename ms into ms2.
  pose proof (s23l_ro_kept _ _ _ _ _ HFr eq_refl) as K2. clear HF HFr HG.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  assert (KT : forall a, rdW W (ms_mem ms2) a = rdW W mem a) by (intros a; rewrite K2; apply K1).
  pose proof HB0 as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
  assert (P2' : spZ (ms_regs ms2) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
  { unfold spZ. rewrite P2, EO1, (EEo 2%nat 2%bv eq_refl), R2 by lia. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (P3' : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite P3, EO1, (EEo 3%nat 3%bv eq_refl), R3 by lia; exact Hgp0).
  assert (P4' : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite P4, EO1, (EEo 4%nat 4%bv eq_refl), R4 by lia; exact Htp0).
  assert (P10' : getr (ms_regs ms2) 10 = w64 (mt + 20 * Z.of_nat q)) by (rewrite P10, EO1 by lia; exact E23).
  assert (P11' : getr (ms_regs ms2) 11 = w64 (x_fr cx + FO_V)) by (rewrite P11, EO1 by lia; exact E33).
  assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + 4008))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Ho16 : (x_s1 cx - x_sp0 cx) mod 16 = 0).
  { apply Z.mod_divide in Hs132; [|lia]. apply Z.mod_divide in Hsp016; [|lia]. destruct Hs132 as [u Hu]. destruct Hsp016 as [u' Hu'].
    apply Z.mod_divide; [lia|]. exists (2 * u - u'). lia. }
  (* the two strings: mt[q]'s parent and v's *)
  assert (Hez2 : sa_strz (rdW W (ms_mem ms2)) (mt + 20 * Z.of_nat q) (fst e)) by (apply (s23_strz_kept B MT (rdW W mem)); [intros a _; apply KT | exact Hez]).
  assert (Hv2 : sa_strz (rdW W (ms_mem ms2)) (x_fr cx + FO_V) par) by (apply (s23_strz_kept B MT (rdW W mem)); [intros a _; apply KT | exact Hv]).
  destruct (sa_strz_bytes SEGS (w_H W) (ms_mem ms2) _ _ Hez2) as (BYx & NZx & ZSx).
  destruct (sa_strz_bytes SEGS (w_H W) (ms_mem ms2) _ _ Hv2) as (BYy & NZy & ZSy).
  assert (Lx : astr_len (seg_spec.zb (fst e)) = Z.of_nat (length (fst e))) by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
  assert (Ly : astr_len (seg_spec.zb par) = Z.of_nat (length par)) by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
  assert (HFSH2 : sa_zs (rdW W (ms_mem ms2)) (x_sh cx) (lt_fsh LFO_NV)) by (apply (s23l_zs_kept (rdW W mem)); [intros a _; apply KT | exact HFSH]).
  destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hfin) as (_ & _ & Happ).
  rewrite Hfa in Happ. change (fs_frame_bytes LT_FCLS) with 512 in Happ.
  pose proof asan_consts as (_ & _ & Ck2 & Ck3 & Ck4).
  pose proof HIMG as (HRO & _).
  assert (RDx : aread_ok SEGS (2 * ESTACK) W (ms_regs ms2) (ms_mem ms2) (mt + 20 * Z.of_nat q) (astr_len (seg_spec.zb (fst e)) + 1)).
  { rewrite Lx. apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) ly S W (ms_regs ms2) (ms_mem ms2) md2 mt (x_mtn cx));
      [exact (proj1 HJ) | exact Hmtin | lia | lia | lia | rewrite P2'; lia]. }
  assert (RDy : aread_ok SEGS (2 * ESTACK) W (ms_regs ms2) (ms_mem ms2) (x_fr cx + FO_V) (astr_len (seg_spec.zb par) + 1)).
  { rewrite Ly. unfold FO_V. rewrite Hsh in HFSH2.
    destruct (s23l_v_read (rdW W (ms_mem ms2)) (x_fr cx) (Z.of_nat (length par) + 1) Hfr32 ltac:(lia) HFSH2 ltac:(lia)) as [RA HV].
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [rewrite KT; apply (aview_some_of_apresent SEGS); apply Hfrpres; lia | unfold ascratch_stk; rewrite P2'; lia]. }
    split; [unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *; lia|]. split; [exact RA | intros _; exact HV]. }
  assert (TLx : atail_vis SEGS W (ms_mem ms2) (mt + 20 * Z.of_nat q + astr_len (seg_spec.zb (fst e)))).
  { rewrite Lx. intros a Ha. rewrite KT. apply (aview_some_of_apresent SEGS). apply Hmtpres.
    apply Z.mod_divide in Hmt16; [|lia]. destruct Hmt16 as [u Hu].
    pose proof (Z.div_mod (mt + 20 * Z.of_nat q + Z.of_nat (length (fst e))) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (mt + 20 * Z.of_nat q + Z.of_nat (length (fst e))) 8 ltac:(lia)) as M. lia. }
  assert (TLy : atail_vis SEGS W (ms_mem ms2) (x_fr cx + FO_V + astr_len (seg_spec.zb par))).
  { rewrite Ly. intros a Ha. rewrite KT. apply (aview_some_of_apresent SEGS). apply Hfrpres. unfold FO_V in *.
    apply Z.mod_divide in Hfr32; [|lia]. destruct Hfr32 as [u Hu].
    pose proof (Z.div_mod (x_fr cx + 32 + Z.of_nat (length par)) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (x_fr cx + 32 + Z.of_nat (length par)) 8 ltac:(lia)) as M. lia. }
  assert (ROM : rt_rom_view SEGS B W (ms_mem ms2)) by (intros a Hr Ho He; rewrite KT; exact (HRO a (or_introl Hr) Ho He)).
  eapply SRr_bind.
  { exact (s23l_strcmp_at W (ms_regs ms2) (ms_mem ms2) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx)
      (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md2 k (mt + 20 * Z.of_nat q) (x_fr cx + FO_V) (seg_spec.zb (fst e))
      (seg_spec.zb par) (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + 4008)) HJ P10' P11' ltac:(lia) ltac:(unfold FO_V; lia)
      P2' Ho16 ltac:(lia) ltac:(rewrite HSTK, Hes; lia) P3' P4' P1 Hraw (conj BYx NZx) (conj BYy NZy) RDx RDy TLx TLy ROM). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md3 & -> & HJ2 & HP2 & HQ2 & HK2).
  (* back at 0x85d68: the callee-saved registers kept, memory kept outside strcmp's scratch below s1 *)
  pose proof (regs_kept_of_st_ok SEGS E1 _ _ regs XA [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE1 ltac:(vm_compute; reflexivity)) as RKc.
  cbn [ms_regs restrict] in RKc. clear HS SHOK.
  assert (RK2 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 r = getr regs r)
    by (intros r Hr; rewrite (s23l_pres_keep _ _ HP2 r Hr); exact (RKc r Hr)).
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - 2 * ESTACK <= a < x_s1 cx) -> rdW W mem2 a = rdW W mem a)
    by (intros a Ha Hn; rewrite (HK2 a Ha ltac:(lia) ltac:(tauto)); apply KT).
  assert (H200b : rdword (rdW W mem2) (x_s1 cx + 200) = Some SHADOW_OFF)
    by (rewrite (rdword_ext (rdW W mem) (rdW W mem2)); [exact H200 | intros j Hj; apply K3; lia]).
  (* the seat at 0x85d68: every register its own atom, the slot 200(s1) *)
  pose proof (s23l_E_img regs2 []) as HEIb. pose proof (s23l_E_agree regs2 []) as HAEb.
  pose proof (s23l_E_reg regs2 []) as EEb.
  remember (s23l_E regs2 []) as Eb eqn:HEb.
  assert (Eb9 : ew Eb 9 = w64 (x_s1 cx)) by (rewrite (EEb 9%nat 9%bv eq_refl), (RK2 9%bv) by (cbn; tauto); exact R9).
  assert (HRSb : Forall (region_ok SEGS Eb (mrestrict (w_H W) mem2)) [YP09.mkRegion (Some 9%nat) 200 208 0 0 [YP09.mkChunk 200 (CVal 8 (SLit SHADOW_OFF))]]).
  { constructor; [|constructor]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Eb9. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (s23l_chunk8 W mem2 Eb _ 200 _ _ H200b); [unfold SHADOW_OFF; lia | reflexivity]. }
  pose proof (s23l_seat W regs2 mem2 4008 [] [YP09.mkRegion (Some 9%nat) 200 208 0 0 [YP09.mkChunk 200 (CVal 8 (SLit SHADOW_OFF))]] [] eq_refl) as HSb. rewrite <- HEb in HSb.
  specialize (HSb HRSb ltac:(apply pairwise_disjoint_of_extents; cbn; tauto) I).
  assert (SHOKb : sh_ok SEGS (SOff 16 0) [] Eb (mrestrict (w_H W) mem2)) by apply Forall_nil.
  clear HRSb.
  paj_run_to_tok RUNTO HSb HJ2 SHOKb (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) LO_D78.
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md4 := d) in *; clearbody md4 end.
  rename ms into ms4.
  pose proof (s23l_ro_kept _ _ _ _ _ HFr eq_refl) as K4. clear HF HFr HG.
  (* 0x85d68 .. 0x85d70 done: a6 = the shadow base, a0 = seqz of strcmp's answer *)
  pose proof (regs_kept_of_st_ok_pi Eb _ _ regs2 [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HSb HAEb ltac:(vm_compute; reflexivity)) as RK4.
  cbn [ms_regs restrict] in RK4.
  assert (RK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms4) r = getr regs r)
    by (intros r Hr; rewrite (RK4 r Hr); exact (RK2 r Hr)).
  destruct (s23l_carry cx ly S W regs mem md k acc c m tab mt i par vid (ms_regs ms4) (ms_mem ms4) md4 HB0 HBD HRG HSL HTB Hv Hvid HJ2)
    as (HBD' & HRG' & HSL' & HTB' & Hv' & Hvid').
  { intros r Hr. apply RK. cbn [In] in Hr |- *. tauto. }
  { s23l_vreg HSb (16%bv : bv 5). apply U_lit. unfold SHADOW_OFF. lia. }
  { intros a Ha Hn. rewrite K4. exact (K3 a Ha Hn). }
  pmkst HSb.
  apply (HX cx ly S W (ms_regs ms4) (ms_mem ms4) md4 k acc c m tab mt par vid HB0 Hfrm HBD' HRG' Hq HSL' HTB' Hv' Hvid').
  + s23l_vreg HSb (10%bv : bv 5). rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit.
    rewrite (EEb 10%nat 10%bv eq_refl), Z.add_0_r. change (zcanon 1) with 1. rewrite (zcanon_id (bv_unsigned (getr regs2 10))) by (pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as R; change (bv_modulus 64) with (2 ^ 64) in R; unfold M64; lia).
    unfold s23l_hit. fold t. fold e. rewrite Hc, Z.eqb_refl, andb_true_l.
    rewrite <- (s23l_hit_eq (getr regs2 10) (fst e) par HQ2 ZSx ZSy (proj2 Hez) Hp0).
    destruct (bv_unsigned (getr regs2 10) <? 1); reflexivity.
  + rewrite (RK 18%bv) by (cbn; tauto). exact R18.
  + rewrite (RK 19%bv) by (cbn; tauto). exact R19.
  + rewrite (RK 23%bv) by (cbn; tauto). exact R23.
  + rewrite (RK 24%bv) by (cbn; tauto). exact R24.
  + rewrite (RK 25%bv) by (cbn; tauto). exact R25.
Qed.

End e.
End f.
End d.

(* ======================================= the loop and the segment ======================================= *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation SIGMA s := (@pa_sigma _ seg_listing PI s).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : PALib B.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strcmp).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA SS___asan_memcpy).

(* no turn q >= 40 of the dup loop is reached: q < mn = length (the table) <= cap < 40 (lt_tabs) *)
Lemma s23_L_vacuous : forall i q, (40 <= q)%nat -> S23_L_stmt B MT i q.
Proof.
intros i q Hq. unfold S23_L_stmt. intros cx ly S W regs mem md k acc c m tab mt par vid _ _ _ _ Hlt _ HT.
intros. exfalso. destruct HT as ((_ & Hcap) & _ & _ & _ & _ & Hle). lia.
Qed.

(* the dup loop, by downward induction on its turn *)
Lemma s23_L_all : forall i, S23_J_stmt B MT i -> S23_N_stmt B MT i -> forall q, S23_L_stmt B MT i q.
Proof.
intros i HJ HN.
assert (H : forall d q, (40 <= q + d)%nat -> S23_L_stmt B MT i q).
{ induction d as [|d IH]; intros q Hqd.
  - apply s23_L_vacuous. lia.
  - eapply s23_L; try eassumption. apply IH. lia. }
intros q. exact (H 40%nat q ltac:(lia)).
Qed.

(* S15: K85d04 i -> (K85b0c (i + 1) | K85e50) *)
Theorem lt_seg_S15 : lt_seg_S15_stmt B MT.
Proof.
unfold lt_seg_S15_stmt. intros i HB0c HE50.
assert (HJ : S23_J_stmt B MT i) by (eapply s23_J; eassumption).
assert (HN : S23_N_stmt B MT i) by (eapply s23_N; eassumption).
pose proof (s23_L_all i HJ HN) as HL.
eapply s23_D; [apply HL | exact HN].
Qed.
End e.
End f.
End d.
