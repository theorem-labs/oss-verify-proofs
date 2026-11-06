(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: number's walk on the ASan build of plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v and ACam.v (a walk segment, the side-stack frame's release): from strtol's return (0x8e534) to number's return, the four paths of number's tests (the word's first byte, the end pointer's byte, the range of the value) and the release of the class-0 frame. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/numberB.v, with its module paths and module names changed; 646 of its 709 lines of code are new or changed and 368 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3...): refuse's prefix
   walk, from the cut RB_PRE (0x894ac) through the two snprintf arms to the canonical cut state ss_txt at RB_TEXT
   (0x894e4), and on through refuse_Pt.v's rbp_txt (the vsnprintf call, checks 4 and 5, the UBSan traps T4 and T5,
    the n_refusals store) to the release RB_REL_stmt. Two sub-lanes (one for the first half, one for the cut and the
   integration) under the image-B refuse walk lane of the image-B G3 walk owner, 2026-10-30.

   proves no function (kind: segment lemma of refuse's image-B walk): Theorem rb_pre : RB_PRE_stmt (refuse_K.v).
   Rule 24: ref-common.md "Rule 24" (no released proof of refuse). ADAPTED from plugin-hostd/fuzz_command
   lib/B/Prog/check_reply_s4.v (origin/ossv/recipes 501c0d516c69: an snprintf call through PaFx.srr_after_artF and
   the walk at the FP state the wrapper returns), numberA.v (the re-seat jafter_call_keep_hi), and the image-A
   parse_file piece pf_a10b_s.v (the image-A G3 walk owner); the record facts are refuse_f.v / refuse_Pf.v's, the step lemma
   refuse_Ps.rbs_aj_snprintf_atSF.

   THE CODE (refuse.fuzz_segconf.asan-ubsan.s lines 111-124, 14 instructions):
     0x894ac add s6,a0,a1 (dst = c->refusal[n]); 0x894b0 blez s4 (s4 = line);
     line > 0 : 0x894b4 .. 0x894c4 a2 = .str.31 "%s:%d: " (listing object 71), a1 = 200, a0 = dst, a4 = line;
                0x894c8 jal wrapper_snprintf, returns at 0x894cc (RB_SNP_RET); 0x894cc j 0x894e4;
     line <= 0: 0x894d0 .. 0x894dc a2 = .str.32 "%s: " (listing object 72), a1 = 200, a0 = dst;
                0x894e0 jal wrapper_snprintf, returns at 0x894e4 (RB_TEXT).
   a3 = where (atom 1101: c->reading or .str.1 "reac-pw.conf"). No UBSan trap site lies in this part (T4 and T5
   are after RB_TEXT, in refuse_Pt.v). The call writes the address prefix T1 = SegModel.fmt (r_addr_fmt ln)
   (r_addr_args rcs ln) and its NUL into the slot (|T1| <= 108 < 200, so all of it), and keeps every other byte
   outside its window.

   Section hypotheses beyond RB_PRE_stmt's premises: SNP / VSNP (rows 4 and 5 at every FP state), FFR (the format
   family), REL (the release), LAWS (the AR laws), OBJ71 / OBJ72 (the two address formats are listing objects
   71 / 72), FMTS (each format below the GOT word), GOTW (the GOT word and the guard cell in [0x10000, kImgEnd)),
   CRP (rows 4 and 5's read-only list in the image). The second half RBP_TXT_stmt (refuse_Pk.v) is refuse_Pt.v's
   rbp_txt, taken below as the Let TXT. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YI16 YM05 YN2j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall PaCallRun PaArt PaArtOwn PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtPFupoison RtPFPf RtPFShared RtPFCmd RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c refuse_E refuse_K refuse_f refuse_pft refuse_Pk refuse_Pf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require refuse_Ps.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_Pt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== pure helpers ======================================== *)
(* the stored refused + 1: its low 32 bits are refused + 1 (refuse_H.v's rb_inc_mod, the image-B refuse walk lane) *)
Lemma rpp_inc_mod : forall E rf, ew E 36 = Z_to_bv 64 rf -> 0 <= rf -> rf + 1 < 2 ^ 32 ->
U E (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) mod 2 ^ 32 = rf + 1.
Proof.
intros E rf H36 H0 H1.
rewrite U_SAlu, U_SExt, (U_atom E 36 rf H36) by lia. rewrite U_SLit. cbn [zalu_raw].
unfold zcanon, M64, bv_swrap. change (bv_half_modulus 32) with (2 ^ 31). unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small rf (2 ^ 32)) by lia.
rewrite (Z.mod_small 1 (2 ^ 64)) by lia.
destruct (Z_lt_le_dec rf (2 ^ 31)) as [Hs|Hs].
- rewrite (Z.mod_small (rf + 2 ^ 31) (2 ^ 32)) by lia. replace (rf + 2 ^ 31 - 2 ^ 31) with rf by lia.
  rewrite (Z.mod_small rf (2 ^ 64)) by lia. rewrite (Z.mod_small (rf + 1) (2 ^ 64)) by lia.
  apply Z.mod_small. lia.
- rewrite <- (Z.mod_unique (rf + 2 ^ 31) (2 ^ 32) 1 (rf + 2 ^ 31 - 2 ^ 32)) by lia.
  replace (rf + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with (rf - 2 ^ 32) by lia.
  rewrite <- (Z.mod_unique (rf - 2 ^ 32) (2 ^ 64) (-1) (rf - 2 ^ 32 + 2 ^ 64)) by lia.
  rewrite (Z.mod_small (rf - 2 ^ 32 + 2 ^ 64 + 1) (2 ^ 64)) by lia.
  symmetry. apply (Z.mod_unique (rf - 2 ^ 32 + 2 ^ 64 + 1) (2 ^ 32) (2 ^ 32 - 1) (rf + 1)); lia.
Qed.
Lemma rpp_le_byte_mod : forall v k, OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.YG0f.le_byte v 4 k =
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.YG0f.le_byte (v mod 2 ^ 32) 4 k.
Proof.
intros v k. unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.YG0f.le_byte.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma rpp_rd32_mod : forall (rd : YG0f.reader) a v w, rd32 rd a v -> v mod 2 ^ 32 = w mod 2 ^ 32 -> rd32 rd a w.
Proof.
intros rd a v w H Hm k Hk. rewrite (H k Hk). f_equal. rewrite (rpp_le_byte_mod v k), (rpp_le_byte_mod w k), Hm. reflexivity.
Qed.
(* a 4-byte chunk of a region read back as a u32 (refuse_H.v's rb_chunk4_aval / rb_region_aval4) *)
Lemma rpp_chunk4_aval : forall {fx : YK11.FPState} segs E H (m : word -> option byte) base off e (v : Z),
YP09.chunk_ok segs E (mrestrict H m) base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
rd32 (aview segs H m) (base + off) v.
Proof.
intros fx segs E H m base off e v Hc He k Hk.
destruct (Hc (Z.of_nat k) ltac:(unfold YP09.c_len; cbn [YP09.c_val YP09.cv_len]; lia)) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite He, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64).
unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.YG0f.le_byte.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). change 256 with (2 ^ 8).
apply Z.bits_inj'. intros j Hj.
destruct (Z_lt_le_dec j 8) as [Hj8|Hj8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma rpp_region_aval4 : forall {fx : YK11.FPState} segs E H (m : word -> option byte) n b cs lo hi wlo whi od e v,
region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 4 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
rd32 (aview segs H m) (b + od) v.
Proof.
intros fx segs E H m n b cs lo hi wlo whi od e v (_ & _ & _ & Hcs) Hn Hc He.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (rpp_chunk4_aval segs E H m b od e v Hck He).
Qed.
(* the stack-protector cells and a string kept by a reader that agrees on their bytes *)
Lemma rpp_rdword_keep : forall (rd rd' : YG0f.reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a K. unfold rdword.
rewrite <- (Z.add_0_r a) at 1 2. rewrite (K 0), (K 1), (K 2), (K 3), (K 4), (K 5), (K 6), (K 7) by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma rpp_ssp_keep : forall (rd rd' : YG0f.reader) gotw guard, sa_ssp rd gotw guard ->
(forall i, 0 <= i < 8 -> rd' (gotw + i) = rd (gotw + i)) -> (forall i, 0 <= i < 8 -> rd' (guard + i) = rd (guard + i)) ->
sa_ssp rd' gotw guard.
Proof.
intros rd rd' gotw guard (G1 & g & G2) K1 K2. split; [rewrite (rpp_rdword_keep rd rd' gotw K1); exact G1|].
exists g. rewrite (rpp_rdword_keep rd rd' guard K2). exact G2.
Qed.
Lemma rpp_str_keep : forall (rd rd' : YG0f.reader) p s, sa_str rd p s ->
(forall x, p <= x < p + Z.of_nat (length s) + 8 -> rd' x = rd x) -> sa_str rd' p s.
Proof.
intros rd rd' p s ((Hz & Hn) & Ht) K. split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite K by lia. exact (Hz i Hi).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as Hm.
  rewrite K by lia. exact (Ht x Hx).
Qed.
(* the `blez s4` at 0x894b0 (bge zero, s4) with s4 = line in [0, 2 ^ 31) *)
Lemma rpp_br_ge : forall E ln, ew E 11 = Z_to_bv 64 ln -> 0 <= ln < 2 ^ 31 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff 11 0)) = (ln <=? 0).
Proof.
intros E ln H Hl. rewrite OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YO0c.branch_ge.
change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)).
change (bv_unsigned (sv_denot E (SOff 11 0))) with (U E (SOff 11 0)).
rewrite U_lit by lia. rewrite (U_atom E 11 ln H) by lia.
rewrite !OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YO0b.s64_small by lia.
destruct (Z.leb_spec ln 0); destruct (Z.ltb_spec 0 ln); cbn [negb]; first [reflexivity | lia].
Qed.
(* 64-bit words as the executor's terms leave them (trim_k.v's w64_mod / md_mul_lit) *)
Lemma rpp_w64_mod : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. exact H.
Qed.
Lemma rpp_md_mul_lit : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
intros a b. rewrite m_mul. unfold v_mul. apply rpp_w64_mod. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite <- Z.mul_mod by lia. reflexivity.
Qed.
(* refuse's lia over the layout constants *)
Ltac rpp_zl := unfold seg_spec.RC_REFUSED, seg_spec.RC_READING, seg_spec.SEG_C_SIZE, seg_spec.RC_REFUSAL,
  seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF, SB in *; lia.
Ltac rpp_in_tac := let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; vm_compute in Hx; repeat (destruct Hx as [<- | Hx]; [vm_compute; repeat (first [left; reflexivity | right]) |]); destruct Hx.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variables (STK RLO RHI : Z) (lit : list Z -> Z) (gotw guard : Z) (cr : list (Z * Z)).
Hypothesis SNP : forall fx0 : YK11.FPState, @seg_asnprintf_realizes fx0 rc SEGS B 0x10000 kImgEnd cr
  (SIGMA SS___interceptor_trampoline_snprintf) gotw guard.
Hypothesis VSNP : forall fx0 : YK11.FPState, @seg_avsnprintf_realizes fx0 rc SEGS B 0x10000 kImgEnd cr
  (SIGMA SS___interceptor_trampoline_vsnprintf) gotw guard.
Hypothesis FFR : ffr_family SEGS B gotw (FR_seg 0x10000 gotw).
Hypothesis REL : forall fx0 : YK11.FPState, RB_REL_stmt (fx := fx0) B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis OBJ71 : VAL (A_OBJ 71) = lit SegModel.F_addr_line.
Hypothesis OBJ72 : VAL (A_OBJ 72) = lit SegModel.F_addr.
Hypothesis FMTS : forall fmt, In fmt REFUSE_ALL_FMTS ->
  0x10000 <= lit fmt /\ lit fmt + Z.of_nat (length fmt) + 1 <= gotw.
Hypothesis GOTW : 0x10000 <= gotw /\ gotw + 8 <= kImgEnd /\ 0x10000 <= guard /\ guard + 8 <= kImgEnd.
Hypothesis CRP : Forall (fun r => 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kImgEnd) cr.
(* the second half, from RB_TEXT to the return, at every FP state (refuse_Pt.v) *)
Let TXT : forall fx0 : YK11.FPState, RBP_TXT_stmt (fx := fx0) B STK RLO RHI lit gotw guard :=
  fun fx0 => rbp_txt (fx := fx0) B STK RLO RHI lit gotw guard cr VSNP FFR REL LAWS FMTS GOTW CRP.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.


(* a literal of the image keeps its bytes across a journal whose footprint misses the image (reac_segconf_parse.v's
   sa_lit_journal, with the footprint premise taken for every image byte) *)
Lemma rpp_lit_journal : forall STK0 sp FP ly0 S0 (W0 : world SEGS) mem0 md0 own ly' S' (W' : world SEGS) mem' md' k a s,
  ajournal SEGS B STK0 sp FP ly0 S0 W0 mem0 md0 own ly' S' W' mem' md' k -> ~ YI16.sink_open_fp FP ->
  (forall x, in_img SEGS x -> ~ inFP FP x) ->
  sa_lit SEGS B (rdW W0 mem0) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros STK0 sp FP ly0 S0 W0 mem0 md0 own ly' S' W' mem' md' k a s HJ HC HnF (Ha & ((Hz & Hn) & _) & Hp & Hr & Hi).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Hm & Ho & He).
rewrite F3; [exact (Hz i Hi') | exact Hm | exact Ho | exact He | apply fp_spares_closed; [exact HC | apply HnF; exact Hm]].
Qed.

Theorem rb_pre : RB_PRE_stmt B STK RLO RHI lit gotw guard.
Proof.
unfold RB_PRE_stmt.
intros ly S W regs mem md ch c line fp ln rcs f args ms md2 S2 fpos Ev
  HCX HSTK HN8 HEI HS HJ Hfrs2 Eab HS2f AGR E32 E33 E34 E35 E36 E37 E1028 E1040 E1041 E1101 HKEEP HR32 HSSP.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HCX as (HPRE & HROD & H10 & Hc64 & H11 & Hl64 & H12 & Hfp64 & HRPRE & HROOM & HEV).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HRPRE as (Hc0 & Hc16 & HRC & HHEAP & HADDR & HREF1 & Hln & Hlne & Hinf & Hck & Hfp0 & Hfpl & HLIT
  & HVA & HLOCS & HFRM & HSSP0 & HLITS).
pose proof (proj1 HJ) as HAR2.
(* the block c at the state of the cut *)
assert (HHEAP2 : sa_heap B ly S2 c seg_spec.SEG_C_SIZE)
  by (destruct HHEAP as (b & m & Hin & H1 & H2); exists b, m; split; [rewrite Eab; exact Hin | lia]).
destruct HHEAP2 as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR2 Hbc) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbm).
pose proof (req_size_pos mc (proj1 Hbm)) as [_ Hreq].
set (sp0 := spZ regs) in *.
(* the environment at the cut *)
assert (U10 : U Ev (SOff 10 0) = c)
  by (apply (U_atom Ev 10 c); [rewrite (AGR 10%nat 10%bv eq_refl); exact H10 | lia]).
assert (UB : U Ev (SOff 32 0) = SHADOW_OFF)
  by (rewrite (U_atom Ev 32 SB E32) by (unfold SB; lia); reflexivity).
assert (HRAc : range_addressable (rdW W (ms_mem ms)) SHADOW_OFF c seg_spec.SEG_C_SIZE)
  by (apply (range_addressable_of_block SEGS B LAWS ly S2 W (ms_mem ms) md2 bc mc); [exact HAR2 | exact Hbc |
      lia | unfold seg_spec.SEG_C_SIZE in *; lia]).
assert (SHOK : sh_ok SEGS (SOff 32 0) rb_SH Ev (mrestrict (w_H W) (ms_mem ms))).
{ unfold sh_ok, rb_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) (ms_mem ms) Ev (SOff 32 0) 10 c seg_spec.SEG_C_SIZE c 0 16616
    HRAc UB U10); [unfold seg_spec.SEG_C_SIZE; lia | unfold seg_spec.SEG_C_SIZE; lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  unfold SHADOW_OFF. unfold seg_spec.SEG_C_SIZE in *. lia. }
assert (Usp : bv_unsigned (ew Ev 2) = sp0) by (rewrite (AGR 2%nat 2%bv eq_refl); reflexivity).
destruct (rsp1_facts sp0 Hal16) as (Hs1al & Hs1).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hs1r : alloc_ceiling <= rsp1 sp0 /\ rsp1 sp0 <= sp0 - 160) by lia.
assert (Usp1 : bv_unsigned (ew Ev 33) = rsp1 sp0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U10b : bv_unsigned (ew Ev 10) = c)
  by (rewrite (AGR 10%nat 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (HWB : forall a, c + seg_spec.RC_REFUSED <= a < c + seg_spec.RC_REFUSED + 4 ->
  awr_byte SEGS B STK sp0 (refuse_W c rcs) (ablocks B ly S) (ablocks B ly S2) (frames S) ly [(0, fpos)] a).
{ intros a Ha. right; left. split.
  - exists (c + seg_spec.RC_REFUSED, c + seg_spec.RC_REFUSED + 4).
    split; [unfold refuse_W; cbn [app In]; left; reflexivity | cbn [fst snd]; lia].
  - exists bc, mc. split; [exact Hbc|].
    unfold seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *. lia. }
Ltac rbw_ro := apply awr_ok_cons_ro; [cbn; lia|].
Ltac rbw_awr sp0 c Usp Usp1 U10b HWB :=
  lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc0 ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc0 fr0 lyx own) end;
  do 4 rbw_ro;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |];
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |];
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 33%nat (rsp1 sp0 - sp0)); [reflexivity | rewrite Usp1; lia | cbn; lia | cbn; lia |];
  do 4 rbw_ro;
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat c);
    [reflexivity | exact U10b
    | let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply HWB; unfold seg_spec.RC_REFUSED in *; lia |];
  rbw_ro; apply awr_ok_nil.
(* 0x894ac .. 0x894b0: dst, then the `blez s4` *)
assert (HOFF : c + seg_spec.SEG_C_SIZE <= 0x10000 \/ kImgEnd <= c).
{ pose proof (blk_off_imgP B ly S2 W (ms_mem ms) md2 bc mc HAR2 Hbc) as Ho. unfold off_img in Ho.
  unfold seg_spec.SEG_C_SIZE, kImgEnd in *. lia. }
assert (HNFPI : forall a, in_img SEGS a -> ~ inFP (refuse_W c rcs) a).
{ intros a Hia (r & Hin & Hr). pose proof (pa_img_range a Hia) as Hrg.
  unfold refuse_W in Hin. cbn [app In] in Hin.
  destruct (Nat.ltb (length (rc_refusal rcs)) 8) eqn:E8; cbn [In] in Hin;
  [ destruct Hin as [<- | [<- | [<- | []]]] | destruct Hin as [<- | []] ];
  cbn [fst snd] in Hr; unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
    seg_spec.RC_REFUSED, seg_spec.RC_NREF, seg_spec.SEG_C_SIZE, kImgEnd in *;
  pose proof (Nat2Z.is_nonneg (length (rc_refusal rcs))); lia. }
assert (HNSK : ~ YI16.sink_open_fp (refuse_W c rcs)).
{ intros (r & Hin & Hr). unfold refuse_W in Hin. cbn [app In] in Hin.
  destruct (Nat.ltb (length (rc_refusal rcs)) 8) eqn:E8; cbn [In] in Hin;
  [ destruct Hin as [<- | [<- | [<- | []]]] | destruct Hin as [<- | []] ];
  cbn [fst snd] in Hr; unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
    seg_spec.RC_REFUSED, seg_spec.RC_NREF in *;
  pose proof (Nat2Z.is_nonneg (length (rc_refusal rcs))); lia. }
(* rt_rom_view at the cut: the entry's read-only bytes, kept by the journal *)
assert (HROM : RtDefs.rt_rom_view SEGS B W (ms_mem ms)).
{ intros a (sg & Hsg & Hw & Hr) Hoa Hea.
  assert (Hia : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Hia Hoa Hea (fp_spares_closed _ a HNSK (HNFPI a Hia))).
  exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Hoa Hea). }
paj_run_tok RUN HS HJ SHOK Bspan.
{ rbw_awr sp0 c Usp Usp1 U10b HWB. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => (sp0 - 176 <= a < sp0) \/ (c + seg_spec.RC_REFUSED <= a < c + seg_spec.RC_REFUSED + 4)) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin; cbv beta;
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?Usp1, ?U10b in Hrr;
       unfold seg_spec.RC_REFUSED; clear - Hrr Hs1; lia |]);
    destruct Hin)) as UN1.
clear HF HFr HG.

(* ======================= what both arms share: the record, the slot, the where pointer ======================= *)
pose proof GOTW as (Gw0 & Gw1 & Gd0 & Gd1).
pose proof HRC as (bs & Hbs & Henc).
pose proof Henc as (_ & _ & _ & _ & _ & _ & _ & (Hrf0 & _) & _).
destruct (rf_T1 rcs bs ln Henc Hln) as (HT1l & _ & _).
change (SegModel.fmt (SegModel.r_addr_fmt ln) (SegModel.r_addr_args rcs ln)) with (rbp_T1 rcs ln) in HT1l.
assert (HSN : sn_len (200 - 1) (rbp_T1 rcs ln) = Z.of_nat (length (rbp_T1 rcs ln)) + 1).
{ unfold sn_len, sn_bytes. rewrite length_app, length_firstn. cbn [length]. lia. }
assert (HSB : sn_bytes (200 - 1) (rbp_T1 rcs ln) = rbp_T1 rcs ln ++ [0]).
{ unfold sn_bytes. rewrite firstn_all2 by lia. reflexivity. }
assert (E11 : ew Ev 11 = Z_to_bv 64 ln) by (rewrite (AGR 11%nat 11%bv eq_refl), H11, Hlne; reflexivity).
pose (d := seg_spec.refusal_addr c (length (rc_refusal rcs))).
assert (Hdv : d = c + 11912 + 200 * Z.of_nat (length (rc_refusal rcs)))
  by (unfold d, seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN; lia).
assert (HnR : 0 <= Z.of_nat (length (rc_refusal rcs)) <= 7) by lia.
assert (Hbc2' : c + 16616 <= bc + mc) by exact Hbc2.
assert (HcB : 4096 <= c /\ c + 16616 <= alloc_ceiling) by lia.
assert (Hs1lo : sp0 - 176 <= rsp1 sp0) by lia.
assert (HWn : alloc_ceiling + 8192 <= rsp1 sp0) by lia.
assert (HIE : kImgEnd + 8192 <= alloc_ceiling) by (unfold kImgEnd; lia).
assert (HKK : SEG_SNP_K = 8192) by (unfold SEG_SNP_K; rewrite Hes; reflexivity).
assert (HOFF' : c + 16616 <= 65536 \/ kImgEnd <= c) by exact HOFF.
assert (Hc8 : c mod 8 = 0)
  by (pose proof (Z.div_mod c 16 ltac:(lia)) as D; rewrite Hc16, Z.add_0_r in D; rewrite D;
      replace (16 * (c / 16)) with ((2 * (c / 16)) * 8) by lia; apply Z_mod_mult).
pose (wv := if SegModel.hd0 (rc_reading rcs) =? 0 then lit SegModel.S_base else c + seg_spec.RC_READING).
pose proof (Z.mod_pos_bound (- (wv + Z.of_nat (length (SegModel.r_where rcs)) + 1)) 8 ltac:(lia)) as Hwm.
assert (WLOC : (0x10000 <= wv /\ wv + Z.of_nat (length (SegModel.r_where rcs)) + 1 <= kImgEnd) \/
  (wv = c + seg_spec.RC_READING /\ (length (SegModel.r_where rcs) <= 95)%nat)).
{ unfold wv, SegModel.r_where. destruct (Z.eqb_spec (SegModel.hd0 (rc_reading rcs)) 0) as [Hh|Hh].
  - left. destruct (HLITS SegModel.S_base ltac:(left; reflexivity)) as (_ & _ & _ & _ & Hi).
    pose proof (pa_img_range _ (proj1 (Hi (lit SegModel.S_base) ltac:(lia)))) as R0.
    pose proof (pa_img_range _ (proj1 (Hi (lit SegModel.S_base + Z.of_nat (length SegModel.S_base)) ltac:(lia)))) as R1.
    lia.
  - right. split; [reflexivity|]. exact (proj1 (proj2 (rf_reading _ c rcs HRC Hc8 Hh))). }
assert (Hwv : 0 <= wv < 2 ^ 64) by (unfold kImgEnd, seg_spec.RC_READING in *; lia).
(* the memory facts every state that keeps the bytes outside the stack and c->refused has *)
assert (MEMF : forall m, (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 176 <= a < sp0) ->
    ~ (c + seg_spec.RC_REFUSED <= a < c + seg_spec.RC_REFUSED + 4) -> rdW W m a = rdW W (ms_mem ms) a) ->
  sa_ssp (rdW W m) gotw guard /\ RtDefs.rt_rom_view SEGS B W m /\
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
     rdW W m (c + i) = rdW W mem (c + i))).
{ intros m UNm. split; [|split].
  - apply (rpp_ssp_keep (rdW W (ms_mem ms)) _ gotw guard HSSP); intros i Hi; apply UNm; unfold kImgEnd in *; rpp_zl.
  - eapply RtDefs.rt_rom_view_keep; [exact HROM|]. intros a (sg & Hsg & Hw & Hr) _ _.
    pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as Hia. apply UNm; unfold kImgEnd in *; rpp_zl.
  - intros i Hi Hr. rewrite UNm by rpp_zl. apply HKEEP; assumption. }
(* the where string at every AR state that keeps the block outside c->refused *)
assert (WHM : forall m md', AR SEGS B ly S2 W m md' ->
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
     rdW W m (c + i) = rdW W mem (c + i)) ->
  sa_lit SEGS B (rdW W m) (lit SegModel.S_base) SegModel.S_base ->
  0 < wv /\ sa_str (rdW W m) wv (SegModel.r_where rcs) /\
  sa_addr (rdW W m) wv (Z.of_nat (length (SegModel.r_where rcs)) + 1) /\
  amem_range wv (Z.of_nat (length (SegModel.r_where rcs)) + 8) /\ (length (SegModel.r_where rcs) <= 95)%nat).
{ intros m md' HARm KBm LITm. unfold wv, SegModel.r_where.
  destruct (Z.eqb_spec (SegModel.hd0 (rc_reading rcs)) 0) as [Hh|Hh].
  - destruct LITm as (Ha & Hs & Hp & Hr & Hi).
    pose proof (pa_img_range _ (proj1 (Hi (lit SegModel.S_base + Z.of_nat (length SegModel.S_base)) ltac:(lia)))) as R1.
    split; [exact Ha|]. split; [exact Hs|]. split; [exact (Hp ly S2 W m md' HARm)|].
    split; [apply amem8_of_low; unfold kImgEnd in R1; lia | apply Nat.leb_le; vm_compute; reflexivity].
  - destruct (rf_reading _ c rcs HRC Hc8 Hh) as (Hs & Hl & _).
    unfold seg_spec.RC_READING in *.
    split; [lia|]. split.
    { apply (rpp_str_keep (rdW W mem)); [exact Hs|]. intros x Hx.
      replace x with (c + (x - c)) by lia. apply KBm; rpp_zl. }
    split.
    { split; [lia|]. split; [lia|]. split.
      { apply (amem_range_sub_app bc (req_size mc)); [exact Hbapp | exact Hbceil | lia | lia | lia]. }
      split.
      { apply (range_addressable_of_block SEGS B LAWS ly S2 W m md' bc mc); [exact HARm | exact Hbc | lia | lia]. }
      intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S2 W m md' bc mc); [exact HARm | exact Hbc | lia | lia | lia]. }
    split; [|exact Hl].
    apply (amem_range_sub_app bc (req_size mc)); [exact Hbapp | exact Hbceil | lia | lia | lia]. }
(* what a token run kept: every byte outside the stack below sp0 and c->refused *)
Ltac rpp_unch HFx UN U2 U33 U10 sp0 c Hs1 :=
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => (sp0 - 176 <= a < sp0) \/ (c + seg_spec.RC_REFUSED <= a < c + seg_spec.RC_REFUSED + 4)) HFx
    ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
      let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
      intros b wlo whi a Hin Hrr; vm_compute in Hin; cbv beta;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2, ?U33, ?U10 in Hrr;
         unfold seg_spec.RC_REFUSED; clear - Hrr Hs1; lia |]);
      destruct Hin)) as UN.
(* the branch at 0x894b0 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* line <= 0: a2 = object 72 ("%s: "), the jal at 0x894e0 returns at RB_TEXT *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { rbw_awr sp0 c Usp Usp1 U10b HWB. }
  rpp_unch HFr UN2 Usp Usp1 U10b sp0 c Hs1. clear HF HFr HG.
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (13%bv : bv 5) Q13.
  assert (Eln : (0 <? ln) = false).
  { rewrite (rpp_br_ge Ev ln E11 Hln) in Hc. apply Z.ltb_ge. apply Z.leb_le in Hc. exact Hc. }
  assert (EF : SegModel.r_addr_fmt ln = SegModel.F_addr) by (unfold SegModel.r_addr_fmt; rewrite Eln; reflexivity).
  assert (INF : In SegModel.F_addr REFUSE_ALL_FMTS) by (right; left; reflexivity).
  assert (INL : In SegModel.F_addr REFUSE_LITS) by (right; right; left; reflexivity).
  assert (UNc : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 176 <= a < sp0) ->
    ~ (c + seg_spec.RC_REFUSED <= a < c + seg_spec.RC_REFUSED + 4) -> rdW W (ms_mem ms1) a = rdW W (ms_mem ms) a).
  { intros a Ha N1 N2. rewrite (UN2 a Ha) by (cbv beta; tauto). apply UN1; [exact Ha | cbv beta; tauto]. }
  destruct (MEMF (ms_mem ms1) UNc) as (SSP1 & ROM1 & KB1).
  assert (LIT1 : forall x, In x REFUSE_LITS -> sa_lit SEGS B (rdW W (ms_mem ms1)) (lit x) x).
  { intros x Hx. eapply rpp_lit_journal; [exact HJ | exact HNSK | exact HNFPI | exact (HLITS x Hx)]. }
  destruct (WHM (ms_mem ms1) mdv (proj1 HJ) KB1 (LIT1 SegModel.S_base ltac:(left; reflexivity))) as (W0 & W1 & W2 & W3 & W4).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc (proj1 HJ) Hbc) as (_ & _ & _ & _ & HbpresT & _).
  assert (Rsp : spZ (ms_regs ms1) = sp0 + (rsp1 sp0 - sp0))
    by (unfold spZ; rewrite Q2, E33, unsigned_lit_small by lia; lia).
  assert (HRS : snp_out SEG_SNP_K (spZ (ms_regs ms1)) d (sn_len (200 - 1) (rbp_T1 rcs ln)) =
      [(rsp1 sp0 - 8192, 8192); (d, Z.of_nat (length (rbp_T1 rcs ln)) + 1)]).
  { unfold snp_out. rewrite Rsp, HSN, HKK.
    replace (sp0 + (rsp1 sp0 - sp0) - 8192) with (rsp1 sp0 - 8192) by lia. reflexivity. }
  assert (Harg3 : argZ (ms_regs ms1) 3 = wv).
  { unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q13, E1101. apply unsigned_lit_small. exact Hwv. }
  assert (WDIS : Forall (zdisjoint (wv, seg_spec.cstr_span wv (SegModel.r_where rcs)))
      (snp_out SEG_SNP_K (spZ (ms_regs ms1)) d (sn_len (200 - 1) (rbp_T1 rcs ln)))).
  { rewrite HRS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold zdisjoint, seg_spec.cstr_span; cbn [fst snd]; unfold kImgEnd in *; rpp_zl. }
  assert (WARG : refuse_pft.ffr_arg (rdW W (ms_mem ms1))
      (snp_out SEG_SNP_K (spZ (ms_regs ms1)) d (sn_len (200 - 1) (rbp_T1 rcs ln)))
      (argZ (ms_regs ms1) 3) (SegModel.AS (SegModel.r_where rcs))).
  { rewrite Harg3.
    pose proof (rbf_ffr_args_addr W (ms_mem ms1) _ wv ln rcs [] W0 W1 W2 W3 W4 WDIS Hln) as HA.
    unfold SegModel.r_addr_args in HA. destruct (0 <? ln); cbn [refuse_pft.ffr_args] in HA; exact (proj1 HA). }
  assert (HARGS : refuse_pft.ffr_args (rdW W (ms_mem ms1))
      (snp_out SEG_SNP_K (spZ (ms_regs ms1)) d (sn_len (200 - 1) (rbp_T1 rcs ln)))
      (map (argZ (ms_regs ms1)) [3; 4; 5; 6; 7]) (SegModel.r_addr_args rcs ln)).
  { unfold SegModel.r_addr_args. rewrite Eln. cbn [map refuse_pft.ffr_args]. split; [exact WARG | exact I]. }
  assert (R10 : getr (ms_regs ms1) 10 = w64 d)
    by (rewrite Q10, U10b, E35, rpp_md_mul_lit, alu64_add_lit; unfold w64; f_equal; lia).
  assert (R12 : getr (ms_regs ms1) 12 = w64 (lit SegModel.F_addr))
    by (rewrite Q12, (img_env_atomP Ev 313%nat HEI) by (unfold A_TEXT, A_LIM; lia); rewrite <- OBJ72; reflexivity).
  assert (Ro16 : (rsp1 sp0 - sp0) mod 16 = 0).
  { destruct Hs1 as [Hq|Hq]; rewrite Hq;
      [replace (sp0 - 160 - sp0) with (-160) by lia | replace (sp0 - 176 - sp0) with (-176) by lia]; reflexivity. }
  assert (R3 : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite Q3, (AGR 3%nat 3%bv eq_refl); exact Hgp).
  assert (R4 : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite Q4, (AGR 4%nat 4%bv eq_refl); exact Htp).
  assert (HDEST : forall a, d <= a < d + 200 ->
    awr_byte SEGS B STK sp0 (refuse_W c rcs) (ablocks B ly S) (ablocks B ly S2) (frames S) ly [(0, fpos)] a /\
    ~ (sp0 + (rsp1 sp0 - sp0) - SEG_SNP_K <= a < sp0 + (rsp1 sp0 - sp0))).
  { intros a Ha. split; [|rewrite HKK; lia]. right; left. split.
    - exists (d, d + seg_spec.RC_REFUSAL_LEN). split; [|cbn [fst snd]; unfold seg_spec.RC_REFUSAL_LEN; lia].
      unfold refuse_W. rewrite (proj2 (Nat.ltb_lt _ _) HN8). cbn [app In]. right; left. reflexivity.
    - exists bc, mc. split; [exact Hbc | lia]. }
  assert (HWR : forall a, d <= a < d + 200 -> inFP (refuse_W c rcs) a ->
      (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ sp0 <= a < ly_top ly ->
      writable_at SEGS (mrestrict (w_H W) (ms_mem ms1)) a).
  { intros a Ha _ _. apply (apresent_writable SEGS). exact (proj1 (HbpresT a ltac:(lia))). }
  assert (HAM : amem_range d (200 + 8))
    by (apply (amem_range_sub_app bc (req_size mc)); [exact Hbapp | exact Hbceil | lia | lia | lia]).
  assert (HRA : range_addressable (rdW W (ms_mem ms1)) SHADOW_OFF d 200)
    by (apply (range_addressable_of_block SEGS B LAWS ly S2 W (ms_mem ms1) mdv bc mc); [exact (proj1 HJ) | exact Hbc | lia | lia]).
  assert (HHV : shadow_hull_vis (rdW W (ms_mem ms1)) d 200)
    by (apply (shadow_hull_vis_of_block SEGS B LAWS ly S2 W (ms_mem ms1) mdv bc mc); [exact (proj1 HJ) | exact Hbc | lia | lia | lia]).
  assert (HFF : FR_seg 0x10000 gotw (rdW W (ms_mem ms1))
      (snp_out SEG_SNP_K (spZ (ms_regs ms1)) d (sn_len (200 - 1) (rbp_T1 rcs ln)))
      (lit SegModel.F_addr) (map (argZ (ms_regs ms1)) [3; 4; 5; 6; 7]) (rbp_T1 rcs ln)).
  { apply (FFR _ _ _ (SegModel.r_addr_fmt ln) _ (SegModel.r_addr_args rcs ln)).
    - exact (rbf_addr_fmt_in ln).
    - exact (rbf_addr_conv rcs ln).
    - rewrite EF. destruct (FMTS SegModel.F_addr INF) as (F1 & F2).
      eapply rbf_ffr_fmt; [exact (proj1 HJ) | exact (LIT1 SegModel.F_addr INL) | exact F1 | exact F2 | exact Gw1 |].
      rewrite HRS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
        unfold zdisjoint, seg_spec.cstr_span; cbn [fst snd];
        pose proof (Z.mod_pos_bound (- (lit SegModel.F_addr + Z.of_nat (length SegModel.F_addr) + 1)) 8 ltac:(lia));
        unfold kImgEnd in *; lia.
    - exact HARGS. }
  unfold RB_POST.
  eapply (srr_after_artF SEGS).
  { exact (refuse_Ps.rbs_aj_snprintf_atSF SEGS B LAWS pa_segs_low (FR_seg 0x10000 gotw) SEG_SNP_K gotw guard 0x10000 kImgEnd cr
      (SIGMA SS___interceptor_trampoline_snprintf) (SNP fx) ltac:(rewrite HKK, Hes; lia) ltac:(lia) Gw0 Gd0
      ltac:(unfold kImgEnd; lia) CRP
      W (ms_regs ms1) (ms_mem ms1) STK sp0 (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 mdv 0 d 200
      (lit SegModel.F_addr) (rbp_T1 rcs ln) (rsp1 sp0 - sp0) (Z_to_bv 64 (BASE + 18212))
      HJ R10 Q11 R12 ltac:(lia) ltac:(lia) ltac:(lia) Rsp Ro16 ltac:(lia) ltac:(rewrite HKK; lia) R3 R4 Q1
      (ret_ok_codeptr_v 18212 ltac:(lia) eq_refl) HDEST HWR HAM HRA HHV ltac:(lia) ltac:(rewrite HKK; lia) SSP1
      ltac:(lia) Gw1 ltac:(lia) Gd1 HFF ltac:(lia) ROM1 HFRM). }
  cbv beta. intros fx1 regs2 mem2 md3 Hfx (HJ2 & HP2 & Ha0 & HBY & HK2 & HPR2 & Hsame).
  (* after the call: the regions it keeps, the state at fx1, the fresh atoms 1300.. of its clobbered registers *)
  assert (Hfin : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly S2 W (ms_mem ms1) mdv 0 fpos (proj1 HJ) Hfin) as (HF4096 & HFceil & HFapp).
  pose proof (sep_block_frame SEGS B LAWS ly S2 W (ms_mem ms1) mdv bc mc 0 fpos (proj1 HJ) Hbc Hfin) as HSBF.
  change (fs_frame_bytes 0) with 64 in HFceil, HFapp, HSBF.
  unfold zdisjoint in HSBF. cbn [fst snd] in HSBF.
  assert (HF8 : 0 <= frame_addr ly 0 fpos / 8 /\ 8 * (frame_addr ly 0 fpos / 8) <= frame_addr ly 0 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (U1028 : bv_unsigned (ew Ev 1028) = frame_addr ly 0 fpos) by (rewrite E1028; apply unsigned_lit_small; lia).
  assert (U1041 : bv_unsigned (ew Ev 1041) = SB + frame_addr ly 0 fpos / 8)
    by (rewrite E1041; apply unsigned_lit_small; unfold SB; lia).
  jafter_call_keep_hi HS rbp_KS regs2 (mrestrict (w_H W) mem2) HP2 rbp_keepi HS2.
  match type of HS2 with ?A -> _ => assert (HQ : A); [|specialize (HS2 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    all: eapply region_kept_aview; [first [exact U1041 | exact U1028 | exact Usp | exact U10b] | | exact HPR2].
    all: intros a Ha; apply HK2;
      [ unfold SB in *; lia
      | rewrite HSN; intros Hq;
        first [ lia
              | exact (fshadow_not_app (frame_addr ly 0 fpos) 8 bc (req_size mc) a HF4096 ltac:(lia) Hbapp
                  ltac:(unfold SB in Ha; lia) ltac:(lia)) ]
      | rewrite HKK; unfold SB in *; lia ]. }
  rewrite <- restrict_mkst_fx in HS2.
  apply (st_ok_pi_restrict_xfx fx fx1) in HS2.
  set (Ev' := havoc Ev rbp_KS (map (getr regs2) CLOB)) in HS2.
  assert (HEI' : img_env VAL A_LIM Ev') by (unfold Ev'; apply img_env_havoc_hi; [exact HEI | unfold rbp_KS, A_LIM; lia]).
  assert (AG' : forall n, (n < 1300)%nat -> ew Ev' n = ew Ev n) by (intros n Hn; unfold Ev'; apply ew_havoc_old; exact Hn).
  assert (E1304 : ew Ev' 1304 = Z_to_bv 64 (Z.of_nat (length (rbp_T1 rcs ln)))).
  { unfold Ev'. change 1304%nat with (rbp_KS + 4)%nat.
    rewrite (ew_havoc_new Ev rbp_KS (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbn; lia).
    cbn [nth map CLOB]. exact Ha0. }
  assert (Usp' : bv_unsigned (ew Ev' 2) = sp0) by (rewrite AG' by lia; exact Usp).
  assert (U10b' : bv_unsigned (ew Ev' 10) = c) by (rewrite AG' by lia; exact U10b).
  pose proof (st_ok_pi_facts_incl3 _ _ _ (f_atoms (ss_facts ss_pre)) [] (f_alias (ss_facts ss_pre)) HS2
    ltac:(rpp_in_tac) (fun x (Hx : In x []) => match Hx with end) ltac:(rpp_in_tac)) as HS3.
  clear HS2. rbp_to HS3 ss_txt.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 176 <= a < sp0) ->
    ~ (c + seg_spec.RC_REFUSED <= a < c + seg_spec.RC_REFUSED + 4) -> rdW W mem2 a = rdW W mem2 a) by reflexivity.
  (* RB_TEXT: what RBP_TXT_stmt asks at the final memory, then TXT at fx1 *)
  lazymatch type of HS3 with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let i := eval vm_compute in (rbp_find (ss_mem ssx) 10%nat 13512 0) in
    let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) i r HS3 ltac:(vm_compute; reflexivity)) as HRcnt;
    cbn [ms_mem restrict] in HRcnt end.
  pose proof (rpp_region_aval4 SEGS Ev' (w_H W) _ 10 c _ _ _ _ _ 13516 (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) _
    HRcnt U10b' ltac:(first [left; reflexivity | right; left; reflexivity]) (eq_sym (Z_to_bv_bv_unsigned _ _))) as Vrf.
  assert (E36' : ew Ev' 36 = Z_to_bv 64 (rc_refused rcs)) by (rewrite AG' by lia; exact E36).
  assert (RFF : rd32 (rdW W mem2) (c + seg_spec.RC_REFUSED) (rc_refused rcs + 1)).
  { change seg_spec.RC_REFUSED with 13516. apply (rpp_rd32_mod _ _ _ _ Vrf).
    change (bv_unsigned (sv_denot Ev' (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1))))
      with (U Ev' (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1))).
    rewrite (rpp_inc_mod Ev' (rc_refused rcs) E36' (proj1 Hrf0) HREF1). symmetry. apply Z.mod_small. lia. }
  assert (SSPF : sa_ssp (rdW W mem2) gotw guard).
  { apply (rpp_ssp_keep (rdW W (ms_mem ms1)) _ gotw guard SSP1); intros i Hi;
      try (rewrite KF by (unfold kImgEnd in *; rpp_zl));
      (apply HK2; [ unfold kImgEnd in *; lia | rewrite HSN; unfold kImgEnd in *; rpp_zl | rewrite HKK; unfold kImgEnd in *; lia ]). }
  assert (KEEPF : forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
      ~ (seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) <= i <
         seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat (length (rbp_T1 rcs ln)) + 1) ->
      rdW W mem2 (c + i) = rdW W mem (c + i)).
  { intros i Hi Hr Hs. try (rewrite KF by rpp_zl).
    rewrite HK2 by (first [rewrite HSN; rpp_zl | rewrite HKK; rpp_zl | rpp_zl]). apply KB1; assumption. }
  assert (ZSF : sa_zs (rdW W mem2) d (rbp_T1 rcs ln ++ [0])).
  { intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    try (rewrite KF by rpp_zl). rewrite (HBY (Z.of_nat i)) by (rewrite HSN; lia).
    rewrite Nat2Z.id, HSB. reflexivity. }
  assert (HFRM1 : sa_frm0 (fx := fx1)) by exact (fxrel_frm0 fx fx1 HFRM Hfx).
  assert (HCX1 : rb_cx (fx := fx1) B STK RLO RHI lit gotw guard ly S W regs mem md ch c line fp ln rcs f args)
    by exact (conj HPRE (conj HROD (conj H10 (conj Hc64 (conj H11 (conj Hl64 (conj H12 (conj Hfp64
      (conj (conj Hc0 (conj Hc16 (conj HRC (conj HHEAP (conj HADDR (conj HREF1 (conj Hln (conj Hlne (conj Hinf
        (conj Hck (conj Hfp0 (conj Hfpl (conj HLIT (conj HVA (conj HLOCS (conj HFRM1 (conj HSSP0 HLITS)))))))))))))))))
      (conj HROOM HEV)))))))))).
  assert (AGR' : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ev' n = getr regs r).
  { intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    rewrite AG' by lia. apply AGR. exact Hn. }
  lazymatch goal with |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
    refine (TXT fx1 ly S W regs mem md ch c line fp ln rcs f args msF mdF S2 fpos Ev' HCX1 HSTK HN8 HEI' HS3 HJ2
      Hfrs2 Eab HS2f AGR' _ _ _ _ _ _ _ E1304 SSPF KEEPF RFF ZSF) end;
    rewrite AG' by lia; assumption.
- (* line > 0: a2 = object 71 ("%s:%d: "), a4 = line, the jal at 0x894c8 returns at RB_SNP_RET, then the `j` *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { rbw_awr sp0 c Usp Usp1 U10b HWB. }
  rpp_unch HFr UN2 Usp Usp1 U10b sp0 c Hs1. clear HF HFr HG.
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
  assert (Eln : (0 <? ln) = true).
  { rewrite (rpp_br_ge Ev ln E11 Hln) in Hc. apply Z.ltb_lt. apply Z.leb_gt in Hc. exact Hc. }
  assert (EF : SegModel.r_addr_fmt ln = SegModel.F_addr_line) by (unfold SegModel.r_addr_fmt; rewrite Eln; reflexivity).
  assert (INF : In SegModel.F_addr_line REFUSE_ALL_FMTS) by (left; reflexivity).
  assert (INL : In SegModel.F_addr_line REFUSE_LITS) by (right; left; reflexivity).
  assert (UNc : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 176 <= a < sp0) ->
    ~ (c + seg_spec.RC_REFUSED <= a < c + seg_spec.RC_REFUSED + 4) -> rdW W (ms_mem ms1) a = rdW W (ms_mem ms) a).
  { intros a Ha N1 N2. rewrite (UN2 a Ha) by (cbv beta; tauto). apply UN1; [exact Ha | cbv beta; tauto]. }
  destruct (MEMF (ms_mem ms1) UNc) as (SSP1 & ROM1 & KB1).
  assert (LIT1 : forall x, In x REFUSE_LITS -> sa_lit SEGS B (rdW W (ms_mem ms1)) (lit x) x).
  { intros x Hx. eapply rpp_lit_journal; [exact HJ | exact HNSK | exact HNFPI | exact (HLITS x Hx)]. }
  destruct (WHM (ms_mem ms1) mdv (proj1 HJ) KB1 (LIT1 SegModel.S_base ltac:(left; reflexivity))) as (W0 & W1 & W2 & W3 & W4).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc (proj1 HJ) Hbc) as (_ & _ & _ & _ & HbpresT & _).
  assert (Rsp : spZ (ms_regs ms1) = sp0 + (rsp1 sp0 - sp0))
    by (unfold spZ; rewrite Q2, E33, unsigned_lit_small by lia; lia).
  assert (HRS : snp_out SEG_SNP_K (spZ (ms_regs ms1)) d (sn_len (200 - 1) (rbp_T1 rcs ln)) =
      [(rsp1 sp0 - 8192, 8192); (d, Z.of_nat (length (rbp_T1 rcs ln)) + 1)]).
  { unfold snp_out. rewrite Rsp, HSN, HKK.
    replace (sp0 + (rsp1 sp0 - sp0) - 8192) with (rsp1 sp0 - 8192) by lia. reflexivity. }
  assert (Harg3 : argZ (ms_regs ms1) 3 = wv).
  { unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q13, E1101. apply unsigned_lit_small. exact Hwv. }
  assert (WDIS : Forall (zdisjoint (wv, seg_spec.cstr_span wv (SegModel.r_where rcs)))
      (snp_out SEG_SNP_K (spZ (ms_regs ms1)) d (sn_len (200 - 1) (rbp_T1 rcs ln)))).
  { rewrite HRS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold zdisjoint, seg_spec.cstr_span; cbn [fst snd]; unfold kImgEnd in *; rpp_zl. }
  assert (WARG : refuse_pft.ffr_arg (rdW W (ms_mem ms1))
      (snp_out SEG_SNP_K (spZ (ms_regs ms1)) d (sn_len (200 - 1) (rbp_T1 rcs ln)))
      (argZ (ms_regs ms1) 3) (SegModel.AS (SegModel.r_where rcs))).
  { rewrite Harg3.
    pose proof (rbf_ffr_args_addr W (ms_mem ms1) _ wv ln rcs [] W0 W1 W2 W3 W4 WDIS Hln) as HA.
    unfold SegModel.r_addr_args in HA. destruct (0 <? ln); cbn [refuse_pft.ffr_args] in HA; exact (proj1 HA). }
  assert (HARGS : refuse_pft.ffr_args (rdW W (ms_mem ms1))
      (snp_out SEG_SNP_K (spZ (ms_regs ms1)) d (sn_len (200 - 1) (rbp_T1 rcs ln)))
      (map (argZ (ms_regs ms1)) [3; 4; 5; 6; 7]) (SegModel.r_addr_args rcs ln)).
  { unfold SegModel.r_addr_args. rewrite Eln. cbn [map refuse_pft.ffr_args].
    split; [exact WARG|]. split; [|exact I]. cbn [refuse_pft.ffr_arg]. split; [exact Hln|].
    unfold argZ. replace (Z_to_bv 5 (10 + 4)) with (14%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q14, E11. apply unsigned_lit_small. lia. }
  assert (R10 : getr (ms_regs ms1) 10 = w64 d)
    by (rewrite Q10, U10b, E35, rpp_md_mul_lit, alu64_add_lit; unfold w64; f_equal; lia).
  assert (R12 : getr (ms_regs ms1) 12 = w64 (lit SegModel.F_addr_line))
    by (rewrite Q12, (img_env_atomP Ev 312%nat HEI) by (unfold A_TEXT, A_LIM; lia); rewrite <- OBJ71; reflexivity).
  assert (Ro16 : (rsp1 sp0 - sp0) mod 16 = 0).
  { destruct Hs1 as [Hq|Hq]; rewrite Hq;
      [replace (sp0 - 160 - sp0) with (-160) by lia | replace (sp0 - 176 - sp0) with (-176) by lia]; reflexivity. }
  assert (R3 : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite Q3, (AGR 3%nat 3%bv eq_refl); exact Hgp).
  assert (R4 : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite Q4, (AGR 4%nat 4%bv eq_refl); exact Htp).
  assert (HDEST : forall a, d <= a < d + 200 ->
    awr_byte SEGS B STK sp0 (refuse_W c rcs) (ablocks B ly S) (ablocks B ly S2) (frames S) ly [(0, fpos)] a /\
    ~ (sp0 + (rsp1 sp0 - sp0) - SEG_SNP_K <= a < sp0 + (rsp1 sp0 - sp0))).
  { intros a Ha. split; [|rewrite HKK; lia]. right; left. split.
    - exists (d, d + seg_spec.RC_REFUSAL_LEN). split; [|cbn [fst snd]; unfold seg_spec.RC_REFUSAL_LEN; lia].
      unfold refuse_W. rewrite (proj2 (Nat.ltb_lt _ _) HN8). cbn [app In]. right; left. reflexivity.
    - exists bc, mc. split; [exact Hbc | lia]. }
  assert (HWR : forall a, d <= a < d + 200 -> inFP (refuse_W c rcs) a ->
      (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ sp0 <= a < ly_top ly ->
      writable_at SEGS (mrestrict (w_H W) (ms_mem ms1)) a).
  { intros a Ha _ _. apply (apresent_writable SEGS). exact (proj1 (HbpresT a ltac:(lia))). }
  assert (HAM : amem_range d (200 + 8))
    by (apply (amem_range_sub_app bc (req_size mc)); [exact Hbapp | exact Hbceil | lia | lia | lia]).
  assert (HRA : range_addressable (rdW W (ms_mem ms1)) SHADOW_OFF d 200)
    by (apply (range_addressable_of_block SEGS B LAWS ly S2 W (ms_mem ms1) mdv bc mc); [exact (proj1 HJ) | exact Hbc | lia | lia]).
  assert (HHV : shadow_hull_vis (rdW W (ms_mem ms1)) d 200)
    by (apply (shadow_hull_vis_of_block SEGS B LAWS ly S2 W (ms_mem ms1) mdv bc mc); [exact (proj1 HJ) | exact Hbc | lia | lia | lia]).
  assert (HFF : FR_seg 0x10000 gotw (rdW W (ms_mem ms1))
      (snp_out SEG_SNP_K (spZ (ms_regs ms1)) d (sn_len (200 - 1) (rbp_T1 rcs ln)))
      (lit SegModel.F_addr_line) (map (argZ (ms_regs ms1)) [3; 4; 5; 6; 7]) (rbp_T1 rcs ln)).
  { apply (FFR _ _ _ (SegModel.r_addr_fmt ln) _ (SegModel.r_addr_args rcs ln)).
    - exact (rbf_addr_fmt_in ln).
    - exact (rbf_addr_conv rcs ln).
    - rewrite EF. destruct (FMTS SegModel.F_addr_line INF) as (F1 & F2).
      eapply rbf_ffr_fmt; [exact (proj1 HJ) | exact (LIT1 SegModel.F_addr_line INL) | exact F1 | exact F2 | exact Gw1 |].
      rewrite HRS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
        unfold zdisjoint, seg_spec.cstr_span; cbn [fst snd];
        pose proof (Z.mod_pos_bound (- (lit SegModel.F_addr_line + Z.of_nat (length SegModel.F_addr_line) + 1)) 8 ltac:(lia));
        unfold kImgEnd in *; lia.
    - exact HARGS. }
  unfold RB_POST.
  eapply (srr_after_artF SEGS).
  { exact (refuse_Ps.rbs_aj_snprintf_atSF SEGS B LAWS pa_segs_low (FR_seg 0x10000 gotw) SEG_SNP_K gotw guard 0x10000 kImgEnd cr
      (SIGMA SS___interceptor_trampoline_snprintf) (SNP fx) ltac:(rewrite HKK, Hes; lia) ltac:(lia) Gw0 Gd0
      ltac:(unfold kImgEnd; lia) CRP
      W (ms_regs ms1) (ms_mem ms1) STK sp0 (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 mdv 0 d 200
      (lit SegModel.F_addr_line) (rbp_T1 rcs ln) (rsp1 sp0 - sp0) (Z_to_bv 64 (BASE + 18188))
      HJ R10 Q11 R12 ltac:(lia) ltac:(lia) ltac:(lia) Rsp Ro16 ltac:(lia) ltac:(rewrite HKK; lia) R3 R4 Q1
      (ret_ok_codeptr_v 18188 ltac:(lia) eq_refl) HDEST HWR HAM HRA HHV ltac:(lia) ltac:(rewrite HKK; lia) SSP1
      ltac:(lia) Gw1 ltac:(lia) Gd1 HFF ltac:(lia) ROM1 HFRM). }
  cbv beta. intros fx1 regs2 mem2 md3 Hfx (HJ2 & HP2 & Ha0 & HBY & HK2 & HPR2 & Hsame).
  (* after the call: the regions it keeps, the state at fx1, the fresh atoms 1300.. of its clobbered registers *)
  assert (Hfin : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly S2 W (ms_mem ms1) mdv 0 fpos (proj1 HJ) Hfin) as (HF4096 & HFceil & HFapp).
  pose proof (sep_block_frame SEGS B LAWS ly S2 W (ms_mem ms1) mdv bc mc 0 fpos (proj1 HJ) Hbc Hfin) as HSBF.
  change (fs_frame_bytes 0) with 64 in HFceil, HFapp, HSBF.
  unfold zdisjoint in HSBF. cbn [fst snd] in HSBF.
  assert (HF8 : 0 <= frame_addr ly 0 fpos / 8 /\ 8 * (frame_addr ly 0 fpos / 8) <= frame_addr ly 0 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (U1028 : bv_unsigned (ew Ev 1028) = frame_addr ly 0 fpos) by (rewrite E1028; apply unsigned_lit_small; lia).
  assert (U1041 : bv_unsigned (ew Ev 1041) = SB + frame_addr ly 0 fpos / 8)
    by (rewrite E1041; apply unsigned_lit_small; unfold SB; lia).
  jafter_call_keep_hi HS rbp_KS regs2 (mrestrict (w_H W) mem2) HP2 rbp_keepi HS2.
  match type of HS2 with ?A -> _ => assert (HQ : A); [|specialize (HS2 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    all: eapply region_kept_aview; [first [exact U1041 | exact U1028 | exact Usp | exact U10b] | | exact HPR2].
    all: intros a Ha; apply HK2;
      [ unfold SB in *; lia
      | rewrite HSN; intros Hq;
        first [ lia
              | exact (fshadow_not_app (frame_addr ly 0 fpos) 8 bc (req_size mc) a HF4096 ltac:(lia) Hbapp
                  ltac:(unfold SB in Ha; lia) ltac:(lia)) ]
      | rewrite HKK; unfold SB in *; lia ]. }
  rewrite <- restrict_mkst_fx in HS2.
  apply (st_ok_pi_restrict_xfx fx fx1) in HS2.
  set (Ev' := havoc Ev rbp_KS (map (getr regs2) CLOB)) in HS2.
  assert (HEI' : img_env VAL A_LIM Ev') by (unfold Ev'; apply img_env_havoc_hi; [exact HEI | unfold rbp_KS, A_LIM; lia]).
  assert (AG' : forall n, (n < 1300)%nat -> ew Ev' n = ew Ev n) by (intros n Hn; unfold Ev'; apply ew_havoc_old; exact Hn).
  assert (E1304 : ew Ev' 1304 = Z_to_bv 64 (Z.of_nat (length (rbp_T1 rcs ln)))).
  { unfold Ev'. change 1304%nat with (rbp_KS + 4)%nat.
    rewrite (ew_havoc_new Ev rbp_KS (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbn; lia).
    cbn [nth map CLOB]. exact Ha0. }
  assert (Usp' : bv_unsigned (ew Ev' 2) = sp0) by (rewrite AG' by lia; exact Usp).
  assert (U10b' : bv_unsigned (ew Ev' 10) = c) by (rewrite AG' by lia; exact U10b).
  (* 0x894cc: the `j` to RB_TEXT, a plain run at fx1 that writes nothing *)
  pose proof (SRr_run_to_pi_AJ (fx := fx1) B LAWS) as RUNTOP1.
  paj_run_to_sh RUNTOP1 HS2 HJ2 RB_TEXT.
  { lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc0 ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc0 fr0 lyx own) end.
    do 4 rbw_ro.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite Usp'; lia | cbn; lia | cbn; lia |].
    eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat c);
      [reflexivity | exact U10b'
      | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply HWB; unfold seg_spec.RC_REFUSED in *; lia |].
    apply awr_ok_nil. }
  try (set (mdj := with_vm_backing _ _ _) in *; clearbody mdj).
  rpp_unch HFr UN3 Usp' Usp' U10b' sp0 c Hs1. clear HF HFr HG.
  pose proof (st_ok_pi_facts_incl3 _ _ _ (f_atoms (ss_facts ss_pre)) [] (f_alias (ss_facts ss_pre)) HS2
    ltac:(rpp_in_tac) (fun x (Hx : In x []) => match Hx with end) ltac:(rpp_in_tac)) as HS3.
  clear HS2. rbp_to HS3 ss_txt.
  lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (msj := msx) in * end.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 176 <= a < sp0) ->
    ~ (c + seg_spec.RC_REFUSED <= a < c + seg_spec.RC_REFUSED + 4) -> rdW W (ms_mem msj) a = rdW W mem2 a).
  { intros a Ha N1 N2. apply UN3; [exact Ha | cbv beta; tauto]. }
  (* RB_TEXT: what RBP_TXT_stmt asks at the final memory, then TXT at fx1 *)
  lazymatch type of HS3 with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let i := eval vm_compute in (rbp_find (ss_mem ssx) 10%nat 13512 0) in
    let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) i r HS3 ltac:(vm_compute; reflexivity)) as HRcnt;
    cbn [ms_mem restrict] in HRcnt end.
  pose proof (rpp_region_aval4 SEGS Ev' (w_H W) _ 10 c _ _ _ _ _ 13516 (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) _
    HRcnt U10b' ltac:(first [left; reflexivity | right; left; reflexivity]) (eq_sym (Z_to_bv_bv_unsigned _ _))) as Vrf.
  assert (E36' : ew Ev' 36 = Z_to_bv 64 (rc_refused rcs)) by (rewrite AG' by lia; exact E36).
  assert (RFF : rd32 (rdW W (ms_mem msj)) (c + seg_spec.RC_REFUSED) (rc_refused rcs + 1)).
  { change seg_spec.RC_REFUSED with 13516. apply (rpp_rd32_mod _ _ _ _ Vrf).
    change (bv_unsigned (sv_denot Ev' (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1))))
      with (U Ev' (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1))).
    rewrite (rpp_inc_mod Ev' (rc_refused rcs) E36' (proj1 Hrf0) HREF1). symmetry. apply Z.mod_small. lia. }
  assert (SSPF : sa_ssp (rdW W (ms_mem msj)) gotw guard).
  { apply (rpp_ssp_keep (rdW W (ms_mem ms1)) _ gotw guard SSP1); intros i Hi;
      try (rewrite KF by (unfold kImgEnd in *; rpp_zl));
      (apply HK2; [ unfold kImgEnd in *; lia | rewrite HSN; unfold kImgEnd in *; rpp_zl | rewrite HKK; unfold kImgEnd in *; lia ]). }
  assert (KEEPF : forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
      ~ (seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) <= i <
         seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat (length (rbp_T1 rcs ln)) + 1) ->
      rdW W (ms_mem msj) (c + i) = rdW W mem (c + i)).
  { intros i Hi Hr Hs. try (rewrite KF by rpp_zl).
    rewrite HK2 by (first [rewrite HSN; rpp_zl | rewrite HKK; rpp_zl | rpp_zl]). apply KB1; assumption. }
  assert (ZSF : sa_zs (rdW W (ms_mem msj)) d (rbp_T1 rcs ln ++ [0])).
  { intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    try (rewrite KF by rpp_zl). rewrite (HBY (Z.of_nat i)) by (rewrite HSN; lia).
    rewrite Nat2Z.id, HSB. reflexivity. }
  assert (HFRM1 : sa_frm0 (fx := fx1)) by exact (fxrel_frm0 fx fx1 HFRM Hfx).
  assert (HCX1 : rb_cx (fx := fx1) B STK RLO RHI lit gotw guard ly S W regs mem md ch c line fp ln rcs f args)
    by exact (conj HPRE (conj HROD (conj H10 (conj Hc64 (conj H11 (conj Hl64 (conj H12 (conj Hfp64
      (conj (conj Hc0 (conj Hc16 (conj HRC (conj HHEAP (conj HADDR (conj HREF1 (conj Hln (conj Hlne (conj Hinf
        (conj Hck (conj Hfp0 (conj Hfpl (conj HLIT (conj HVA (conj HLOCS (conj HFRM1 (conj HSSP0 HLITS)))))))))))))))))
      (conj HROOM HEV)))))))))).
  assert (AGR' : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ev' n = getr regs r).
  { intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    rewrite AG' by lia. apply AGR. exact Hn. }
  lazymatch goal with |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
    refine (TXT fx1 ly S W regs mem md ch c line fp ln rcs f args msF mdF S2 fpos Ev' HCX1 HSTK HN8 HEI' HS3 HJ2
      Hfrs2 Eab HS2f AGR' _ _ _ _ _ _ _ E1304 SSPF KEEPF RFF ZSF) end;
    rewrite AG' by lia; assumption.
Qed.
End e.
End f.
End d.
