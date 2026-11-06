(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 598 of its 645 lines of code are new or changed and 406 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): stretch B of segment A9 of reac_segconf_parse_file's walk,
   K2 0x87fe4 -> K3 0x87ff4 (lib/A/Prog/pf_a9_d.v SA9_B). Part of segment A9's proof, by the G3 walk owner, 2026-10-30.

   proves no function (kind: segment lemma of reac_segconf_parse_file's image-A walk, one stretch of segment A9;
   the whole function's rule-24 line, its pasted released-proof index output and the G3 walk owner's CONFIRM of
   2026-10-30T15:42:08Z are in the unit's internal record, commit dfb49d6ad789,
   path records/segp/g3-lookup.md, reuse verdict none:
   written new)

   THE CODE (the excerpt reac_segconf_parse_file.fuzz_segconf.asan.s in records/segp/dis/ at that commit;
   reac_segconf.c:221-222):
     0x87fe4 addi a0, s8, 1     a0 = eq + 1 (s8 = eq = lp + ei)
     0x87fe8 jal  trim          trim(eq + 1): the value (listing slot PCall SS_trim, return BASE + 0x32b8)
     0x87fec mv   s9, a0        s9 = vp0 = eq + 1 + trim_lead rest
     0x87ff0 jal  strlen        the strlen trampoline, a0 = vp0 (return BASE + 0x32c0 = BASE + A9_K3)
   No branch, no inline check. 4 instructions walked (the two runs are the executor's, plain, no region: the stretch
   reads and writes no memory itself).

   THE TRANSPORT. Both calls keep every byte outside a window below s1 and one written set E inside buf: trim
   writes its stack window [s1 - STK_trim, s1) and the NUL at trim_end_addr (trim_c.v sa_kept); strlen writes
   its scratch window [s1 - ESTACK, s1) (art_post, E = False). b2_core_move rebuilds a9_core across either call
   from segment A5's pf_a5_k.v a5_move0 (no Section hypothesis), a5_keep_fsh / a5_keep_st / a5_keep_slot; the
   window bytes stay visible by the caller's journal, the E bytes by the callee's post (b2_vis). The same lemma
   serves the strlen return, so neither A7's a7_keep_art nor A6's a6_keeps_low is used. The key survives trim's
   NUL by INV_K2's kp + |key| <= lp + ei (b2_keep_inbuf); the value is trim's answer (b2_trim_str, from trim_c.v's
   post bytes and pfA_facts.v L_trim_holds). trim is stepped by PaNoChain.v cl_callS_wide (its footprint, the
   NUL, lies in parse_file's own class-5 frame: awr_byte's own-frame arm), the chain from pf_a5_k.v a5_chain;
   strlen by PaArt.v aj_art_at.

   SECTION HYPOTHESES: TL (PALib, for aj_art_at's errno cell), SIGP (trim's call target), ASTRLEN, TRIM. The
   brief's list also had OBJ and VRO; neither is needed (no auipc pair in the stretch; a5_move0 needs no VRO), so
   neither is declared. No SSPX, no ROMV: sa_ssp and arodata_okP ride on a5_move0, rt_rom_view is pf_a5_k.v
   a5_rom.

   COPIED, with attribution (READ ONLY donors of segment A7's proof, at the commits named below, renamed
   a7_ -> b2_ and restated over pf_base / a9_core in place of A7's a7_st):
     lib/A/Prog/pf_a7_d.v (980fbe9c6015): a7_sh_at -> b2_sh_at, a7_addr_buf -> b2_addr_buf (a7_sh_some inlined);
     lib/A/Prog/pf_a7_s.v (980fbe9c6015): a7_trim_site_ok -> trim_site_ok_87fe8 (a7_fframe_buf inlined);
     lib/A/Prog/pf_a7_r.v (ebe0b30cca65): a7_str_some -> b2_str_some, a7_astr_of_sa -> b2_astr_of_sa,
       a7_read_ok_of_addr -> b2_read_ok_of_addr, a7_strlen_pre_88338 -> b2_strlen_pre (a7_ecall_pre_buf,
       a7_read_ok_buf, a7_frame_some inlined). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import trim_c refuse_c reac_segconf_parse_file_c
  SegInstA pf_pieces pf_a5_d pf_a5_k pf_a9_d pf_a9_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= pure helpers ======================= *)
(* a reader of the ASan view depends on the address only modulo 2 ^ 64 *)
Lemma b2_aview_mod : forall segs H mem a, aview segs H mem a = aview segs H mem (a mod 2 ^ 64).
Proof.
intros segs H mem a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* every byte of a C string and its NUL is mapped (pf_a7_r.v a7_str_some) *)
Lemma b2_str_some : forall (rd : reader) p s a, sa_str rd p s -> p <= a <= p + Z.of_nat (length s) ->
  rd a <> None.
Proof.
intros rd p s a [[Hz _] _] Ha.
assert (Hi : (Z.to_nat (a - p) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
pose proof (Hz _ Hi) as E. rewrite Z2Nat.id in E by lia.
replace (p + (a - p)) with a in E by lia. rewrite E. discriminate.
Qed.

(* the bytes after a NUL up to its word's end are within the next word's end of a later NUL *)
Lemma b2_tail_mono : forall e e' x, e <= e' -> e < x < e - e mod 8 + 8 -> x <= e' \/ e' < x < e' - e' mod 8 + 8.
Proof.
intros e e' x H Hx.
pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
pose proof (Z.div_mod e' 8 ltac:(lia)). pose proof (Z.mod_pos_bound e' 8 ltac:(lia)).
assert (e / 8 <= e' / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the C string s at q of an ASan reader, as the runtime rows state a string (pf_a7_r.v a7_astr_of_sa) *)
Lemma b2_astr_of_sa : forall (W : world SEGS) mem q l,
  sa_str (rdW W mem) q l ->
  astr_at SEGS W mem q (seg_spec.zb l) /\ astr_atR (rdW W mem) q (seg_spec.zb l) /\
  astr_len (seg_spec.zb l) = Z.of_nat (length l) /\ seg_spec.zs (seg_spec.zb l) = l /\
  atail_vis SEGS W mem (q + astr_len (seg_spec.zb l)).
Proof.
intros W mem q l [Hz Ht].
destruct (sa_strz_bytes SEGS (w_H W) mem q l Hz) as (Hb & Hn & Hzs).
assert (HR : astr_atR (rdW W mem) q (seg_spec.zb l)) by (split; [exact Hb | exact Hn]).
assert (HL : astr_len (seg_spec.zb l) = Z.of_nat (length l))
  by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
split; [apply astr_atR_view; exact HR|].
split; [exact HR|]. split; [exact HL|]. split; [exact Hzs|].
rewrite HL. exact Ht.
Qed.

(* a range the walk's memory holds, as aread_ok (pf_a7_r.v a7_read_ok_of_addr) *)
Lemma b2_read_ok_of_addr : forall (W : world SEGS) regs mem stk q n,
  sa_addr (rdW W mem) q n -> 0 <= n < 2 ^ 32 ->
  (forall a, q <= a < q + n -> rdW W mem a <> None) -> q + n <= spZ regs - stk ->
  aread_ok SEGS stk W regs mem q n.
Proof.
intros W regs mem stk q n (A0 & A1 & A2 & A3 & A4) Hn Hm Hw.
split; [exact A0|]. split; [exact A1|]. split; [exact Hn|].
split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
intros a Ha. split; [exact (Hm a Ha)|]. unfold ascratch_stk. lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis TRIM : forall fx0 : YK11.FPState,
  trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.

(* ======================= the cut's geometry and buf ======================= *)
Lemma b2_geo : forall n x lyc Sc Wc rX memc mdc, a9_core B n x lyc Sc Wc rX memc mdc ->
  AR SEGS B lyc Sc Wc memc mdc /\ lyc = p_ly (y_v x) /\ In (5, y_pos x) (frames Sc) /\ a5_G (y_v x) (y_pos x) /\
  (forall a, pf_F (y_v x) (y_pos x) <= a < pf_F (y_v x) (y_pos x) + 2048 -> rdW Wc memc a <> None).
Proof.
intros n x lyc Sc Wc rX memc mdc (HB & _).
destruct (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HP & _).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hin|]. split; [exact G|].
intros a Ha. apply (aview_some_of_apresent SEGS). exact (HP a Ha).
Qed.

(* buf's shadow cell for an address of buf (pf_a7_d.v a7_sh_at) *)
Lemma b2_sh_at : forall (rd : reader) v pos x, a5_G v pos -> pf_fsh rd (pf_SH v pos) PF_SC_LINE ->
  pf_F v pos + PF_O_BUF <= x < pf_F v pos + PF_O_BUF + 512 ->
  rd (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
intros rd v pos x G HF Hx.
pose proof G as (_ & _ & _ & _ & _ & G6 & G7 & G8 & _ & G10 & _).
unfold PF_O_BUF in Hx.
assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
replace x with (pf_F v pos + (x - pf_F v pos)) by lia.
rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8).
change (shadow_of_addr SHADOW_OFF (pf_F v pos)) with (pf_SH v pos).
rewrite (HF ((x - pf_F v pos) / 8)).
- f_equal. apply a9_shb_buf.
  split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
- split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* a range of buf is addressable, with its shadow mapped (pf_a7_d.v a7_addr_buf) *)
Lemma b2_addr_buf : forall (rd : reader) v pos q n, a5_G v pos -> pf_fsh rd (pf_SH v pos) PF_SC_LINE ->
  pf_F v pos + PF_O_BUF <= q -> 0 <= n -> q + n <= pf_F v pos + PF_O_BUF + 512 ->
  sa_addr rd q n.
Proof.
intros rd v pos q n G HF Hq Hn Hqn.
pose proof G as (_ & _ & _ & _ & _ & G6 & G7 & G8 & G9 & G10 & _).
pose proof alloc_ceiling_lt as HC.
unfold PF_O_BUF in Hq, Hqn.
assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
split; [lia|]. split; [lia|].
split.
{ apply amem_range_high; [lia| |lia].
  destruct G9 as [_ [Hlo | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
  [left; lia | right; lia]. }
split.
- intros y Hy. exists 0. split; [|left; reflexivity].
  apply (b2_sh_at rd v pos y G HF). unfold PF_O_BUF. lia.
- intros Hn0 s Hs.
  assert (E1 : shadow_addr q = pf_SH v pos + (q - pf_F v pos) / 8).
  { unfold shadow_addr. replace q with (pf_F v pos + (q - pf_F v pos)) at 1 by lia.
    change (SHADOW_OFF + (pf_F v pos + (q - pf_F v pos)) / 8)
      with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q - pf_F v pos))).
    rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q - pf_F v pos) HF8). reflexivity. }
  assert (E2 : shadow_addr (q + n - 1) = pf_SH v pos + (q + n - 1 - pf_F v pos) / 8).
  { unfold shadow_addr. replace (q + n - 1) with (pf_F v pos + (q + n - 1 - pf_F v pos)) at 1 by lia.
    change (SHADOW_OFF + (pf_F v pos + (q + n - 1 - pf_F v pos)) / 8)
      with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q + n - 1 - pf_F v pos))).
    rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q + n - 1 - pf_F v pos) HF8). reflexivity. }
  assert (B1 : 8 <= (q - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (B2 : (q + n - 1 - pf_F v pos) / 8 < 72) by (apply Z.div_lt_upper_bound; lia).
  rewrite E1, E2 in Hs.
  pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
  rewrite (HF (s - pf_SH v pos) ltac:(lia)). discriminate.
Qed.

(* ======================= the transport across a step ======================= *)
(* the reader after a step that keeps every byte off [lo, s1) and off E (E inside buf), whose new journal
   keeps parse_file's window present and whose E bytes are mapped: every mapped byte stays mapped *)
Lemma b2_vis : forall v pos lyc Sc' (Wc : world SEGS) memc (Wc' : world SEGS) memc' mdc' (E : Z -> Prop) lo,
  a5_G v pos ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' Wc' memc' mdc' 0 ->
  pf_sp0 v - STK_reac_segconf_parse_file <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < pf_s1 v) -> ~ E a -> rdW Wc' memc' a = rdW Wc memc a) ->
  (forall a, E a \/ ~ E a) -> (forall a, E a -> rdW Wc' memc' a <> None) ->
  forall a, rdW Wc memc a <> None -> rdW Wc' memc' a <> None.
Proof.
intros v pos lyc Sc' Wc memc Wc' memc' mdc' E lo G HJ Hlo HK HED HEV a Ha.
pose proof G as (G1 & G2 & G3 & G4 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
rewrite b2_aview_mod in Ha |- *.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as M.
set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' lo) as [H1 | H1]; [|destruct (Z_lt_le_dec a' (pf_s1 v)) as [H2 | H2]].
- destruct (HED a') as [He | He]; [exact (HEV a' He)|].
  rewrite HK; [exact Ha | exact M | lia | exact He].
- apply (aview_some_of_apresent SEGS). apply Hpres. lia.
- destruct (HED a') as [He | He]; [exact (HEV a' He)|].
  rewrite HK; [exact Ha | exact M | lia | exact He].
Qed.

(* a9_core after such a step (pf_a5_k.v a5_move0 for pf_base, a5_keep_fsh / a5_keep_st / a5_keep_slot) *)
Lemma b2_core_move : forall n x lyc Sc Wc rX memc mdc Sc' Wc' rX' memc' mdc' (E : Z -> Prop) lo,
  a9_core B n x lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc' Wc' memc' mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  pf_sp0 (y_v x) - STK_reac_segconf_parse_file <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < pf_s1 (y_v x)) -> ~ E a -> rdW Wc' memc' a = rdW Wc memc a) ->
  (forall a, E a -> a9_buf x <= a < a9_buf x + 512) ->
  (forall a, E a \/ ~ E a) -> (forall a, E a -> rdW Wc' memc' a <> None) ->
  pf_rg rX' (a5_FI B (y_v x)) ->
  a9_core B n x lyc Sc' Wc' rX' memc' mdc'.
Proof.
intros n x lyc Sc Wc rX memc mdc Sc' Wc' rX' memc' mdc' E lo HC HJ' HSf HPerm Hlo HK HE HED HEV HRG.
pose proof (b2_geo n x lyc Sc Wc rX memc mdc HC) as (HAR & Hly & Hin & G & _).
destruct HC as (HB & HM & HS & HL & HLT & HD0 & HDL).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _).
assert (HV : forall a, rdW Wc memc a <> None -> rdW Wc' memc' a <> None)
  by exact (b2_vis (y_v x) (y_pos x) lyc Sc' Wc memc Wc' memc' mdc' E lo G HJ' Hlo HK HED HEV).
assert (KW : forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx (y_v x) (y_pos x) sl shw a -> rdW Wc' memc' a = rdW Wc memc a).
{ intros sl shw a Ha Hw. apply HK; [exact Ha | |].
  - intros Hw'. apply Hw. left. lia.
  - intros He. apply Hw. right. right. left. pose proof (HE a He) as Hb. unfold a9_buf in Hb. unfold a5_buf. lia. }
split; [|split; [exact HM | split; [|split; [|split; [exact HLT | split; [exact HD0 | exact HDL]]]]]].
- apply (a5_move0 B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE Sc' Wc' rX' memc' mdc' PF_SC_LINE HB HJ' HSf
    HPerm (KW true true) HV HRG).
  destruct HB as (_ & _ & _ & _ & HFSH).
  exact (a5_keep_fsh (y_v x) (y_pos x) _ _ true PF_SC_LINE G (KW true false) HFSH).
- destruct HB as (_ & _ & HOBJ & _).
  pose proof HOBJ as (_ & _ & _ & _ & Hc & _).
  eapply (a5_keep_st B (y_v x) (y_pos x) lyc Sc Wc memc mdc Wc' memc');
    first [exact G | exact HAR | exact Hin | exact Hly | exact (KW true true) | exact HV | exact Hc | exact HS].
- exact (a5_keep_slot (y_v x) (y_pos x) _ _ true _ G (KW false true) HL).
Qed.

(* a C string of buf after such a step, when E misses its bytes and its NUL *)
Lemma b2_keep_inbuf : forall x (Wc : world SEGS) memc (Wc' : world SEGS) memc' (E : Z -> Prop) lo q s,
  a5_G (y_v x) (y_pos x) ->
  pf_sp0 (y_v x) - STK_reac_segconf_parse_file <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < pf_s1 (y_v x)) -> ~ E a -> rdW Wc' memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc' memc' a <> None) ->
  (forall a, E a -> ~ (q <= a <= q + Z.of_nat (length s))) ->
  a9_inbuf (rdW Wc memc) x q s -> a9_inbuf (rdW Wc' memc') x q s.
Proof.
intros x Wc memc Wc' memc' E lo q s G Hlo HK HV HE (((Hz & Hn) & Ht) & Hb1 & Hb2).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
unfold a9_buf, PF_O_BUF in Hb1, Hb2.
split; [|split; [exact Hb1 | exact Hb2]].
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite HK; [exact (Hz i Hi) | lia | lia |].
  intros He. apply (HE _ He). lia.
- intros y Hy. apply HV. exact (Ht y Hy).
Qed.

(* trim's answer at eq + 1: the C string at eq + 1 + trim_lead rest is r_trim rest = a9_v0 x ei
   (trim_c.v's post bytes and pfA_facts.v L_trim_holds) *)
Lemma b2_trim_str : forall x ei (Wc : world SEGS) memc (W2 : world SEGS) mem2 p,
  p = y_lp x + Z.of_nat ei + 1 ->
  a9_inbuf (rdW Wc memc) x p (skipn (S ei) (a9_line x)) ->
  sa_bytes (rdW W2 mem2) p
    (seg_spec.zb (firstn (seg_spec.trim_lead (skipn (S ei) (a9_line x)) +
                          length (r_trim (skipn (S ei) (a9_line x)))) (skipn (S ei) (a9_line x))) ++
     [seg_spec.ZERO]) ->
  (forall a, rdW Wc memc a <> None -> rdW W2 mem2 a <> None) ->
  a9_inbuf (rdW W2 mem2) x (p + Z.of_nat (seg_spec.trim_lead (skipn (S ei) (a9_line x)))) (a9_v0 x ei).
Proof.
intros x ei Wc memc W2 mem2 p Hp (((Hz & Hn) & Ht) & Hb1 & Hb2) HBY HV.
unfold a9_v0.
set (r := skipn (S ei) (a9_line x)) in *.
pose proof (L_trim_holds r Hn) as (L1 & L2 & L3).
set (ld := seg_spec.trim_lead r) in *. set (rt := r_trim r) in *.
assert (HR : forall j, (j < length r)%nat -> 0 <= nth j r 0 < 256).
{ intros j Hj. assert (Hj' : (j < length (r ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (Hz j Hj') as E. rewrite app_nth1 in E by exact Hj. exact (sa_aview_rng _ _ _ _ _ E). }
assert (HLB : length (seg_spec.zb (firstn (ld + length rt) r)) = (ld + length rt)%nat)
  by (unfold seg_spec.zb; rewrite length_map, length_firstn; lia).
assert (HNTH : forall i, (i < length rt)%nat -> nth i rt 0 = nth (ld + i) r 0).
{ intros i Hi. rewrite L2, nth_firstn.
  replace ((i <? length rt)%nat) with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite nth_skipn; try reflexivity; f_equal; lia. }
split; [|split].
- split; [split; [|exact L3]|].
  + intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    replace (p + Z.of_nat ld + Z.of_nat i) with (p + Z.of_nat (ld + i)) by lia.
    rewrite (HBY (ld + i)%nat) by (rewrite length_app, HLB; cbn [length]; lia). f_equal.
    destruct (Nat.lt_ge_cases i (length rt)) as [Hl | Hg].
    * rewrite app_nth1 by (rewrite HLB; lia). unfold seg_spec.zb, ZB0.
      rewrite (map_nth (Z_to_bv 8) (firstn (ld + length rt) r) 0 (ld + i)).
      rewrite nth_firstn. replace ((ld + i <? ld + length rt)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite app_nth1 by exact Hl. rewrite HNTH by exact Hl.
      rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. apply HR. lia.
    * assert (i = length rt) as -> by lia.
      rewrite app_nth2 by (rewrite HLB; lia). rewrite HLB, Nat.sub_diag. cbn [nth].
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  + intros y Hy. apply HV.
    replace (p + Z.of_nat ld + Z.of_nat (length rt)) with (p + Z.of_nat (ld + length rt)) in Hy by lia.
    destruct (b2_tail_mono (p + Z.of_nat (ld + length rt)) (p + Z.of_nat (length r)) y ltac:(lia) Hy) as [Hy' | Hy'].
    * exact (b2_str_some _ p r y (conj (conj Hz Hn) Ht) ltac:(lia)).
    * exact (Ht y Hy').
- unfold a9_buf in *. lia.
- unfold a9_buf in *. lia.
Qed.

(* ======================= the two call sites ======================= *)
(* the register list of a cut, carried to a register file that agrees on every register of the list *)
Lemma b2_rg_same : forall (r1 r2 : bvmap 5 word) L,
  Forall (fun rv => getr r2 (Z_to_bv 5 (fst rv)) = getr r1 (Z_to_bv 5 (fst rv))) L -> pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 L HE H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HE rv Hin). exact (H rv Hin).
Qed.

(* the facts of a cut's frame part every call site reads *)
Lemma b2_site_facts : forall n x lyc Sc Wc rX memc mdc, a9_core B n x lyc Sc Wc rX memc mdc ->
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\ st_nev Sc <= EV_MAX /\
  pf_fsh (rdW Wc memc) (pf_SH (y_v x) (y_pos x)) PF_SC_LINE /\
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc mdc 0.
Proof.
intros n x lyc Sc Wc rX memc mdc ((HCX & HFI & HOBJ & _ & HFSH) & _).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV).
pose proof HFI as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HOBJ as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
unfold EV_reac_segconf_parse_file in HEV.
split; [exact HROD|]. split; [lia|]. split; [exact HFSH | exact HJ].
Qed.

(* VERIFY rule 1j-bis, edge reac_segconf_parse_file -> trim at 0x87fe8: a cut of A9 whose memory holds the rest of
   the line at p = eq + 1 (the C string s = skipn (S ei) line in buf) and a0 = p gives every premise of
   trim_contract besides afn_pre (which cl_callS_wide builds from the journal). From pf_a7_s.v a7_trim_site_ok. *)
Lemma trim_site_ok_87fe8 : forall n x ei lyc Sc Wc rX memc mdc (regs : bvmap 5 word),
  a9_core B n x lyc Sc Wc rX memc mdc ->
  a9_inbuf (rdW Wc memc) x (y_lp x + Z.of_nat ei + 1) (skipn (S ei) (a9_line x)) ->
  getr regs 10 = w64 (y_lp x + Z.of_nat ei + 1) ->
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  getr regs 10 = w64 (y_lp x + Z.of_nat ei + 1) /\ 0 <= y_lp x + Z.of_nat ei + 1 < 2 ^ 64 /\
  trim_pre SEGS B lyc Sc Wc memc regs (y_lp x + Z.of_nat ei + 1) (skipn (S ei) (a9_line x)) /\
  st_nev Sc + EV_trim <= EV_MAX.
Proof.
intros n x ei lyc Sc Wc rX memc mdc regs HC HS R10.
pose proof (b2_geo n x lyc Sc Wc rX memc mdc HC) as (HAR & Hly & Hin & G & _).
pose proof (b2_site_facts n x lyc Sc Wc rX memc mdc HC) as (HROD & HEV & HFSH & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof alloc_ceiling_lt as HCL.
destruct HS as (HSTR & Hb1 & Hb2). unfold a9_buf, PF_O_BUF in Hb1, Hb2.
set (p := y_lp x + Z.of_nat ei + 1) in *. set (s := skipn (S ei) (a9_line x)) in *.
pose proof (b2_addr_buf (rdW Wc memc) (y_v x) (y_pos x) p (Z.of_nat (length s) + 1) G HFSH
  ltac:(unfold PF_O_BUF; lia) ltac:(lia) ltac:(unfold PF_O_BUF; lia)) as HA.
pose proof HA as (_ & _ & _ & HRA & _).
split; [exact HROD|]. split; [exact R10|]. split; [lia|].
split; [|unfold EV_trim; lia].
split; [lia|]. split; [exact HSTR|]. split; [exact HA|].
split; [|lia].
left. split; [|exact HRA].
exists 5, (y_pos x). split; [exact Hin|]. split; [lia|].
rewrite Hly. change (frame_addr (p_ly (y_v x)) 5 (y_pos x)) with (pf_F (y_v x) (y_pos x)).
change (fs_frame_bytes 5) with 2048. lia.
Qed.

(* the strlen call at 0x87ff0: RtString.astrlen_realizes's premises in its order, for a C string l at q in buf,
   at a call made at s1 (pf_a7_r.v a7_strlen_pre_88338, over a9_core) *)
Lemma b2_strlen_pre : forall n x lyc Sc Wc rX memc mdc (regsc : bvmap 5 word) q l,
  a9_core B n x lyc Sc Wc rX memc mdc ->
  spZ regsc = pf_s1 (y_v x) -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 q -> a9_inbuf (rdW Wc memc) x q l ->
  ecall_pre_stk SEGS B ESTACK lyc Sc Wc regsc memc mdc /\
  getr regsc 10 = w64 q /\ 0 < q /\
  astr_at SEGS Wc memc q (seg_spec.zb l) /\
  aread_ok SEGS ESTACK Wc regsc memc q (astr_len (seg_spec.zb l) + 1) /\
  atail_vis SEGS Wc memc (q + astr_len (seg_spec.zb l)) /\
  rt_rom_view SEGS B Wc memc.
Proof.
intros n x lyc Sc Wc rX memc mdc regsc q l HC Hsp Hra Hgp Htp H10 (HS & Hb1 & Hb2).
pose proof (b2_geo n x lyc Sc Wc rX memc mdc HC) as (HAR & Hly & Hin & G & HFV).
pose proof (b2_site_facts n x lyc Sc Wc rX memc mdc HC) as (_ & _ & HFSH & HJ).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof alloc_ceiling_lt as HCL.
unfold a9_buf, PF_O_BUF in Hb1, Hb2.
destruct (b2_astr_of_sa Wc memc q l HS) as (HA & _ & HLn & _ & HT).
assert (Ho16 : (pf_s1 (y_v x) - pf_sp0 (y_v x)) mod 16 = 0).
{ pose proof (Z.div_mod (pf_sp0 (y_v x)) 16 ltac:(lia)) as D0.
  pose proof (Z.div_mod (pf_s1 (y_v x)) 32 ltac:(lia)) as D1.
  pose proof (Z.div_mod (pf_s1 (y_v x) - pf_sp0 (y_v x)) 16 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_s1 (y_v x) - pf_sp0 (y_v x)) 16 ltac:(lia)) as M2. lia. }
split.
{ apply (PaArt.ecall_pre_stk_at SEGS B ESTACK STK_reac_segconf_parse_file (pf_sp0 (y_v x))
    (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x))
    [(5, y_pos x)] lyc Sc Wc memc mdc 0 regsc (pf_s1 (y_v x) - pf_sp0 (y_v x)) HJ);
    [lia | exact Ho16 | lia | unfold ESTACK; lia | unfold ESTACK; lia | exact Hra | exact Hgp | exact Htp]. }
split; [exact H10|]. split; [lia|]. split; [exact HA|].
split.
{ rewrite HLn. apply b2_read_ok_of_addr.
  - apply (b2_addr_buf (rdW Wc memc) (y_v x) (y_pos x) q _ G HFSH); unfold PF_O_BUF; lia.
  - lia.
  - intros a Ha. apply HFV. lia.
  - rewrite Hsp. unfold ESTACK. lia. }
split; [exact HT|].
destruct HC as (HB & _). exact (a5_rom B _ _ _ _ _ _ _ _ _ HB).
Qed.

(* a9_core with the registers and the model changed, the memory kept (a run that writes nothing) *)
Lemma b2_core_regs : forall n x lyc Sc Wc rX memc mdc (rX' : bvmap 5 word) mdc',
  a9_core B n x lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc mdc' 0 ->
  pf_rg rX' (a5_FI B (y_v x)) ->
  a9_core B n x lyc Sc Wc rX' memc mdc'.
Proof.
intros n x lyc Sc Wc rX memc mdc rX' mdc'
  ((HCX & (_ & HLY & HFS & HPERM & HSV & HFL & HFRM & _) & HOBJ & HSL & HFSH) & REST) HJ HRG.
split; [|exact REST].
split; [exact HCX|]. split; [|exact (conj HOBJ (conj HSL HFSH))].
exact (conj HJ (conj HLY (conj HFS (conj HPERM (conj HSV (conj HFL (conj HFRM HRG))))))).
Qed.

(* a register list carried to a register file that agrees on the registers ks it names *)
Lemma b2_rg_kept : forall (r1 r2 : bvmap 5 word) (ks : list Z) L,
  (forall r, In r (map (Z_to_bv 5) ks) -> getr r2 r = getr r1 r) ->
  Forall (fun rv => In (fst rv) ks) L -> pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 ks L HK HL H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HK (Z_to_bv 5 (fst rv)) (in_map _ _ _ (HL rv Hin))). exact (H rv Hin).
Qed.

(* the registers stretch B keeps from K2 to K3: pf_fi's, A9_RC's, s8, s4, s7 *)
Definition B2_KS : list Z := [2; 3; 4; 8; 9; 22; 18; 19; 27; 21; 26; 24; 20; 23].
Lemma b2_ks_fi : forall v, Forall (fun rv => In (fst rv) B2_KS) (a5_FI B v).
Proof.
intros v. unfold a5_FI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst];
  apply In_of_existsb; reflexivity.
Qed.
Lemma b2_ks_rc : forall x ei kp, Forall (fun rv => In (fst rv) B2_KS)
  (A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x); (23, kp)]).
Proof.
intros x ei kp. unfold A9_RC, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst];
  apply In_of_existsb; reflexivity.
Qed.
Lemma b2_cs_rc : forall x ei kp, Forall (fun rv => acallee_saved (fst rv))
  (A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x); (23, kp)]).
Proof.
intros x ei kp. unfold A9_RC, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst];
  unfold acallee_saved; lia.
Qed.

(** ** Stretch B: from K3, the walk reaches A9's goal from K2 *)
Lemma a9_sB : SA9_B B.
Proof.
unfold SA9_B, from_K2, a9_from.
intros n HK3 x ei kp lyc Sc Wc rX memc mdc HI.
destruct HI as (HC & HCH & HKEY & HKLE & HREST & HRG).
pose proof (b2_geo n x lyc Sc Wc rX memc mdc HC) as (HAR & Hly & Hin & G & HFV).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (b2_site_facts n x lyc Sc Wc rX memc mdc HC) as (HROD & HEVc & HFSH & HJ).
pose proof HC as (HB & HMID & HST & HSL0 & HLT & HD0 & HDL).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
destruct (a5_chain B _ _ _ _ _ _ _ _ _ HB) as [ch1 HCH1].
pose proof STK_values as (STR & _ & _ & SPF & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof alloc_ceiling_lt as HCL.
assert (Ho16 : (pf_s1 (y_v x) - pf_sp0 (y_v x)) mod 16 = 0).
{ pose proof (Z.div_mod (pf_sp0 (y_v x)) 16 ltac:(lia)) as D0.
  pose proof (Z.div_mod (pf_s1 (y_v x)) 32 ltac:(lia)) as D1.
  pose proof (Z.div_mod (pf_s1 (y_v x) - pf_sp0 (y_v x)) 16 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_s1 (y_v x) - pf_sp0 (y_v x)) 16 ltac:(lia)) as M2. lia. }
(* the line's rest at p = eq + 1 and the NUL trim stores *)
set (p := y_lp x + Z.of_nat ei + 1) in *.
assert (Hp : p = y_lp x + Z.of_nat ei + 1) by reflexivity.
set (s := skipn (S ei) (a9_line x)) in *.
pose proof HREST as (((_ & HNs) & _) & Hrb1 & Hrb2). unfold a9_buf, PF_O_BUF in Hrb1, Hrb2.
pose proof (L_trim_holds s HNs) as (L1 & _ & _).
assert (HTE : p <= trim_end_addr p s <= p + Z.of_nat (length s)) by (unfold trim_end_addr; lia).
pose proof HKEY as (_ & Hkb1 & Hkb2). unfold a9_buf, PF_O_BUF in Hkb1, Hkb2.
(* the registers of the cut *)
assert (R24 : getr rX 24 = w64 (y_lp x + Z.of_nat ei))
  by (exact (a5_rg_get rX _ 24 _ HRG ltac:(apply in_or_app; right; left; reflexivity))).
(* the seed at K2: every register its own atom, no region *)
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (mkSS A9_K2 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + A9_K2)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
    [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]]. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (HA0 : env_agree 32 (Ereg rX []) (Eimg (Ereg rX [])))
  by (split; [intros k Hk; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg rX [])) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
revert HS HEI HA0 EE. generalize (Eimg (Ereg rX [])) as E. intros E HS HEI HA0 EE.
change (cfg_at SEGS (BASE + A9_K2) rX memc mdc)
  with (mkCfg (mkst rX (Z_to_bv 64 (BASE + A9_K2)) memc (seg_rom SEGS)) mdc).
(* 0x87fe4 addi a0, s8, 1; 0x87fe8 jal trim *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ first [apply awr_ok_nil | cbn; apply awr_ok_nil]. }
assert (Hmem : ms_mem ms = memc).
{ apply functional_extensionality. intros y. unfold frame_of in HF. rewrite HF; [reflexivity|].
  intros (r & Hr & _). cbn in Hr. destruct Hr. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
pmkst HS. rewrite Hmem in HJ |- *.
clear HF HFr HG.
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX [] HS HA0 ltac:(vm_compute; reflexivity)) as HPR.
assert (C2 : getr (ms_regs ms) 2 = w64 (pf_s1 (y_v x))).
{ transitivity (getr rX 2); [exact (HPR 2 ltac:(unfold acallee_saved; lia))|].
  exact (a5_rg_get rX _ 2 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
assert (C3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ transitivity (getr rX 3); [exact (HPR 3 ltac:(unfold acallee_saved; lia))|].
  exact (a5_rg_get rX _ 3 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
assert (C4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ transitivity (getr rX 4); [exact (HPR 4 ltac:(unfold acallee_saved; lia))|].
  exact (a5_rg_get rX _ 4 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
assert (C8 : getr (ms_regs ms) 8 = w64 (pf_sp0 (y_v x))).
{ transitivity (getr rX 8); [exact (HPR 8 ltac:(unfold acallee_saved; lia))|].
  exact (a5_rg_get rX _ 8 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
assert (Csp : spZ (ms_regs ms) = pf_s1 (y_v x)).
{ unfold spZ. rewrite C2. unfold w64. apply unsigned_lit_small. lia. }
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
assert (C1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 0x32b8)).
{ rewrite Q1. reflexivity. }
assert (C10 : getr (ms_regs ms) 10 = w64 p).
{ rewrite Q10. rewrite (EE 24%nat 24%bv eq_refl), R24. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
(* the cut at the call: the same memory, the run's journal, the callee-saved registers *)
assert (HCc : a9_core B n x lyc Sc Wc (ms_regs ms) memc mdq).
{ apply (b2_core_regs n x lyc Sc Wc rX memc mdc (ms_regs ms) mdq HC HJ).
  exact (a5_rg_pres rX (ms_regs ms) _ HPR (a5_FI_cs B _) HFI). }
(* VERIFY rule 1j-bis at 0x87fe8: trim_contract's premises besides afn_pre *)
pose proof (trim_site_ok_87fe8 n x ei lyc Sc Wc (ms_regs ms) memc mdq (ms_regs ms) HCc HREST C10)
  as (ROD & _ & Hp64 & TPRE & TEV).
rewrite (SIGP SS_trim ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_trim) with AF_trim by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc (ms_regs ms) memc _ STK_reac_segconf_parse_file (pf_sp0 (y_v x))
    (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x))
    [(5, y_pos x)] lyc Sc mdq 0 STK_trim [(trim_end_addr p s, trim_end_addr p s + 1)] EV_trim
    (pf_s1 (y_v x) - pf_sp0 (y_v x)) (Z_to_bv 64 (BASE + 0x32b8)) ch1
    (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (p + Z.of_nat (seg_spec.trim_lead s)) /\
       sa_bytes (aview SEGS (w_H W') mem') p
         (seg_spec.zb (firstn (seg_spec.trim_lead s + length (SegModel.r_trim s)) s) ++ [seg_spec.ZERO]) /\
       sa_kept SEGS Wc memc W' mem' (ms_regs ms) STK_trim (fun a => a = trim_end_addr p s) /\
       sa_noalloc B lyc Sc ly' S') HJ).
  - rewrite Csp. lia.
  - exact Ho16.
  - lia.
  - rewrite STR. lia.
  - rewrite STR, SPF. lia.
  - exact C3.
  - exact C4.
  - exact C1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (pf_sp0 (y_v x) + (pf_s1 (y_v x) - pf_sp0 (y_v x))) with (pf_s1 (y_v x)) by lia.
    unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH1.
  - intros HPRE1. eapply SRr_mono.
    { exact (TRIM fx lyc Sc Wc (ms_regs ms) memc mdq ch1 p s HPRE1 ROD C10 Hp64 TPRE TEV). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
    right; right; right; left. exists 5, (y_pos x). split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite Hly.
    change (frame_addr (p_ly (y_v x)) 5 (y_pos x)) with (pf_F (y_v x) (y_pos x)).
    change (fs_frame_bytes 5) with 2048. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw Hn.
    apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
    exfalso. rewrite SPF in Hw. lia. }
(* back at 0x87fec, at the same FP state *)
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (Ha02 & HBY2 & HKT2 & HNA2)).
destruct HNA2 as (HPm2 & Hly2 & HSf2). subst ly2.
replace (0 + EV_trim) with 0 in HJ2 by (unfold EV_trim; lia).
assert (HKT : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 (y_v x) - STK_trim <= a < pf_s1 (y_v x)) ->
  ~ (a = trim_end_addr p s) -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Hw He. apply HKT2; [exact Ha | rewrite Csp; exact Hw | exact He]. }
assert (HTEV : rdW W2 mem2 (trim_end_addr p s) <> None).
{ unfold trim_end_addr. rewrite (HBY2 (seg_spec.trim_lead s + length (r_trim s))%nat); [discriminate|].
  unfold seg_spec.zb. rewrite length_app, length_map, length_firstn. cbn [length]. lia. }
assert (HED : forall a, (a = trim_end_addr p s) \/ ~ (a = trim_end_addr p s))
  by (intros a; destruct (Z.eq_dec a (trim_end_addr p s)); [left | right]; assumption).
assert (HLO : pf_sp0 (y_v x) - STK_reac_segconf_parse_file <= pf_s1 (y_v x) - STK_trim) by (rewrite STR, SPF; lia).
assert (HVT : forall a, rdW Wc memc a <> None -> rdW W2 mem2 a <> None)
  by exact (b2_vis (y_v x) (y_pos x) lyc S2 Wc memc W2 mem2 md2 (fun a => a = trim_end_addr p s)
    (pf_s1 (y_v x) - STK_trim) G HJ2 HLO HKT HED ltac:(intros a ->; exact HTEV)).
assert (HPR2 : aregs_preserved rX regs2) by exact (aregs_preserved_trans _ _ _ HPR HP2).
assert (HCT : a9_core B n x lyc S2 W2 regs2 mem2 md2).
{ apply (b2_core_move n x lyc Sc Wc (ms_regs ms) memc mdq S2 W2 regs2 mem2 md2 (fun a => a = trim_end_addr p s)
    (pf_s1 (y_v x) - STK_trim) HCc HJ2 HSf2 HPm2 HLO HKT).
  - intros a ->. unfold a9_buf, PF_O_BUF. lia.
  - exact HED.
  - intros a ->. exact HTEV.
  - exact (a5_rg_pres rX regs2 _ HPR2 (a5_FI_cs B _) HFI). }
pose proof (b2_trim_str x ei Wc memc W2 mem2 p eq_refl HREST HBY2 HVT) as HV0T.
pose proof (b2_keep_inbuf x Wc memc W2 mem2 (fun a => a = trim_end_addr p s) (pf_s1 (y_v x) - STK_trim) kp
  (a9_key x ei) G HLO HKT HVT ltac:(intros a -> Hr; lia) HKEY) as HKEYT.
set (vp0 := p + Z.of_nat (seg_spec.trim_lead s)) in *.
assert (Hvp : vp0 = p + Z.of_nat (seg_spec.trim_lead s)) by reflexivity.
(* the state after the call, re-seated: the caller-saved registers fresh atoms from 1024 on *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W2) mem2) HP2 (@nil nat) HS2.
lazymatch type of HS2 with ?P -> _ => assert (HQ : P); [| specialize (HS2 HQ); clear HQ] end.
{ constructor. }
rewrite <- restrict_mkst_fx in HS2.
pose proof (img_env_havoc_hi E 1024 (map (getr regs2) CLOB) HEI ltac:(unfold A_LIM; lia)) as HEI2.
assert (HA2 : env_agree 32 (Ereg rX []) (havoc E 1024 (map (getr regs2) CLOB))).
{ split; [intros k Hk; rewrite ew_havoc_old by lia; exact (proj1 HA0 k Hk) | exact (proj2 HA0)]. }
clear HS.
rename ms into ms1.
(* 0x87fec mv s9, a0; 0x87ff0 jal strlen *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS2 HJ2.
{ first [apply awr_ok_nil | cbn; apply awr_ok_nil]. }
assert (Hmem2 : ms_mem ms = mem2).
{ apply functional_extensionality. intros y. unfold frame_of in HF. rewrite HF; [reflexivity|].
  intros (r & Hr & _). cbn in Hr. destruct Hr. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq2 := dM) in *; clearbody mdq2 end.
pmkst HS2. rewrite Hmem2 in HJ2 |- *.
clear HF HFr HG.
pose proof (regs_kept_of_st_ok SEGS _ _ _ rX [] (map (Z_to_bv 5) B2_KS) HS2 HA2 ltac:(vm_compute; reflexivity))
  as HKR.
cbn [ms_regs restrict] in HKR.
assert (HFI2 : pf_rg (ms_regs ms) (a5_FI B (y_v x))) by exact (b2_rg_kept rX _ B2_KS _ HKR (b2_ks_fi _) HFI).
assert (HRG2 : pf_rg (ms_regs ms) (A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x); (23, kp)]))
  by exact (b2_rg_kept rX _ B2_KS _ HKR (b2_ks_rc x ei kp) HRG).
assert (D2 : getr (ms_regs ms) 2 = w64 (pf_s1 (y_v x)))
  by exact (a5_rg_get _ _ 2 _ HFI2 ltac:(cbn [a5_FI In]; tauto)).
assert (D3 : getr (ms_regs ms) 3 = w64 (as_gp B))
  by exact (a5_rg_get _ _ 3 _ HFI2 ltac:(cbn [a5_FI In]; tauto)).
assert (D4 : getr (ms_regs ms) 4 = w64 (as_tp B))
  by exact (a5_rg_get _ _ 4 _ HFI2 ltac:(cbn [a5_FI In]; tauto)).
assert (Dsp : spZ (ms_regs ms) = pf_s1 (y_v x)).
{ unfold spZ. rewrite D2. unfold w64. apply unsigned_lit_small. lia. }
prreg HS2 (1%bv : bv 5) P1. prreg HS2 (10%bv : bv 5) P10. prreg HS2 (Z_to_bv 5 25) P25.
assert (D1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 0x32c0)).
{ rewrite P1. reflexivity. }
assert (D10 : getr (ms_regs ms) 10 = w64 vp0).
{ rewrite P10. exact Ha02. }
assert (D25 : getr (ms_regs ms) (Z_to_bv 5 25) = w64 vp0).
{ rewrite P25. exact Ha02. }
(* the cut at the strlen call *)
assert (HCS : a9_core B n x lyc S2 W2 (ms_regs ms) mem2 mdq2)
  by exact (b2_core_regs n x lyc S2 W2 regs2 mem2 md2 (ms_regs ms) mdq2 HCT HJ2 HFI2).
destruct (b2_strlen_pre n x lyc S2 W2 (ms_regs ms) mem2 mdq2 (ms_regs ms) vp0 (a9_v0 x ei) HCS Dsp
  ltac:(rewrite D1; apply ret_ok_codeptr_v; [lia | reflexivity]) D3 D4 D10 HV0T)
  as (ECP & _ & Hvp0 & HAS & HRD & HTV & HROM).
destruct HSf2 as [f2 HS2e].
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low ESTACK (fun _ => False)
    (SIG SS___interceptor_trampoline_strlen) W2 (ms_regs ms) mem2 STK_reac_segconf_parse_file (pf_sp0 (y_v x))
    (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x))
    [(5, y_pos x)] lyc S2 mdq2 0 (pf_s1 (y_v x) - pf_sp0 (y_v x)) (Z_to_bv 64 (BASE + 0x32c0)) _ HJ2
    ltac:(rewrite Dsp; lia) Ho16 ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite SPF; unfold ESTACK; lia) D1
    (fun a (H : False) => False_ind _ H)).
  exact (ASTRLEN fx lyc S2 W2 (ms_regs ms) mem2 mdq2 vp0 (seg_spec.zb (a9_v0 x ei)) ECP D10 Hvp0 HAS HRD HTV HROM). }
(* back at 0x87ff4 = K3 *)
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & HK3').
assert (HKS : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 (y_v x) - ESTACK <= a < pf_s1 (y_v x)) -> ~ False ->
  rdW W2 mem3 a = rdW W2 mem2 a).
{ intros a Ha Hw _. apply HK3'; [exact Ha | intros Hc; apply Hw; lia | tauto]. }
assert (HLO2 : pf_sp0 (y_v x) - STK_reac_segconf_parse_file <= pf_s1 (y_v x) - ESTACK)
  by (rewrite SPF; unfold ESTACK; lia).
assert (HVS : forall a, rdW W2 mem2 a <> None -> rdW W2 mem3 a <> None)
  by exact (b2_vis (y_v x) (y_pos x) lyc S2 W2 mem2 W2 mem3 md3 (fun _ => False) (pf_s1 (y_v x) - ESTACK) G HJ3
    HLO2 HKS ltac:(intros a; right; tauto) ltac:(intros a [])).
assert (HCK : a9_core B n x lyc S2 W2 regs3 mem3 md3).
{ apply (b2_core_move n x lyc S2 W2 (ms_regs ms) mem2 mdq2 S2 W2 regs3 mem3 md3 (fun _ => False)
    (pf_s1 (y_v x) - ESTACK) HCS HJ3).
  - exists f2. rewrite HS2e at 1. rewrite HS2e, a5_set_fs2. reflexivity.
  - apply Permutation_refl.
  - exact HLO2.
  - exact HKS.
  - intros a [].
  - intros a. right. tauto.
  - intros a [].
  - exact (a5_rg_pres (ms_regs ms) regs3 _ HP3 (a5_FI_cs B _) HFI2). }
pose proof (b2_keep_inbuf x W2 mem2 W2 mem3 (fun _ => False) (pf_s1 (y_v x) - ESTACK) kp (a9_key x ei) G HLO2 HKS
  HVS ltac:(intros a []) HKEYT) as HKEY3.
pose proof (b2_keep_inbuf x W2 mem2 W2 mem3 (fun _ => False) (pf_s1 (y_v x) - ESTACK) vp0 (a9_v0 x ei) G HLO2 HKS
  HVS ltac:(intros a []) HV0T) as HV03.
destruct HV0T as (HV0S & _).
destruct (b2_astr_of_sa W2 mem2 vp0 (a9_v0 x ei) HV0S) as (_ & _ & HLn & _ & _).
change (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + 0x32c0)) mem3 (seg_rom SEGS)) md3)
  with (cfg_at SEGS (BASE + A9_K3) regs3 mem3 md3).
apply (HK3 x ei kp vp0 lyc S2 W2 regs3 mem3 md3).
unfold INV_K3.
split; [exact HCK|]. split; [exact HCH|]. split; [exact HKEY3|].
split; [lia|]. split; [exact HV03|].
replace (A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x); (23, kp); (25, vp0);
                     (10, Z.of_nat (length (a9_v0 x ei)))])
  with ((A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x); (23, kp)]) ++
        [(25, vp0); (10, Z.of_nat (length (a9_v0 x ei)))]) by (rewrite <- app_assoc; reflexivity).
apply a5_rg_app. split.
- exact (a5_rg_pres (ms_regs ms) regs3 _ HP3 (b2_cs_rc x ei kp) HRG2).
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
  + rewrite (HP3 25 ltac:(unfold acallee_saved; lia)). exact D25.
  + rewrite <- HLn. exact Ha03.
Qed.

End e.
End f.
End d.
