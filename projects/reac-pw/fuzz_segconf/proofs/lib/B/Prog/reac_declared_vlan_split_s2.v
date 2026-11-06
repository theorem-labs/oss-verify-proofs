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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 256 of its 302 lines of code are new or changed and 407 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image B (fuzz_segconf.asan-ubsan): the point K2 (0x8a2fc), the set-up and
   call of the strtol wrapper. Image A's walk (commit ceb7e39832b2) has no K2 segment yet; this
   file is written for image B. 0x8a2fc `li a2,10`, 0x8a300 `li a1,0`, 0x8a304 `jal` the strtol wrapper
   (SS___interceptor_trampoline_strtol, 0x43b44) with a0 = dot + 1; the wrapper returns to K3 (0x8a308). No UBSan
   trap branch, no instrumented check and no store lie in the stretch.
   The call applies RtSeg.astrtol0_realizes (row 3) through PaArt.aj_art_at with the string str = the tail
   skipn (S di) s as bytes (seg_spec.zb) at dot + 1. Its premises come from the contract through vs_entry and from
   vs_ctx0 at K2: the string, its bytes' shadow (sa_addr), the band room (amem_range), the slack after the NUL
   (sa_tail), all of the segment, a suffix of it; the errno cell apart from the string (sa_loc: a heap block or a
   side-stack frame is no image byte, the errno cell is one, AR_client_img_law and api_env; an image object of
   sa_img is not the errno cell); rd32 of the errno cell from AR_errno_present under ERR; rt_rom_view from
   arodata_okP; aguard_ok from sa_ssp, carried to K2 because gotw and guard are image words below kLowMemEnd (the
   premise of vs_K2, which the top file discharges at gotw = 0xa3e98, guard = 0x5ff838).
   After the call, a0 = s10_val str = SegModel.strtol10 tail (SegBridge.bridge_strtol10_str) and the errno cell
   holds s10_errno str ev = ev (SegBridge.bridge_strtol10_errno: 1 to 14 digits), so every byte outside the stack
   window reads as at the entry again: vs_ctx0 holds at K3. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require __intscan_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the registers the run from K2 to the call leaves as their atoms *)
Definition vsk2_kr : list (bv 5) :=
  map (Z_to_bv 5) [2; 3; 4; 8; 9; 10; 18; 19; 20; 22; 23; 24; 25; 26; 27].

Lemma vsk2_skipn_map : forall {A C : Type} (f : A -> C) n l, skipn n (map f l) = map f (skipn n l).
Proof. intros A C f n. induction n as [|n IH]; intros [|a l]; cbn [skipn map]; try reflexivity. apply IH. Qed.

(* the shadow hull of a sub-range lies in the hull of the range *)
Lemma vsk2_hull_sub : forall rd x n x' n', shadow_hull_vis rd x n -> x <= x' -> 0 < n' -> x' + n' <= x + n ->
  shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
assert (D1 : x / 8 <= x' / 8) by (apply Z.div_le_mono; lia).
assert (D2 : (x' + n' - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
assert (D3 : (SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + x' / 8) / 8) by (apply Z.div_le_mono; lia).
assert (D4 : (SHADOW_OFF + (x' + n' - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.

(* the low 32 bits of a word's value are those of the value *)
Lemma vsk2_le_byte_wrap : forall v k, le_byte (bv_unsigned (Z_to_bv 64 v)) 4 k = le_byte v 4 k.
Proof.
intros v k. rewrite Z_to_bv_unsigned. unfold bv_wrap, le_byte. change (bv_modulus 64) with (2 ^ 64).
change (8 * Z.of_nat 4) with 32.
assert (M : (v mod 2 ^ 64) mod 2 ^ 32 = v mod 2 ^ 32).
{ rewrite (Z.div_mod v (2 ^ 64)) at 2 by lia.
  replace (2 ^ 64 * (v / 2 ^ 64) + v mod 2 ^ 64) with (v mod 2 ^ 64 + (2 ^ 32 * (v / 2 ^ 64)) * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. reflexivity. }
rewrite M. reflexivity.
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
Section e.
Variable B : asyms.
Variables gotw guard : Z.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis STRTOL : forall fx0 : YK11.FPState, @RtSeg.astrtol0_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strtol) gotw guard.
Hypothesis TL : PALib B.
Hypothesis ERR : errno_rom SEGS B.
Let RUN := paj_run B LAWS.

(* where an object of sa_loc lies: below the allocation ceiling, and off the errno cell *)
Lemma vsk2_loc : forall ly S W mem md q n, AR SEGS B ly S W mem md -> 0 < n -> sa_loc SEGS B ly S q n ->
  0 <= q /\ q + n <= alloc_ceiling /\ (forall a, q <= a < q + n -> ~ (as_errno B <= a < as_errno B + 4)).
Proof using TL.
intros ly S W mem md q n HAR Hn HL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pal_env B TL) as (_ & HEI & _).
destruct HL as [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & Hc & H1 & H2) | HI]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & B0 & B1 & B2 & _ & _ & Bm).
  pose proof (req_size_pos m ltac:(lia)) as [Q1 Q2].
  split; [lia|]. split; [lia|]. intros a Ha He.
  refine (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ b (ex_intro _ m (conj Hin _))))) (HEI a He)).
  lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (F0 & F1 & F2).
  split; [lia|]. split; [lia|]. intros a Ha He.
  refine (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
    (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin _)))))) (HEI a He)).
  lia.
- pose proof (HI q ltac:(lia)) as (Hq & _ & _). pose proof (HI (q + n - 1) ltac:(lia)) as (Hq' & _ & _).
  pose proof (pa_segs_low _ Hq) as R1. pose proof (pa_segs_low _ Hq') as R2.
  split; [lia|]. split; [lia|]. intros a Ha. exact (proj2 (proj2 (HI a Ha))).
Qed.

Lemma vs_K2 : (0 <= gotw /\ gotw + 8 <= kLowMemEnd /\ 0 <= guard /\ guard + 8 <= kLowMemEnd) ->
  vs_K3_stmt B gotw guard -> vs_K2_stmt B gotw guard.
Proof using STRTOL TL ERR.
intros HGW HK3. unfold vs_K2_stmt. intros e regs' mem' md' di HE HC Hdi Hdi0 Hne Hdig R10 R20.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj2 (@YG0f.ASAN_CEIL_range _)) as CM. unfold YG0f.ASAN_CEIL in CM.
pose proof HC as (HJ & HR & HSL & HKP & HPP).
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & Hp0 & Hcap & Hpdst & Hpadd & Hpdisj & Hv0 & Hv2 & Hvdst & Hvadd & Hvdisj & Hssp).
pose proof (pal_env B TL) as ((Her0 & Her4) & _ & _).
assert (HVS : VS_STK = 12352) by reflexivity.
assert (HE3 : 3 * ESTACK = 12288) by reflexivity.
unfold e_sp in *.
(* ---- the tail, the string and its bounds ---- *)
set (tail := vs_tail e di) in *.
set (str := seg_spec.zb tail).
assert (Hd : (S di <= length (e_s e))%nat).
{ destruct (Nat.le_gt_cases (S di) (length (e_s e))) as [Hq|Hq]; [exact Hq|].
  exfalso. apply Hne. unfold tail, vs_tail. apply skipn_all2. lia. }
assert (Hlt : (length tail + S di = length (e_s e))%nat) by (unfold tail, vs_tail; rewrite length_skipn; lia).
assert (Hlt0 : (0 < length tail)%nat).
{ apply Nat.neq_0_lt_0. intros H0. apply Hne. apply length_zero_iff_nil. exact H0. }
assert (Hlstr : length str = length tail) by (unfold str, seg_spec.zb; apply length_map).
assert (Hls : astr_len str = Z.of_nat (length tail)) by (unfold astr_len; rewrite Hlstr; reflexivity).
destruct (vsk2_loc (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) (e_seg e) (Z.of_nat (length (e_s e)) + 1) HAR
  ltac:(lia) Hsloc) as (Lq0 & Lqc & Lerr).
set (x := e_seg e + Z.of_nat di + 1) in R10.
assert (Hx : x = e_seg e + Z.of_nat di + 1) by reflexivity.
clearbody x.
set (lo := spZ (e_regs e) - VS_STK).
assert (Hlo' : lo = spZ (e_regs e) - VS_STK) by reflexivity.
clearbody lo.
assert (Hxlo : x + Z.of_nat (length tail) + 1 <= alloc_ceiling) by lia.
assert (Hlo : alloc_ceiling <= lo) by lia.
assert (Hlo64 : lo < 2 ^ 64) by lia.
(* the bytes and the NUL of the tail at x, at the entry *)
destruct (sa_strz_bytes SEGS (w_H (e_W e)) (e_mem e) (e_seg e) (e_s e) (proj1 Hstr)) as (SB1 & SB2 & SB3).
assert (STRs : astr_atR (rdW (e_W e) (e_mem e)) (e_seg e) (seg_spec.zb (e_s e))) by (split; [exact SB1 | exact SB2]).
pose proof (astr_atR_skipn _ _ _ (S di) STRs ltac:(unfold seg_spec.zb; rewrite length_map; lia)) as STRe.
assert (Ezb : skipn (S di) (seg_spec.zb (e_s e)) = str) by (unfold str, seg_spec.zb, tail, vs_tail; apply vsk2_skipn_map).
rewrite Ezb in STRe. replace (e_seg e + Z.of_nat (S di)) with x in STRe by lia.
assert (Ezs : seg_spec.zs str = tail).
{ unfold str, tail, vs_tail. unfold seg_spec.zs, seg_spec.zb in SB3 |- *.
  rewrite <- (vsk2_skipn_map (Z_to_bv 8)), <- (vsk2_skipn_map (@bv_unsigned 8)), SB3. reflexivity. }
assert (Hstr_ne : str <> []).
{ unfold str, seg_spec.zb. intros H0. apply Hne. exact (map_eq_nil _ _ H0). }
assert (Hstr_d : forallb SegModel.isdigit (seg_spec.zs str) = true) by (rewrite Ezs; exact Hdig).
assert (Hstr_l : (length str <= 18)%nat) by lia.
(* the range strtol checks, at the entry *)
assert (RDe : aread_ok SEGS VS_STK (e_W e) (e_regs e) (e_mem e) x (astr_len str + 1)).
{ rewrite Hls. destruct Hsadd as (Q0 & Q63 & QM & QRA & QHV).
  split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros a Ha. split.
    - pose proof (proj1 (proj1 Hstr) (Z.to_nat (a - e_seg e)) ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
      replace (e_seg e + Z.of_nat (Z.to_nat (a - e_seg e))) with a in Hb by lia. rewrite Hb. discriminate.
    - unfold ascratch_stk. lia. }
  split; [unfold amem_range in *; lia|]. split.
  - apply (range_addressable_sub _ _ (e_seg e) (Z.of_nat (length (e_s e)) + 1)); [exact QRA | lia | lia].
  - intros _. apply (vsk2_hull_sub _ (e_seg e) (Z.of_nat (length (e_s e)) + 1)); [apply QHV; lia | lia | lia | lia]. }
assert (TLe : atail_vis SEGS (e_W e) (e_mem e) (x + astr_len str)).
{ rewrite Hls. replace (x + Z.of_nat (length tail)) with (e_seg e + Z.of_nat (length (e_s e))) by lia. exact (proj2 Hstr). }
assert (ROMe : rt_rom_view SEGS B (e_W e) (e_mem e)) by (intros a Hr Ho He; exact (HROD a (or_introl Hr) Ho He)).
assert (ERRx : as_errno B + 4 <= x \/ x + astr_len str + 1 <= as_errno B).
{ rewrite Hls. destruct (Z_le_gt_dec (as_errno B + 4) x) as [Hq|Hq]; [left; exact Hq|].
  destruct (Z_le_gt_dec (x + Z.of_nat (length tail) + 1) (as_errno B)) as [Hq'|Hq']; [right; exact Hq'|].
  exfalso. apply (Lerr (Z.max x (as_errno B))); lia. }
assert (Hbnd : (x + astr_len str) - (x + astr_len str) mod 8 + 8 <= lo).
{ pose proof (tail_below (x + astr_len str) alloc_ceiling ltac:(rewrite Hls; lia) CM). lia. }
(* ---- the seeded state at K2 and the run to the call ---- *)
assert (HSL' : vs_slots (rdW (e_W e) mem') (spZ regs' + 64) (e_regs e)) by (replace (spZ regs' + 64) with (spZ (e_regs e)) by lia; exact HSL).
assert (Hspr : 2 ^ 46 <= spZ regs' <= 2 ^ 47 - 64) by lia.
assert (Hspal : spZ regs' mod 16 = 0).
{ rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
pose proof (vs_seedK (e_W e) (e_regs e) regs' mem' VS_K2 [] [] HSL' Hspr Hspal G22 I) as HS.
set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ []))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs' (vs_xs (e_regs e) ++ [])) E)
  by (unfold E; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clearbody E.
assert (SHOK : sh_ok SEGS (SOff 22 0) [] E (mrestrict (w_H (e_W e)) mem')) by (unfold sh_ok; apply Forall_nil).
unfold vs_goal, vs_cfg.
(* 0x8a2fc `li a2,10`, 0x8a300 `li a1,0`, 0x8a304 `jal` the strtol wrapper: no branch, no load, no store *)
paj_run_tok RUN HS HJ SHOK (SB, SB + 2 ^ 44 - 1).
{ vs_awr_ro. }
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]); destruct Hin)) as UN end.
prreg HS (1%bv : bv 5) R1. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12.
lazymatch type of HS with st_ok _ ?Ecur _ _ => assert (HAEc : env_agree 32 (Ereg regs' (vs_xs (e_regs e) ++ [])) Ecur) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs' _ vsk2_kr HS HAEc ltac:(vm_compute; reflexivity)) as KA.
cbn [ms_regs restrict] in KA.
assert (KAZ : forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 10 \/ (18 <= r <= 27 /\ r <> 21) ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)).
{ intros r Hr. apply KA.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 10 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  unfold vsk2_kr. apply in_map. cbn [In]. lia. }
assert (Hsp1 : spZ (ms_regs ms) = spZ (e_regs e) + -64).
{ unfold spZ at 1. change (getr (ms_regs ms) 2) with (getr (ms_regs ms) (Z_to_bv 5 2)). rewrite (KAZ 2 ltac:(lia)).
  change (bv_unsigned (getr regs' (Z_to_bv 5 2))) with (spZ regs'). lia. }
assert (Hraw : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ change (getr (ms_regs ms) 3) with (getr (ms_regs ms) (Z_to_bv 5 3)). rewrite (KAZ 3 ltac:(lia)). exact (eq_trans G3 Hgp). }
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ change (getr (ms_regs ms) 4) with (getr (ms_regs ms) (Z_to_bv 5 4)). rewrite (KAZ 4 ltac:(lia)). exact (eq_trans G4 Htp). }
assert (R10c : getr (ms_regs ms) 10 = w64 x).
{ change (getr (ms_regs ms) 10) with (getr (ms_regs ms) (Z_to_bv 5 10)). rewrite (KAZ 10 ltac:(lia)). exact R10. }
(* ---- the state at the call: what the wrapper's contract asks, carried from the entry ---- *)
assert (KO : kept_out (rdW (e_W e) (e_mem e)) (rdW (e_W e) (ms_mem ms)) lo (spZ (e_regs e))).
{ intros a Ha Hw. rewrite (UN a Ha (fun q => q)). apply (HKP a Ha); [rewrite <- Hlo'; exact Hw | intros q; exact q]. }
pose proof (AR_errno_present SEGS B (e_W e) (ms_mem ms) ERR) as (ev & Hev).
assert (AGt : aguard_ok SEGS (e_W e) (ms_mem ms) gotw guard)
  by (apply (aguard_ok_kept SEGS (e_W e) (e_mem e) (ms_mem ms) lo (spZ (e_regs e)) gotw guard KO Hssp); lia).
assert (STRt : astr_at SEGS (e_W e) (ms_mem ms) x str).
{ apply (astr_atR_view SEGS (e_W e) (ms_mem ms) x str).
  apply (astr_atR_kept _ _ lo (spZ (e_regs e)) x str KO STRe); lia. }
assert (RDt : aread_ok SEGS (3 * ESTACK) (e_W e) (ms_regs ms) (ms_mem ms) x (astr_len str + 1)).
{ apply (aread_ok_kept SEGS VS_STK (3 * ESTACK) (e_W e) (e_regs e) (ms_regs ms) (e_mem e) (ms_mem ms) lo (spZ (e_regs e))
    x (astr_len str + 1) KO RDe); rewrite ?Hls, ?HE3; lia. }
assert (TLt : atail_vis SEGS (e_W e) (ms_mem ms) (x + astr_len str))
  by (apply (atail_vis_kept SEGS (e_W e) (e_mem e) (ms_mem ms) lo (spZ (e_regs e)) _ KO TLe); rewrite ?Hls; lia).
assert (ROMt : rt_rom_view SEGS B (e_W e) (ms_mem ms)).
{ apply (rt_rom_view_keep SEGS B (e_W e) (e_mem e) (ms_mem ms) ROMe). intros a Hr Ho He.
  assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hs & _ & Hsr); exists sg; split; [exact Hs | exact Hsr]).
  pose proof (pa_segs_low _ Hi) as Ra. apply KO; lia. }
(* the apresent bytes of K2 stay present at the call (the run grows memory) *)
assert (PRt : forall a, apresent (w_H (e_W e)) mem' a -> apresent (w_H (e_W e)) (ms_mem ms) a).
{ intros a (Hh & b & Hb). split; [exact Hh|].
  specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG.
  destruct (ms_mem ms (Z_to_bv 64 a)) as [b'|] eqn:Eb; [exists b'; reflexivity|].
  exfalso. apply HG; [rewrite Hb; intros Hq; discriminate Hq | reflexivity]. }
pmkst HS.
(* ---- the call: RtSeg.astrtol0_realizes through aj_art_at ---- *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (3 * ESTACK) (aerrno_cell B) (SIG SS___interceptor_trampoline_strtol)
    (e_W e) (ms_regs ms) (ms_mem ms) VS_STK (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) []
    (e_ly e) (e_S e) _ 0 (-64) (getr (ms_regs ms) 1)
    (fun regs2 mem2 => (getr regs2 10 = w64 (__intscan_c.s10_val str) /\
       rd32 (rdW (e_W e) mem2) (as_errno B) (bv_unsigned (__intscan_c.s10_errno str (Z_to_bv 64 ev)))) /\
       (forall a, apresent (w_H (e_W e)) (ms_mem ms) a -> apresent (w_H (e_W e)) mem2 a)) HJ).
  1: exact Hsp1. 1: reflexivity. 1: lia. 1: unfold ESTACK; lia. 1: rewrite HE3, HVS; lia. 1: reflexivity.
  1: intros a Ha; exact Ha.
  eapply SRr_mono.
  - eapply (STRTOL fx (e_ly e) (e_S e) (e_W e) (ms_regs ms) (ms_mem ms) _ x str ev).
    + exact AGt.
    + eapply (ecall_pre_stk_at SEGS B (3 * ESTACK) VS_STK (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e)
        (e_md e) [] (e_ly e) (e_S e) (e_W e) (ms_mem ms) _ 0 (ms_regs ms) (-64) HJ);
      [exact Hsp1 | reflexivity | lia | unfold ESTACK; lia | rewrite HE3, HVS; lia | exact Hraw | exact R3 | exact R4].
    + exact R10c.
    + rewrite R11. reflexivity.
    + rewrite R12. reflexivity.
    + lia.
    + exact STRt.
    + rewrite Hls. lia.
    + exact RDt.
    + rewrite Hls. unfold amem_range in *. lia.
    + exact TLt.
    + exact ERRx.
    + exact Hev.
    + exact ROMt.
  - intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsm & HQ & Hfr & Hpr & Hscr).
    split; [reflexivity|]. exists regs2, mem2, md2.
    exact (conj eq_refl (conj HAR2 (conj HP2 (conj Hsm (conj (conj HQ Hpr) (conj Hfr (conj Hpr Hscr))))))). }
(* ---- K3: a0 = strtol10 tail, and vs_ctx0 again ---- *)
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & ((HA10 & Herr2) & HPR2) & Hfr2).
rewrite R1.
pose proof (SegBridge.bridge_strtol10_errno str (Z_to_bv 64 ev) Hstr_ne Hstr_d Hstr_l) as ERRB.
pose proof (SegBridge.bridge_strtol10_str str Hstr_ne Hstr_d Hstr_l) as VALB.
assert (CS2 : forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ (18 <= r <= 27 /\ r <> 21) ->
  getr regs2 (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)). apply KAZ. lia. }
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (e_regs e) - VS_STK <= a < spZ (e_regs e) - 64) -> ~ aerrno_cell B a ->
  rdW (e_W e) mem2 a = rdW (e_W e) mem' a).
{ intros a Ha Hw He. rewrite (Hfr2 a Ha ltac:(rewrite HE3; lia) He). exact (UN a Ha (fun q => q)). }
unfold vs_K3_stmt in HK3.
refine (HK3 e regs2 mem2 md2 di HE _ Hdi Hdi0 Hne Hdig _ _).
- unfold vs_ctx0, vs_ctxW. split; [exact HJ2|]. split; [|split; [|split]].
  + unfold vs_regs, e_sp.
    split; [unfold spZ at 1; change (getr regs2 2) with (getr regs2 (Z_to_bv 5 2)); rewrite (CS2 2 ltac:(lia));
      change (bv_unsigned (getr regs' (Z_to_bv 5 2))) with (spZ regs'); exact Hsp|].
    split; [change (getr regs2 3) with (getr regs2 (Z_to_bv 5 3)); rewrite (CS2 3 ltac:(lia)); exact G3|].
    split; [change (getr regs2 4) with (getr regs2 (Z_to_bv 5 4)); rewrite (CS2 4 ltac:(lia)); exact G4|].
    split; [change (getr regs2 8) with (getr regs2 (Z_to_bv 5 8)); rewrite (CS2 8 ltac:(lia)); exact G8|].
    split; [change (getr regs2 9) with (getr regs2 (Z_to_bv 5 9)); rewrite (CS2 9 ltac:(lia)); exact G9|].
    split; [change (getr regs2 18) with (getr regs2 (Z_to_bv 5 18)); rewrite (CS2 18 ltac:(lia)); exact G18|].
    split; [change (getr regs2 19) with (getr regs2 (Z_to_bv 5 19)); rewrite (CS2 19 ltac:(lia)); exact G19|].
    split; [change (getr regs2 22) with (getr regs2 (Z_to_bv 5 22)); rewrite (CS2 22 ltac:(lia)); exact G22|].
    intros r Hr. rewrite (CS2 r ltac:(lia)). exact (G27 r Hr).
  + unfold e_sp. apply (vs_slots_kept (rdW (e_W e) mem')); [exact HSL|].
    intros a Ha. apply K2; [lia | lia | unfold aerrno_cell; lia].
  + unfold e_sp. intros a Ha Hw _.
    destruct (Z_lt_le_dec a (as_errno B)) as [Hl1|Hl1]; [|destruct (Z_lt_le_dec a (as_errno B + 4)) as [Hl2|Hl2]].
    * rewrite (K2 a Ha ltac:(lia) ltac:(unfold aerrno_cell; lia)). exact (HKP a Ha Hw (fun q => q)).
    * (* the errno cell: strtol wrote s10_errno str ev = ev back *)
      assert (Hk : (Z.to_nat (a - as_errno B) < 4)%nat) by lia.
      replace a with (as_errno B + Z.of_nat (Z.to_nat (a - as_errno B))) by lia.
      set (k := Z.to_nat (a - as_errno B)) in *.
      rewrite (Herr2 k Hk), <- (HKP (as_errno B + Z.of_nat k) ltac:(lia) ltac:(lia) (fun q => q)),
        <- (UN (as_errno B + Z.of_nat k) ltac:(lia) (fun q => q)), (Hev k Hk), ERRB, vsk2_le_byte_wrap.
      reflexivity.
    * rewrite (K2 a Ha ltac:(lia) ltac:(unfold aerrno_cell; lia)). exact (HKP a Ha Hw (fun q => q)).
  + intros a Hpa. exact (HPR2 a (PRt a (HPP a Hpa))).
- rewrite HA10, VALB, Ezs. reflexivity.
- change (getr regs2 20) with (getr regs2 (Z_to_bv 5 20)). rewrite (CS2 20 ltac:(lia)). exact R20.
Qed.
End e.
End f.
End d.
