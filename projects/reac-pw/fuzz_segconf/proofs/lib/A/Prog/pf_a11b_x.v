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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 295 of its 348 lines of code are new or changed and 400 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment A11b of reac_segconf_parse_file's walk, the
   half LOWOUT 0x88774 -> TAIL 0x88068, and the transport that half and the KEXIT half share.
   Part of segment A11b's proof, by the G3 walk owner, 2026-10-30.

   THE CODE (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s), four instructions:
     0x88774  sb a0,0x5c(s11)   a0 = -8, s11 = SH: the shadow cell of low146's first granule
     0x88778  sb a0,0x5d(s11)
     0x8877c  sb a0,0x5e(s11)
     0x88780  j  0x88068        TAIL
   low146 (F + 0x2e0, 24 bytes, shadow cells 0x5c .. 0x5e) goes OUT of scope: the frame's scope moves from
   pf_pieces.v's PF_SC_L146 to PF_SC_LINE, which is exactly what INV_TAIL asks. Nothing else is written, no
   register changes, and the post of H_LOWOUT at (o, ln) is LITERALLY H_TAIL's post at
   (pf_next (p_s v) o, ln + 1), so the exit is one application of HA_TAIL.

   WHY A PLAIN RUN. The three stores go into the shadow band, and a writable region there breaks a token
   run's sh_static_ok, so the token executor cannot take them. The run is therefore `paj_run_to_sh` with
   stop = PF_TAIL over ONE writable region on the s11 atom at [0x5c, 0x5f).

   THE TRANSPORT (x_keeps / x_base_sh / x_keeps_sh), which pf_a11b_x2.v and the A11b MISS piece also want.
   `pf_a6_k.a6_base_move` rebuilds pf_base only for a step whose writes miss the frame AND ALL 256 of its
   shadow cells, and gives back the SAME scope sc; it cannot serve a step that WRITES shadow cells, which is
   both halves of A11b. `x_base_sh` is its generalisation for a step that changes neither the world, the
   layout nor the allocator state: the frame's BYTES are kept, and the new `pf_fsh` at the new scope is a
   premise. Its proof is pf_a6_k.v's a6_base_move (segment A6's proof, in the base at pf_a6_k.v:291-353) with the
   fourth keep clause split, and it reuses that file's a6_heap_addr / a6_heap_bounds / a6_lit_move /
   a6_cat_move / a6_sl_move / a6_PF_SL_offs rather than restating them.

   NO SECTION HYPOTHESIS IS TAKEN HERE: not SSPX, not VRO. sa_ssp and arodata_okP come back from the keep
   clause over [0x10000, kImgEnd), because gotwA = 0xa36d8, guardA = 0x5ff078 and the read-only window
   RLO_A .. RHI_A = 0xa14a0 .. 0xa3748 all lie in that range and the three stores do not (SHADOW_OFF is
   0x7fff8000); this is the A5 proof's a5_low_out argument (pf_a5_k.v), made directly over the step's own
   write window. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_d pf_a5_k pf_a6_k pf_a11b_d pf_a11b_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The frame's shadow cells are bytes (the A7 proof's a7_shb_range) *)
Lemma x_shb_range : forall sc i, 0 <= pf_shb sc i < 256.
Proof.
intros sc i. unfold pf_shb, pf_io.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.

(** ** PF_SC_L146 and PF_SC_LINE differ at the cells 0x5c .. 0x5e only *)
Lemma x_shb_out146 : forall i, i < 0x5c \/ 0x5f <= i -> pf_shb PF_SC_LINE i = pf_shb PF_SC_L146 i.
Proof.
intros i H. unfold pf_shb, PF_SC_LINE, PF_SC_L146.
cbn [sc_cn sc_buf sc_low sc_l146 sc_known].
destruct (i <? 4); [reflexivity|]. destruct (i <? 6); [reflexivity|].
destruct (i <? 8); [reflexivity|]. destruct (i <? 72); [reflexivity|].
destruct (i <? 80); [reflexivity|]. destruct (i <? 88); [reflexivity|].
destruct (i <? 92) eqn:E7; [reflexivity|].
destruct (i <? 95) eqn:E8; [|reflexivity].
exfalso. apply Z.ltb_ge in E7. apply Z.ltb_lt in E8. lia.
Qed.
Lemma x_shb_l146_at : forall i, 0x5c <= i < 0x5f -> pf_shb PF_SC_LINE i = 0xf8.
Proof.
intros i H. unfold pf_shb, PF_SC_LINE, pf_io. cbn [sc_cn sc_buf sc_low sc_l146 sc_known].
replace (i <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 6) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 72) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 80) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 88) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 92) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 95) with true by (symmetry; apply Z.ltb_lt; lia).
reflexivity.
Qed.

(** ** The state's frame part is unchanged by a step that keeps the allocator state *)
Lemma x_set_fs_id : forall S : astate, S = set_fs (st_fs S) S.
Proof. intros S. destruct S. reflexivity. Qed.

(** ** One byte of a region's chunk list, read back through the state's reader (PaDenot.v's
    field_of_region_any and PaLibF.v's aview_of_val_mem1): see x_byte1 below. *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma x_byte1 : forall E (H : word -> bool) (m : word -> option byte) nb b cs lo hi wlo whi od e,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nb) lo hi wlo whi cs) ->
  bv_unsigned (ew E nb) = b -> In (YP09.mkChunk od (CVal 1 e)) cs ->
  aview SEGS H m (b + od) = Some (bv_unsigned (sv_denot E e) mod 256).
Proof.
intros E H m nb b cs lo hi wlo whi od e HR Hb Hin.
pose proof (field_of_region_any E (mrestrict H m) nb b cs lo hi wlo whi od 1%N e HR Hb Hin ltac:(cbn; lia))
  as Hm.
change (8 * Z.of_N 1) with 8 in Hm. change (N.to_nat 1) with 1%nat in Hm.
apply aview_of_val_mem1; [exact Hm|]. change (2 ^ 8) with 256 in Hm.
pose proof (Z.mod_pos_bound (bv_unsigned (sv_denot E e)) 256 ltac:(lia)). lia.
Qed.

(** ** The seed of a plain run of A11b over the frame's shadow
    Atoms 0..31 are the registers at the cut (sr_atoms, no register remapped); the one region is based on the
    s11 atom (27), whose value is SH (PF_RL / INV_KEXIT's register list). The region carries no chunk: the run
    only stores into it, and the stored bytes are read back from the chunks the run leaves. *)
Definition x_sh_r (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 27%nat) wlo whi wlo whi [].
Definition x_sh_ss (pc wlo whi : Z) : sstate :=
  mkSS pc sr_atoms [x_sh_r wlo whi] None (mkFacts [] [] []).

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** What a step that writes only inside the frame's 256 shadow cells leaves alone
    (pf_a6_k.v's a6_keeps, with its fourth clause split: the frame's bytes only, and the image clause widened
    to the whole image range so that sa_ssp and arodata_okP come back with no Section hypothesis) *)
Definition x_keeps (v : pfv) (pos : Z) (Wc : world SEGS) (memc : word -> option byte)
  (memc' : word -> option byte) : Prop :=
  (forall a, pf_s1 v <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) /\
  (forall i, 0 <= i <= Z.of_nat (length (p_s v)) -> rdW Wc memc' (p_t v + i) = rdW Wc memc (p_t v + i)) /\
  (forall a, 0x10000 <= a < kImgEnd -> rdW Wc memc' a = rdW Wc memc a) /\
  (forall a, pf_F v pos <= a < pf_F v pos + 2048 -> rdW Wc memc' a = rdW Wc memc a).

(** a step whose only writes are shadow cells of the frame keeps all four *)
Lemma x_keeps_sh : forall v pos lyc Sc Wc rX memc mdc sc (memc' : word -> option byte) (lo hi : Z),
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> 0 <= lo -> hi <= 256 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_SH v pos + lo <= a < pf_SH v pos + hi) ->
     rdW Wc memc' a = rdW Wc memc a) ->
  x_keeps v pos Wc memc memc'.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc memc' lo hi HB Hlo Hhi K.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (HAR & Hly & Hfin & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof alloc_ceiling_lt as Hac.
destruct HB as (HCX & HFI & HOBJ & _ & _).
destruct HOBJ as (_ & _ & HT & _ & HC & _).
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
  as (bt & mt & _ & Hb1 & Hb2 & Hb3 & Hb4 & Happt).
unfold kLowMemEnd, kHighShadowEnd in G11, G12.
split.
{ intros a Ha. apply K; [lia | lia]. }
split.
{ intros i Hi. apply K; [lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happt. lia. }
split.
{ intros a Ha. apply K; [unfold kImgEnd in Ha; lia | unfold kImgEnd in Ha; lia]. }
intros a Ha. apply K; [lia|].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. lia.
Qed.

(** ** pf_base after such a step: the generalisation of pf_a6_k.v's a6_base_move named in the head comment *)
Lemma x_base_sh : forall v pos lyc Sc Wc rX memc mdc sc (rX' : bvmap 5 word) memc' mdc' sc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  x_keeps v pos Wc memc memc' ->
  pf_rg rX' (a5_FI B v) ->
  pf_fsh (rdW Wc memc') (pf_SH v pos) sc' ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc'.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' sc' HB HJ' (K1 & K2 & K3 & K4) HRG HFSH.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (HAR & Hly & Hfin & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof alloc_ceiling_lt as Hac.
pose proof (proj1 HJ') as HAR'.
destruct HB as (HCX & HFI & HOBJ & HSL & _).
destruct HFI as (_ & Hly0 & (f0 & HS0) & HPerm & HSV & HFLW & HFRM & _).
destruct HOBJ as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
(* the image bytes are kept *)
assert (KI : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (as_errno B <= x < as_errno B + 4) -> rdW Wc memc' x = rdW Wc memc x).
{ intros x Hi _ _. pose proof (pa_img_range x Hi) as Hr. apply K3. exact Hr. }
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly0|]. split; [exists f0; exact HS0|].
  split; [exact HPerm|].
  split.
  { intros j r Hj. rewrite <- (HSV j r Hj). apply rdword_ext. intros k Hk.
    pose proof (proj1 (nth_error_Some PF_SAVED j) ltac:(rewrite Hj; discriminate)) as Hj13.
    unfold PF_SAVED in Hj13. cbn [length] in Hj13.
    apply K1. lia. }
  split.
  { rewrite <- HFLW. apply rdword_ext. intros k Hk. apply K4.
    change (fs_frame_bytes 5) with 2048. lia. }
  split; [exact HFRM | exact HRG]. }
split.
{ destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
    as (bt & mt & Hint & Hbt1 & Hbt2 & _ & _ & _).
  split.
  { destruct STR as ((Hz & Hn) & _). split; [split; [|exact Hn]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      rewrite K2 by lia. exact (Hz i Hi).
    - intros x Hx.
      apply (AR_block_word_vis SEGS B lyc Sc Wc memc' mdc' bt mt
               (p_t v + Z.of_nat (length (p_s v))) x HAR' Hint); lia. }
  split; [exact (a6_heap_addr B lyc Sc Wc memc' mdc' _ _ HAR' HT ltac:(unfold pf_len; lia))|].
  split; [exact HT|].
  split; [exact (a6_heap_addr B lyc Sc Wc memc' mdc' _ _ HAR' HC
                   ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact HC|].
  split; [exact (a6_cat_move B _ Wc memc' CAT KI)|].
  split; [intros x Hx; exact (a6_lit_move B _ Wc memc' _ _ (LITS x Hx) KI)|].
  split.
  { intros a Hro Ho He. rewrite K3; [exact (ROD a Hro Ho He)|].
    destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
    - apply pa_img_range. exists sg. split; [exact Hsg | exact Hr].
    - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. unfold kImgEnd. lia. }
  destruct SSP as (SSP1 & g & SSP2). split.
  - rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc')); [exact SSP1|].
    intros k Hk. apply K3. unfold gotwA, kImgEnd. lia.
  - exists g. rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc')); [exact SSP2|].
    intros k Hk. apply K3. unfold guardA, kImgEnd. lia. }
split; [|exact HFSH].
apply (a6_sl_move (rdW Wc memc) _ (pf_s1 v) _ HSL (a6_PF_SL_offs v pos)); [lia | lia |].
intros a Ha. apply K1. exact Ha.
Qed.

(** ** The spine's state across the same step: c's bytes are in the block and cur_name's in the frame, and
    both are apart from the frame's shadow cells *)
Lemma x_st_sh : forall v pos lyc Sc Wc rX memc mdc sc (memc' : word -> option byte) cf cur nm k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_SH v pos <= a < pf_SH v pos + 256) ->
     rdW Wc memc' a = rdW Wc memc a) ->
  pf_st v pos (rdW Wc memc) cf cur nm k -> pf_st v pos (rdW Wc memc') cf cur nm k.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc memc' cf cur nm k HB K (RC & COK & NM & CNT).
destruct (x_keeps_sh v pos lyc Sc Wc rX memc mdc sc memc' 0 256 HB ltac:(lia) ltac:(lia)
  ltac:(intros a Ha Hn; apply K; [exact Ha | lia])) as (_ & _ & _ & K4).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (HAR & _ & _ & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (_ & _ & HOBJ & _). destruct HOBJ as (_ & _ & _ & _ & HC & _).
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HC
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & _ & Hc1 & Hc2 & Hc3 & Hc4 & Hcapp).
unfold kLowMemEnd, kHighShadowEnd in G11, G12.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp.
split.
- destruct RC as (bs & Hbs & Henc). exists bs. split; [|exact Henc].
  intros i Hi. pose proof Henc as [Hl _].
  rewrite K; [exact (Hbs i Hi) | unfold seg_spec.SEG_C_SIZE in *; lia |].
  unfold seg_spec.SEG_C_SIZE in *. lia.
- split; [exact COK|]. split; [|exact CNT].
  apply (a6_nm_move v pos (rdW Wc memc) (rdW Wc memc') nm NM).
  intros a Ha. apply K4. change (fs_frame_bytes 5) with 2048 in Ha. lia.
Qed.

(* the seed and the walk run at the Section's own FP state fx: a plain run changes no FP state *)

(** ** The seed of the LOWOUT run *)
Lemma x_sh_seed : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc sc (pc wlo whi : Z),
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  getr rX (Z_to_bv 5 27) = w64 (pf_SH v pos) -> 0 <= wlo -> wlo <= whi -> whi <= 256 ->
  regions_wf [x_sh_r wlo whi] = true ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (x_sh_ss pc wlo whi)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc pc wlo whi HB R27 Hw0 Hw1 Hw2 HWF.
destruct (a5_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (_ & _ & _ & G & _ & HSHP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold kLowMemEnd, kHighShadowEnd in G11, G12.
assert (U27 : bv_unsigned (ew (Eimg (Ereg rX [])) 27) = pf_SH v pos).
{ rewrite (ew_Eimg_Ereg_nat rX [] 27%nat (Z_to_bv 5 27) eq_refl), R27.
  unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold x_sh_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- exact HWF.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, x_sh_r.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U27. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply HSHP. lia.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [exact I | split; exact I].
Qed.

(** ** LOWOUT 0x88774 -> TAIL: pfx_lowout_ok *)
Theorem pfx_lowout_ok : forall n : nat, HA_TAIL B n -> H_LOWOUT B n.
Proof.
intros n HTAIL v pos lyc Sc Wc rX memc mdc cf nm o ln d gi HINV.
pose proof HINV as (HB & HMID & HST & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_L146 HB) as (HAR & Hly & Hfin & G & HFP & HSHP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof alloc_ceiling_lt as Hac.
unfold kLowMemEnd, kHighShadowEnd in G11, G12.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_L146 HB) as HFIRG.
pose proof (proj1 HFI) as HJ0.
destruct HMID as (HMo & HMn & HMlctx).
(* the registers of the cut *)
assert (R27 : getr rX (Z_to_bv 5 27) = w64 (pf_SH v pos)).
{ eapply a5_rg_get; [exact HRG|]. unfold PF_RL, PF_RM.
  cbn [app In]. repeat (first [left; reflexivity | right]). }
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (-8)).
{ eapply a5_rg_get; [exact HRG|]. unfold PF_RL, PF_RM.
  cbn [app In]. repeat (first [left; reflexivity | right]). }
(* the seed *)
pose proof (x_sh_seed v pos lyc Sc Wc rX memc mdc PF_SC_L146 PF_LOWOUT 0x5c 0x5f HB R27
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (U27 : bv_unsigned (ew E 27) = pf_SH v pos)
  by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = 2 ^ 64 - 8).
{ rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), R10. unfold w64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). vm_compute. reflexivity. }
unfold cfg_at. change (w64 (BASE + PF_LOWOUT)) with (Z_to_bv 64 (BASE + PF_LOWOUT)).
(* the run: three shadow stores and the jump to TAIL *)
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS HJ0 PF_TAIL.
{ intros a (r & Hr & Ha). unfold x_sh_ss, x_sh_r in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U27 in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite Hly.
  change (fs_frame_bytes 5 / 8) with 256. unfold pf_SH, pf_F in Ha. lia. }
(* what the run kept *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_SH v pos + 0x5c <= a < pf_SH v pos + 0x5f) ->
  rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn.
  apply (kept_of_frame (segs := SEGS) E (ss_mem (x_sh_ss PF_LOWOUT 0x5c 0x5f)) (w_H Wc) memc (ms_mem ms)
    (fun x => pf_SH v pos + 0x5c <= x < pf_SH v pos + 0x5f) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | []]. injection Hq as <- <- <-.
  cbn [base_val] in Hrr. rewrite U27 in Hrr. lia. }
(* the three bytes the run stored *)
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx _ => pose proof (st_ok_pi_region_nth Ex ssx _ 0%nat _ HS eq_refl) as HR
end.
assert (VSH : forall i, 0x5c <= i < 0x5f -> rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some 0xf8).
{ intros i Hi.
  assert (HE : bv_unsigned (sv_denot E (SOff 10 0)) mod 256 = 0xf8).
  { cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, U10. vm_compute. reflexivity. }
  assert (Hi3 : i = 0x5c \/ i = 0x5d \/ i = 0x5e) by lia.
  destruct Hi3 as [-> | [-> | ->]];
    (erewrite <- HE; eapply (x_byte1 E (w_H Wc) (ms_mem ms) 27%nat (pf_SH v pos));
     [cbn [ms_mem restrict] in HR; exact HR | exact U27 | cbn [In]; tauto]). }
(* the new frame shadow: low146 out of scope *)
assert (HFSH2 : pf_fsh (rdW Wc (ms_mem ms)) (pf_SH v pos) PF_SC_LINE).
{ intros i Hi. destruct (Z_lt_le_dec i 0x5c) as [Hlt | Hge].
  - rewrite KEEP by lia. rewrite (x_shb_out146 i ltac:(lia)). exact (HFSH i Hi).
  - destruct (Z_lt_le_dec i 0x5f) as [Hlt2 | Hge2].
    + rewrite (VSH i ltac:(lia)). f_equal. symmetry. exact (x_shb_l146_at i ltac:(lia)).
    + rewrite KEEP by lia. rewrite (x_shb_out146 i ltac:(lia)). exact (HFSH i Hi). }
(* the registers are unchanged: the run stores and jumps, it writes no register *)
assert (RK : forall k, In k [18; 19; 20; 21; 24; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k)).
{ intros k Hk.
  apply (regs_kept_of_st_ok_pi E _ _ rX [] (map (Z_to_bv 5) [18; 19; 20; 21; 24; 26; 27]) HS).
  - split; [intros nn Hnn; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - vm_compute. reflexivity.
  - apply in_map. exact Hk. }
assert (RKF : forall k, In k [2; 3; 4; 8; 9; 22] ->
  getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k)).
{ intros k Hk.
  apply (regs_kept_of_st_ok_pi E _ _ rX [] (map (Z_to_bv 5) [2; 3; 4; 8; 9; 22]) HS).
  - split; [intros nn Hnn; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - vm_compute. reflexivity.
  - apply in_map. exact Hk. }
(* pf_base at the new state, with low146 out of scope *)
assert (HB2 : pf_base B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy mdc) mat mdc) PF_SC_LINE).
{ apply (x_base_sh v pos lyc Sc Wc rX memc mdc PF_SC_L146 _ _ _ PF_SC_LINE HB HJ0);
    [| | exact HFSH2].
  - apply (x_keeps_sh v pos lyc Sc Wc rX memc mdc PF_SC_L146 _ 0x5c 0x5f HB ltac:(lia) ltac:(lia)).
    exact KEEP.
  - unfold pf_rg, a5_FI in *. rewrite Forall_forall in HFIRG |- *. intros rv Hin.
    rewrite (RKF (fst rv)); [exact (HFIRG rv Hin)|].
    unfold a5_FI in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
(* the exit: INV_TAIL at the next line *)
pmkst HS.
unfold pf_postm.
apply (HTAIL fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc)
  cf (Some gi) nm (pf_next (p_s v) o) (ln + 1) d).
unfold INV_TAIL.
split; [exact HB2|].
split; [exact HMlctx|].
split; [pose proof (pf_next_skipn_lt (p_s v) o HMo); lia|].
split; [exact (x_st_sh v pos lyc Sc Wc rX memc mdc PF_SC_L146 _ cf (Some gi) nm _ HB
                 ltac:(intros a Ha Hn; apply KEEP; [exact Ha | lia]) HST)|].
(* the registers INV_TAIL asks are the cut's *)
unfold pf_rg in HRG |- *. rewrite Forall_forall in HRG |- *. intros rv Hin.
rewrite (RK (fst rv)).
- apply HRG. unfold PF_RL, PF_RM, pf_cur_ptr in Hin |- *. cbn [In app] in Hin |- *.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]];
    cbn [In app]; repeat (first [left; reflexivity | right]).
- unfold PF_RL, PF_RM, pf_cur_ptr in Hin. cbn [In app] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]; cbn [fst In]; tauto.
Qed.


End e.
End f.
End d.
