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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 393 of its 446 lines of code are new or changed and 400 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the TRANSPORT KIT of segment B7 of
   reac_segconf_parse_file's walk -- the cut facts pf_pieces.v's pf_base carries to a later state (after a step of
   B7's own code, after an interceptor call, after the call of refuse). The B7 segment lane of the image-B G3 walk owner, 2026-10-30.
   No instruction is walked here.
   ADAPTED from the image-A G3 walk owner's image-A A6 segment lane lib/A/Prog/pf_a6_k.v (commit 442a71316831), whose
   b7k_base_move / b7k_keeps_call / b7k_keeps_refuse are the general transport of pf_base over ANY callee whose
   footprint lies in the block c (refuse is that shape) and over any step that writes only below s1. Changed for
   image B: the realigned locals base is s1 = (sp0 - 0x160) & -32 (B's 0x87e38 `addi sp,sp,-352`), so
   sp0 - 0x180 < s1 <= sp0 - 0x160 (A: 0x140); parse_file's window is STK_reac_segconf_parse_file = 12832
   (SegInstB.STK_values, A: 12800). Dropped from the A file: its segment-A6 pure facts (strspn's set and the
   `[`-mask of 0x87e50) and its own refuse call site 0x87e74 (B7's three sites are lib/B/Prog/pf_seg_B7_s.v);
   a5_ro_img is inlined (b7k_relro_img / b7k_in_roP_img) so that the A5 kit is not Required.
   Section hypotheses: VRO (the listing's read-only range, SegObj.v) and SSPX (the image-A owner's route A: the
   stack-protector cells at every AR state, which image B's stage-2 SegRecCells will discharge). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======================================== pure facts ======================================== *)
Lemma b7k_w64_u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof.
intros z Hz. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* every byte refuse writes lies in [c + RC_REFUSAL, c + RC_OVERFLOW) (the image-A cross_check walk lane's cross_check_r.v) *)
Lemma b7k_refuse_W_in_block : forall c rcs a, inFP (refuse_W c rcs) a ->
  c + seg_spec.RC_REFUSAL <= a < c + seg_spec.RC_OVERFLOW.
Proof.
intros c rcs a (r & Hr & Ha). unfold refuse_W in Hr. apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold seg_spec.RC_REFUSED, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW in *. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat eqn:E; intros Hr; [|destruct Hr].
  apply Nat.ltb_lt in E.
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha;
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF,
      seg_spec.RC_OVERFLOW in *; lia.
Qed.
Lemma b7k_refuse_W_pos : forall c rcs, 0 < c -> ~ YI16.sink_open_fp (refuse_W c rcs).
Proof.
intros c rcs Hc. apply sink_closed_pos. apply Forall_forall. intros r Hr. unfold refuse_W in Hr.
apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst]. unfold seg_spec.RC_REFUSED. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat; intros Hr; [|destruct Hr].
  destruct Hr as [<- | [<- | []]]; cbn [fst];
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF; lia.
Qed.
(* refuse's footprint is inside parse_file's (the range refusal[0] .. overflow + 4 of RC_PARSE_W) *)
Lemma b7k_refuse_W_sub : forall c rcs a, inFP (refuse_W c rcs) a -> inFP (seg_spec.RC_PARSE_W c) a.
Proof.
intros c rcs a Ha. apply b7k_refuse_W_in_block in Ha.
exists (c + seg_spec.RC_REFUSAL, c + seg_spec.RC_OVERFLOW + 4). split.
- unfold seg_spec.RC_PARSE_W. right. left. reflexivity.
- cbn [fst snd]. lia.
Qed.
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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the listing's read-only range (SegObj.v; the pinned instance gives it by computation) *)
Hypothesis VRO : seg_val_relro (PI := PI).
(* the image-A owner's route A: the stack-protector cells at every AR state (discharged from SegRecCells.seg_rec_cells
   after the listing's stage 2) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(* ---------------------------------------- the image ---------------------------------------- *)
Lemma b7k_relro_img : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof.
intros a Ha. destruct VRO as [Hlo Hhi]. apply pa_relro_img. rewrite Hlo, Hhi.
unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Ha. lia.
Qed.
Lemma b7k_in_roP_img : forall a, in_roP SEGS RLO_A RHI_A a -> in_img SEGS a.
Proof.
intros a [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (b7k_relro_img a Hr)].
Qed.
(* a literal keeps its bytes where the image bytes are kept; its tail is ROM, its shadow pinned *)
Lemma b7k_lit_move : forall (rd : reader) (W' : world SEGS) mem' a s, sa_lit SEGS B rd a s ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
     rdW W' mem' x = rd x) ->
  sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros rd W' mem' a s (Ha & ((Hz & Hn) & _) & Hp & Hr & Hi) K.
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Hm & Ho & He). rewrite (K _ Hm Ho He). exact (Hz i Hi').
Qed.
Lemma b7k_cat_move : forall (rd : reader) (W' : world SEGS) mem', sa_cat SEGS B rd catA ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
     rdW W' mem' x = rd x) ->
  sa_cat SEGS B (rdW W' mem') catA.
Proof.
intros rd W' mem' (Hp & Hi & Hrows) K. split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (b7k_lit_move rd W' mem' tp _ Hl K)].
assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (rdword_ext rd (rdW W' mem')); [exact Htp|]. intros k Hk.
unfold pin_spec.row_addr, pin_spec.CAT_ROW in *.
destruct (Hi (catA + 296 * Z.of_nat i + k) ltac:(unfold pin_spec.CAT_BYTES; lia)) as (Hm & Ho & He).
exact (K _ Hm Ho He).
Qed.

(* ---------------------------------------- blocks and frames ---------------------------------------- *)
(* a range inside a live heap block is addressable, with its shadow words visible, at any state it is live
   (the image-A cross_check walk lane's cc_block_addr) *)
Lemma b7k_heap_addr : forall ly S (W : world SEGS) mem md q n,
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 <= n -> sa_addr (rdW W mem) q n.
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hq) Hn.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
pose proof alloc_ceiling_lt as Hac.
unfold sa_addr.
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin Hb ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin Hb ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin Hb ltac:(lia) Hn0).
Qed.
Lemma b7k_heap_bounds : forall ly S (W : world SEGS) mem md q n,
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 <= n ->
  exists b m, In (b, m) (ablocks B ly S) /\ b <= q /\ q + n <= b + req_size m /\ 4096 <= b /\
    b + req_size m <= alloc_ceiling /\ in_app b (req_size m).
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hq) Hn.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
exists b, m. split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Happ].
Qed.
Lemma b7k_heap_perm : forall ly S ly' S' q n, Permutation (ablocks B ly' S') (ablocks B ly S) ->
  sa_heap B ly S q n -> sa_heap B ly' S' q n.
Proof.
intros ly S ly' S' q n HP (b & m & Hin & Hb & Hq). exists b, m.
split; [exact (Permutation_in _ (Permutation_sym HP) Hin) | lia].
Qed.
(* a byte of the shadow band is in no app range *)
Lemma b7k_band_not_app : forall b n s, in_app b n -> SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> ~ (b <= s < b + n).
Proof.
intros b n s Happ Hs Hin.
unfold in_app, SHADOW_OFF, kLowShadowBeg, YG0f.kHighMemBeg in *. lia.
Qed.

(* ---------------------------------------- the entry facts ---------------------------------------- *)
Lemma b7k_cx : forall v, pf_cx B v ->
  0 < p_c v /\ p_c v mod 16 = 0 /\ Z.of_nat (length (p_s v)) <= 65535 /\
  sa_disj (p_t v) (seg_spec.cstr_span (p_t v) (p_s v)) (p_c v) seg_spec.SEG_C_SIZE /\
  alloc_ceiling <= ly_stk_lo (p_ly v) /\ ly_stk_lo (p_ly v) + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\
  pf_sp0 v mod 16 = 0.
Proof.
intros v (HPRE & _ & _ & Hc64 & _ & _ & _ & _ & (fe & (C0 & C16 & _ & _ & _ & _ & _ & _ & _ & _ & LS & _ & _ & DJ & _) & _)
  & _ & _).
pose proof HPRE as (_ & _ & _ & _ & _ & (Hal & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
assert (LSz : Z.of_nat (length (p_s v)) <= 65535)
  by (apply Nat2Z.inj_le in LS; change (Z.of_nat 65535) with 65535 in LS; exact LS).
unfold pf_sp0. rewrite SPF in Hslo. split; [lia|]. repeat split; first [exact C16 | exact LSz | exact DJ | lia].
Qed.
(* the realigned locals base s1 = (sp0 - 0x160) & -32 (pf_s1) *)
Definition b7k_s1v (sp0 : Z) : Z := (sp0 - 0x160) - (sp0 - 0x160) mod 32.
Lemma b7k_s1 : forall sp0, sp0 mod 16 = 0 ->
  sp0 - 0x180 < b7k_s1v sp0 <= sp0 - 0x160 /\ b7k_s1v sp0 mod 32 = 0 /\ b7k_s1v sp0 mod 16 = 0 /\
  (b7k_s1v sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H16. unfold b7k_s1v.
pose proof (Z.mod_pos_bound (sp0 - 0x160) 32 ltac:(lia)) as Hm.
pose proof (Z.div_mod (sp0 - 0x160) 32 ltac:(lia)) as Hd.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd16. rewrite H16 in Hd16.
split; [lia|].
replace ((sp0 - 0x160) - (sp0 - 0x160) mod 32) with (32 * ((sp0 - 0x160) / 32)) by lia.
split; [rewrite Z.mul_comm; apply Z_mod_mult|].
split; [replace (32 * ((sp0 - 0x160) / 32)) with ((2 * ((sp0 - 0x160) / 32)) * 16) by lia; apply Z_mod_mult|].
replace (32 * ((sp0 - 0x160) / 32) - sp0) with ((2 * ((sp0 - 0x160) / 32) - sp0 / 16) * 16) by lia.
apply Z_mod_mult.
Qed.
Lemma b7k_s1_eq : forall v, pf_s1 v = b7k_s1v (pf_sp0 v).
Proof. reflexivity. Qed.
Lemma b7k_frame : forall v pos lyc Sc Wc rX memc mdc,
  pf_fi B v pos lyc Sc Wc rX memc mdc ->
  In (5, pos) (frames Sc) /\ 4096 <= pf_F v pos /\ pf_F v pos + fs_frame_bytes 5 <= alloc_ceiling /\
  pf_F v pos mod 32 = 0 /\ in_app (pf_F v pos) (fs_frame_bytes 5) /\ frame_addr lyc 5 pos = pf_F v pos.
Proof.
intros v pos lyc Sc Wc rX memc mdc (HJ & Hly & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 5 pos HAR Hin) as (H4 & Hc & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 5 pos HAR Hin) as (Hal & Happ & _).
unfold pf_F. rewrite <- Hly.
split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Happ | reflexivity].
Qed.

(* ---------------------------------------- the cut facts at a later state ---------------------------------------- *)
Lemma b7k_sl_move : forall (rd rd' : reader) b L, pf_sl rd b L ->
  Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0x100) L -> 0 <= b -> b + 0x100 <= 2 ^ 64 ->
  (forall a, b <= a < 2 ^ 64 -> rd' a = rd a) -> pf_sl rd' b L.
Proof.
intros rd rd' b L HL HB Hb Hb2 K. unfold pf_sl in *. rewrite Forall_forall in HL, HB |- *.
intros ov Hin. rewrite <- (HL ov Hin). apply rdword_ext. intros k Hk.
pose proof (HB ov Hin). apply K. lia.
Qed.
Lemma b7k_PF_SL_offs : forall v pos, Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0x100) (PF_SL v pos).
Proof. intros v pos. unfold PF_SL. repeat constructor; cbn [fst]; lia. Qed.
(* what a later state must agree on for the cut facts to hold there: the stack from s1 up, the text and its NUL,
   the unowned image bytes, the class-5 frame and its shadow *)
Definition b7k_keeps (v : pfv) (pos : Z) (Wc : world SEGS) memc (W2 : world SEGS) mem2 : Prop :=
  (forall a, pf_s1 v <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a) /\
  (forall i, 0 <= i <= Z.of_nat (length (p_s v)) -> rdW W2 mem2 (p_t v + i) = rdW Wc memc (p_t v + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW Wc memc a) /\
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 \/
             pf_SH v pos <= a < pf_SH v pos + fs_frame_bytes 5 / 8 ->
     rdW W2 mem2 a = rdW Wc memc a).
Lemma b7k_base_move : forall (fx1 : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc ly2 S2 (W2 : world SEGS) regs2
  mem2 md2,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc sc ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 0 ->
  ly2 = lyc -> (exists f, S2 = set_fs f Sc) -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  b7k_keeps v pos Wc memc W2 mem2 ->
  (forall r, In r [2; 3; 4; 8; 9; 20] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 sc.
Proof.
intros fx1 v pos lyc Sc Wc rX memc mdc sc ly2 S2 W2 regs2 mem2 md2 (CX & FI & OBJ & SL & FSH) Hfx HJ2 Hly2
  (f2 & HS2) HP2 (K1 & K2 & K3 & K4) KR.
destruct (b7k_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (b7k_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
destruct FI as (HJ & Hly & (f & HSf) & HPerm & HSV & HFLW & HFRM & HTF & HC8 & HRG).
destruct OBJ as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
pose proof (proj1 HJ2) as HAR2. pose proof (proj1 HJ) as HAR.
pose proof alloc_ceiling_lt as Hac.
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
split; [exact CX|].
split.
{ split; [exact HJ2|]. split; [rewrite Hly2; exact Hly|].
  split; [exists f2; rewrite HS2, HSf; reflexivity|].
  split; [exact (Permutation_trans HP2 HPerm)|].
  split.
  { intros j r Hj. rewrite <- (HSV j r Hj). apply rdword_ext. intros k Hk.
    pose proof (proj1 (nth_error_Some PF_SAVED j) ltac:(rewrite Hj; discriminate)) as Hj13.
    unfold PF_SAVED in Hj13. cbn [length] in Hj13.
    apply K1. lia. }
  split.
  { rewrite <- HFLW. apply rdword_ext. intros k Hk. apply K4. left. lia. }
  split; [exact (fxrel_frm0 fx fx1 HFRM Hfx)|].
  split; [exact HTF|].
  split.
  { apply (b7k_sl_move (rdW Wc memc) (rdW W2 mem2) (pf_s1 v) [(0xc8, p_c v)] HC8);
      [apply Forall_cons; [cbn [fst]; lia | apply Forall_nil] | lia | lia |].
    intros a Ha. apply K1. exact Ha. }
  unfold pf_rg in *. rewrite Forall_forall in HRG |- *. intros rv Hin.
  rewrite (KR (fst rv)); [exact (HRG rv Hin)|].
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
split.
{ destruct (b7k_heap_bounds lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
    as (bt & mt & Hint & Hbt1 & Hbt2 & _ & _ & _).
  assert (HT2 : sa_heap B ly2 S2 (p_t v) (Z.of_nat (length (p_s v)) + 1)) by exact (b7k_heap_perm _ _ _ _ _ _ HP2 HT).
  assert (HC2 : sa_heap B ly2 S2 (p_c v) seg_spec.SEG_C_SIZE) by exact (b7k_heap_perm _ _ _ _ _ _ HP2 HC).
  split.
  { destruct STR as ((Hz & Hn) & _). split; [split; [|exact Hn]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      rewrite K2 by lia. exact (Hz i Hi).
    - intros x Hx. apply (AR_block_word_vis SEGS B ly2 S2 W2 mem2 md2 bt mt (p_t v + Z.of_nat (length (p_s v))) x HAR2).
      + exact (Permutation_in _ (Permutation_sym HP2) Hint).
      + lia.
      + lia. }
  split; [exact (b7k_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HT2 ltac:(lia))|].
  split; [exact HT2|].
  split; [exact (b7k_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HC2 ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact HC2|].
  split; [exact (b7k_cat_move _ W2 mem2 CAT K3)|].
  split; [intros x Hx; exact (b7k_lit_move _ W2 mem2 _ _ (LITS x Hx) K3)|].
  split; [intros a Hro Ho He; rewrite (K3 a (b7k_in_roP_img a Hro) Ho He); exact (ROD a Hro Ho He)|].
  exact (SSPX ly2 S2 W2 mem2 md2 HAR2). }
split.
{ apply (b7k_sl_move (rdW Wc memc) _ (pf_s1 v) _ SL (b7k_PF_SL_offs v pos)); [lia | lia |].
  intros a Ha. apply K1. exact Ha. }
intros i Hi. rewrite K4; [exact (FSH i Hi)|]. right. rewrite E5. change (2048 / 8) with 256. lia.
Qed.
(* the same for a step that writes some of the frame's 144 shadow cells (a scope in or out): b7k_keeps without its
   shadow clause (only the frame's BYTES kept), the new scope's cells as a premise, pf_base at the new scope sc'
   (asked by an image-A segment lane; b7k_base_move is its instance at sc' = sc) *)
Definition b7k_keeps_sc (v : pfv) (pos : Z) (Wc : world SEGS) memc (W2 : world SEGS) mem2 : Prop :=
  (forall a, pf_s1 v <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a) /\
  (forall i, 0 <= i <= Z.of_nat (length (p_s v)) -> rdW W2 mem2 (p_t v + i) = rdW Wc memc (p_t v + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW Wc memc a) /\
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 -> rdW W2 mem2 a = rdW Wc memc a).
Lemma b7k_keeps_sc_of : forall v pos Wc memc W2 mem2, b7k_keeps v pos Wc memc W2 mem2 -> b7k_keeps_sc v pos Wc memc W2 mem2.
Proof.
intros v pos Wc memc W2 mem2 (K1 & K2 & K3 & K4). split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
intros a Ha. apply K4. left. exact Ha.
Qed.
Lemma b7k_base_move_sc : forall (fx1 : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc sc' ly2 S2 (W2 : world SEGS)
  regs2 mem2 md2,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc sc ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 0 ->
  ly2 = lyc -> (exists f, S2 = set_fs f Sc) -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  b7k_keeps_sc v pos Wc memc W2 mem2 ->
  pf_fsh (rdW W2 mem2) (pf_SH v pos) sc' ->
  (forall r, In r [2; 3; 4; 8; 9; 20] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 sc'.
Proof.
intros fx1 v pos lyc Sc Wc rX memc mdc sc sc' ly2 S2 W2 regs2 mem2 md2 (CX & FI & OBJ & SL & FSH) Hfx HJ2 Hly2
  (f2 & HS2) HP2 (K1 & K2 & K3 & K4) FSH2 KR.
destruct (b7k_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (b7k_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
destruct FI as (HJ & Hly & (f & HSf) & HPerm & HSV & HFLW & HFRM & HTF & HC8 & HRG).
destruct OBJ as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
pose proof (proj1 HJ2) as HAR2. pose proof (proj1 HJ) as HAR.
pose proof alloc_ceiling_lt as Hac.
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
split; [exact CX|].
split.
{ split; [exact HJ2|]. split; [rewrite Hly2; exact Hly|].
  split; [exists f2; rewrite HS2, HSf; reflexivity|].
  split; [exact (Permutation_trans HP2 HPerm)|].
  split.
  { intros j r Hj. rewrite <- (HSV j r Hj). apply rdword_ext. intros k Hk.
    pose proof (proj1 (nth_error_Some PF_SAVED j) ltac:(rewrite Hj; discriminate)) as Hj13.
    unfold PF_SAVED in Hj13. cbn [length] in Hj13.
    apply K1. lia. }
  split.
  { rewrite <- HFLW. apply rdword_ext. intros k Hk. apply K4. lia. }
  split; [exact (fxrel_frm0 fx fx1 HFRM Hfx)|].
  split; [exact HTF|].
  split.
  { apply (b7k_sl_move (rdW Wc memc) (rdW W2 mem2) (pf_s1 v) [(0xc8, p_c v)] HC8);
      [apply Forall_cons; [cbn [fst]; lia | apply Forall_nil] | lia | lia |].
    intros a Ha. apply K1. exact Ha. }
  unfold pf_rg in *. rewrite Forall_forall in HRG |- *. intros rv Hin.
  rewrite (KR (fst rv)); [exact (HRG rv Hin)|].
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
split.
{ destruct (b7k_heap_bounds lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
    as (bt & mt & Hint & Hbt1 & Hbt2 & _ & _ & _).
  assert (HT2 : sa_heap B ly2 S2 (p_t v) (Z.of_nat (length (p_s v)) + 1)) by exact (b7k_heap_perm _ _ _ _ _ _ HP2 HT).
  assert (HC2 : sa_heap B ly2 S2 (p_c v) seg_spec.SEG_C_SIZE) by exact (b7k_heap_perm _ _ _ _ _ _ HP2 HC).
  split.
  { destruct STR as ((Hz & Hn) & _). split; [split; [|exact Hn]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      rewrite K2 by lia. exact (Hz i Hi).
    - intros x Hx. apply (AR_block_word_vis SEGS B ly2 S2 W2 mem2 md2 bt mt (p_t v + Z.of_nat (length (p_s v))) x HAR2).
      + exact (Permutation_in _ (Permutation_sym HP2) Hint).
      + lia.
      + lia. }
  split; [exact (b7k_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HT2 ltac:(lia))|].
  split; [exact HT2|].
  split; [exact (b7k_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HC2 ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact HC2|].
  split; [exact (b7k_cat_move _ W2 mem2 CAT K3)|].
  split; [intros x Hx; exact (b7k_lit_move _ W2 mem2 _ _ (LITS x Hx) K3)|].
  split; [intros a Hro Ho He; rewrite (K3 a (b7k_in_roP_img a Hro) Ho He); exact (ROD a Hro Ho He)|].
  exact (SSPX ly2 S2 W2 mem2 md2 HAR2). }
split; [|exact FSH2].
apply (b7k_sl_move (rdW Wc memc) _ (pf_s1 v) _ SL (b7k_PF_SL_offs v pos)); [lia | lia |].
intros a Ha. apply K1. exact Ha.
Qed.
(* after strspn: it writes only its window below s1, which is above every object below alloc_ceiling *)
Lemma b7k_keeps_low : forall v pos lyc Sc Wc rX memc mdc sc (W2 : world SEGS) mem2,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  (forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling \/ pf_s1 v <= a -> rdW W2 mem2 a = rdW Wc memc a) ->
  b7k_keeps v pos Wc memc W2 mem2.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc W2 mem2 (CX & FI & OBJ & _ & _) K.
destruct (b7k_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (b7k_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
pose proof (proj1 (proj1 FI)) as HAR.
destruct OBJ as (_ & _ & HT & _).
destruct (b7k_heap_bounds _ _ _ _ _ (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
  as (bt & mt & _ & Hb1 & Hb2 & Hb3 & Hb4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
split; [intros a Ha; apply K; lia|].
split; [intros i Hi; apply K; lia|].
split.
{ intros a Ha _ _. pose proof (pa_img_range a Ha). unfold kImgEnd in *. apply K; lia. }
intros a Ha. unfold pf_SH, shadow_addr in Ha. rewrite E5 in Ha. change (2048 / 8) with 256 in Ha.
pose proof (Z.div_lt_upper_bound (pf_F v pos) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
pose proof (Z.div_pos (pf_F v pos) 8 ltac:(lia) ltac:(lia)).
apply K; unfold SHADOW_OFF in *; lia.
Qed.
(* after a call made at sp = s1 whose footprint lies in the block c (refuse; any callee of that shape): its journal
   keeps the stack outside its window and footprint, the live blocks outside the footprint, the unowned image
   bytes and the entry's side-stack frames *)
Lemma b7k_keeps_call : forall v pos lyc Sc Wc rX memc mdc sc STKc FPc ly2 S2 (W2 : world SEGS) mem2 md2 k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STKc (pf_s1 v) FPc lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k ->
  (forall a, inFP FPc a -> p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) -> ~ YI16.sink_open_fp FPc ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  b7k_keeps v pos Wc memc W2 mem2.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc STKc FPc ly2 S2 W2 mem2 md2 k (CX & FI & OBJ & _ & _) HJc NFP HCl HP2.
destruct (b7k_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (b7k_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
pose proof (proj1 (proj1 FI)) as HAR.
destruct OBJ as (_ & _ & HT & _ & HC & _).
destruct (b7k_heap_bounds _ _ _ _ _ (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
  as (bt & mt & Hint & Hb1 & Hb2 & Hb3 & Hb4 & _).
destruct (b7k_heap_bounds _ _ _ _ _ (p_c v) seg_spec.SEG_C_SIZE HAR HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as (bc & mc & Hinc & Hc1 & Hc2 & Hc3 & Hc4 & Hcapp).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
(* the footprint lies in the block c *)
split.
{ intros a Ha. apply F1; [lia | lia | intros Hf; apply NFP in Hf; unfold seg_spec.SEG_C_SIZE in *; lia]. }
split.
{ intros i Hi. replace (p_t v + i) with (bt + (p_t v + i - bt)) by lia.
  apply (F2 bt mt (p_t v + i - bt)); [exact Hint | exact (Permutation_in _ (Permutation_sym HP2) Hint) | lia |].
  intros Hf. apply NFP in Hf. unfold sa_disj, seg_spec.cstr_span in HDJ.
  pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)). lia. }
split.
{ intros a Ha Ho He. apply F3; [exact Ha | exact Ho | exact He |].
  apply fp_spares_closed; [exact HCl|].
  intros Hf. apply NFP in Hf. exact (blk_img SEGS B LAWS lyc Sc Wc memc mdc bc mc a HAR Hinc ltac:(lia) Ha). }
intros a Ha. apply (F4 5 pos a Hfin).
- unfold frame_rng, in_zr. cbn [fst snd]. rewrite HFE. unfold pf_SH in Ha. exact Ha.
- intros Hf. apply NFP in Hf. destruct Ha as [Ha | Ha].
  + pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mc 5 pos HAR Hinc Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFE in Hd. unfold seg_spec.SEG_C_SIZE in *. lia.
  + unfold pf_SH, shadow_addr in Ha. rewrite E5 in Ha. change (2048 / 8) with 256 in Ha.
    pose proof (Z.div_lt_upper_bound (pf_F v pos) 8 (2 ^ 44 - 256) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (pf_F v pos) 8 ltac:(lia) ltac:(lia)).
    apply (b7k_band_not_app bc (req_size mc) a Hcapp); [lia|].
    unfold seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* after refuse: its footprint refuse_W lies in the block c (refusal[n], n_refusals, refused) *)
Lemma b7k_keeps_refuse : forall v pos lyc Sc Wc rX memc mdc sc cf ly2 S2 (W2 : world SEGS) mem2 md2 k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_refuse (pf_s1 v) (refuse_W (p_c v) cf) lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  b7k_keeps v pos Wc memc W2 mem2.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc cf ly2 S2 W2 mem2 md2 k HB HJc HP2.
destruct (b7k_cx v (proj1 HB)) as (Hc0 & _).
apply (b7k_keeps_call v pos lyc Sc Wc rX memc mdc sc STK_refuse (refuse_W (p_c v) cf) ly2 S2 W2 mem2 md2 k HB HJc);
  [| exact (b7k_refuse_W_pos _ cf Hc0) | exact HP2].
intros a Ha. apply b7k_refuse_W_in_block in Ha. unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW,
  seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* cur_name's bytes are in the frame *)
Lemma b7k_nm_move : forall v pos (rd rd' : reader) nm, pf_nm rd (pf_F v pos + PF_O_CN) nm ->
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 -> rd' a = rd a) ->
  pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros v pos rd rd' nm (f & Hb & He) K. exists f. split; [|exact He].
intros i Hi. destruct He as (Hl & _). rewrite Hl in Hi. rewrite K; [exact (Hb i ltac:(lia))|].
change (fs_frame_bytes 5) with 2048. unfold PF_O_CN. lia.
Qed.

End e.
End f.
End d.
