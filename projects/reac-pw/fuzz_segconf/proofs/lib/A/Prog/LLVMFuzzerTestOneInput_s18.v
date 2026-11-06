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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 1860 of its 1907 lines of code are new or changed and 406 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): segment S09 of the walk of
   the test harness's entry function LLVMFuzzerTestOneInput (0x84d34), file group _s18: from the cut K854a0
   (0x854a0) to the cut K8559c (0x8559c), the statement lt_seg_S09_stmt of LLVMFuzzerTestOneInput_defs.v:
   check_segments, check 19, then the per-segment loop 0x854f0 <- 0x85588 of nine calls (reac_segconf_role,
   check_role, reac_segconf_model, check_model, reac_segconf_ignored, check_ignore, reac_segconf_role_file,
   reac_segconf_ignore_file, check_provenance) and check 20.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; checker (fresh, read-only): CONFIRM; none: written new)

   THE FORM: one lemma per stretch between two calls (s9_head, s9_cs, s9_T0 .. s9_T9), each a paj_run_tok /
   paj_run_to_tok run from a seed whose regions are the slots, shadow bytes and model cells the stretch reads or
   writes, then the callee's contract through cl_callS (cl_callS_wide for reac_segconf_role, whose out is r, the
   class-3 frame's object at FR + 176). Between the points the invariant is s9M (the cut's lt_core with r's shadow as
   the point says, the blocks c and m, the slots, lt_cm) and s9R (the loop's registers); s9M_agree carries it across a
   run or a call from the bytes s9_agree names. The loop closes by induction on 32 - i (m->n <= 32).
   Every check's abort is refuted by its contract's pre: the reader queries' posts (r's value, the model / role_file /
   ignore_file pointers) and SegModel.segconf_agrees (s18_harness, the kit) give check_seg for every segment.
   Checks 19 and 20 read SH(m + 0x2000), 0 because m's 9236 bytes are addressable (s9_mn_shadow). *)

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaLibF PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase SegBase SegObj SegRep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s18k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_segconf_find_c check_segments_c
  reac_segconf_role_c check_role_c reac_segconf_model_c check_model_c reac_segconf_ignored_c check_ignore_c
  reac_segconf_role_file_c reac_segconf_ignore_file_c check_provenance_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the return points and loop points of S09 (offsets from BASE = 0x84d34) *)
Definition LO9_CS : Z := 0x778.    (* 0x854ac: check_segments returned *)
Definition LO9_LOOP : Z := 0x7bc.  (* 0x854f0: the head of the per-segment loop, turn i *)
Definition LO9_R1 : Z := 0x7d8.    (* 0x8550c: reac_segconf_role returned *)
Definition LO9_R2 : Z := 0x7e4.    (* 0x85518: check_role returned *)
Definition LO9_R3 : Z := 0x7f0.    (* 0x85524: reac_segconf_model returned *)
Definition LO9_R4 : Z := 0x7f8.    (* 0x8552c: check_model returned *)
Definition LO9_R5 : Z := 0x804.    (* 0x85538: reac_segconf_ignored returned *)
Definition LO9_R6 : Z := 0x80c.    (* 0x85540: check_ignore returned *)
Definition LO9_R7 : Z := 0x818.    (* 0x8554c: reac_segconf_role_file returned *)
Definition LO9_R8 : Z := 0x828.    (* 0x8555c: reac_segconf_ignore_file returned *)
Definition LO9_R9 : Z := 0x838.    (* 0x8556c: check_provenance returned *)
(* r (frame + 176) usable, every other object out of scope *)
Definition LFO_R : lfo := mkLFO false false true false false.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* the memory and frame part every point of S09 keeps: K854a0's facts with r's shadow as o says *)
Definition s9M (cx : lcx) ly S (W : world SEGS) regs mem md k acc (o : lfo) (c m : Z) : Prop :=
  lt_core B MT cx ly S W regs mem md k acc 6 o [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_slots cx (rdW W mem) (LT_L cx c m) /\ lt_cm (rdW W mem) c m (x_run cx).
(* the loop's registers (0x854c8 .. 0x854ec): s2 = i, s3 = &m->seg[i], s5 = SH(FR), s6 = 4, s7 = 90, s8 = -8,
   s10 = c, s11 = SH(m + 0x2000) *)
Definition s9R (cx : lcx) (i : nat) (regs : bvmap 5 word) (c m : Z) : Prop :=
  getr regs 18 = w64 (Z.of_nat i) /\ getr regs 19 = w64 (seg_spec.mseg_addr m i) /\
  getr regs 21 = w64 (x_sh cx) /\ getr regs 22 = w64 4 /\ getr regs 23 = w64 90 /\
  getr regs 24 = w64 (-8) /\ getr regs 26 = w64 c /\ getr regs 27 = w64 (shadow_addr (m + seg_spec.MC_N)).

Lemma s9_base_facts : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - LTOI_FRAME_MAX <= x_s1 cx <= x_sp0 cx - LT_FRAME /\
  getr (x_regs cx) 3 = w64 (as_gp B) /\ getr (x_regs cx) 4 = w64 (as_tp B).
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0 in *. unfold LTOI_FRAME_MAX, LT_FRAME.
set (sp := spZ (x_regs cx)) in *.
assert (Hm : 0 <= (sp - 320) mod 32 < 32) by (apply Z.mod_pos_bound; lia).
assert (Hm16 : (sp - 320) mod 32 = 0 \/ (sp - 320) mod 32 = 16).
{ pose proof (Z.div_mod sp 16 ltac:(lia)) as D. rewrite Hal in D.
  replace (sp - 320) with (16 * (sp / 16 - 20)) by lia.
  pose proof (Z.mod_pos_bound (sp / 16 - 20) 2 ltac:(lia)) as M2.
  pose proof (Z.div_mod (sp / 16 - 20) 2 ltac:(lia)) as D2.
  destruct (Z.eq_dec ((sp / 16 - 20) mod 2) 0) as [E|E].
  - left. rewrite D2, E. replace (16 * (2 * ((sp / 16 - 20) / 2) + 0)) with (((sp / 16 - 20) / 2) * 32) by lia.
    apply Z.mod_mul. lia.
  - right. assert (E1 : (sp / 16 - 20) mod 2 = 1) by lia. rewrite D2, E1.
    replace (16 * (2 * ((sp / 16 - 20) / 2) + 1)) with (16 + ((sp / 16 - 20) / 2) * 32) by lia.
    rewrite Z.mod_add by lia. reflexivity. }
split; [exact Hal|]. split; [lia|]. split.
{ rewrite Zminus_mod, Z.mod_mod, Z.sub_diag, Z.mod_0_l by lia. reflexivity. }
split; [lia|]. split; [exact Hgp | exact Htp].
Qed.

(* the walk's journal at a point of S09 (lt_frame's first conjunct) *)
Definition s9J (cx : lcx) ly S (W : world SEGS) mem md k : Prop :=
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k.

Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* the class-3 frame at a point: live in S, at frame_addr of the point's layout, 32-aligned, below the ceiling *)
Lemma s9_frame_at : forall cx ly S W mem md k, lt_base B MT cx -> s9J cx ly S W mem md k ->
  AR SEGS B ly S W mem md /\ In (LT_FCLS, x_fpos cx) (frames S) /\ x_fr cx = frame_addr ly LT_FCLS (x_fpos cx) /\
  x_fr cx mod 32 = 0 /\ 4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512.
Proof.
intros cx ly S W mem md k HB HJ.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : x_fr cx = frame_addr ly LT_FCLS (x_fpos cx)).
{ unfold x_fr, frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
pose proof (al_frames _ _ LAWS ly S W mem md _ _ HAR Hin) as (Hal & Happ & _).
pose proof (frames_bounds SEGS B LAWS ly S W mem md _ _ HAR Hin) as (H1 & H2 & _).
change (fs_frame_bytes LT_FCLS) with 512 in *.
rewrite <- EF in Hal, Happ, H1, H2. split; [exact HAR|]. split; [exact Hin|]. split; [exact EF|].
split; [exact Hal|]. split; [exact H1|]. split; [exact H2 | exact Happ].
Qed.

(* a live block of an AR state is a harness block: its alignment, its place and its shadow from AR's laws *)
Lemma s9_hblk_AR : forall ly S W mem md p n, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n ->
  lt_hblk B ly S (rdW W mem) p n.
Proof.
intros ly S W mem md p n HAR Hin Hn.
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (H16 & H4096 & Hceil & Happ & _).
pose proof (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hhull).
assert (Er : req_size n = n) by (unfold req_size; replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
rewrite Er in *. pose proof ASAN_CEIL_range as [CR _]. pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
unfold sa_addr. split; [lia|]. split; [unfold ASAN_CEIL in CR; lia|]. split.
{ unfold amem_range. destruct Happ as (_ & [Hl | (Hh1 & Hh2)]); [left | right];
  unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia. }
split; [|intros _; exact Hhull].
exact (range_addressable_of_block SEGS B LAWS ly S W mem md p n p n HAR Hin ltac:(lia) ltac:(rewrite Er; lia)).
Qed.

(* ---- the image facts survive any change that keeps the image's bytes [0x10000, kImgEnd) ---- *)
Lemma s9_img_bound : forall a, in_img SEGS a -> 0x10000 <= a < kImgEnd.
Proof. intros a H. exact (pa_img_range a H). Qed.
Lemma s9_rdword_kept : forall (rd rd' : reader) a v, rdword rd a = Some v ->
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd' a = Some v.
Proof. intros rd rd' a v H K. rewrite (rdword_ext rd rd' a) by (intros k Hk; apply K; lia). exact H. Qed.
Lemma s9_lit_kept : forall (W W' : world SEGS) mem mem' a s,
  (forall x, 0x10000 <= x < kImgEnd -> rdW W' mem' x = rdW W mem x) ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros W W' mem mem' a s K (Ha & ((Hz & Hn) & _) & Hp & Hr & Hi).
split; [exact Ha|]. split; [|split; [exact Hp | split; [exact Hr | exact Hi]]].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hr)].
intros i Hl. rewrite K; [exact (Hz i Hl)|].
apply s9_img_bound. refine (proj1 (Hi (a + Z.of_nat i) _)). rewrite length_app in Hl; cbn [length] in Hl. lia.
Qed.
Lemma s9_img_kept : forall cx (W W' : world SEGS) mem mem',
  (forall x, 0x10000 <= x < kImgEnd -> rdW W' mem' x = rdW W mem x) ->
  lt_img B cx (rdW W mem) -> lt_img B cx (rdW W' mem').
Proof.
intros cx W W' mem mem' K (HRO & HIMG & HGI).
split; [|split].
- intros a Hro Ho He. rewrite K; [exact (HRO a Hro Ho He)|].
  destruct Hro as [(sg & Hs & _ & Hr) | Hr]; [apply s9_img_bound; exists sg; split; [exact Hs | exact Hr]|].
  unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
- destruct HIMG as (HM & HMi & HFZ & HRC & HCAT & HCATa & HW & HR & HSSP & HLp & HLt & HLi & HD1 & HD2 & HD3).
  split; [|split; [exact HMi|split; [|split; [|split; [|split; [exact HCATa|split; [|split; [|split]]]]]]]].
  + intros k0 Hk0. rewrite K; [exact (HM k0 Hk0)|]. apply s9_img_bound.
    exact (proj1 (HMi (mod40A + Z.of_nat k0) ltac:(lia))).
  + intros s Hs. destruct (HFZ s Hs) as [H1 H2]. split; [exact (s9_lit_kept W W' mem mem' _ _ K H1) | exact H2].
  + intros s Hs. destruct (HRC s Hs) as [H1 H2]. split; [exact (s9_lit_kept W W' mem mem' _ _ K H1) | exact H2].
  + destruct HCAT as (Hcp & Hci & Hrows). split; [exact Hcp|]. split; [exact Hci|].
    intros i Hi. destruct (Hrows i Hi) as (tp & Htp & Hl). exists tp. split; [|exact (s9_lit_kept W W' mem mem' _ _ K Hl)].
    apply (s9_rdword_kept _ _ _ _ Htp). intros x Hx. apply K. apply s9_img_bound. apply (proj1 (Hci x ltac:(
      unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *; lia))).
  + destruct HW as (Hwp & Hwi & Hrows). split; [exact Hwp|]. split; [exact Hwi|].
    intros i Hi. destruct (Hrows i Hi) as (wp & Hwp' & Hl). exists wp. split; [|exact (s9_lit_kept W W' mem mem' _ _ K Hl)].
    apply (s9_rdword_kept _ _ _ _ Hwp'). intros x Hx. apply K. apply s9_img_bound. apply (proj1 (Hwi x ltac:(lia))).
  + destruct HR as (Hrp & Hri & Hrows). split; [exact Hrp|]. split; [exact Hri|].
    intros i Hi k0 Hk0. rewrite K; [exact (Hrows i Hi k0 Hk0)|]. apply s9_img_bound.
    apply (proj1 (Hri (rolesA + 4 * Z.of_nat i + Z.of_nat k0) ltac:(lia))).
  + destruct HSSP as (Hg & g & Hgv). split.
    * apply (s9_rdword_kept _ _ _ _ Hg). intros x Hx. apply K. unfold gotwA, kImgEnd in *. lia.
    * exists g. apply (s9_rdword_kept _ _ _ _ Hgv). intros x Hx. apply K. unfold guardA, kImgEnd in *. lia.
  + split; [exact HLp|]. split; [exact HLt|]. split; [exact HLi|]. split; [exact HD1|]. split; [exact HD2 | exact HD3].
- intros i Hi. rewrite K; [exact (HGI i Hi)|]. destruct HIMG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLi & _).
  apply s9_img_bound. apply (proj1 (HLi (longlA + LONGL_W + i) ltac:(unfold LONGL_W, LONGL_N in *; lia))).
Qed.

(* ---- the bytes a point of S09 reads, but r's shadow byte SH(FR) + 22 (and r itself, which s9M does not read) ---- *)
Definition s9_agree (cx : lcx) (c m : Z) (rd rd' : reader) : Prop :=
  (forall a, 0x10000 <= a < kImgEnd -> rd' a = rd a) /\
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE -> rd' a = rd a) /\
  (forall a, m <= a < m + seg_spec.SEG_M_SIZE -> rd' a = rd a) /\
  (forall j, 0 <= j < 36 -> j <> 22 -> rd' (x_sh cx + j) = rd (x_sh cx + j)) /\
  (forall j, (0 <= j < 24 \/ LT_FLAGW <= j < LT_FLAGW + 8) -> rd' (x_fr cx + j) = rd (x_fr cx + j)) /\
  (forall a, x_s1 cx <= a < x_sp0 cx -> rd' a = rd a).

Hypothesis MTFL : ameter_fs_laws MT.

Lemma s9_LT_L_off : forall cx c m o v, In (o, v) (LT_L cx c m) -> 0 <= o <= 184.
Proof.
intros cx c m o v Hin. unfold LT_L in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- _; lia|]). destruct Hin.
Qed.

Lemma s9M_agree : forall cx ly S W regs mem md k acc o o' c m ly2 S2 W2 regs2 mem2 md2,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  s9J cx ly2 S2 W2 mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  s9_agree cx c m (rdW W mem) (rdW W2 mem2) ->
  rdW W2 mem2 (x_sh cx + 22) = Some (if fo_r o' then 4 else 0xf8) ->
  fo_v o' = fo_v o -> fo_label o' = fo_label o -> fo_probe o' = fo_probe o -> fo_n o' = fo_n o ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  (S2 = S \/ exists f, S2 = set_fs f S) ->
  s9M cx ly2 S2 W2 regs2 mem2 md2 k acc o' c m.
Proof.
intros cx ly S W regs mem md k acc o o' c m ly2 S2 W2 regs2 mem2 md2 HB HM HJ2 E2 E3 E4 E8 E9 HAG Hr22 Ev El Ep En HP HS2.
destruct HM as ((HFR & HIMG & HBL & HBUD) & HC & HMb & HSL & HCM).
destruct HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSAV & W0 & W8 & W16 & W504 & W176 & HZS).
destruct HAG as (KI & KC & KM & KS & KF & KK).
pose proof (s9_base_facts cx HB) as (Hal & Hsp0 & Hs1a & Hs1 & _ & _).
pose proof HJ2 as (HAR2 & _).
unfold LTOI_FRAME_MAX, LT_FRAME in Hs1.
assert (KW : forall a v, rdword (rdW W mem) a = Some v -> x_s1 cx <= a -> a + 8 <= x_sp0 cx ->
  rdword (rdW W2 mem2) a = Some v) by (intros a v H H1 H2; apply (s9_rdword_kept _ _ _ _ H); intros x Hx; apply KK; lia).
assert (KFW : forall j v, rdword (rdW W mem) (x_fr cx + j) = Some v -> (j = 0 \/ j = 8 \/ j = 16 \/ j = LT_FLAGW) ->
  rdword (rdW W2 mem2) (x_fr cx + j) = Some v).
{ intros j v H Hj. apply (s9_rdword_kept _ _ _ _ H). intros x Hx.
  replace x with (x_fr cx + (x - x_fr cx)) by lia. apply KF. unfold LT_FLAGW in *. lia. }
split; [split; [|split; [|split]]|split; [|split; [|split]]].
- (* lt_frame *)
  split; [exact HJ2|]. split; [unfold spZ in *; rewrite E2; exact R2|].
  split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. split; [rewrite E8; exact R8|].
  split; [rewrite E9; exact R9|]. split.
  { intros i r Hi. pose proof (proj1 (nth_error_Some LT_SAVED i) ltac:(rewrite Hi; discriminate)) as Hl.
    cbn [length LT_SAVED] in Hl. apply KW; [exact (HSAV i r Hi) | lia | lia]. }
  split; [replace (x_fr cx) with (x_fr cx + 0) by lia; apply KFW; [rewrite Z.add_0_r; exact W0 | lia]|].
  split; [apply KFW; [exact W8 | lia]|]. split; [apply KFW; [exact W16 | lia]|].
  split; [apply KFW; [exact W504 | lia]|]. split; [apply KW; [exact W176 | lia | lia]|].
  intros i Hi. rewrite lt_fsh_len in Hi.
  destruct (Nat.eq_dec i 22) as [->|Hne].
  + change (Z.of_nat 22) with 22. rewrite Hr22. destruct o' as [[] [] [] [] []]; reflexivity.
  + rewrite KS by lia. rewrite (HZS i ltac:(rewrite lt_fsh_len; exact Hi)). f_equal.
    destruct o as [v1 l1 r1 p1 n1], o' as [v2 l2 r2 p2 n2]. cbn [fo_v fo_label fo_probe fo_n] in *. subst v2 l2 p2 n2.
    destruct v1, l1, r1, r2, p1, n1; cbn [lt_fsh];
    do 36 (destruct i as [|i]; [first [reflexivity | lia] |]); lia.
- exact (s9_img_kept cx W W2 mem mem2 KI HIMG).
- unfold lt_blocks in *. exact (perm_trans HP HBL).
- destruct HBUD as (Hk & Hr & Hkr & Hle & Hacc & Hacr). split; [exact Hk|]. split; [exact Hr|]. split; [exact Hkr|].
  split; [|split; [exact Hacc | exact Hacr]].
  destruct HS2 as [-> | (f & ->)]; [exact Hle | exact (mo_le_set_fs_r MT MTFL _ _ _ _ Hle)].
- destruct HC as (Hin & _). apply (s9_hblk_AR ly2 S2 W2 mem2 md2 c _ HAR2); [|unfold seg_spec.SEG_C_SIZE; lia].
  exact (Permutation_in _ (Permutation_sym HP) Hin).
- destruct HMb as (Hin & _). apply (s9_hblk_AR ly2 S2 W2 mem2 md2 m _ HAR2); [|unfold seg_spec.SEG_M_SIZE; lia].
  exact (Permutation_in _ (Permutation_sym HP) Hin).
- intros o0 v Hin. pose proof (s9_LT_L_off cx c m o0 v Hin) as Ho. apply KW; [exact (HSL o0 v Hin) | lia | lia].
- destruct HCM as ((bs & Hbs & Henc) & (bs' & Hbs' & Henc')). split.
  + exists bs. split; [|exact Henc]. intros i Hi. rewrite KC; [exact (Hbs i Hi)|].
    pose proof Henc as (Hlen & _). lia.
  + exists bs'. split; [|exact Henc']. intros i Hi. rewrite KM; [exact (Hbs' i Hi)|].
    pose proof Henc' as (Hlen & _). lia.
Qed.

(* ---- where the bytes of s9_agree lie: below the ceiling or in the harness's own stack frame, never r's shadow
   byte nor r ---- *)
Definition s9_P (cx : lcx) (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ a <> x_sh cx + 22 /\ ~ (x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) /\
  (a < alloc_ceiling \/ x_s1 cx <= a).

Lemma s9_blk_frame_apart : forall ly S W mem md p n cid pos a, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> In (cid, pos) (frames S) -> p <= a < p + req_size n ->
  ~ (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid).
Proof.
intros ly S W mem md p n cid pos a HAR Hb Hf Ha Hfa.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [HP _].
pose proof (pairwise_In zdisjoint _ (p, req_size n) (frame_addr ly cid pos, fs_frame_bytes cid) _ _ eq_refl HP
  (in_map (fun b => (fst b, req_size (snd b))) _ _ Hb)
  (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hf)) as HD.
unfold zdisjoint in HD. cbn [fst snd] in HD. lia.
Qed.

Lemma s9_classes : forall cx ly S W regs mem md k acc o c m,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  (forall a, 0x10000 <= a < kImgEnd -> s9_P cx a) /\
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE -> s9_P cx a) /\
  (forall a, m <= a < m + seg_spec.SEG_M_SIZE -> s9_P cx a) /\
  (forall j, 0 <= j < 36 -> j <> 22 -> s9_P cx (x_sh cx + j)) /\
  (forall j, (0 <= j < 24 \/ LT_FLAGW <= j < LT_FLAGW + 8) -> s9_P cx (x_fr cx + j)) /\
  (forall a, x_s1 cx <= a < x_sp0 cx -> s9_P cx a) /\
  (0 <= x_sh cx + 22 < alloc_ceiling /\ ~ (x_fr cx + FO_R <= x_sh cx + 22 < x_fr cx + FO_R + 4)).
Proof.
intros cx ly S W regs mem md k acc o c m HB HM.
destruct HM as ((HFR & _) & HC & HMb & _).
pose proof HFR as (HJ & _).
destruct (s9_frame_at cx ly S W mem md k HB HJ) as (HAR & Hin & EF & Hfa & Hf4 & Hfc & Happ).
pose proof (s9_base_facts cx HB) as (Hal & Hsp0 & Hs1a & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_img_cover ly S md (proj1 (proj2 HAR))) as [IC1 IC2].
assert (Hfr8 : x_fr cx = 8 * (x_fr cx / 8)).
{ pose proof (Z.div_mod (x_fr cx) 32 ltac:(lia)) as D. rewrite Hfa, Z.add_0_r in D.
  rewrite D at 2. replace (32 * (x_fr cx / 32)) with ((4 * (x_fr cx / 32)) * 8) by lia.
  rewrite Z.div_mul by lia. lia. }
assert (Hsh : x_sh cx = SHADOW_OFF + x_fr cx / 8) by reflexivity.
unfold SHADOW_OFF in Hsh.
(* a byte of r is a byte of the frame, apart from the image and from every block *)
assert (Rimg : forall a, x_fr cx + FO_R <= a < x_fr cx + FO_R + 4 -> ~ (0x10000 <= a < kImgEnd)).
{ intros a Ha Hi. destruct (al_client_img _ _ LAWS ly S W mem md a HAR) as [Hn _].
  - right; left. exists LT_FCLS, (x_fpos cx). split; [exact Hin|]. rewrite <- EF.
    change (fs_frame_bytes LT_FCLS) with 512. unfold FO_R in Ha. lia.
  - apply Hn. unfold in_zr. lia. }
assert (Rblk : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  ~ (x_fr cx + FO_R <= a < x_fr cx + FO_R + 4)).
{ intros p n a Hb Ha Hr. apply (s9_blk_frame_apart ly S W mem md p n LT_FCLS (x_fpos cx) a HAR Hb Hin Ha).
  rewrite <- EF. change (fs_frame_bytes LT_FCLS) with 512. unfold FO_R in Hr. lia. }
assert (Rsh : forall j, 0 <= j < 36 -> ~ (x_fr cx + FO_R <= x_sh cx + j < x_fr cx + FO_R + 4)).
{ intros j Hj Hr. rewrite Hsh in Hr. unfold FO_R in Hr. destruct Happ as (_ & [Hl | (Hh & _)]);
  unfold kLowShadowBeg, kHighMemBeg in *; lia. }
assert (Hshc : x_sh cx + 36 <= alloc_ceiling) by (rewrite Hsh; lia).
assert (Hshl : 0x7fff8000 <= x_sh cx) by (rewrite Hsh; lia).
destruct HC as (Hcin & Hc4 & _). destruct HMb as (Hmin & Hm4 & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcin) as (_ & _ & Hcc & Hcapp & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & Hmapp & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc, Hcapp.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc, Hmapp.
assert (Rsh22 : forall a, app_addr a -> a <> x_sh cx + 22).
{ intros a [_ [Ha | [Ha _]]] E; rewrite E, Hsh in Ha; unfold kLowShadowBeg, kHighMemBeg in Ha; lia. }
split; [|split; [|split; [|split; [|split; [|split]]]]].
- intros a Ha. split; [unfold kImgEnd in *; lia|]. split; [unfold kImgEnd in *; lia|].
  split; [intros Hr; exact (Rimg a Hr Ha) | left; unfold kImgEnd in *; lia].
- intros a Ha. split; [unfold seg_spec.SEG_C_SIZE in *; lia|].
  split; [apply Rsh22; exact (in_app_addr _ _ a Hcapp Ha)|].
  split; [apply (Rblk c seg_spec.SEG_C_SIZE a Hcin); change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE; lia|].
  left; lia.
- intros a Ha. split; [unfold seg_spec.SEG_M_SIZE in *; lia|].
  split; [apply Rsh22; exact (in_app_addr _ _ a Hmapp Ha)|].
  split; [apply (Rblk m seg_spec.SEG_M_SIZE a Hmin); change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE; lia|].
  left; lia.
- intros j Hj Hne. split; [lia|]. split; [lia|]. split; [exact (Rsh j Hj) | left; lia].
- intros j Hj. unfold LT_FLAGW in Hj. split; [lia|].
  split; [apply Rsh22; exact (in_app_addr _ _ (x_fr cx + j) Happ ltac:(lia))|]. split; [unfold FO_R; lia | left; lia].
- intros a Ha. split; [lia|]. split; [lia|]. split; [unfold FO_R; lia | right; lia].
- split; [lia | exact (Rsh 22 ltac:(lia))].
Qed.

(* a call that keeps every byte outside its window [S1 - STK1, S1) and outside r *)
Lemma s9_agree_kept : forall cx ly S W regs mem md k acc o c m regsc W2 mem2 STK1 (E : Z -> Prop),
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  spZ regsc = x_s1 cx -> 0 <= STK1 -> LTOI_FRAME_MAX + STK1 <= STK_LLVMFuzzerTestOneInput ->
  sa_kept SEGS W mem W2 mem2 regsc STK1 E ->
  (forall a, E a -> x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
  s9_agree cx c m (rdW W mem) (rdW W2 mem2) /\ rdW W2 mem2 (x_sh cx + 22) = rdW W mem (x_sh cx + 22).
Proof.
intros cx ly S W regs mem md k acc o c m regsc W2 mem2 STK1 E HB HM Hsp HS1 HS2 HK HE.
pose proof (s9_base_facts cx HB) as (Hal & Hsp0 & Hs1a & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
assert (KP : forall a, s9_P cx a -> rdW W2 mem2 a = rdW W mem a).
{ intros a (Ha & _ & Hr & Hlo). apply HK; [exact Ha | rewrite Hsp; lia | intros He; exact (Hr (HE a He))]. }
destruct (s9_classes cx ly S W regs mem md k acc o c m HB HM) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
split; [|apply HK; [lia | rewrite Hsp; lia | intros He; exact (P8 (HE _ He))]].
split; [intros a Ha; exact (KP a (P1 a Ha))|]. split; [intros a Ha; exact (KP a (P2 a Ha))|].
split; [intros a Ha; exact (KP a (P3 a Ha))|]. split; [intros j Hj Hn; exact (KP _ (P4 j Hj Hn))|].
split; [intros j Hj; exact (KP _ (P5 j Hj)) | intros a Ha; exact (KP a (P6 a Ha))].
Qed.

(* a run whose only stores are r's shadow byte and r *)
Lemma s9_agree_win : forall cx ly S W regs mem md k acc o c m (W2 : world SEGS) mem2,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> x_sh cx + 22 -> ~ (x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
    rdW W2 mem2 a = rdW W mem a) ->
  s9_agree cx c m (rdW W mem) (rdW W2 mem2).
Proof.
intros cx ly S W regs mem md k acc o c m W2 mem2 HB HM HK.
assert (KP : forall a, s9_P cx a -> rdW W2 mem2 a = rdW W mem a) by (intros a (Ha & H22 & Hr & _); exact (HK a Ha H22 Hr)).
destruct (s9_classes cx ly S W regs mem md k acc o c m HB HM) as (P1 & P2 & P3 & P4 & P5 & P6 & _).
split; [intros a Ha; exact (KP a (P1 a Ha))|]. split; [intros a Ha; exact (KP a (P2 a Ha))|].
split; [intros a Ha; exact (KP a (P3 a Ha))|]. split; [intros j Hj Hn; exact (KP _ (P4 j Hj Hn))|].
split; [intros j Hj; exact (KP _ (P5 j Hj)) | intros a Ha; exact (KP a (P6 a Ha))].
Qed.

(* ---- what every call of S09 asks of the caller's frame (cl_callS's premises), at sp = S1 ---- *)
Lemma s9_call_frame : forall cx ly S W regs mem md k acc o c m (regsc : bvmap 5 word),
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  getr regsc 2 = getr regs 2 -> getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
  getr regsc 8 = getr regs 8 ->
  spZ regsc = x_sp0 cx + (x_s1 cx - x_sp0 cx) /\ (x_s1 cx - x_sp0 cx) mod 16 = 0 /\ x_s1 cx - x_sp0 cx <= 0 /\
  getr regsc 3 = w64 (as_gp B) /\ getr regsc 4 = w64 (as_tp B) /\
  (exists ch, achain ly (rdW W mem) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regsc) ch) /\
  arodata_okP SEGS RLO_A RHI_A B (rdW W mem) /\ st_nev S <= EV_MAX /\
  (forall STK1, In STK1 LTOI_CALLEE_STKS -> 0 <= STK1 /\ STK1 - (x_s1 cx - x_sp0 cx) <= STK_LLVMFuzzerTestOneInput).
Proof.
intros cx ly S W regs mem md k acc o c m regsc HB HM E2 E3 E4 E8.
pose proof (s9_base_facts cx HB) as (Hal & Hsp0 & Hs1a & Hs1 & Hgp & Htp).
pose proof HB as (_ & HPRES & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV & _).
destruct HM as ((HFR & (HRO & _) & _ & HBUD) & _).
destruct HFR as (HJ & R2 & R3 & R4 & R8 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HBUD as (Hk & _ & Hkr & _).
pose proof asan_consts as (C1 & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
assert (Hsp : spZ regsc = x_s1 cx).
{ unfold spZ. rewrite E2, R2. apply unsigned_lit_small. lia. }
assert (Hd : (x_s1 cx - x_sp0 cx) mod 16 = 0).
{ pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)) as D1. pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D2.
  rewrite Hs1a in D1. rewrite Hal in D2.
  replace (x_s1 cx - x_sp0 cx) with ((2 * (x_s1 cx / 32) - x_sp0 cx / 16) * 16) by lia. apply Z.mod_mul; lia. }
split; [lia|]. split; [exact Hd|]. split; [lia|].
split; [rewrite E3, R3; exact Hgp|]. split; [rewrite E4, R4; exact Htp|]. split.
- assert (HP : astack_pres ly (w_H W) mem (x_sp0 cx - 32768)).
  { eapply (astack_pres_journal SEGS B pa_segs_low); [exact HJ | exact HPRES |].
    intros a (r & Hr & Ha) Ha2. destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
    exfalso. unfold longlA, A_LONGL, LONGL_N, x_sp0 in *. lia. }
  apply achain_any.
  + apply astack_rd_of_pres. apply (astack_pres_mono _ _ _ (x_sp0 cx - 32768)); [lia | exact HP].
  + right; right; right. unfold s0Z. rewrite E8, R8. rewrite unsigned_lit_small by lia. lia.
- split; [exact HRO|]. split; [unfold EV_LTOI in *; lia|].
  intros STK1 Hin. pose proof (ltoi_callee_stks STK1 Hin) as [H1 H2].
  unfold LTOI_FRAME_MAX, STK_LLVMFuzzerTestOneInput in H2. split; lia.
Qed.

(* ---- the seed of the run 0x854a0 .. jal check_segments: s1's slot 160 holds c (atom 32) ---- *)
Definition s9_ssA : sstate :=
  mkSS LO_K854a0 sr_atoms [YP09.mkRegion (Some 9%nat) 160 168 0 0 [YP09.mkChunk 160 (CVal 8 (SOff 32 0))]] None
    (mkFacts [] [] []).
Definition s9_EA (regs : bvmap 5 word) (c : Z) : env := Eimg (Ereg regs [w64 c]).
Lemma s9_seedA : forall cx (W : world SEGS) regs mem c m,
  lt_base B MT cx -> getr regs 9 = w64 (x_s1 cx) -> lt_slots cx (rdW W mem) (LT_L cx c m) -> 0 <= c < 2 ^ 64 ->
  st_ok_pi SEGS VAL (s9_EA regs c) s9_ssA
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K854a0)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 9 0) [] (s9_EA regs c) (mrestrict (w_H W) mem).
Proof.
intros cx W regs mem c m HB R9 HSL Hc.
pose proof (s9_base_facts cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *. pose proof asan_consts as (C1 & _).
assert (E9 : ew (s9_EA regs c) 9 = w64 (x_s1 cx)).
{ unfold s9_EA. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl). exact R9. }
assert (E32 : ew (s9_EA regs c) 32 = w64 c).
{ unfold s9_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
split.
- unfold s9_ssA. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold s9_EA. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (x_s1 cx) 160 8 _ c).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hc.
    * lia.
    * apply (val_mem_of_rdword SEGS). exact (HSL 160 c ltac:(unfold LT_L; cbn [In]; tauto)).
  + cbn. tauto.
  + unfold facts_ok. cbn. tauto.
- apply Forall_nil.
Qed.

(* r's shadow byte at a point *)
Lemma s9_r_shadow : forall cx ly S W regs mem md k acc o c m, s9M cx ly S W regs mem md k acc o c m ->
  rdW W mem (x_sh cx + 22) = Some (if fo_r o then 4 else 0xf8).
Proof.
intros cx ly S W regs mem md k acc o c m ((HFR & _) & _).
destruct HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HZS).
pose proof (HZS 22%nat ltac:(rewrite lt_fsh_len; lia)) as H. change (Z.of_nat 22) with 22 in H. rewrite H.
destruct o as [[] [] [] [] []]; reflexivity.
Qed.

Hypothesis SIGP : seg_sig_prog.
Hypothesis HCSEG : forall fx0 : YK11.FPState,
  check_segments_contract (fx := fx0) SEGS B (BASE + AF_check_segments) STK_check_segments RLO_A RHI_A.

(* 0x854ac: check_segments returned; s10 = (m + 0x2000) >> 3 *)
Definition S9_cs_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> s9M cx ly S W regs mem md k acc LFO0 c m ->
  getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO9_CS) regs mem md) (lt_post B MT cx).

Let RUN := paj_run B LAWS.

(* 0x854a0 .. 0x854a8: a0 = c (160(s1)), a2 = s6 = returned, jal check_segments; the call; to 0x854ac *)
Lemma s9_head : S9_cs_stmt -> LT_K854a0_stmt B MT.
Proof.
intros HN cx ly S W regs mem md k acc c m HB HFRM HC Hc Hm R11 R22 R26 HSL HCM.
assert (HM : s9M cx ly S W regs mem md k acc LFO0 c m) by (split; [exact HC|]; split; [exact Hc|]; split; [exact Hm|];
  split; [exact HSL | exact HCM]).
pose proof HC as ((HJ & R2 & R3 & R4 & R8 & R9 & _) & _).
pose proof Hc as (Hcin & Hc4 & Hc16 & Hcaddr). pose proof Hm as (Hmin & Hm4 & Hm16 & Hmaddr).
pose proof HJ as (HAR & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcin) as (_ & _ & Hcc & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc.
pose proof asan_consts as (C1 & _).
assert (Hc64 : 0 <= c < 2 ^ 64) by (unfold seg_spec.SEG_C_SIZE in *; lia).
assert (Hm64 : 0 <= m < 2 ^ 64) by (unfold seg_spec.SEG_M_SIZE in *; lia).
destruct (s9_seedA cx W regs mem c m HB R9 HSL Hc64) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (s9_EA regs c)) by (unfold s9_EA; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 c]) (s9_EA regs c)).
{ unfold s9_EA. split; [intros i Hi; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r0 & Hr0 & Hw). cbn [s9_ssA ss_mem In] in Hr0.
  destruct Hr0 as [<-|[]]. cbn in Hw. lia. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [w64 c] HS); [exact HAE | vm_compute; reflexivity]. }
rewrite (SIGP SS_check_segments ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_check_segments) with AF_check_segments by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
assert (EE32 : ew (s9_EA regs c) 32 = w64 c).
{ unfold s9_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (EE22 : ew (s9_EA regs c) 22 = getr regs 22).
{ unfold s9_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 22 22%bv eq_refl). }
assert (EE11 : ew (s9_EA regs c) 11 = getr regs 11).
{ unfold s9_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 11 11%bv eq_refl). }
rewrite EE32 in P10. rewrite EE22, R22 in P12. rewrite EE11, R11 in P11.
assert (E2 : getr (ms_regs ms) 2 = getr regs 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (E3 : getr (ms_regs ms) 3 = getr regs 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
assert (E4 : getr (ms_regs ms) 4 = getr regs 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
assert (E8 : getr (ms_regs ms) 8 = getr regs 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
destruct (s9_call_frame cx ly S W regs mem md k acc LFO0 c m (ms_regs ms) HB HM E2 E3 E4 E8)
  as (Hspc & Ho16 & Honeg & P3c & P4c & (ch & Hch) & HRO & Hnev & HSTKS).
destruct (HSTKS STK_check_segments ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto)) as [HS1 HS2].
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBlo.
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
pose proof (s18_harness (x_pl cx)) as [HCS _].
assert (Hret : 0 <= seg_spec.b2z (seg_spec.seg_ret (x_run cx)) < 2 ^ 64)
  by (unfold seg_spec.b2z; destruct (seg_spec.seg_ret (x_run cx)); lia).
assert (HPRE : check_segments_pre B ly S (rdW W mem) c m (seg_spec.b2z (seg_spec.seg_ret (x_run cx)))
  (seg_spec.seg_rc (x_run cx)) (seg_spec.seg_mc (x_run cx)) (seg_spec.seg_ret (x_run cx))).
{ destruct HCM as [HRC HMC].
  split; [lia|]. split; [exact Hc16|]. split; [exact HRC|].
  split; [exists c, seg_spec.SEG_C_SIZE; split; [exact Hcin | lia]|]. split; [exact Hcaddr|].
  split; [lia|]. split; [exact Hm16|]. split; [exact HMC|].
  split; [exists m, seg_spec.SEG_M_SIZE; split; [exact Hmin | lia]|]. split; [exact Hmaddr|].
  split; [reflexivity | exact HCS]. }
eapply SRr_bind.
{ eapply (cl_callS B LAWS W (ms_regs ms) mem _ STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx)
    (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S mdv k STK_check_segments [] EV_check_segments
    (x_s1 cx - x_sp0 cx) (getr (ms_regs ms) 1) ch
    (fun ly2 S2 W2 regs2 mem2 md2 => sa_kept SEGS W mem W2 mem2 (ms_regs ms) STK_check_segments (fun _ => False) /\
       sa_noalloc B ly S ly2 S2)
    HJ Hspc Ho16 Honeg HS1 HS2 P3c P4c eq_refl HraT Hra4T Hch).
  - intros HPRE1. eapply SRr_mono.
    + exact (HCSEG fx ly S W (ms_regs ms) mem mdv ch c m _ _ _ _ HPRE1 HRO P10 Hc64 P11 Hm64 P12 Hret HPRE
        ltac:(unfold EV_check_segments; lia)).
    + cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. split; [exact Ec|]. split; [exact HJ3|]. split; [exact HP3 | exact HQ3].
  - intros a (r0 & Hr0 & _). destruct Hr0. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJ3 & HJc3 & HP3 & HK3 & HNA3).
subst c3.
replace (k + EV_check_segments) with k in HJ3 by (unfold EV_check_segments; lia).
assert (HPALL : aregs_preserved regs regs3) by (intros z Hz; rewrite (HP3 z Hz); exact (HPR z Hz)).
assert (Hsp' : spZ (ms_regs ms) = x_s1 cx) by (rewrite Hspc; lia).
destruct (s9_agree_kept cx ly S W regs mem md k acc LFO0 c m (ms_regs ms) W3 mem3 STK_check_segments (fun _ => False)
  HB HM Hsp' HS1 ltac:(pose proof (ltoi_callee_stks STK_check_segments ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto));
  lia) HK3 (fun a H => False_ind _ H)) as [HAG H22].
destruct HNA3 as (HPm & -> & HSf).
pose proof (s9M_agree cx ly S W regs mem md k acc LFO0 LFO0 c m ly S3 W3 regs3 mem3 md3 HB HM HJ3
  (HPALL 2 ltac:(unfold acallee_saved; lia)) (HPALL 3 ltac:(unfold acallee_saved; lia))
  (HPALL 4 ltac:(unfold acallee_saved; lia)) (HPALL 8 ltac:(unfold acallee_saved; lia))
  (HPALL 9 ltac:(unfold acallee_saved; lia)) HAG
  ltac:(rewrite H22; exact (s9_r_shadow cx ly S W regs mem md k acc LFO0 c m HM))
  eq_refl eq_refl eq_refl eq_refl HPm (or_intror HSf)) as HM3.
rewrite P1.
exact (HN cx ly S3 W3 regs3 mem3 md3 k acc c m HB HFRM HM3 (eq_trans (HPALL 26 ltac:(unfold acallee_saved; lia)) R26)).
Qed.

(* ---- small facts the seeds share ---- *)
Lemma s9_val_of_rd : forall H (mem : word -> option byte) a n v,
  sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
Lemma s9_lts : forall (x y : word), 0 <= bv_unsigned x < 2 ^ 63 -> 0 <= bv_unsigned y < 2 ^ 63 ->
  bv_lts x y = (bv_unsigned x <? bv_unsigned y).
Proof.
intros x y Hx Hy. unfold bv_lts, bv_signed.
rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia). reflexivity.
Qed.
(* m->n's shadow byte, SH(m + 0x2000), is 0: the 8 bytes m + 0x2000 .. m + 0x2007 are addressable *)
Lemma s9_mn_shadow : forall rd m, sa_addr rd m seg_spec.SEG_M_SIZE -> m mod 16 = 0 ->
  rd (shadow_addr (m + seg_spec.MC_N)) = Some 0.
Proof.
intros rd m (_ & _ & _ & HR & _) H16.
destruct (HR (m + seg_spec.MC_N + 7) ltac:(unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE; lia)) as (s & Hs & Hok).
assert (E : shadow_of_addr SHADOW_OFF (m + seg_spec.MC_N + 7) = shadow_addr (m + seg_spec.MC_N)).
{ unfold shadow_of_addr, shadow_addr, seg_spec.MC_N. f_equal. Z.div_mod_to_equations. lia. }
rewrite E in Hs. rewrite Hs. f_equal.
destruct Hok as [-> | (Hm & Hs8)]; [reflexivity|].
exfalso. assert (Hm7 : (m + seg_spec.MC_N + 7) mod 8 = 7) by (unfold seg_spec.MC_N; Z.div_mod_to_equations; lia). lia.
Qed.

(* ---- the seed at 0x854ac: s1's slots 144 (SH(FR), atom 36), 160 (c, 32), 168 (m, 33), 176 (the shadow base, 34),
   184 (m + 0x2000); m->n (atom 35, at most 32); SH(m + 0x2000) (atom 37), named by the alias s10 + base, holds 0
   (check 19 reads it); cs the branch conditions the caller knows ---- *)
Definition s9_slotsB : YP09.region :=
  YP09.mkRegion (Some 9%nat) 144 192 0 0
   [ YP09.mkChunk 144 (CVal 8 (SOff 36 0)); YP09.mkChunk 160 (CVal 8 (SOff 32 0));
     YP09.mkChunk 168 (CVal 8 (SOff 33 0)); YP09.mkChunk 176 (CVal 8 (SOff 34 0));
     YP09.mkChunk 184 (CVal 8 (SOff 33 0x2000)) ].
Definition s9_nB : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x2000 0x2004 0 0 [YP09.mkChunk 0x2000 (CVal 4 (SOff 35 0))].
Definition s9_sbB : YP09.region := YP09.mkRegion (Some 37%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition s9_ssB (cs : list acond) : sstate :=
  mkSS LO9_CS sr_atoms [s9_slotsB; s9_nB; s9_sbB] None
    (mkFacts [(35%nat, mkAF 0 32 0)] cs [(SAlu ALU_ADD (SOff 26 0) (SOff 34 0), SOff 37 0)]).
Definition s9_xB (cx : lcx) (c m n : Z) : list word :=
  [w64 c; w64 m; w64 SHADOW_OFF; w64 n; w64 (x_sh cx); w64 (shadow_addr (m + seg_spec.MC_N))].
Definition s9_EB (regs : bvmap 5 word) (cx : lcx) (c m n : Z) : env := Eimg (Ereg regs (s9_xB cx c m n)).
Lemma s9_seedB : forall cx ly S W regs mem md k acc c m cs,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc LFO0 c m ->
  getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  conds_ok (s9_EB regs cx c m (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) cs ->
  st_ok_pi SEGS VAL (s9_EB regs cx c m (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) (s9_ssB cs)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO9_CS)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 9 0) [] (s9_EB regs cx c m (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) (mrestrict (w_H W) mem).
Proof.
intros cx ly S W regs mem md k acc c m cs HB HM R26 HCS.
pose proof (s9_base_facts cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
pose proof HM as ((HFR & _) & Hc & Hm & HSL & (HRC & HMC)).
destruct HFR as (HJ & _ & _ & _ & _ & R9 & _ & _ & _ & _ & _ & W176 & _).
pose proof Hc as (Hcin & Hc4 & Hc16 & _). pose proof Hm as (Hmin & Hm4 & Hm16 & Hmaddr).
pose proof HJ as (HAR & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcin) as (_ & _ & Hcc & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & Hmapp & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc, Hmapp.
pose proof asan_consts as (C1 & _).
destruct (s9_frame_at cx ly S W mem md k HB HJ) as (_ & _ & _ & _ & Hf4 & Hfc & _).
set (n := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
assert (Hn : 0 <= n <= 32) by (pose proof (s18_mconf_len _ _ _ HMC); unfold n, x_mcF; lia).
assert (Hsh : 0x7fff8000 <= x_sh cx < 0x7fff8000 + 2 ^ 44).
{ unfold x_sh, shadow_addr, SHADOW_OFF. split; [pose proof (Z.div_pos (x_fr cx) 8); lia|].
  assert (x_fr cx / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (Hsm : 0x7fff8000 <= shadow_addr (m + seg_spec.MC_N) < 0x7fff8000 + 2 ^ 44).
{ unfold shadow_addr, SHADOW_OFF, seg_spec.MC_N. split; [pose proof (Z.div_pos (m + 8192) 8); lia|].
  assert ((m + 8192) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; unfold seg_spec.SEG_M_SIZE in *; lia). lia. }
set (E := s9_EB regs cx c m n).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs (s9_xB cx c m n)) q)
  by (intros q Hq; unfold E, s9_EB; apply Eimg_low; exact Hq).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E26 : ew E 26 = w64 ((m + seg_spec.MC_N) / 8))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = w64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 m) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 (x_sh cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = w64 (shadow_addr (m + seg_spec.MC_N))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (SL : forall o v, In (o, v) (LT_L cx c m) -> val_mem SEGS (mrestrict (w_H W) mem) (x_s1 cx + o) 8 v)
  by (intros o v Hin; apply (val_mem_of_rdword SEGS); exact (HSL o v Hin)).
split.
- unfold s9_ssB. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold E, s9_EB. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold s9_slotsB, s9_nB, s9_sbB.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS _ _ (x_s1 cx) 144 8 _ (x_sh cx));
           [cbn [sv_denot]; rewrite E36, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia
           | exact (SL 144 _ ltac:(unfold LT_L; cbn [In]; tauto))].
      -- apply (chunk_ok_val SEGS _ _ (x_s1 cx) 160 8 _ c);
           [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.SEG_C_SIZE in *; lia | lia
           | exact (SL 160 _ ltac:(unfold LT_L; cbn [In]; tauto))].
      -- apply (chunk_ok_val SEGS _ _ (x_s1 cx) 168 8 _ m);
           [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.SEG_M_SIZE in *; lia | lia
           | exact (SL 168 _ ltac:(unfold LT_L; cbn [In]; tauto))].
      -- apply (chunk_ok_val SEGS _ _ (x_s1 cx) 176 8 _ SHADOW_OFF);
           [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | lia
           | exact (val_mem_of_rdword SEGS _ _ _ _ W176)].
      -- apply (chunk_ok_val SEGS _ _ (x_s1 cx) 184 8 _ (m + seg_spec.MC_N));
           [cbn [sv_denot]; rewrite E33; unfold w64; rewrite unsigned_lit_small by (unfold seg_spec.SEG_M_SIZE in *; lia);
            reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.SEG_M_SIZE, seg_spec.MC_N in *; lia | lia
           | exact (SL 184 _ ltac:(unfold LT_L; cbn [In]; tauto))].
    * rewrite E33, unsigned_lit_small by (unfold seg_spec.SEG_M_SIZE in *; lia).
      split; [lia|]. split; [unfold seg_spec.SEG_M_SIZE in *; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ m 0x2000 4 _ n);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia
        | exact (s9_val_of_rd _ _ _ _ _ (s18_mconf_n _ _ _ HMC))].
    * rewrite E37, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (shadow_addr (m + seg_spec.MC_N)) 0 1 _ 0); [reflexivity | lia | lia |].
      apply s9_val_of_rd. intros k0 Hk0. destruct k0 as [|k0]; [|lia]. rewrite Z.add_0_r, Z.add_0_r.
      rewrite (s9_mn_shadow _ m Hmaddr Hm16). reflexivity.
  + apply pairwise_disjoint_of_extents.
    unfold s9_slotsB, s9_nB, s9_sbB, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E33, E37, !unsigned_lit_small by (unfold seg_spec.SEG_M_SIZE in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct Hmapp as (_ & [Hl | (Hh & _)]); unfold kLowShadowBeg, kHighMemBeg, seg_spec.SEG_M_SIZE in *;
    repeat split; lia.
  + split; [|split; [exact HCS|]].
    * cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E35, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
    * cbn [f_alias alias_ok]. split; [|exact I]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      assert (Hq : 0 <= (m + seg_spec.MC_N) / 8 < 2 ^ 44).
      { unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
      rewrite (U_atom E 26 _ E26) by lia. rewrite (U_atom E 34 _ E34) by (unfold SHADOW_OFF; lia).
      rewrite (U_atom E 37 _ E37) by lia.
      unfold shadow_addr. rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF in *. lia.
- apply Forall_nil.
Qed.

(* a run that stores nothing keeps s9M with the run's registers and model *)
Lemma s9M_run : forall cx ly S W regs mem md k acc o c m regs2 md2,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m -> s9J cx ly S W mem md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  s9M cx ly S W regs2 mem md2 k acc o c m.
Proof.
intros cx ly S W regs mem md k acc o c m regs2 md2 HB HM HJ E2 E3 E4 E8 E9.
apply (s9M_agree cx ly S W regs mem md k acc o o c m ly S W regs2 mem md2 HB HM HJ E2 E3 E4 E8 E9);
  [| exact (s9_r_shadow cx ly S W regs mem md k acc o c m HM) | reflexivity | reflexivity | reflexivity | reflexivity
   | apply Permutation_refl | left; reflexivity].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros; reflexivity | intros; reflexivity].
Qed.

(* the loop head at 0x854f0, turn i < m->n *)
Definition S9_loop_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  s9M cx ly S W regs mem md k acc LFO0 c m -> s9R cx i regs c m ->
  SRr SEGS W (cfg_at SEGS (BASE + LO9_LOOP) regs mem md) (lt_post B MT cx).

Let RUNTO := paj_run_to B LAWS.

(* 0x854ac .. 0x854ec: check 19 (SH(m + 0x2000) is 0), m->n, `blez` to 0x8559c when it is 0, else the loop's
   registers and the head of turn 0 *)
Lemma s9_cs : S9_loop_stmt 0 -> LTA_K8559c B MT -> S9_cs_stmt.
Proof.
intros HL HK cx ly S W regs mem md k acc c m HB HFRM HM R26.
pose proof HM as ((HFR & _) & Hc & Hm & HSL & HCM).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof (s9_base_facts cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
pose proof HJ as (HAR & _).
pose proof Hc as (Hcin & _ & Hc16 & _). pose proof Hm as (Hmin & _ & Hm16 & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcin) as (_ & Hc4 & Hcc & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & Hm4 & Hmc & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc.
pose proof asan_consts as (C1 & _).
destruct HCM as [HRC HMC].
set (n := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
assert (Hn : 0 <= n <= 32) by (pose proof (s18_mconf_len _ _ _ HMC); unfold n, x_mcF; lia).
set (E := s9_EB regs cx c m n).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs (s9_xB cx c m n)) q)
  by (intros q Hq; unfold E, s9_EB; apply Eimg_low; exact Hq).
assert (E35 : ew E 35 = w64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (D0 : sv_denot E (SLit 0) = Z_to_bv 64 0) by reflexivity.
assert (D35 : sv_denot E (SOff 35 0) = Z_to_bv 64 n)
  by (cbn [sv_denot]; rewrite E35, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HEI : img_env VAL A_LIM E) by (unfold E, s9_EB; apply Eimg_env).
destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
- (* m->n = 0: blez to 0x8559c *)
  destruct (s9_seedB cx ly S W regs mem md k acc c m [mkAC BC_GE (SLit 0) (SOff 35 0)] HB HM R26) as [HS SHOK].
  { cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
    change (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) with n. fold E.
    rewrite D0, D35, s9_lts by (rewrite !unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia.
    rewrite Hn0. reflexivity. }
  change (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) with n in HS, SHOK. fold E in HS, SHOK.
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) LO_K8559c.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  assert (EM : ms_mem ms = mem).
  { apply functional_extensionality. intros x. apply HF. intros (r0 & Hr0 & Hw). cbn [ss_mem In] in Hr0.
    destruct Hr0 as [<-|[<-|[<-|[]]]]; cbn in Hw; lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (27%bv : bv 5) P27.
  rewrite EL in P2, P3, P4, P8, P9, P27 by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in P2. rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl) in P3.
  rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl) in P4. rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl) in P8.
  rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl) in P9. rewrite (ew_Ereg_extra regs _ 5) in P27.
  rewrite EM in HJ |- *.
  pose proof (s9M_run cx ly S W regs mem md k acc LFO0 c m (ms_regs ms) mdv HB HM HJ P2 P3 P4 P8 P9)
    as (HC' & Hc' & Hm' & HSL' & HCM').
  exact (HK fx cx ly S W (ms_regs ms) mem mdv k acc c m HB HFRM HC' Hc' Hm' P27 HSL' HCM').
- (* m->n >= 1: the loop's registers, then turn 0 *)
  destruct (s9_seedB cx ly S W regs mem md k acc c m [mkAC BC_LT (SLit 0) (SOff 35 0)] HB HM R26) as [HS SHOK].
  { cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
    change (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) with n. fold E.
    rewrite D0, D35, s9_lts by (rewrite !unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia.
    apply Z.ltb_lt. lia. }
  change (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) with n in HS, SHOK. fold E in HS, SHOK.
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) LO9_LOOP.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  assert (EM : ms_mem ms = mem).
  { apply functional_extensionality. intros x. apply HF. intros (r0 & Hr0 & Hw). cbn [ss_mem In] in Hr0.
    destruct Hr0 as [<-|[<-|[<-|[]]]]; cbn in Hw; lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  rewrite EL in P2, P3, P4, P8, P9, P19, P21, P26, P27 by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in P2. rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl) in P3.
  rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl) in P4. rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl) in P8.
  rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl) in P9.
  rewrite (ew_Ereg_extra regs _ 1) in P19. rewrite (ew_Ereg_extra regs _ 4) in P21.
  rewrite (ew_Ereg_extra regs _ 0) in P26. rewrite (ew_Ereg_extra regs _ 5) in P27.
  rewrite EM in HJ |- *.
  pose proof (s9M_run cx ly S W regs mem md k acc LFO0 c m (ms_regs ms) mdv HB HM HJ P2 P3 P4 P8 P9) as HM'.
  apply (HL cx ly S W (ms_regs ms) mem mdv k acc c m HB HFRM ltac:(unfold n in Hn0; lia) HM').
  split; [exact P18|]. split; [rewrite P19; unfold seg_spec.mseg_addr; cbn [Z.of_nat]; rewrite Z.mul_0_r, Z.add_0_r; reflexivity|].
  split; [exact P21|]. split; [exact P22|]. split; [exact P23|].
  split; [rewrite P24; apply bv_eq; reflexivity|]. split; [exact P26 | exact P27].
Qed.

(* ---- one program call of S09 whose footprint is [] and which keeps every byte outside its window: the
   callee's contract (abstracted as HCALL), cl_callS, and s9M back at the return ---- *)
Lemma s9_call_step : forall cx ly S W regs mem md k acc o c m (regsc : bvmap 5 word) (A ret STK1 : Z)
  (Rpost : bvmap 5 word -> Prop),
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  getr regsc 2 = getr regs 2 -> getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
  getr regsc 8 = getr regs 8 -> getr regsc 9 = getr regs 9 ->
  In STK1 LTOI_CALLEE_STKS ->
  getr regsc 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall ch, afn_pre SEGS B STK1 ly S W regsc mem md ch ->
     SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 A) mem (seg_rom SEGS)) md)
       (apost_base SEGS B STK1 [] regsc ly S W mem md 0
         (fun ly' S' W' regs' mem' md' => Rpost regs' /\ sa_kept SEGS W mem W' mem' regsc STK1 (fun _ => False) /\
            sa_noalloc B ly S ly' S'))) ->
  (forall S2 (W2 : world SEGS) regs2 mem2 md2, s9M cx ly S2 W2 regs2 mem2 md2 k acc o c m ->
     aregs_preserved regsc regs2 -> Rpost regs2 ->
     SRr SEGS W2 (cfg_at SEGS (BASE + ret) regs2 mem2 md2) (lt_post B MT cx)) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 A) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros cx ly S W regs mem md k acc o c m regsc A ret STK1 Rpost HB HM E2 E3 E4 E8 E9 HIn P1 Hret Hret2 HCALL HNEXT.
pose proof HM as ((HFR & _) & _). pose proof HFR as (HJ & _).
destruct (s9_call_frame cx ly S W regs mem md k acc o c m regsc HB HM E2 E3 E4 E8)
  as (Hspc & Ho16 & Honeg & P3c & P4c & (ch & Hch) & HRO & Hnev & HSTKS).
destruct (HSTKS STK1 HIn) as [HS1 HS2].
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBlo.
assert (HraT : YK0s.ret_ok (getr regsc 1)) by (rewrite P1; apply ret_ok_codeptr_v; lia).
assert (Hra4T : 4096 <= bv_unsigned (getr regsc 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
eapply SRr_bind.
{ eapply (cl_callS B LAWS W regsc mem _ STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx)
    (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k STK1 [] 0
    (x_s1 cx - x_sp0 cx) (getr regsc 1) ch
    (fun ly2 S2 W2 regs2 mem2 md2 => Rpost regs2 /\ sa_kept SEGS W mem W2 mem2 regsc STK1 (fun _ => False) /\
       sa_noalloc B ly S ly2 S2)
    HJ Hspc Ho16 Honeg HS1 HS2 P3c P4c eq_refl HraT Hra4T Hch).
  - intros HPRE1. eapply SRr_mono; [exact (HCALL ch HPRE1)|].
    cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJ3 & HP3 & HQ3).
    exists ly3, S3, regs3, mem3, md3. split; [exact Ec|]. split; [exact HJ3|]. split; [exact HP3 | exact HQ3].
  - intros a (r0 & Hr0 & _). destruct Hr0. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJ3 & HJc3 & HP3 & HR3 & HK3 & HNA3).
subst c3. rewrite Z.add_0_r in HJ3.
assert (Hsp' : spZ regsc = x_s1 cx) by (rewrite Hspc; lia).
pose proof (ltoi_callee_stks STK1 HIn) as [_ HSTK].
destruct (s9_agree_kept cx ly S W regs mem md k acc o c m regsc W3 mem3 STK1 (fun _ => False)
  HB HM Hsp' HS1 HSTK HK3 (fun a H => False_ind _ H)) as [HAG H22].
destruct HNA3 as (HPm & -> & HSf).
assert (Q2 : getr regs3 2 = getr regs 2) by exact (eq_trans (HP3 2 ltac:(unfold acallee_saved; lia)) E2).
assert (Q3 : getr regs3 3 = getr regs 3) by exact (eq_trans (HP3 3 ltac:(unfold acallee_saved; lia)) E3).
assert (Q4 : getr regs3 4 = getr regs 4) by exact (eq_trans (HP3 4 ltac:(unfold acallee_saved; lia)) E4).
assert (Q8 : getr regs3 8 = getr regs 8) by exact (eq_trans (HP3 8 ltac:(unfold acallee_saved; lia)) E8).
assert (Q9 : getr regs3 9 = getr regs 9) by exact (eq_trans (HP3 9 ltac:(unfold acallee_saved; lia)) E9).
pose proof (s9M_agree cx ly S W regs mem md k acc o o c m ly S3 W3 regs3 mem3 md3 HB HM HJ3 Q2 Q3 Q4 Q8 Q9 HAG
  ltac:(rewrite H22; exact (s9_r_shadow cx ly S W regs mem md k acc o c m HM))
  eq_refl eq_refl eq_refl eq_refl HPm (or_intror HSf)) as HM3.
rewrite P1. exact (HNEXT S3 W3 regs3 mem3 md3 HM3 HP3 HR3).
Qed.

(* ---- the same for a call that may write r (reac_segconf_role's out): its footprint FP1 and its write set E lie
   in r; when FP1 is empty the callee's journal keeps r ---- *)
Lemma s9_call_step_w : forall cx ly S W regs mem md k acc o c m (regsc : bvmap 5 word) (A ret STK1 : Z)
  (FP1 : list (Z * Z)) (E : Z -> Prop) (Rpost : world SEGS -> bvmap 5 word -> (word -> option byte) -> Prop),
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  getr regsc 2 = getr regs 2 -> getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
  getr regsc 8 = getr regs 8 -> getr regsc 9 = getr regs 9 ->
  In STK1 LTOI_CALLEE_STKS ->
  getr regsc 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall a, inFP FP1 a -> x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
  (forall a, E a -> x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
  (forall ch, afn_pre SEGS B STK1 ly S W regsc mem md ch ->
     SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 A) mem (seg_rom SEGS)) md)
       (apost_base SEGS B STK1 FP1 regsc ly S W mem md 0
         (fun ly' S' W' regs' mem' md' => Rpost W' regs' mem' /\ sa_kept SEGS W mem W' mem' regsc STK1 E /\
            sa_noalloc B ly S ly' S'))) ->
  (forall S2 (W2 : world SEGS) regs2 mem2 md2, s9M cx ly S2 W2 regs2 mem2 md2 k acc o c m ->
     aregs_preserved regsc regs2 -> Rpost W2 regs2 mem2 ->
     (FP1 = [] -> forall a, x_fr cx + FO_R <= a < x_fr cx + FO_R + 4 -> rdW W2 mem2 a = rdW W mem a) ->
     SRr SEGS W2 (cfg_at SEGS (BASE + ret) regs2 mem2 md2) (lt_post B MT cx)) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 A) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros cx ly S W regs mem md k acc o c m regsc A ret STK1 FP1 E Rpost HB HM E2 E3 E4 E8 E9 HIn P1 Hret Hret2
  HFP HE HCALL HNEXT.
pose proof HM as ((HFR & _) & _). pose proof HFR as (HJ & _).
destruct (s9_frame_at cx ly S W mem md k HB HJ) as (HAR & Hin & EF & _ & _ & Hfc & _).
pose proof (s9_base_facts cx HB) as (_ & Hsp0 & _ & _ & _ & _).
destruct (s9_call_frame cx ly S W regs mem md k acc o c m regsc HB HM E2 E3 E4 E8)
  as (Hspc & Ho16 & Honeg & P3c & P4c & (ch & Hch) & HRO & Hnev & HSTKS).
destruct (HSTKS STK1 HIn) as [HS1 HS2].
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBlo.
assert (HraT : YK0s.ret_ok (getr regsc 1)) by (rewrite P1; apply ret_ok_codeptr_v; lia).
assert (Hra4T : 4096 <= bv_unsigned (getr regsc 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W regsc mem _ STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx)
    (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k STK1 FP1 0
    (x_s1 cx - x_sp0 cx) (getr regsc 1) ch
    (fun ly2 S2 W2 regs2 mem2 md2 => Rpost W2 regs2 mem2 /\ sa_kept SEGS W mem W2 mem2 regsc STK1 E /\
       sa_noalloc B ly S ly2 S2)
    HJ Hspc Ho16 Honeg HS1 HS2 P3c P4c eq_refl HraT Hra4T Hch).
  - intros HPRE1. eapply SRr_mono; [exact (HCALL ch HPRE1)|].
    cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJ3 & HP3 & HQ3).
    exists ly3, S3, regs3, mem3, md3. split; [exact Ec|]. split; [exact HJ3|]. split; [exact HP3 | exact HQ3].
  - intros a Ha. pose proof (HFP a Ha) as Hr. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite <- EF. change (fs_frame_bytes LT_FCLS) with 512. unfold FO_R in Hr. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HFP a Ha) as Hr.
    unfold STK_LLVMFuzzerTestOneInput, FO_R in *. lia. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJ3 & HJc3 & HP3 & HR3 & HK3 & HNA3).
subst c3. rewrite Z.add_0_r in HJ3.
assert (Hsp' : spZ regsc = x_s1 cx) by (rewrite Hspc; lia).
pose proof (ltoi_callee_stks STK1 HIn) as [_ HSTK].
destruct (s9_agree_kept cx ly S W regs mem md k acc o c m regsc W3 mem3 STK1 E
  HB HM Hsp' HS1 HSTK HK3 HE) as [HAG H22].
destruct HNA3 as (HPm & -> & HSf).
assert (KR : FP1 = [] -> forall a, x_fr cx + FO_R <= a < x_fr cx + FO_R + 4 -> rdW W3 mem3 a = rdW W mem a).
{ intros EFP a Ha. subst FP1.
  destruct (acall_kept_of_journal SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => False) HJc3 HAR)
    as (_ & _ & _ & KF & _).
  - intros a0 (r0 & Hr0 & _). destruct Hr0.
  - intros b m0 i0 Hb _ _. exact (Permutation_in _ (Permutation_sym HPm) Hb).
  - exact sink_closed_nil.
  - intros a0 (r0 & Hr0 & _). destruct Hr0.
  - apply (KF LT_FCLS (x_fpos cx) a Hin); [|intros []]. left. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite <- EF. change (fs_frame_bytes LT_FCLS) with 512. unfold FO_R in Ha. lia. }
assert (Q2 : getr regs3 2 = getr regs 2) by exact (eq_trans (HP3 2 ltac:(unfold acallee_saved; lia)) E2).
assert (Q3 : getr regs3 3 = getr regs 3) by exact (eq_trans (HP3 3 ltac:(unfold acallee_saved; lia)) E3).
assert (Q4 : getr regs3 4 = getr regs 4) by exact (eq_trans (HP3 4 ltac:(unfold acallee_saved; lia)) E4).
assert (Q8 : getr regs3 8 = getr regs 8) by exact (eq_trans (HP3 8 ltac:(unfold acallee_saved; lia)) E8).
assert (Q9 : getr regs3 9 = getr regs 9) by exact (eq_trans (HP3 9 ltac:(unfold acallee_saved; lia)) E9).
pose proof (s9M_agree cx ly S W regs mem md k acc o o c m ly S3 W3 regs3 mem3 md3 HB HM HJ3 Q2 Q3 Q4 Q8 Q9 HAG
  ltac:(rewrite H22; exact (s9_r_shadow cx ly S W regs mem md k acc o c m HM))
  eq_refl eq_refl eq_refl eq_refl HPm (or_intror HSf)) as HM3.
rewrite P1. exact (HNEXT S3 W3 regs3 mem3 md3 HM3 HP3 HR3 KR).
Qed.

(* ---- the callees' premises at turn i, from s9M and the model ---- *)
Definition s9_nm (cx : lcx) (i : nat) : list Z := SegModel.ms_name (x_seg cx i).

Lemma s9_blocks : forall cx ly S W regs mem md k acc o c m, s9M cx ly S W regs mem md k acc o c m ->
  c <> 0 /\ c mod 16 = 0 /\ 0 < c /\ c + seg_spec.SEG_C_SIZE < 2 ^ 63 /\
  m <> 0 /\ m mod 16 = 0 /\ 0 < m /\ m + seg_spec.SEG_M_SIZE < 2 ^ 63 /\
  sa_heap B ly S c seg_spec.SEG_C_SIZE /\ sa_heap B ly S m seg_spec.SEG_M_SIZE.
Proof.
intros cx ly S W regs mem md k acc o c m HM.
pose proof HM as ((HFR & _) & (Hcin & Hc4 & Hc16 & Hca) & (Hmin & Hm4 & Hm16 & Hma) & _).
pose proof HFR as ((HAR & _) & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcin) as (_ & _ & Hcc & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc.
pose proof asan_consts as (C1 & _).
split; [lia|]. split; [exact Hc16|]. split; [lia|]. split; [unfold seg_spec.SEG_C_SIZE in *; lia|].
split; [lia|]. split; [exact Hm16|]. split; [lia|]. split; [unfold seg_spec.SEG_M_SIZE in *; lia|].
split; [exists c, seg_spec.SEG_C_SIZE; split; [exact Hcin | lia] | exists m, seg_spec.SEG_M_SIZE; split; [exact Hmin | lia]].
Qed.

Lemma s9_query_pre : forall cx ly S W regs mem md k acc o c m i, s9M cx ly S W regs mem md k acc o c m ->
  (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  query_pre SEGS B ly S (rdW W mem) c (seg_spec.mseg_addr m i) (x_rcF cx) (s9_nm cx i) /\
  0 <= c < 2 ^ 64 /\ 0 <= seg_spec.mseg_addr m i < 2 ^ 64.
Proof.
intros cx ly S W regs mem md k acc o c m i HM Hi.
destruct (s9_blocks cx ly S W regs mem md k acc o c m HM) as (Hc0 & Hc16 & Hcp & Hcb & Hm0 & Hm16 & Hmp & Hmb & Hch & Hmh).
pose proof HM as (_ & (_ & _ & _ & Hca) & (_ & _ & _ & Hma) & _ & (HRC & HMC)).
pose proof (s18_mconf_len _ _ _ HMC) as Hl32.
destruct (s18_mname _ _ _ i HMC Hm16 Hi) as [Hstr Hlen].
unfold s9_nm, x_seg. fold (x_mcF cx) in *.
assert (Ha : m <= seg_spec.mseg_addr m i /\ seg_spec.mseg_addr m i + 16 <= m + seg_spec.SEG_M_SIZE)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE; lia).
split; [|split; [unfold seg_spec.SEG_C_SIZE in *; lia | unfold seg_spec.SEG_M_SIZE in *; lia]].
split; [exact Hc0|]. split; [exact Hc16|]. split; [exact HRC|]. split; [exact Hch|]. split; [exact Hca|].
split; [unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia|]. split; [exact Hstr|]. split.
- left. destruct Hmh as (b & n & Hin & H1 & H2). exists b, n. split; [exact Hin | lia].
- split; [apply (s18_sa_addr_sub _ m seg_spec.SEG_M_SIZE); [exact Hma | lia | lia | lia] | lia].
Qed.

Lemma s9_want : forall cx ly S W regs mem md k acc o c m i, s9M cx ly S W regs mem md k acc o c m ->
  (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  seg_spec.mseg_addr m i mod 4 = 0 /\ sa_mseg (rdW W mem) (seg_spec.mseg_addr m i) (x_seg cx i) /\
  sa_heap B ly S (seg_spec.mseg_addr m i) seg_spec.MSEG_SIZE /\
  sa_addr (rdW W mem) (seg_spec.mseg_addr m i) seg_spec.MSEG_SIZE.
Proof.
intros cx ly S W regs mem md k acc o c m i HM Hi.
destruct (s9_blocks cx ly S W regs mem md k acc o c m HM) as (_ & _ & _ & _ & _ & Hm16 & _ & _ & _ & Hmh).
pose proof HM as (_ & _ & (_ & _ & _ & Hma) & _ & (_ & HMC)).
pose proof (s18_mconf_len _ _ _ HMC) as Hl32.
assert (Ha : m <= seg_spec.mseg_addr m i /\ seg_spec.mseg_addr m i + seg_spec.MSEG_SIZE <= m + seg_spec.SEG_M_SIZE)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE; unfold x_mcF in Hi; lia).
split; [unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; Z.div_mod_to_equations; lia|].
split; [exact (s18_mseg _ _ _ i HMC Hi)|].
split; [destruct Hmh as (b & n & Hin & H1 & H2); exists b, n; split; [exact Hin | lia]|].
apply (s18_sa_addr_sub _ m seg_spec.SEG_M_SIZE); [exact Hma | lia | lia | unfold seg_spec.MSEG_SIZE; lia].
Qed.

Lemma s9_check_seg : forall cx i, (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  SegModel.check_seg (x_rcF cx) (x_seg cx i) = true.
Proof.
intros cx i Hi. pose proof (s18_harness (x_pl cx)) as [_ H].
exact (s18_check_seg_nth _ _ i H Hi).
Qed.

(* the seed of a run that touches registers only *)
Definition s9_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma s9_seed0 : forall (W : world SEGS) regs mem pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (s9_ss0 pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 9 0) [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem pc. split.
- unfold s9_ss0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + exact I.
  + unfold facts_ok. cbn. tauto.
- apply Forall_nil.
Qed.
Lemma s9_E0_agree : forall regs, env_agree 32 (Ereg regs []) (Eimg (Ereg regs [])).
Proof. intros regs. split; [intros i Hi; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.
Lemma s9_E0_reg : forall regs (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs [])) n = getr regs r.
Proof. intros regs n r Hn Hr. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs [] n r Hr). Qed.

Lemma s9R_pres : forall cx i regs regs2 c m, s9R cx i regs c m ->
  (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) -> s9R cx i regs2 c m.
Proof.
intros cx i regs regs2 c m (R18 & R19 & R21 & R22 & R23 & R24 & R26 & R27) HP.
split; [exact (eq_trans (HP 18 ltac:(unfold acallee_saved; lia)) R18)|].
split; [exact (eq_trans (HP 19 ltac:(unfold acallee_saved; lia)) R19)|].
split; [exact (eq_trans (HP 21 ltac:(unfold acallee_saved; lia)) R21)|].
split; [exact (eq_trans (HP 22 ltac:(unfold acallee_saved; lia)) R22)|].
split; [exact (eq_trans (HP 23 ltac:(unfold acallee_saved; lia)) R23)|].
split; [exact (eq_trans (HP 24 ltac:(unfold acallee_saved; lia)) R24)|].
split; [exact (eq_trans (HP 26 ltac:(unfold acallee_saved; lia)) R26)|].
exact (eq_trans (HP 27 ltac:(unfold acallee_saved; lia)) R27).
Qed.

(* ---- the points of turn i: s9M with r's shadow as o says, the loop's registers, and X ---- *)
Definition S9_at (i : nat) (off : Z) (o : lfo) (X : lcx -> bvmap 5 word -> reader -> Z -> Z -> Prop) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  s9M cx ly S W regs mem md k acc o c m -> s9R cx i regs c m -> X cx regs (rdW W mem) c m ->
  SRr SEGS W (cfg_at SEGS (BASE + off) regs mem md) (lt_post B MT cx).
Definition s9_X0 : lcx -> bvmap 5 word -> reader -> Z -> Z -> Prop := fun _ _ _ _ _ => True.
(* r's value after reac_segconf_role: the role when it answers Some, else the 0x5a stored before the call *)
Definition s9_rval (cx : lcx) (i : nat) : Z :=
  match SegModel.r_role (x_rcF cx) (s9_nm cx i) with Some v => v | None => 90 end.
Definition s9_rset (cx : lcx) (i : nat) : Z :=
  match SegModel.r_role (x_rcF cx) (s9_nm cx i) with Some _ => 1 | None => 0 end.
Definition S9_R1 (i : nat) : Prop := S9_at i LO9_R1 LFO_R (fun cx regs rd c m =>
  getr regs 20 = w64 (x_fr cx + FO_R) /\ getr regs 10 = w64 (s9_rset cx i) /\ sa_val rd (x_fr cx + FO_R) 4 (s9_rval cx i)).
Definition S9_R2 (i : nat) : Prop := S9_at i LO9_R2 LFO_R s9_X0.
Definition S9_R3 (i : nat) : Prop := S9_at i LO9_R3 LFO_R (fun cx regs rd c m =>
  getr regs 10 = w64 (seg_spec.model_ptr c (x_rcF cx) (s9_nm cx i))).
Definition S9_R4 (i : nat) : Prop := S9_at i LO9_R4 LFO_R s9_X0.
Definition S9_R5 (i : nat) : Prop := S9_at i LO9_R5 LFO_R (fun cx regs rd c m =>
  getr regs 10 = w64 (seg_spec.b2z (SegModel.r_ignored (x_rcF cx) (s9_nm cx i)))).
Definition S9_R6 (i : nat) : Prop := S9_at i LO9_R6 LFO_R s9_X0.
Definition S9_R7 (i : nat) : Prop := S9_at i LO9_R7 LFO_R (fun cx regs rd c m =>
  getr regs 10 = w64 (seg_spec.role_file_ptr c (x_rcF cx) (s9_nm cx i))).
Definition S9_R8 (i : nat) : Prop := S9_at i LO9_R8 LFO_R (fun cx regs rd c m =>
  getr regs 20 = w64 (seg_spec.role_file_ptr c (x_rcF cx) (s9_nm cx i)) /\
  getr regs 10 = w64 (seg_spec.ignore_file_ptr c (x_rcF cx) (s9_nm cx i))).
Definition S9_R9 (i : nat) : Prop := S9_at i LO9_R9 LFO_R s9_X0.

Hypothesis HMODEL : forall fx0 : YK11.FPState,
  reac_segconf_model_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_model) STK_reac_segconf_model RLO_A RHI_A.

(* 0x85518 .. 0x85520: a0 = c, a1 = &m->seg[i], jal reac_segconf_model; to 0x85524 *)
Lemma s9_T2 : forall i, S9_R3 i -> S9_R2 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HR _.
pose proof HM as ((HFR & (HRO & _) & _ & _) & _). pose proof HFR as (HJ & _).
destruct (s9_seed0 W regs mem LO9_R2) as [HS SHOK].
set (E0 := Eimg (Ereg regs [])) in HS, SHOK.
assert (EL0 : forall q, (q < A_TEXT)%nat -> ew E0 q = ew (Ereg regs []) q) by (intros q Hq; apply Eimg_low; exact Hq).
assert (HEI : img_env VAL A_LIM E0) by apply Eimg_env.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem) by (apply functional_extensionality; intros x; apply HF; intros (r0 & Hr0 & _); destruct Hr0).
pmkst HS. prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS); [exact (s9_E0_agree regs) | vm_compute; reflexivity]. }
rewrite (SIGP SS_reac_segconf_model ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_model) with AF_reac_segconf_model by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
rewrite EL0, (ew_Ereg_nat regs [] 26 26%bv eq_refl) in P10 by (unfold A_TEXT; lia).
rewrite EL0, (ew_Ereg_nat regs [] 19 19%bv eq_refl) in P11 by (unfold A_TEXT; lia).
pose proof HR as (_ & R19 & _ & _ & _ & _ & R26 & _). rewrite R26 in P10. rewrite R19 in P11.
pose proof (s9M_run cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mdv HB HM HJ
  (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (HQ & Hc64 & Hn64).
destruct (s9_call_frame cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) HB HM'
  eq_refl eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & _ & Hnev & _).
apply (s9_call_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_reac_segconf_model) LO9_R3
  STK_reac_segconf_model (fun r => getr r 10 = w64 (seg_spec.model_ptr c (x_rcF cx) (s9_nm cx i)))
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R3; lia) eq_refl).
- intros ch HPRE1. exact (HMODEL fx ly S W (ms_regs ms) mem mdv ch c (seg_spec.mseg_addr m i) (x_rcF cx) (s9_nm cx i)
    HPRE1 HRO P10 Hc64 P11 Hn64 HQ ltac:(unfold EV_reac_segconf_model; lia)).
- intros S2 W2 regs2 mem2 md2 HM2 HP2 HR2.
  exact (HN cx ly S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) HR2).
Qed.

Lemma s9_apost_true : forall STK FP regs ly S (W : world SEGS) mem md k Q W' c',
  apost_base SEGS B STK FP regs ly S W mem md k Q W' c' ->
  apost_base SEGS B STK FP regs ly S W mem md k (fun a b d e f g => True /\ Q a b d e f g) W' c'.
Proof.
intros STK FP regs ly S W mem md k Q W' c' (ly' & S' & regs' & mem' & md' & Ec & HJ & HP & HQ).
exists ly', S', regs', mem', md'. split; [exact Ec|]. split; [exact HJ|]. split; [exact HP | split; [exact I | exact HQ]].
Qed.

(* a C string the reader block holds at p (or NULL): what check_model / check_provenance ask of it *)
Lemma s9_str_in_c : forall cx ly S W regs mem md k acc o c m (p : Z) (os : option (list Z)),
  s9M cx ly S W regs mem md k acc o c m ->
  (forall s, os = Some s -> c <= p /\ p + Z.of_nat (length s) + 1 <= c + seg_spec.SEG_C_SIZE /\ (length s < 96)%nat) ->
  match os with
  | Some s => Z.of_nat (length s) + 1 < 2 ^ 32 /\ sa_heap B ly S p (Z.of_nat (length s) + 1) /\
              sa_addr (rdW W mem) p (Z.of_nat (length s) + 1)
  | None => True
  end.
Proof.
intros cx ly S W regs mem md k acc o c m p os HM Hb.
destruct os as [s|]; [|exact I]. destruct (Hb s eq_refl) as (H1 & H2 & H3).
destruct (s9_blocks cx ly S W regs mem md k acc o c m HM) as (_ & _ & _ & _ & _ & _ & _ & _ & Hch & _).
pose proof HM as (_ & (_ & _ & _ & Hca) & _).
split; [lia|]. split; [destruct Hch as (b & n & Hin & Hb1 & Hb2); exists b, n; split; [exact Hin | lia]|].
apply (s18_sa_addr_sub _ c seg_spec.SEG_C_SIZE); [exact Hca | lia | lia | lia].
Qed.

Ltac s9_pure_run W regs mem E0 EL0 HEI HS SHOK HJ pc :=
  destruct (s9_seed0 W regs mem pc) as [HS SHOK];
  set (E0 := Eimg (Ereg regs [])) in HS, SHOK;
  assert (EL0 : forall q, (q < A_TEXT)%nat -> ew E0 q = ew (Ereg regs []) q) by (intros q Hq; apply Eimg_low; exact Hq);
  assert (HEI : img_env VAL A_LIM E0) by apply Eimg_env;
  unfold cfg_at, w64;
  paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1); [apply awr_ok_nil|].

Hypothesis HCMODEL : forall fx0 : YK11.FPState,
  check_model_contract (fx := fx0) SEGS B (BASE + AF_check_model) STK_check_model RLO_A RHI_A.
Hypothesis HIGNORED : forall fx0 : YK11.FPState,
  reac_segconf_ignored_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_ignored) STK_reac_segconf_ignored RLO_A RHI_A.
Hypothesis HCIGNORE : forall fx0 : YK11.FPState,
  check_ignore_contract (fx := fx0) SEGS B (BASE + AF_check_ignore) STK_check_ignore.
Hypothesis HROLEFILE : forall fx0 : YK11.FPState,
  reac_segconf_role_file_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_role_file) STK_reac_segconf_role_file
    RLO_A RHI_A.

(* 0x85524 .. 0x85528: a1 = &m->seg[i], jal check_model (a0 = model_ptr); to 0x8552c *)
Lemma s9_T3 : forall i, S9_R4 i -> S9_R3 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HR HX.
pose proof HM as ((HFR & (HRO & _) & _ & _) & _ & _ & _ & (HRC & _)). pose proof HFR as (HJ & _).
s9_pure_run W regs mem E0 EL0 HEI HS SHOK HJ LO9_R3.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem) by (apply functional_extensionality; intros x; apply HF; intros (r0 & Hr0 & _); destruct Hr0).
pmkst HS. prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS); [exact (s9_E0_agree regs) | vm_compute; reflexivity]. }
rewrite (SIGP SS_check_model ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_check_model) with AF_check_model by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
rewrite EL0, (ew_Ereg_nat regs [] 10 10%bv eq_refl) in P10 by (unfold A_TEXT; lia).
rewrite EL0, (ew_Ereg_nat regs [] 19 19%bv eq_refl) in P11 by (unfold A_TEXT; lia).
pose proof HR as (_ & R19 & _ & _ & _ & _ & R26 & _). rewrite HX in P10. rewrite R19 in P11.
pose proof (s9M_run cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mdv HB HM HJ
  (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (_ & Hc64 & Hn64).
destruct (s9_call_frame cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) HB HM'
  eq_refl eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & _ & Hnev & _).
destruct (s9_blocks cx ly S W regs mem md k acc LFO_R c m HM) as (_ & Hc16 & Hcp & Hcb & _).
destruct (s18_model_str _ _ _ (s9_nm cx i) HRC Hc16 Hcp) as [HSTR HB2].
pose proof (s18_ptr_rng _ _ _ (s9_nm cx i) HRC ltac:(lia)) as (Hp1 & _).
pose proof (s9_check_seg cx i Hi) as HCK. apply s18_check_seg_split in HCK. destruct HCK as (_ & HCK2 & _).
apply (s9_call_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_check_model) LO9_R4
  STK_check_model (fun _ => True)
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R4; lia) eq_refl).
- intros ch HPRE1. eapply SRr_mono; [|intros W' c' _ H'; exact (s9_apost_true _ _ _ _ _ _ _ _ _ _ _ _ H')].
  assert (Hg64 : 0 <= seg_spec.model_ptr c (x_rcF cx) (s9_nm cx i) < 2 ^ 64) by (unfold x_rcF; unfold seg_spec.SEG_C_SIZE in *; lia).
  destruct (s9_want cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (Hw1 & Hw2 & Hw3 & Hw4).
  assert (HPRE : check_model_pre B ly S (rdW W mem) (seg_spec.model_ptr c (x_rcF cx) (s9_nm cx i))
    (seg_spec.mseg_addr m i) (SegModel.r_model (x_rcF cx) (s9_nm cx i)) (x_seg cx i)).
  { split; [exact Hw1|]. split; [exact Hw2|]. split; [exact Hw3|]. split; [exact Hw4|]. split; [exact HSTR|].
    split; [|exact HCK2].
    apply (s9_str_in_c cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m _ _ HM').
    intros s Hs. destruct (HB2 s Hs) as (h1 & h2 & h3). split; [exact h1|]. split; [exact h2 | lia]. }
  exact (HCMODEL fx ly S W (ms_regs ms) mem mdv ch _ _ _ _ HPRE1 HRO P10 Hg64 P11 Hn64 HPRE
    ltac:(unfold EV_check_model; lia)).
- intros S2 W2 regs2 mem2 md2 HM2 HP2 _.
  exact (HN cx ly S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) I).
Qed.

(* 0x8552c .. 0x85534: a0 = c, a1 = &m->seg[i], jal reac_segconf_ignored; to 0x85538 *)
Lemma s9_T4 : forall i, S9_R5 i -> S9_R4 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HR _.
pose proof HM as ((HFR & (HRO & _) & _ & _) & _). pose proof HFR as (HJ & _).
s9_pure_run W regs mem E0 EL0 HEI HS SHOK HJ LO9_R4.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem) by (apply functional_extensionality; intros x; apply HF; intros (r0 & Hr0 & _); destruct Hr0).
pmkst HS. prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS); [exact (s9_E0_agree regs) | vm_compute; reflexivity]. }
rewrite (SIGP SS_reac_segconf_ignored ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_ignored) with AF_reac_segconf_ignored by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
rewrite EL0, (ew_Ereg_nat regs [] 26 26%bv eq_refl) in P10 by (unfold A_TEXT; lia).
rewrite EL0, (ew_Ereg_nat regs [] 19 19%bv eq_refl) in P11 by (unfold A_TEXT; lia).
pose proof HR as (_ & R19 & _ & _ & _ & _ & R26 & _). rewrite R26 in P10. rewrite R19 in P11.
pose proof (s9M_run cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mdv HB HM HJ
  (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (HQ & Hc64 & Hn64).
destruct (s9_call_frame cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) HB HM'
  eq_refl eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & _ & Hnev & _).
apply (s9_call_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_reac_segconf_ignored) LO9_R5
  STK_reac_segconf_ignored (fun r => getr r 10 = w64 (seg_spec.b2z (SegModel.r_ignored (x_rcF cx) (s9_nm cx i))))
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R5; lia) eq_refl).
- intros ch HPRE1. exact (HIGNORED fx ly S W (ms_regs ms) mem mdv ch c (seg_spec.mseg_addr m i) (x_rcF cx) (s9_nm cx i)
    HPRE1 HRO P10 Hc64 P11 Hn64 HQ ltac:(unfold EV_reac_segconf_ignored; lia)).
- intros S2 W2 regs2 mem2 md2 HM2 HP2 HR2.
  exact (HN cx ly S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) HR2).
Qed.

(* 0x85538 .. 0x8553c: a1 = &m->seg[i], jal check_ignore (a0 = r_ignored); to 0x85540 *)
Lemma s9_T5 : forall i, S9_R6 i -> S9_R5 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HR HX.
pose proof HM as ((HFR & _) & _). pose proof HFR as (HJ & _).
s9_pure_run W regs mem E0 EL0 HEI HS SHOK HJ LO9_R5.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem) by (apply functional_extensionality; intros x; apply HF; intros (r0 & Hr0 & _); destruct Hr0).
pmkst HS. prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS); [exact (s9_E0_agree regs) | vm_compute; reflexivity]. }
rewrite (SIGP SS_check_ignore ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_check_ignore) with AF_check_ignore by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
rewrite EL0, (ew_Ereg_nat regs [] 10 10%bv eq_refl) in P10 by (unfold A_TEXT; lia).
rewrite EL0, (ew_Ereg_nat regs [] 19 19%bv eq_refl) in P11 by (unfold A_TEXT; lia).
pose proof HR as (_ & R19 & _ & _ & _ & _ & R26 & _). rewrite HX in P10. rewrite R19 in P11.
pose proof (s9M_run cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mdv HB HM HJ
  (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (_ & _ & Hn64).
destruct (s9_call_frame cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) HB HM'
  eq_refl eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & _ & Hnev & _).
pose proof (s9_check_seg cx i Hi) as HCK. apply s18_check_seg_split in HCK. destruct HCK as (_ & _ & HCK3 & _).
destruct (s9_want cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (Hw1 & Hw2 & Hw3 & Hw4).
apply (s9_call_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_check_ignore) LO9_R6
  STK_check_ignore (fun _ => True)
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R6; lia) eq_refl).
- intros ch HPRE1. eapply SRr_mono; [|intros W' c' _ H'; exact (s9_apost_true _ _ _ _ _ _ _ _ _ _ _ _ H')].
  exact (HCIGNORE fx ly S W (ms_regs ms) mem mdv ch _ _ _ _ HPRE1 P10
    ltac:(unfold seg_spec.b2z; destruct (SegModel.r_ignored (x_rcF cx) (s9_nm cx i)); lia) P11 Hn64
    (conj Hw1 (conj Hw2 (conj Hw3 (conj Hw4 (conj eq_refl HCK3))))) ltac:(unfold EV_check_ignore; lia)).
- intros S2 W2 regs2 mem2 md2 HM2 HP2 _.
  exact (HN cx ly S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) I).
Qed.

(* 0x85540 .. 0x85548: a0 = c, a1 = &m->seg[i], jal reac_segconf_role_file; to 0x8554c *)
Lemma s9_T6 : forall i, S9_R7 i -> S9_R6 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HR _.
pose proof HM as ((HFR & (HRO & _) & _ & _) & _). pose proof HFR as (HJ & _).
s9_pure_run W regs mem E0 EL0 HEI HS SHOK HJ LO9_R6.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem) by (apply functional_extensionality; intros x; apply HF; intros (r0 & Hr0 & _); destruct Hr0).
pmkst HS. prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS); [exact (s9_E0_agree regs) | vm_compute; reflexivity]. }
rewrite (SIGP SS_reac_segconf_role_file ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_role_file) with AF_reac_segconf_role_file by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
rewrite EL0, (ew_Ereg_nat regs [] 26 26%bv eq_refl) in P10 by (unfold A_TEXT; lia).
rewrite EL0, (ew_Ereg_nat regs [] 19 19%bv eq_refl) in P11 by (unfold A_TEXT; lia).
pose proof HR as (_ & R19 & _ & _ & _ & _ & R26 & _). rewrite R26 in P10. rewrite R19 in P11.
pose proof (s9M_run cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mdv HB HM HJ
  (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (HQ & Hc64 & Hn64).
destruct (s9_call_frame cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) HB HM'
  eq_refl eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & _ & Hnev & _).
apply (s9_call_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_reac_segconf_role_file)
  LO9_R7 STK_reac_segconf_role_file (fun r => getr r 10 = w64 (seg_spec.role_file_ptr c (x_rcF cx) (s9_nm cx i)))
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R7; lia) eq_refl).
- intros ch HPRE1. exact (HROLEFILE fx ly S W (ms_regs ms) mem mdv ch c (seg_spec.mseg_addr m i) (x_rcF cx) (s9_nm cx i)
    HPRE1 HRO P10 Hc64 P11 Hn64 HQ ltac:(unfold EV_reac_segconf_role_file; lia)).
- intros S2 W2 regs2 mem2 md2 HM2 HP2 HR2.
  exact (HN cx ly S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) HR2).
Qed.

Lemma s9R_of_eq : forall cx i regs regs2 c m, s9R cx i regs c m ->
  getr regs2 18 = getr regs 18 -> getr regs2 19 = getr regs 19 -> getr regs2 21 = getr regs 21 ->
  getr regs2 22 = getr regs 22 -> getr regs2 23 = getr regs 23 -> getr regs2 24 = getr regs 24 ->
  getr regs2 26 = getr regs 26 -> getr regs2 27 = getr regs 27 -> s9R cx i regs2 c m.
Proof.
intros cx i regs regs2 c m (R18 & R19 & R21 & R22 & R23 & R24 & R26 & R27) E18 E19 E21 E22 E23 E24 E26 E27.
split; [rewrite E18; exact R18|]. split; [rewrite E19; exact R19|]. split; [rewrite E21; exact R21|].
split; [rewrite E22; exact R22|]. split; [rewrite E23; exact R23|]. split; [rewrite E24; exact R24|].
split; [rewrite E26; exact R26 | rewrite E27; exact R27].
Qed.

Hypothesis HIGNFILE : forall fx0 : YK11.FPState,
  reac_segconf_ignore_file_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_ignore_file) STK_reac_segconf_ignore_file
    RLO_A RHI_A.
Hypothesis HCPROV : forall fx0 : YK11.FPState,
  check_provenance_contract (fx := fx0) SEGS B (BASE + AF_check_provenance) STK_check_provenance RLO_A RHI_A.

(* 0x8554c .. 0x85558: s4 = a0 (role_file_ptr), a0 = c, a1 = &m->seg[i], jal reac_segconf_ignore_file; to 0x8555c *)
Lemma s9_T7 : forall i, S9_R8 i -> S9_R7 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HR HX.
pose proof HM as ((HFR & (HRO & _) & _ & _) & _). pose proof HFR as (HJ & _).
s9_pure_run W regs mem E0 EL0 HEI HS SHOK HJ LO9_R7.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem) by (apply functional_extensionality; intros x; apply HF; intros (r0 & Hr0 & _); destruct Hr0).
pmkst HS. prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
rewrite EL0 in P10, P11, P2, P3, P4, P8, P9, P18, P19, P20, P21, P22, P23, P24, P26, P27 by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs [] 26 26%bv eq_refl) in P10. rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl) in P11.
rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl) in P2. rewrite (ew_Ereg_nat regs [] 3 3%bv eq_refl) in P3.
rewrite (ew_Ereg_nat regs [] 4 4%bv eq_refl) in P4. rewrite (ew_Ereg_nat regs [] 8 8%bv eq_refl) in P8.
rewrite (ew_Ereg_nat regs [] 9 9%bv eq_refl) in P9. rewrite (ew_Ereg_nat regs [] 18 18%bv eq_refl) in P18.
rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl) in P19. rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl) in P20.
rewrite (ew_Ereg_nat regs [] 21 21%bv eq_refl) in P21. rewrite (ew_Ereg_nat regs [] 22 22%bv eq_refl) in P22.
rewrite (ew_Ereg_nat regs [] 23 23%bv eq_refl) in P23. rewrite (ew_Ereg_nat regs [] 24 24%bv eq_refl) in P24.
rewrite (ew_Ereg_nat regs [] 26 26%bv eq_refl) in P26. rewrite (ew_Ereg_nat regs [] 27 27%bv eq_refl) in P27.
rewrite (SIGP SS_reac_segconf_ignore_file ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_ignore_file) with AF_reac_segconf_ignore_file by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
pose proof (s9R_of_eq cx i regs (ms_regs ms) c m HR P18 P19 P21 P22 P23 P24 P26 P27) as HR'.
pose proof HR as (_ & R19 & _ & _ & _ & _ & R26 & _). rewrite R26 in P10. rewrite R19 in P11. rewrite HX in P20.
pose proof (s9M_run cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mdv HB HM HJ P2 P3 P4 P8 P9) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (HQ & Hc64 & Hn64).
destruct (s9_call_frame cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) HB HM'
  eq_refl eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & _ & Hnev & _).
apply (s9_call_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_reac_segconf_ignore_file)
  LO9_R8 STK_reac_segconf_ignore_file (fun r => getr r 10 = w64 (seg_spec.ignore_file_ptr c (x_rcF cx) (s9_nm cx i)))
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R8; lia) eq_refl).
- intros ch HPRE1. exact (HIGNFILE fx ly S W (ms_regs ms) mem mdv ch c (seg_spec.mseg_addr m i) (x_rcF cx) (s9_nm cx i)
    HPRE1 HRO P10 Hc64 P11 Hn64 HQ ltac:(unfold EV_reac_segconf_ignore_file; lia)).
- intros S2 W2 regs2 mem2 md2 HM2 HP2 HR2.
  apply (HN cx ly S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2
    (s9R_pres cx i (ms_regs ms) regs2 c m HR' HP2)).
  split; [exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) P20) | exact HR2].
Qed.

(* 0x8555c .. 0x85568: a1 = ignore_file_ptr, a0 = s4 (role_file_ptr), a2 = &m->seg[i], jal check_provenance;
   to 0x8556c *)
Lemma s9_T8 : forall i, S9_R9 i -> S9_R8 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HR (HX20 & HX10).
pose proof HM as ((HFR & (HRO & _) & _ & _) & _ & _ & _ & (HRC & _)). pose proof HFR as (HJ & _).
s9_pure_run W regs mem E0 EL0 HEI HS SHOK HJ LO9_R8.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem) by (apply functional_extensionality; intros x; apply HF; intros (r0 & Hr0 & _); destruct Hr0).
pmkst HS. prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS); [exact (s9_E0_agree regs) | vm_compute; reflexivity]. }
rewrite (SIGP SS_check_provenance ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_check_provenance) with AF_check_provenance by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
rewrite EL0, (ew_Ereg_nat regs [] 20 20%bv eq_refl) in P10 by (unfold A_TEXT; lia).
rewrite EL0, (ew_Ereg_nat regs [] 10 10%bv eq_refl) in P11 by (unfold A_TEXT; lia).
rewrite EL0, (ew_Ereg_nat regs [] 19 19%bv eq_refl) in P12 by (unfold A_TEXT; lia).
pose proof HR as (_ & R19 & _ & _ & _ & _ & R26 & _). rewrite HX20 in P10. rewrite HX10 in P11. rewrite R19 in P12.
pose proof (s9M_run cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mdv HB HM HJ
  (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (_ & _ & Hn64).
destruct (s9_call_frame cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) HB HM'
  eq_refl eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & _ & Hnev & _).
destruct (s9_blocks cx ly S W regs mem md k acc LFO_R c m HM) as (_ & Hc16 & Hcp & Hcb & _).
destruct (s18_role_file_str _ _ _ (s9_nm cx i) HRC Hc16 Hcp) as [HSTR1 HB1].
destruct (s18_ignore_file_str _ _ _ (s9_nm cx i) HRC Hc16 Hcp) as [HSTR2 HB2].
pose proof (s18_ptr_rng _ _ _ (s9_nm cx i) HRC ltac:(lia)) as (_ & Hp1 & Hp2).
pose proof (s9_check_seg cx i Hi) as HCK. apply s18_check_seg_split in HCK. destruct HCK as (_ & _ & _ & HCK4 & HCK5).
apply (s9_call_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_check_provenance) LO9_R9
  STK_check_provenance (fun _ => True)
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R9; lia) eq_refl).
- intros ch HPRE1. eapply SRr_mono; [|intros W' c' _ H'; exact (s9_apost_true _ _ _ _ _ _ _ _ _ _ _ _ H')].
  assert (Hg1 : 0 <= seg_spec.role_file_ptr c (x_rcF cx) (s9_nm cx i) < 2 ^ 64)
    by (unfold x_rcF; unfold seg_spec.SEG_C_SIZE in *; lia).
  assert (Hg2 : 0 <= seg_spec.ignore_file_ptr c (x_rcF cx) (s9_nm cx i) < 2 ^ 64)
    by (unfold x_rcF; unfold seg_spec.SEG_C_SIZE in *; lia).
  destruct (s9_want cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (Hw1 & Hw2 & Hw3 & Hw4).
  assert (HPRE : check_provenance_pre B ly S (rdW W mem) (seg_spec.role_file_ptr c (x_rcF cx) (s9_nm cx i))
    (seg_spec.ignore_file_ptr c (x_rcF cx) (s9_nm cx i)) (seg_spec.mseg_addr m i)
    (SegModel.r_role_file (x_rcF cx) (s9_nm cx i)) (SegModel.r_ignore_file (x_rcF cx) (s9_nm cx i)) (x_seg cx i)).
  { split; [exact Hw1|]. split; [exact Hw2|]. split; [exact Hw3|]. split; [exact Hw4|]. split; [exact HSTR1|].
    split; [apply (s9_str_in_c cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m _ _ HM'); exact HB1|].
    split; [exact HSTR2|].
    split; [apply (s9_str_in_c cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m _ _ HM'); exact HB2|].
    split; [exact HCK4 | exact HCK5]. }
  exact (HCPROV fx ly S W (ms_regs ms) mem mdv ch _ _ _ _ _ _ HPRE1 HRO P10 Hg1 P11 Hg2 P12 Hn64 HPRE
    ltac:(unfold EV_check_provenance; lia)).
- intros S2 W2 regs2 mem2 md2 HM2 HP2 _.
  exact (HN cx ly S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) I).
Qed.

(* ---- reading a stored chunk back, and a byte the run did not store ---- *)
Lemma s9_aview_pt : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma s9_chunk_rd : forall E ss (H : word -> bool) ms i r off (w : N) e j,
  st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) -> 0 <= j < Z.of_N w ->
  aview SEGS H (ms_mem ms) (base_val E (YP09.r_base r) + off + j) = Some (bv_unsigned (byte_of_word (sv_denot E e) j)).
Proof.
intros E ss H ms i r off w e j HS Hi Hc Hj.
pose proof (st_ok_region_nth E ss (restrict H ms) i r HS Hi) as HR.
pose proof (region_ok_chunk SEGS E _ r _ HR Hc) as HC.
destruct (HC j ltac:(cbn; lia)) as (b & Hb & Hm). cbn in Hb. injection Hb as <-.
unfold aview. cbn [YP09.c_off] in Hm. change (ms_mem (restrict H ms)) with (mrestrict H (ms_mem ms)) in Hm.
rewrite Hm. reflexivity.
Qed.

(* ---- the seed at the loop head 0x854f0: s1's slot 96 (&r, atom 32), r's shadow byte SH(FR) + 22 and r, both
   written by the run ---- *)
Definition s9_ssL : sstate := mkSS LO9_LOOP sr_atoms
  [ YP09.mkRegion (Some 9%nat) 96 104 0 0 [YP09.mkChunk 96 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 21%nat) 22 23 22 23 [];
    YP09.mkRegion (Some 32%nat) 0 4 0 4 [] ] None
  (mkFacts [(21%nat, mkAF 0x7fff8000 (0x7fff8000 + 2 ^ 44) 0); (32%nat, mkAF 4096 (2 ^ 47) 0)] [] []).
Definition s9_EL (regs : bvmap 5 word) (cx : lcx) : env := Eimg (Ereg regs [w64 (x_fr cx + FO_R)]).

Lemma s9_seedL : forall cx ly S W regs mem md k acc c m i,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc LFO0 c m -> s9R cx i regs c m ->
  st_ok_pi SEGS VAL (s9_EL regs cx) s9_ssL
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO9_LOOP)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 9 0) [] (s9_EL regs cx) (mrestrict (w_H W) mem).
Proof.
intros cx ly S W regs mem md k acc c m i HB HM HR.
pose proof (s9_base_facts cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
pose proof HM as ((HFR & _) & _ & _ & HSL & _). destruct HFR as (HJ & _ & _ & _ & _ & R9 & _).
destruct (s9_frame_at cx ly S W mem md k HB HJ) as (HAR & Hin & EF & Hfa & Hf4 & Hfc & Happ).
pose proof (al_frames _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & _ & HFP & HSP).
rewrite <- EF in HFP, HSP. change (fs_frame_bytes LT_FCLS) with 512 in HFP, HSP.
pose proof HR as (_ & _ & R21 & _).
pose proof asan_consts as (C1 & _).
assert (Hsh : x_sh cx = 0x7fff8000 + x_fr cx / 8) by reflexivity.
assert (Hshr : 0x7fff8000 <= x_sh cx < 0x7fff8000 + 2 ^ 44).
{ rewrite Hsh. split; [pose proof (Z.div_pos (x_fr cx) 8); lia|].
  assert (x_fr cx / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
set (E := s9_EL regs cx).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs [w64 (x_fr cx + FO_R)]) q)
  by (intros q Hq; unfold E, s9_EL; apply Eimg_low; exact Hq).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = w64 (x_sh cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E32 : ew E 32 = w64 (x_fr cx + FO_R)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
split.
- unfold s9_ssL. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold E, s9_EL. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (x_s1 cx) 96 8 _ (x_fr cx + FO_R));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold FO_R; lia | lia
        | apply (val_mem_of_rdword SEGS); exact (HSL 96 _ ltac:(unfold LT_L; cbn [In]; tauto))].
    * rewrite E21, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace o with 22 by lia. apply (apresent_writable SEGS).
      exact (proj1 (HSP 22 ltac:(lia))).
    * rewrite E32, unsigned_lit_small by (unfold FO_R; lia). split; [unfold FO_R; lia|]. split; [unfold FO_R; lia|].
      split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFP (x_fr cx + FO_R + o) ltac:(unfold FO_R; lia))).
  + apply pairwise_disjoint_of_extents.
    unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E21, E32, !unsigned_lit_small by (unfold FO_R; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold FO_R.
    destruct Happ as (_ & [Hl | (Hh & _)]); unfold kLowShadowBeg, kHighMemBeg in *; repeat split; lia.
  + split; [|split; exact I].
    cbn [f_atoms atoms_ok]. split; [|split; [|exact I]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    * rewrite E21, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
    * rewrite E32, unsigned_lit_small by (unfold FO_R; lia). change (2 ^ 0) with 1. rewrite Z.mod_1_r. unfold FO_R. lia.
- apply Forall_nil.
Qed.

Hypothesis HROLE : forall fx0 : YK11.FPState,
  reac_segconf_role_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_role) STK_reac_segconf_role RLO_A RHI_A.

(* 0x854f0 .. 0x85508: r's shadow byte := 4 (r in scope), r := 0x5a, a0 = c, a1 = &m->seg[i], a2 = &r,
   jal reac_segconf_role; to 0x8550c *)
Lemma s9_T0 : forall i, S9_R1 i -> S9_loop_stmt i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HR.
pose proof HM as ((HFR & (HRO & _) & _ & _) & _). pose proof HFR as (HJ & _).
destruct (s9_seedL cx ly S W regs mem md k acc c m i HB HM HR) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (s9_EL regs cx)) by (unfold s9_EL; apply Eimg_env).
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK (0, 0).
{ pose proof (s9_base_facts cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
  pose proof HR as (_ & _ & R21 & _).
  destruct (s9_frame_at cx ly S W mem md k HB HJ) as (_ & _ & EF & _ & Hf4 & Hfc & _).
  assert (E21 : ew (s9_EL regs cx) 21 = w64 (x_sh cx)).
  { unfold s9_EL. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl). exact R21. }
  assert (E32 : ew (s9_EL regs cx) 32 = w64 (x_fr cx + FO_R)).
  { unfold s9_EL. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (Hshr : 0x7fff8000 <= x_sh cx < 0x7fff8000 + 2 ^ 44).
  { change (x_sh cx) with (0x7fff8000 + x_fr cx / 8). split; [pose proof (Z.div_pos (x_fr cx) 8); lia|].
    assert (x_fr cx / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; pose proof asan_consts as (C1 & _); lia). lia. }
  unfold s9_ssL. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | rewrite E21; apply unsigned_lit_small; lia | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite <- EF. change (fs_frame_bytes LT_FCLS / 8) with 64. change (shadow_addr (x_fr cx)) with (x_sh cx). lia. }
  eapply awr_ok_cons_gen; [reflexivity | rewrite E32; apply unsigned_lit_small; unfold FO_R;
    pose proof asan_consts as (C1 & _); lia | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
  exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite <- EF. change (fs_frame_bytes LT_FCLS) with 512. unfold FO_R in Ha. lia. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
pose proof (s9_base_facts cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
pose proof HR as (R18 & R19 & R21 & R22 & R23 & R24 & R26 & R27).
destruct (s9_frame_at cx ly S W (ms_mem ms) mdv k HB HJ) as (HAR & Hin & EF & Hfa & Hf4 & Hfc & Happ).
pose proof asan_consts as (C1 & _).
set (E := s9_EL regs cx) in *.
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs [w64 (x_fr cx + FO_R)]) q)
  by (intros q Hq; unfold E, s9_EL; apply Eimg_low; exact Hq).
assert (E21 : ew E 21 = w64 (x_sh cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 4)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = w64 90)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = w64 (x_fr cx + FO_R)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Hshr : 0x7fff8000 <= x_sh cx < 0x7fff8000 + 2 ^ 44).
{ change (x_sh cx) with (0x7fff8000 + x_fr cx / 8). split; [pose proof (Z.div_pos (x_fr cx) 8); lia|].
  assert (x_fr cx / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (Hfr0 : 0 <= x_fr cx + FO_R < 2 ^ 64) by (unfold FO_R; lia).
(* the bytes the run stored: r's shadow byte 4, r = 0x5a; all others kept *)
assert (KW : forall a, 0 <= a < 2 ^ 64 -> a <> x_sh cx + 22 -> ~ (x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
  rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha H1 H2. apply s9_aview_pt. apply HF. rewrite unsigned_lit_small by lia.
  intros (r0 & Hr0 & Hw). unfold s9_ssL in Hr0. cbn [ss_mem In] in Hr0.
  destruct Hr0 as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  - lia.
  - rewrite E21, unsigned_lit_small in Hw by lia. lia.
  - rewrite E32, unsigned_lit_small in Hw by lia. lia. }
assert (H4 : rdW W (ms_mem ms) (x_sh cx + 22) = Some 4).
{ pose proof (s9_chunk_rd E _ (w_H W) ms 1 _ 22 1 (SOff 22 0) 0 HS eq_refl ltac:(cbn; left; reflexivity) ltac:(lia))
    as Hc. cbn [YP09.r_base base_val] in Hc. rewrite E21, unsigned_lit_small, Z.add_0_r in Hc by lia.
  rewrite Hc. cbn [sv_denot]. rewrite E22. vm_compute. reflexivity. }
assert (H90 : sa_val (rdW W (ms_mem ms)) (x_fr cx + FO_R) 4 90).
{ intros k0 Hk0. pose proof (s9_chunk_rd E _ (w_H W) ms 2 _ 0 4 (SOff 23 0) (Z.of_nat k0) HS eq_refl
    ltac:(cbn; left; reflexivity) ltac:(lia)) as Hc. cbn [YP09.r_base base_val] in Hc.
  rewrite E32, unsigned_lit_small, Z.add_0_r in Hc by lia. rewrite Hc. cbn [sv_denot]. rewrite E23.
  destruct k0 as [|[|[|[|k0]]]]; [vm_compute; reflexivity .. | lia]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
prreg HS (20%bv : bv 5) P20.
rewrite EL, (ew_Ereg_nat regs _ 26 26%bv eq_refl), R26 in P10 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 19 19%bv eq_refl), R19 in P11 by (unfold A_TEXT; lia).
rewrite E32 in P12. rewrite E32 in P20.
(* s4 changed (0x854f4), so the run does not preserve every callee-saved register: the ones S09 keeps, one by one *)
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26.
prreg HS (27%bv : bv 5) Q27.
rewrite EL, (ew_Ereg_nat regs _ 2 2%bv eq_refl) in Q2 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 3 3%bv eq_refl) in Q3 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 4 4%bv eq_refl) in Q4 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 8 8%bv eq_refl) in Q8 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 9 9%bv eq_refl) in Q9 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 18 18%bv eq_refl) in Q18 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 19 19%bv eq_refl) in Q19 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 21 21%bv eq_refl) in Q21 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 22 22%bv eq_refl) in Q22 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 23 23%bv eq_refl) in Q23 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 24 24%bv eq_refl) in Q24 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 26 26%bv eq_refl) in Q26 by (unfold A_TEXT; lia).
rewrite EL, (ew_Ereg_nat regs _ 27 27%bv eq_refl) in Q27 by (unfold A_TEXT; lia).
rewrite (SIGP SS_reac_segconf_role ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_role) with AF_reac_segconf_role by (vm_compute; reflexivity).
pose proof (s9M_agree cx ly S W regs mem md k acc LFO0 LFO_R c m ly S W (ms_regs ms) (ms_mem ms) mdv HB HM HJ
  Q2 Q3 Q4 Q8 Q9 (s9_agree_win cx ly S W regs mem md k acc LFO0 c m W (ms_mem ms) HB HM KW) H4
  eq_refl eq_refl eq_refl eq_refl (Permutation_refl _) (or_introl eq_refl)) as HM'.
pose proof HM' as ((_ & (HRO' & _) & _) & _).
pose proof (s9R_of_eq cx i regs (ms_regs ms) c m HR Q18 Q19 Q21 Q22 Q23 Q24 Q26 Q27) as HR'.
destruct (s9_query_pre cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO_R c m i HM' Hi) as (HQ & Hc64 & Hn64).
destruct (s9_call_frame cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO_R c m (ms_regs ms) HB HM'
  eq_refl eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & _ & Hnev & _).
set (out := x_fr cx + FO_R) in *.
set (o := SegModel.r_role (x_rcF cx) (s9_nm cx i)).
assert (Hout0 : out <> 0) by (unfold out, FO_R; lia).
(* r is a slot of the live class-3 frame, its shadow byte 4 *)
assert (HDST : sa_dst SEGS B ly S W (ms_mem ms) (ms_regs ms) out 4).
{ left. split.
  - exists LT_FCLS, (x_fpos cx). split; [exact Hin|]. split; [unfold LT_FCLS; lia|].
    rewrite <- EF. change (fs_frame_bytes LT_FCLS) with 512. unfold out, FO_R. lia.
  - intros x Hx. exists 4. split.
    + replace (shadow_of_addr SHADOW_OFF x) with (x_sh cx + 22); [exact H4|].
      change (x_sh cx) with (SHADOW_OFF + x_fr cx / 8). unfold shadow_of_addr.
      unfold out, FO_R in Hx. clear -Hx Hfa. Z.div_mod_to_equations. lia.
    + right. split; [|lia]. unfold out, FO_R in Hx. clear -Hx Hfa. Z.div_mod_to_equations. lia. }
apply (s9_call_step_w cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO_R c m (ms_regs ms)
  (BASE + AF_reac_segconf_role) LO9_R1 STK_reac_segconf_role (role_W out o) (fun a => out <> 0 /\ out <= a < out + 4)
  (fun W' regs' mem' => getr regs' 10 = w64 (match o with Some _ => 1 | None => 0 end) /\
     (match o with Some v => out <> 0 -> sa_val (aview SEGS (w_H W') mem') out 4%nat v | None => True end))
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R1; lia) eq_refl).
- intros a (r0 & Hr0 & Ha). unfold role_W in Hr0. destruct o; [|destruct Hr0].
  replace (out =? 0) with false in Hr0 by (symmetry; apply Z.eqb_neq; exact Hout0).
  destruct Hr0 as [<-|[]]. cbn [fst snd] in Ha. exact Ha.
- intros a (_ & Ha). exact Ha.
- intros ch HPRE1.
  assert (Hout4 : out mod 4 = 0) by (unfold out, FO_R; clear -Hfa; Z.div_mod_to_equations; lia).
  eapply SRr_mono.
  + exact (HROLE fx ly S W (ms_regs ms) (ms_mem ms) mdv ch c (seg_spec.mseg_addr m i) out (x_rcF cx) (s9_nm cx i)
      HPRE1 HRO' P10 Hc64 P11 Hn64 P12 Hfr0 (conj HQ (or_intror (conj Hout4 HDST)))
      ltac:(unfold EV_reac_segconf_role; lia)).
  + intros W' c' _ (ly' & S' & regs' & mem' & md' & Ec & HJ' & HP' & (T1 & T2 & T3 & T4)).
    exists ly', S', regs', mem', md'. split; [exact Ec|]. split; [exact HJ'|]. split; [exact HP'|].
    split; [split; [exact T1 | exact T2]|]. split; [exact T3 | exact T4].
- intros S2 W2 regs2 mem2 md2 HM2 HP2 (HR10 & HRv) KR.
  apply (HN cx ly S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2 (s9R_pres cx i (ms_regs ms) regs2 c m HR' HP2)).
  split; [exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) P20)|].
  unfold s9_rset, s9_rval. fold o. split; [exact HR10|].
  destruct o as [v|].
  + exact (HRv Hout0).
  + intros k0 Hk0. rewrite (KR eq_refl) by (unfold out in *; lia). exact (H90 k0 Hk0).
Qed.

Lemma s9_rval_rng : forall cx ly S W regs mem md k acc o c m i, s9M cx ly S W regs mem md k acc o c m ->
  0 <= s9_rval cx i < 2 ^ 31.
Proof.
intros cx ly S W regs mem md k acc o c m i HM. pose proof HM as (_ & _ & _ & _ & (HRC & _)).
unfold s9_rval. destruct (SegModel.r_role (x_rcF cx) (s9_nm cx i)) as [v|] eqn:Ev; [|lia].
exact (s18_role_rng _ _ _ _ _ HRC Ev).
Qed.

(* the seed at 0x8550c: r (at s4, atom 32 its value) *)
Definition s9_ss1 : sstate := mkSS LO9_R1 sr_atoms
  [YP09.mkRegion (Some 20%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))]] None
  (mkFacts [(32%nat, mkAF 0 (2 ^ 31 - 1) 0)] [] []).
Definition s9_E1 (regs : bvmap 5 word) (cx : lcx) (i : nat) : env := Eimg (Ereg regs [w64 (s9_rval cx i)]).

Hypothesis HCROLE : forall fx0 : YK11.FPState,
  check_role_contract (fx := fx0) SEGS B (BASE + AF_check_role) STK_check_role.

(* 0x8550c .. 0x85514: a1 = r (lw), a2 = &m->seg[i], jal check_role (a0 = role's answer); to 0x85518 *)
Lemma s9_T1 : forall i, S9_R2 i -> S9_R1 i.
Proof.
intros i HN cx ly S W regs mem md k acc c m HB HFRM Hi HM HR (X20 & X10 & Xr).
pose proof HM as ((HFR & _) & _). pose proof HFR as (HJ & _).
pose proof (s9_rval_rng cx ly S W regs mem md k acc LFO_R c m i HM) as Hrv.
destruct (s9_frame_at cx ly S W mem md k HB HJ) as (_ & _ & _ & _ & Hf4 & Hfc & _).
pose proof asan_consts as (C1 & _).
set (E := s9_E1 regs cx i).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs [w64 (s9_rval cx i)]) q)
  by (intros q Hq; unfold E, s9_E1; apply Eimg_low; exact Hq).
assert (E20 : ew E 20 = w64 (x_fr cx + FO_R))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact X20).
assert (E32 : ew E 32 = w64 (s9_rval cx i)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HS : st_ok_pi SEGS VAL E s9_ss1 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO9_R1)) mem (seg_rom SEGS)))).
{ unfold s9_ss1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - unfold E, s9_E1. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E20, unsigned_lit_small by (unfold FO_R; lia).
    split; [unfold FO_R; lia|]. split; [unfold FO_R; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (x_fr cx + FO_R) 0 4 _ (s9_rval cx i));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia
      | rewrite Z.add_0_r; exact (s9_val_of_rd _ _ _ _ _ Xr)].
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
assert (SHOK : sh_ok SEGS (SOff 9 0) [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s9_E1; apply Eimg_env).
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK (0, 0).
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r0 & Hr0 & Hw). cbn [s9_ss1 ss_mem In] in Hr0.
  destruct Hr0 as [<-|[]]. cbn in Hw. lia. }
pmkst HS. prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12.
rewrite E32 in P11.
rewrite EL, (ew_Ereg_nat regs _ 10 10%bv eq_refl), X10 in P10 by (unfold A_TEXT; lia).
pose proof HR as (_ & R19 & _).
rewrite EL, (ew_Ereg_nat regs _ 19 19%bv eq_refl), R19 in P12 by (unfold A_TEXT; lia).
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [w64 (s9_rval cx i)] HS); [|vm_compute; reflexivity].
  split; [intros q Hq; unfold E, s9_E1; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
rewrite (SIGP SS_check_role ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_check_role) with AF_check_role by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
pose proof (s9M_run cx ly S W regs mem md k acc LFO_R c m (ms_regs ms) mdv HB HM HJ
  (HPR 2 ltac:(unfold acallee_saved; lia)) (HPR 3 ltac:(unfold acallee_saved; lia))
  (HPR 4 ltac:(unfold acallee_saved; lia)) (HPR 8 ltac:(unfold acallee_saved; lia))
  (HPR 9 ltac:(unfold acallee_saved; lia))) as HM'.
destruct (s9_query_pre cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (_ & _ & Hn64).
destruct (s9_call_frame cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) HB HM'
  eq_refl eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & _ & Hnev & _).
destruct (s9_want cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m i HM' Hi) as (Hw1 & Hw2 & Hw3 & Hw4).
pose proof (s9_check_seg cx i Hi) as HCK. apply s18_check_seg_split in HCK. destruct HCK as (HCK1 & _).
assert (HPRE : check_role_pre B ly S (rdW W mem) (s9_rset cx i) (s9_rval cx i) (seg_spec.mseg_addr m i)
  (SegModel.r_role (x_rcF cx) (s9_nm cx i)) (x_seg cx i)).
{ split; [exact Hw1|]. split; [exact Hw2|]. split; [exact Hw3|]. split; [exact Hw4|].
  unfold s9_rset, s9_rval in *. unfold s9_nm in *.
  destruct (SegModel.r_role (x_rcF cx) (SegModel.ms_name (x_seg cx i))) as [v|];
    (split; [reflexivity|]); (split; [|exact HCK1]); [split; [reflexivity | lia] | exact I]. }
apply (s9_call_step cx ly S W (ms_regs ms) mem mdv k acc LFO_R c m (ms_regs ms) (BASE + AF_check_role) LO9_R2
  STK_check_role (fun _ => True)
  HB HM' eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; tauto) P1
  ltac:(unfold LO9_R2; lia) eq_refl).
- intros ch HPRE1. eapply SRr_mono; [|intros W' c' _ H'; exact (s9_apost_true _ _ _ _ _ _ _ _ _ _ _ _ H')].
  exact (HCROLE fx ly S W (ms_regs ms) mem mdv ch _ _ _ _ _ HPRE1 P10
    ltac:(unfold s9_rset; destruct (SegModel.r_role (x_rcF cx) (s9_nm cx i)); lia) P11 ltac:(lia) P12 Hn64 HPRE
    ltac:(unfold EV_check_role; lia)).
- intros S2 W2 regs2 mem2 md2 HM2 HP2 _.
  exact (HN cx ly S2 W2 regs2 mem2 md2 k acc c m HB HFRM Hi HM2
    (s9R_pres cx i regs regs2 c m HR (fun r Hr => eq_trans (HP2 r Hr) (HPR r Hr))) I).
Qed.

(* ---- the seed at 0x8556c: r's shadow byte (written: out of scope again), SH(m + 0x2000) (check 20 reads it, 0),
   s1's slot 184 (m + 0x2000, m atom 32), m->n (atom 33); i (s2, atom 18) at most 31 ---- *)
Definition s9_ss9 (cs : list acond) : sstate := mkSS LO9_R9 sr_atoms
  [ YP09.mkRegion (Some 9%nat) 184 192 0 0 [YP09.mkChunk 184 (CVal 8 (SOff 32 0x2000))];
    YP09.mkRegion (Some 21%nat) 22 23 22 23 [];
    YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
    YP09.mkRegion (Some 32%nat) 0x2000 0x2004 0 0 [YP09.mkChunk 0x2000 (CVal 4 (SOff 33 0))] ] None
  (mkFacts [(21%nat, mkAF 0x7fff8000 (0x7fff8000 + 2 ^ 44) 0); (18%nat, mkAF 0 31 0); (33%nat, mkAF 1 32 0)] cs []).
Definition s9_E9 (regs : bvmap 5 word) (m n : Z) : env := Eimg (Ereg regs [w64 m; w64 n]).

(* r's shadow byte and m->n's shadow byte are different bytes: the frame and the block m are apart *)
Lemma s9_sh_apart : forall cx ly S W regs mem md k acc o c m, lt_base B MT cx -> s9M cx ly S W regs mem md k acc o c m ->
  x_sh cx + 22 <> shadow_addr (m + seg_spec.MC_N).
Proof.
intros cx ly S W regs mem md k acc o c m HB HM E.
pose proof HM as ((HFR & _) & _ & (Hmin & _ & Hm16 & _) & _). pose proof HFR as (HJ & _).
destruct (s9_frame_at cx ly S W mem md k HB HJ) as (HAR & Hin & EF & Hfa & Hf4 & Hfc & _).
apply (s9_blk_frame_apart ly S W mem md m seg_spec.SEG_M_SIZE LT_FCLS (x_fpos cx) (m + seg_spec.MC_N) HAR Hmin Hin).
- change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE. unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE. lia.
- rewrite <- EF. change (fs_frame_bytes LT_FCLS) with 512.
  change (x_sh cx) with (SHADOW_OFF + x_fr cx / 8) in E. unfold shadow_addr, seg_spec.MC_N in *.
  clear -E Hfa Hm16. Z.div_mod_to_equations. lia.
Qed.

Lemma s9_seed9 : forall cx ly S W regs mem md k acc c m i cs,
  lt_base B MT cx -> s9M cx ly S W regs mem md k acc LFO_R c m -> s9R cx i regs c m ->
  (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  conds_ok (s9_E9 regs m (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) cs ->
  st_ok_pi SEGS VAL (s9_E9 regs m (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) (s9_ss9 cs)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO9_R9)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 9 0) [] (s9_E9 regs m (Z.of_nat (length (SegModel.mc_seg (x_mcF cx))))) (mrestrict (w_H W) mem).
Proof.
intros cx ly S W regs mem md k acc c m i cs HB HM HR Hi HCS.
pose proof (s9_base_facts cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
pose proof (s9_sh_apart cx ly S W regs mem md k acc LFO_R c m HB HM) as Hne.
pose proof HM as ((HFR & _) & Hc & Hm & HSL & (HRC & HMC)).
destruct HFR as (HJ & _ & _ & _ & _ & R9 & _).
pose proof Hm as (Hmin & Hm4 & Hm16 & Hmaddr).
destruct (s9_frame_at cx ly S W mem md k HB HJ) as (HAR & Hin & EF & Hfa & Hf4 & Hfc & Happ).
pose proof (al_frames _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & _ & _ & HSP).
rewrite <- EF in HSP. change (fs_frame_bytes LT_FCLS) with 512 in HSP.
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmin) as (_ & _ & Hmc & Hmapp & _).
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc, Hmapp.
pose proof HR as (R18 & _ & R21 & _ & _ & _ & _ & R27).
pose proof asan_consts as (C1 & _).
set (n := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
assert (Hn : 1 <= n <= 32) by (pose proof (s18_mconf_len _ _ _ HMC); unfold n, x_mcF in *; lia).
assert (Hshr : 0x7fff8000 <= x_sh cx < 0x7fff8000 + 2 ^ 44).
{ change (x_sh cx) with (0x7fff8000 + x_fr cx / 8). split; [pose proof (Z.div_pos (x_fr cx) 8); lia|].
  assert (x_fr cx / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (Hsm : 0x7fff8000 <= shadow_addr (m + seg_spec.MC_N) < 0x7fff8000 + 2 ^ 44).
{ unfold shadow_addr, SHADOW_OFF, seg_spec.MC_N. split; [pose proof (Z.div_pos (m + 8192) 8); lia|].
  assert ((m + 8192) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; unfold seg_spec.SEG_M_SIZE in *; lia). lia. }
set (E := s9_E9 regs m n).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs [w64 m; w64 n]) q)
  by (intros q Hq; unfold E, s9_E9; apply Eimg_low; exact Hq).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 (Z.of_nat i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E21 : ew E 21 = w64 (x_sh cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E27 : ew E 27 = w64 (shadow_addr (m + seg_spec.MC_N)))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = w64 m) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
split.
- unfold s9_ss9. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold E, s9_E9. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (x_s1 cx) 184 8 _ (m + seg_spec.MC_N));
        [cbn [sv_denot]; rewrite E32; unfold w64; rewrite unsigned_lit_small by (unfold seg_spec.SEG_M_SIZE in *; lia);
         reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.SEG_M_SIZE, seg_spec.MC_N in *; lia | lia
        | apply (val_mem_of_rdword SEGS); exact (HSL 184 _ ltac:(unfold LT_L; cbn [In]; tauto))].
    * rewrite E21, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace o with 22 by lia. apply (apresent_writable SEGS).
      exact (proj1 (HSP 22 ltac:(lia))).
    * rewrite E27, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (shadow_addr (m + seg_spec.MC_N)) 0 1 _ 0); [reflexivity | lia | lia |].
      apply s9_val_of_rd. intros k0 Hk0. destruct k0 as [|k0]; [|lia]. rewrite Z.add_0_r, Z.add_0_r.
      rewrite (s9_mn_shadow _ m Hmaddr Hm16). reflexivity.
    * rewrite E32, unsigned_lit_small by (unfold seg_spec.SEG_M_SIZE in *; lia).
      split; [lia|]. split; [unfold seg_spec.SEG_M_SIZE in *; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ m 0x2000 4 _ n);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia
        | exact (s9_val_of_rd _ _ _ _ _ (s18_mconf_n _ _ _ HMC))].
  + apply pairwise_disjoint_of_extents.
    unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E21, E27, E32, !unsigned_lit_small by (unfold seg_spec.SEG_M_SIZE in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct Hmapp as (_ & [Hl | (Hh & _)]); unfold kLowShadowBeg, kHighMemBeg, seg_spec.SEG_M_SIZE in *;
    repeat split; lia.
  + split; [|split; [exact HCS | exact I]].
    cbn [f_atoms atoms_ok]. split; [|split; [|split; [|exact I]]]; unfold afact_ok; cbn [af_lo af_hi af_al2];
      change (2 ^ 0) with 1; rewrite ?Z.mod_1_r.
    * rewrite E21, unsigned_lit_small by lia. lia.
    * rewrite E18, unsigned_lit_small by (pose proof (s18_mconf_len _ _ _ HMC); unfold x_mcF in *; lia).
      pose proof (s18_mconf_len _ _ _ HMC). unfold x_mcF in *. lia.
    * rewrite E33, unsigned_lit_small by lia. lia.
- apply Forall_nil.
Qed.

Ltac s9_t9_awr cx EF E21 :=
  apply awr_ok_cons_ro; [cbn; lia|];
  eapply awr_ok_cons_gen; [reflexivity | rewrite E21; apply unsigned_lit_small; lia | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left;
    exists LT_FCLS, (x_fpos cx); split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd];
    rewrite <- EF; change (fs_frame_bytes LT_FCLS / 8) with 64; change (shadow_addr (x_fr cx)) with (x_sh cx); lia
  | apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil ].

(* 0x8556c .. 0x85588: r's shadow byte := 0xf8 (r out of scope), check 20 (SH(m + 0x2000) is 0), m->n, i + 1,
   &m->seg[i + 1], `blt` to turn i + 1 or out to 0x8559c *)
Lemma s9_T9 : forall i, S9_loop_stmt (Datatypes.S i) -> LTA_K8559c B MT -> S9_R9 i.
Proof.
intros i HL HK cx ly S W regs mem md k acc c m HB HFRM Hi HM HR _.
pose proof HM as ((HFR & _) & Hc & Hm & HSL & (HRC & HMC)). pose proof HFR as (HJ & _).
pose proof (s9_base_facts cx HB) as (_ & Hsp0 & _ & Hs1 & _ & _).
unfold LTOI_FRAME_MAX, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
destruct (s9_frame_at cx ly S W mem md k HB HJ) as (HAR & Hin & EF & Hfa & Hf4 & Hfc & Happ).
pose proof HR as (R18 & R19 & R21 & R22 & R23 & R24 & R26 & R27).
pose proof asan_consts as (C1 & _).
set (n := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
assert (Hn : 1 <= n <= 32) by (pose proof (s18_mconf_len _ _ _ HMC); unfold n, x_mcF in *; lia).
assert (Hshr : 0x7fff8000 <= x_sh cx < 0x7fff8000 + 2 ^ 44).
{ change (x_sh cx) with (0x7fff8000 + x_fr cx / 8). split; [pose proof (Z.div_pos (x_fr cx) 8); lia|].
  assert (x_fr cx / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
set (E := s9_E9 regs m n).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs [w64 m; w64 n]) q)
  by (intros q Hq; unfold E, s9_E9; apply Eimg_low; exact Hq).
assert (E18 : ew E 18 = w64 (Z.of_nat i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E21 : ew E 21 = w64 (x_sh cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E24 : ew E 24 = w64 (-8))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E33 : ew E 33 = w64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (D18 : sv_denot E (SOff 18 1) = Z_to_bv 64 (Z.of_nat i + 1)).
{ cbn [sv_denot]. rewrite E18. unfold w64. rewrite unsigned_lit_small by (unfold n in *; lia). reflexivity. }
assert (D33 : sv_denot E (SOff 33 0) = Z_to_bv 64 n)
  by (cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HEI : img_env VAL A_LIM E) by (unfold E, s9_E9; apply Eimg_env).
destruct (lt_dec (Datatypes.S i) (length (SegModel.mc_seg (x_mcF cx)))) as [Hlt | Hge].
- destruct (s9_seed9 cx ly S W regs mem md k acc c m i [mkAC BC_LT (SOff 18 1) (SOff 33 0)] HB HM HR Hi) as [HS SHOK].
  { cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
    change (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) with n. fold E.
    rewrite D18, D33, s9_lts by (rewrite !unsigned_lit_small; unfold n in *; lia).
    rewrite !unsigned_lit_small by (unfold n in *; lia). apply Z.ltb_lt. unfold n in *. lia. }
  change (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) with n in HS, SHOK. fold E in HS, SHOK.
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO9_LOOP.
  { unfold s9_ss9. cbn [ss_mem]. s9_t9_awr cx EF E21. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> a <> x_sh cx + 22 -> ~ (x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
    rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1 H2. apply s9_aview_pt. apply HF. rewrite unsigned_lit_small by lia.
    intros (r0 & Hr0 & Hw). unfold s9_ss9 in Hr0. cbn [ss_mem In] in Hr0.
    destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | | lia | lia].
    rewrite E21, unsigned_lit_small in Hw by lia. lia. }
  assert (H8 : rdW W (ms_mem ms) (x_sh cx + 22) = Some 0xf8).
  { pose proof (s9_chunk_rd E _ (w_H W) ms 1 _ 22 1 (SOff 24 0) 0 HS eq_refl ltac:(cbn; left; reflexivity) ltac:(lia))
      as Hch. cbn [YP09.r_base base_val] in Hch. rewrite E21, unsigned_lit_small, Z.add_0_r in Hch by lia.
    rewrite Hch. cbn [sv_denot]. rewrite E24. vm_compute. reflexivity. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  rewrite EL in P2, P3, P4, P8, P9, P19, P21, P22, P23, P24, P26, P27 by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in P2. rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl) in P3.
  rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl) in P4. rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl) in P8.
  rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl) in P9. rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl) in P19.
  rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl) in P21. rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl) in P22.
  rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl) in P23. rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl) in P24.
  rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl) in P26. rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl) in P27.
  pose proof (s9M_agree cx ly S W regs mem md k acc LFO_R LFO0 c m ly S W (ms_regs ms) (ms_mem ms) mdv HB HM HJ
    P2 P3 P4 P8 P9 (s9_agree_win cx ly S W regs mem md k acc LFO_R c m W (ms_mem ms) HB HM KW) H8
    eq_refl eq_refl eq_refl eq_refl (Permutation_refl _) (or_introl eq_refl)) as HM'.
  apply (HL cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m HB HFRM Hlt HM').
  split; [rewrite P18, E18; unfold w64; rewrite unsigned_lit_small by (unfold n in *; lia); f_equal; lia|].
  destruct (s9_blocks cx ly S W regs mem md k acc LFO_R c m HM) as (_ & _ & _ & _ & _ & _ & Hmp & Hmb & _).
  pose proof (s18_mconf_len _ _ _ HMC) as Hl32.
  split; [rewrite P19, R19; unfold w64; rewrite unsigned_lit_small
    by (unfold x_mcF, seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE in *; lia);
    unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; f_equal; lia|].
  split; [rewrite P21; exact R21|]. split; [rewrite P22; exact R22|]. split; [rewrite P23; exact R23|].
  split; [rewrite P24; exact R24|]. split; [rewrite P26; exact R26 | rewrite P27; exact R27].
- destruct (s9_seed9 cx ly S W regs mem md k acc c m i [mkAC BC_GE (SOff 18 1) (SOff 33 0)] HB HM HR Hi) as [HS SHOK].
  { cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
    change (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) with n. fold E.
    rewrite D18, D33, s9_lts by (rewrite !unsigned_lit_small; unfold n in *; lia).
    rewrite !unsigned_lit_small by (unfold n in *; lia).
    rewrite (proj2 (Z.ltb_ge _ _)) by (unfold n in *; lia). reflexivity. }
  change (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) with n in HS, SHOK. fold E in HS, SHOK.
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO_K8559c.
  { unfold s9_ss9. cbn [ss_mem]. s9_t9_awr cx EF E21. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> a <> x_sh cx + 22 -> ~ (x_fr cx + FO_R <= a < x_fr cx + FO_R + 4) ->
    rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1 H2. apply s9_aview_pt. apply HF. rewrite unsigned_lit_small by lia.
    intros (r0 & Hr0 & Hw). unfold s9_ss9 in Hr0. cbn [ss_mem In] in Hr0.
    destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | | lia | lia].
    rewrite E21, unsigned_lit_small in Hw by lia. lia. }
  assert (H8 : rdW W (ms_mem ms) (x_sh cx + 22) = Some 0xf8).
  { pose proof (s9_chunk_rd E _ (w_H W) ms 1 _ 22 1 (SOff 24 0) 0 HS eq_refl ltac:(cbn; left; reflexivity) ltac:(lia))
      as Hch. cbn [YP09.r_base base_val] in Hch. rewrite E21, unsigned_lit_small, Z.add_0_r in Hch by lia.
    rewrite Hch. cbn [sv_denot]. rewrite E24. vm_compute. reflexivity. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (27%bv : bv 5) P27.
  rewrite EL in P2, P3, P4, P8, P9, P27 by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in P2. rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl) in P3.
  rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl) in P4. rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl) in P8.
  rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl) in P9. rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), R27 in P27.
  pose proof (s9M_agree cx ly S W regs mem md k acc LFO_R LFO0 c m ly S W (ms_regs ms) (ms_mem ms) mdv HB HM HJ
    P2 P3 P4 P8 P9 (s9_agree_win cx ly S W regs mem md k acc LFO_R c m W (ms_mem ms) HB HM KW) H8
    eq_refl eq_refl eq_refl eq_refl (Permutation_refl _) (or_introl eq_refl)) as (HC' & Hc' & Hm' & HSL' & HCM').
  exact (HK fx cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m HB HFRM HC' Hc' Hm' P27 HSL' HCM').
Qed.
(* ---- one turn of the loop: 0x854f0 at turn i, given turn i + 1 and the exit ---- *)
Lemma s9_turn : forall i, S9_loop_stmt (Datatypes.S i) -> LTA_K8559c B MT -> S9_loop_stmt i.
Proof.
intros i HL HK.
exact (s9_T0 i (s9_T1 i (s9_T2 i (s9_T3 i (s9_T4 i (s9_T5 i (s9_T6 i (s9_T7 i (s9_T8 i (s9_T9 i HL HK)))))))))).
Qed.

(* every turn: by induction on 32 - i, as m->n is at most 32 (the model block's encoding) *)
Lemma s9_loop_all : LTA_K8559c B MT -> forall i, S9_loop_stmt i.
Proof.
intros HK.
assert (H : forall d i, (32 - i <= d)%nat -> S9_loop_stmt i).
{ induction d as [|d IH]; intros i Hd.
  - intros cx ly S W regs mem md k acc c m _ _ Hi HM _.
    pose proof HM as (_ & _ & _ & _ & (_ & HMC)). pose proof (s18_mconf_len _ _ _ HMC) as Hl.
    unfold x_mcF in Hi. lia.
  - apply s9_turn; [apply IH; lia | exact HK]. }
intros i. apply (H (32 - i)%nat). lia.
Qed.

Theorem lt_seg_S09 : lt_seg_S09_stmt B MT.
Proof.
intros HK. apply s9_head. apply s9_cs; [apply s9_loop_all; exact HK | exact HK].
Qed.

End e.
End f.
End d.
Print Assumptions lt_seg_S09.
