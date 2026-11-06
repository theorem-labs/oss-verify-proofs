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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 603 of its 653 lines of code are new or changed and 403 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the helpers of segment A6 of reac_segconf_parse_file's walk
   (lib/A/Prog/pf_pieces.v S_A6: LONG 0x87e2c and REF3 0x87e74 -> TAIL). Segment A6's proof, 2026-10-30.
   No instruction is walked here (the walks are pf_a6_r.v, REF3, and pf_a6_l.v, LONG).
   - the pure facts: strspn's span over the set " \t\r" is SegModel's strspn_blank; the value the mask of
     0x87e50-0x87e60 leaves in s4; refuse's footprint inside the block and inside parse_file's.
   - a6_base_move: the cut facts pf_base carried to a later state whose reader agrees with the cut's on the
     addresses pf_base reads (the stack from s1 up, the text and its NUL, the unowned image bytes, the class-5 frame
     and its shadow); a6_keeps_low gives those agreements after strspn (it writes only its window below s1),
     a6_keeps_refuse after refuse (its journal: the footprint is in the block).
   - refuse_site_ok_87e74: the closed site lemma of the call of refuse at 0x87e74 (VERIFY rule 1j-bis): INV_REF3
     supplies every premise of refuse_contract (refuse_pre, the read-only view, the room for its class-0 frame, the
     event budget).
   The frame chain at a call (a5_chain), the cut geometry and the read-only view come from the shared kit
   lib/A/Prog/pf_a5_k.v (segment A5's, in the base); a6_base_move differs from its a5_move in its keep premise: it
   takes the journal-shaped agreements a6_keeps (the stack from s1 up, the text, the unowned image bytes, the
   class-5 frame and its shadow), which a callee's journal gives, where a5_move asks every byte off A5's write
   set kept, which a step gives but a call of refuse does not (its journal keeps no allocator byte).
   The stack-protector cells after a call are the Section hypothesis SSPX (the image-A owner's route A: sa_ssp at
   every AR state, discharged from SegRecCells.seg_rec_cells once the listing's stage 2 compiles). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec strspn_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstA pf_pieces pf_a5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======================================== pure facts ======================================== *)
Lemma a6_w64_u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof.
intros z Hz. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* strspn's set " \t\r" (the literal at seg_litA_rc [SP; TAB; CR] = 0x21380, slot 0xa8) as bytes *)
Definition A6_SET : list byte := [Z_to_bv 8 32; Z_to_bv 8 9; Z_to_bv 8 13].
Lemma a6_in_set : forall x, 0 <= x < 256 -> strspn_c.in_set A6_SET (Z_to_bv 8 x) = blank x.
Proof.
intros x Hx. unfold strspn_c.in_set, A6_SET, blank. cbn [existsb].
change (bv_unsigned (Z_to_bv 8 32)) with 32. change (bv_unsigned (Z_to_bv 8 9)) with 9.
change (bv_unsigned (Z_to_bv 8 13)) with 13.
rewrite Z_to_bv_unsigned. rewrite bv_wrap_small; [|change (bv_modulus 8) with 256; lia].
rewrite (Z.eqb_sym 32), (Z.eqb_sym 9), (Z.eqb_sym 13), orb_false_r. apply orb_assoc.
Qed.
Lemma a6_spn : forall l : list Z, ~ In 0 l -> Forall (fun x => 0 <= x < 256) l ->
  strspn_c.spn_len A6_SET (map (Z_to_bv 8) l) = strspn_blank l.
Proof.
intros l Hn Hr. unfold strspn_blank. rewrite (cut_nul_id l Hn). clear Hn.
induction Hr as [|x l Hx Hr IH]; [reflexivity|].
cbn [map strspn_c.spn_len takewhile]. rewrite (a6_in_set x Hx).
destruct (blank x); cbn [length]; [rewrite IH|]; reflexivity.
Qed.

(* the mask of 0x87e50-0x87e60 (lbu a0 = at[lead]; a0 - '['; seqz; - 1; and s4): s4 keeps cur unless the byte is
   '[' (0x5b), when it is NULL; the term is the one the token run leaves in s4 *)
Definition A6_MASK : sv :=
  SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 33 (-91)) (SLit 1)) (SLit (-1))) (SOff 20 0).
Lemma a6_mask_U : forall E b x, U E (SOff 33 0) = b -> 0 <= b < 256 -> U E (SOff 20 0) = x -> 0 <= x < 2 ^ 64 ->
  U E A6_MASK = if b =? 91 then 0 else x.
Proof.
intros E b x Hb Hbr Hx Hxr. unfold A6_MASK. rewrite !U_SAlu, !U_SLit, Hx.
assert (H33 : U E (SOff 33 (-91)) = zcanon (b - 91)).
{ rewrite U_SOff. rewrite U_SOff, Z.add_0_r in Hb.
  rewrite zcanon_id in Hb by (pose proof (bv_unsigned_in_range 64 (ew E 33)) as R;
    change (bv_modulus 64) with M64 in R; lia).
  rewrite Hb. reflexivity. }
rewrite H33. cbn [zalu_raw].
assert (Hc : (zcanon (b - 91) <? zcanon 1) = (b =? 91)).
{ unfold zcanon, M64. rewrite (Z.mod_small 1) by lia.
  destruct (Z.eqb_spec b 91) as [->|Hne]; [reflexivity|].
  apply Z.ltb_ge. destruct (Z_lt_le_dec b 91) as [Hl|Hl].
  - assert (Em : (b - 91) mod 2 ^ 64 = b - 91 + 2 ^ 64) by (symmetry; apply Z.mod_unique with (q := -1); lia).
    rewrite Em. lia.
  - rewrite Z.mod_small by lia. lia. }
rewrite Hc. destruct (b =? 91).
- assert (Ho : zcanon (zcanon 1 + zcanon (-1)) = 0) by reflexivity. rewrite Ho, Z.land_0_l. reflexivity.
- assert (Ho : zcanon (zcanon 0 + zcanon (-1)) = Z.ones 64) by reflexivity. rewrite Ho.
  rewrite Z.land_comm, Z.land_ones by lia. unfold zcanon, M64. rewrite (Z.mod_small x) by lia.
  apply Z.mod_small. lia.
Qed.

(* every byte refuse writes lies in [c + RC_REFUSAL, c + RC_OVERFLOW) (the cross_check walk's cross_check_r.v) *)
Lemma a6_refuse_W_in_block : forall c rcs a, inFP (refuse_W c rcs) a ->
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
Lemma a6_refuse_W_pos : forall c rcs, 0 < c -> ~ YI16.sink_open_fp (refuse_W c rcs).
Proof.
intros c rcs Hc. apply sink_closed_pos. apply Forall_forall. intros r Hr. unfold refuse_W in Hr.
apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst]. unfold seg_spec.RC_REFUSED. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat; intros Hr; [|destruct Hr].
  destruct Hr as [<- | [<- | []]]; cbn [fst];
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF; lia.
Qed.
(* refuse's footprint is inside parse_file's (the range refusal[0] .. overflow + 4 of RC_PARSE_W) *)
Lemma a6_refuse_W_sub : forall c rcs a, inFP (refuse_W c rcs) a -> inFP (seg_spec.RC_PARSE_W c) a.
Proof.
intros c rcs a Ha. apply a6_refuse_W_in_block in Ha.
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
(* the image-A owner's route A: the stack-protector cells at every AR state (discharged from
   SegRecCells.seg_rec_cells after the listing's stage 2) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(* ---------------------------------------- the image ---------------------------------------- *)
(* a literal keeps its bytes where the image bytes are kept; its tail is ROM, its shadow pinned *)
Lemma a6_lit_move : forall (rd : reader) (W' : world SEGS) mem' a s, sa_lit SEGS B rd a s ->
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
Lemma a6_cat_move : forall (rd : reader) (W' : world SEGS) mem', sa_cat SEGS B rd catA ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
     rdW W' mem' x = rd x) ->
  sa_cat SEGS B (rdW W' mem') catA.
Proof.
intros rd W' mem' (Hp & Hi & Hrows) K. split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (a6_lit_move rd W' mem' tp _ Hl K)].
assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (rdword_ext rd (rdW W' mem')); [exact Htp|]. intros k Hk.
unfold pin_spec.row_addr, pin_spec.CAT_ROW in *.
destruct (Hi (catA + 296 * Z.of_nat i + k) ltac:(unfold pin_spec.CAT_BYTES; lia)) as (Hm & Ho & He).
exact (K _ Hm Ho He).
Qed.

(* ---------------------------------------- blocks and frames ---------------------------------------- *)
(* a range inside a live heap block is addressable, with its shadow words visible, at any state it is live
   (the cross_check walk's cc_block_addr) *)
Lemma a6_heap_addr : forall ly S (W : world SEGS) mem md q n,
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
Lemma a6_heap_bounds : forall ly S (W : world SEGS) mem md q n,
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 <= n ->
  exists b m, In (b, m) (ablocks B ly S) /\ b <= q /\ q + n <= b + req_size m /\ 4096 <= b /\
    b + req_size m <= alloc_ceiling /\ in_app b (req_size m).
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hq) Hn.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
exists b, m. split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Happ].
Qed.
Lemma a6_heap_perm : forall ly S ly' S' q n, Permutation (ablocks B ly' S') (ablocks B ly S) ->
  sa_heap B ly S q n -> sa_heap B ly' S' q n.
Proof.
intros ly S ly' S' q n HP (b & m & Hin & Hb & Hq). exists b, m.
split; [exact (Permutation_in _ (Permutation_sym HP) Hin) | lia].
Qed.
(* a byte of the shadow band is in no app range *)
Lemma a6_band_not_app : forall b n s, in_app b n -> SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> ~ (b <= s < b + n).
Proof.
intros b n s Happ Hs Hin.
unfold in_app, SHADOW_OFF, kLowShadowBeg, YG0f.kHighMemBeg in *. lia.
Qed.

(* ---------------------------------------- the entry facts ---------------------------------------- *)
Lemma a6_cx : forall v, pf_cx B v ->
  0 < p_c v /\ p_c v mod 16 = 0 /\ Z.of_nat (length (p_s v)) <= 65535 /\
  sa_disj (p_t v) (seg_spec.cstr_span (p_t v) (p_s v)) (p_c v) seg_spec.SEG_C_SIZE /\
  alloc_ceiling <= ly_stk_lo (p_ly v) /\ ly_stk_lo (p_ly v) + 12800 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\
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
(* the realigned locals base s1 = (sp0 - 0x140) & -32 (pf_s1) *)
Definition a6_s1v (sp0 : Z) : Z := (sp0 - 0x140) - (sp0 - 0x140) mod 32.
Lemma a6_s1 : forall sp0, sp0 mod 16 = 0 ->
  sp0 - 0x160 < a6_s1v sp0 <= sp0 - 0x140 /\ a6_s1v sp0 mod 32 = 0 /\ a6_s1v sp0 mod 16 = 0 /\
  (a6_s1v sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H16. unfold a6_s1v.
pose proof (Z.mod_pos_bound (sp0 - 0x140) 32 ltac:(lia)) as Hm.
pose proof (Z.div_mod (sp0 - 0x140) 32 ltac:(lia)) as Hd.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd16. rewrite H16 in Hd16.
split; [lia|].
replace ((sp0 - 0x140) - (sp0 - 0x140) mod 32) with (32 * ((sp0 - 0x140) / 32)) by lia.
split; [rewrite Z.mul_comm; apply Z_mod_mult|].
split; [replace (32 * ((sp0 - 0x140) / 32)) with ((2 * ((sp0 - 0x140) / 32)) * 16) by lia; apply Z_mod_mult|].
replace (32 * ((sp0 - 0x140) / 32) - sp0) with ((2 * ((sp0 - 0x140) / 32) - sp0 / 16) * 16) by lia.
apply Z_mod_mult.
Qed.
Lemma a6_s1_eq : forall v, pf_s1 v = a6_s1v (pf_sp0 v).
Proof. reflexivity. Qed.
Lemma a6_frame : forall v pos lyc Sc Wc rX memc mdc,
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
Lemma a6_sl_move : forall (rd rd' : reader) b L, pf_sl rd b L ->
  Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0x100) L -> 0 <= b -> b + 0x100 <= 2 ^ 64 ->
  (forall a, b <= a < 2 ^ 64 -> rd' a = rd a) -> pf_sl rd' b L.
Proof.
intros rd rd' b L HL HB Hb Hb2 K. unfold pf_sl in *. rewrite Forall_forall in HL, HB |- *.
intros ov Hin. rewrite <- (HL ov Hin). apply rdword_ext. intros k Hk.
pose proof (HB ov Hin). apply K. lia.
Qed.
Lemma a6_PF_SL_offs : forall v pos, Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0x100) (PF_SL v pos).
Proof. intros v pos. unfold PF_SL. repeat constructor; cbn [fst]; lia. Qed.
(* what a later state must agree on for the cut facts to hold there: the stack from s1 up, the text and its NUL,
   the unowned image bytes, the class-5 frame and its shadow *)
Definition a6_keeps (v : pfv) (pos : Z) (Wc : world SEGS) memc (W2 : world SEGS) mem2 : Prop :=
  (forall a, pf_s1 v <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a) /\
  (forall i, 0 <= i <= Z.of_nat (length (p_s v)) -> rdW W2 mem2 (p_t v + i) = rdW Wc memc (p_t v + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW Wc memc a) /\
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 \/
             pf_SH v pos <= a < pf_SH v pos + fs_frame_bytes 5 / 8 ->
     rdW W2 mem2 a = rdW Wc memc a).
Lemma a6_base_move : forall (fx1 : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc ly2 S2 (W2 : world SEGS) regs2
  mem2 md2,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc sc ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 0 ->
  ly2 = lyc -> (exists f, S2 = set_fs f Sc) -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  a6_keeps v pos Wc memc W2 mem2 ->
  (forall r, In r [2; 3; 4; 8; 9; 22] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 sc.
Proof.
intros fx1 v pos lyc Sc Wc rX memc mdc sc ly2 S2 W2 regs2 mem2 md2 (CX & FI & OBJ & SL & FSH) Hfx HJ2 Hly2
  (f2 & HS2) HP2 (K1 & K2 & K3 & K4) KR.
destruct (a6_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (a6_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (a6_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
destruct FI as (HJ & Hly & (f & HSf) & HPerm & HSV & HFLW & HFRM & HRG).
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
  unfold pf_rg in *. rewrite Forall_forall in HRG |- *. intros rv Hin.
  rewrite (KR (fst rv)); [exact (HRG rv Hin)|].
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
split.
{ destruct (a6_heap_bounds lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
    as (bt & mt & Hint & Hbt1 & Hbt2 & _ & _ & _).
  assert (HT2 : sa_heap B ly2 S2 (p_t v) (Z.of_nat (length (p_s v)) + 1)) by exact (a6_heap_perm _ _ _ _ _ _ HP2 HT).
  assert (HC2 : sa_heap B ly2 S2 (p_c v) seg_spec.SEG_C_SIZE) by exact (a6_heap_perm _ _ _ _ _ _ HP2 HC).
  split.
  { destruct STR as ((Hz & Hn) & _). split; [split; [|exact Hn]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      rewrite K2 by lia. exact (Hz i Hi).
    - intros x Hx. apply (AR_block_word_vis SEGS B ly2 S2 W2 mem2 md2 bt mt (p_t v + Z.of_nat (length (p_s v))) x HAR2).
      + exact (Permutation_in _ (Permutation_sym HP2) Hint).
      + lia.
      + lia. }
  split; [exact (a6_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HT2 ltac:(lia))|].
  split; [exact HT2|].
  split; [exact (a6_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HC2 ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact HC2|].
  split; [exact (a6_cat_move _ W2 mem2 CAT K3)|].
  split; [intros x Hx; exact (a6_lit_move _ W2 mem2 _ _ (LITS x Hx) K3)|].
  split; [intros a Hro Ho He; rewrite (K3 a (a5_ro_img VRO a Hro) Ho He); exact (ROD a Hro Ho He)|].
  exact (SSPX ly2 S2 W2 mem2 md2 HAR2). }
split.
{ apply (a6_sl_move (rdW Wc memc) _ (pf_s1 v) _ SL (a6_PF_SL_offs v pos)); [lia | lia |].
  intros a Ha. apply K1. exact Ha. }
intros i Hi. rewrite K4; [exact (FSH i Hi)|]. right. rewrite E5. change (2048 / 8) with 256. lia.
Qed.
(* the same for a step that writes some of the frame's 144 shadow cells (a scope in or out): a6_keeps without its
   shadow clause (only the frame's BYTES kept), the new scope's cells as a premise, pf_base at the new scope sc'
   (asked by segment A11b's proof; a6_base_move is its instance at sc' = sc) *)
Definition a6_keeps_sc (v : pfv) (pos : Z) (Wc : world SEGS) memc (W2 : world SEGS) mem2 : Prop :=
  (forall a, pf_s1 v <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a) /\
  (forall i, 0 <= i <= Z.of_nat (length (p_s v)) -> rdW W2 mem2 (p_t v + i) = rdW Wc memc (p_t v + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW Wc memc a) /\
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 -> rdW W2 mem2 a = rdW Wc memc a).
Lemma a6_keeps_sc_of : forall v pos Wc memc W2 mem2, a6_keeps v pos Wc memc W2 mem2 -> a6_keeps_sc v pos Wc memc W2 mem2.
Proof.
intros v pos Wc memc W2 mem2 (K1 & K2 & K3 & K4). split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
intros a Ha. apply K4. left. exact Ha.
Qed.
Lemma a6_base_move_sc : forall (fx1 : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc sc' ly2 S2 (W2 : world SEGS)
  regs2 mem2 md2,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc sc ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 0 ->
  ly2 = lyc -> (exists f, S2 = set_fs f Sc) -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  a6_keeps_sc v pos Wc memc W2 mem2 ->
  pf_fsh (rdW W2 mem2) (pf_SH v pos) sc' ->
  (forall r, In r [2; 3; 4; 8; 9; 22] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 sc'.
Proof.
intros fx1 v pos lyc Sc Wc rX memc mdc sc sc' ly2 S2 W2 regs2 mem2 md2 (CX & FI & OBJ & SL & FSH) Hfx HJ2 Hly2
  (f2 & HS2) HP2 (K1 & K2 & K3 & K4) FSH2 KR.
destruct (a6_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (a6_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (a6_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
destruct FI as (HJ & Hly & (f & HSf) & HPerm & HSV & HFLW & HFRM & HRG).
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
  unfold pf_rg in *. rewrite Forall_forall in HRG |- *. intros rv Hin.
  rewrite (KR (fst rv)); [exact (HRG rv Hin)|].
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
split.
{ destruct (a6_heap_bounds lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
    as (bt & mt & Hint & Hbt1 & Hbt2 & _ & _ & _).
  assert (HT2 : sa_heap B ly2 S2 (p_t v) (Z.of_nat (length (p_s v)) + 1)) by exact (a6_heap_perm _ _ _ _ _ _ HP2 HT).
  assert (HC2 : sa_heap B ly2 S2 (p_c v) seg_spec.SEG_C_SIZE) by exact (a6_heap_perm _ _ _ _ _ _ HP2 HC).
  split.
  { destruct STR as ((Hz & Hn) & _). split; [split; [|exact Hn]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      rewrite K2 by lia. exact (Hz i Hi).
    - intros x Hx. apply (AR_block_word_vis SEGS B ly2 S2 W2 mem2 md2 bt mt (p_t v + Z.of_nat (length (p_s v))) x HAR2).
      + exact (Permutation_in _ (Permutation_sym HP2) Hint).
      + lia.
      + lia. }
  split; [exact (a6_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HT2 ltac:(lia))|].
  split; [exact HT2|].
  split; [exact (a6_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HC2 ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact HC2|].
  split; [exact (a6_cat_move _ W2 mem2 CAT K3)|].
  split; [intros x Hx; exact (a6_lit_move _ W2 mem2 _ _ (LITS x Hx) K3)|].
  split; [intros a Hro Ho He; rewrite (K3 a (a5_ro_img VRO a Hro) Ho He); exact (ROD a Hro Ho He)|].
  exact (SSPX ly2 S2 W2 mem2 md2 HAR2). }
split; [|exact FSH2].
apply (a6_sl_move (rdW Wc memc) _ (pf_s1 v) _ SL (a6_PF_SL_offs v pos)); [lia | lia |].
intros a Ha. apply K1. exact Ha.
Qed.
(* after strspn: it writes only its window below s1, which is above every object below alloc_ceiling *)
Lemma a6_keeps_low : forall v pos lyc Sc Wc rX memc mdc sc (W2 : world SEGS) mem2,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  (forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling \/ pf_s1 v <= a -> rdW W2 mem2 a = rdW Wc memc a) ->
  a6_keeps v pos Wc memc W2 mem2.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc W2 mem2 (CX & FI & OBJ & _ & _) K.
destruct (a6_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (a6_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (a6_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
pose proof (proj1 (proj1 FI)) as HAR.
destruct OBJ as (_ & _ & HT & _).
destruct (a6_heap_bounds _ _ _ _ _ (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
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
Lemma a6_keeps_call : forall v pos lyc Sc Wc rX memc mdc sc STKc FPc ly2 S2 (W2 : world SEGS) mem2 md2 k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STKc (pf_s1 v) FPc lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k ->
  (forall a, inFP FPc a -> p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) -> ~ YI16.sink_open_fp FPc ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  a6_keeps v pos Wc memc W2 mem2.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc STKc FPc ly2 S2 W2 mem2 md2 k (CX & FI & OBJ & _ & _) HJc NFP HCl HP2.
destruct (a6_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (a6_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (a6_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
pose proof (proj1 (proj1 FI)) as HAR.
destruct OBJ as (_ & _ & HT & _ & HC & _).
destruct (a6_heap_bounds _ _ _ _ _ (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
  as (bt & mt & Hint & Hb1 & Hb2 & Hb3 & Hb4 & _).
destruct (a6_heap_bounds _ _ _ _ _ (p_c v) seg_spec.SEG_C_SIZE HAR HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
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
    apply (a6_band_not_app bc (req_size mc) a Hcapp); [lia|].
    unfold seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* after refuse: its footprint refuse_W lies in the block c (refusal[n], n_refusals, refused) *)
Lemma a6_keeps_refuse : forall v pos lyc Sc Wc rX memc mdc sc cf ly2 S2 (W2 : world SEGS) mem2 md2 k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_refuse (pf_s1 v) (refuse_W (p_c v) cf) lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  a6_keeps v pos Wc memc W2 mem2.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc cf ly2 S2 W2 mem2 md2 k HB HJc HP2.
destruct (a6_cx v (proj1 HB)) as (Hc0 & _).
apply (a6_keeps_call v pos lyc Sc Wc rX memc mdc sc STK_refuse (refuse_W (p_c v) cf) ly2 S2 W2 mem2 md2 k HB HJc);
  [| exact (a6_refuse_W_pos _ cf Hc0) | exact HP2].
intros a Ha. apply a6_refuse_W_in_block in Ha. unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW,
  seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* cur_name's bytes are in the frame *)
Lemma a6_nm_move : forall v pos (rd rd' : reader) nm, pf_nm rd (pf_F v pos + PF_O_CN) nm ->
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 -> rd' a = rd a) ->
  pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros v pos rd rd' nm (f & Hb & He) K. exists f. split; [|exact He].
intros i Hi. destruct He as (Hl & _). rewrite Hl in Hi. rewrite K; [exact (Hb i ltac:(lia))|].
change (fs_frame_bytes 5) with 2048. unfold PF_O_CN. lia.
Qed.

(* ---------------------------------------- the call of refuse at 0x87e74 ---------------------------------------- *)
(* a C string in an object [F + lo, F + hi) of the class-5 frame whose shadow cells are 0 at the cut's scope sc
   (lo, hi multiples of 8, the object between cell 4 and cell 136: cur_name [0x20, 0x30), buf [0x40, 0x240),
   low [0x280, 0x2c0), low146 [0x2e0, 0x2f8), known [0x320, 0x410)): an argument refuse can read (refuse_pre's
   sa_va_arg and refuse_va_locs' sa_fframe); asked by segment A9's proof for the refuse sites of A7, A9, A10b,
   A11b, A12 *)
Lemma a6_obj_arg : forall v pos lyc Sc Wc rX memc mdc sc (lo hi a3 : Z) (x : list Z) (Wl : list (Z * Z)),
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  32 <= lo -> lo mod 8 = 0 -> hi mod 8 = 0 -> hi <= 1088 ->
  (forall i, lo / 8 <= i < hi / 8 -> pf_shb sc i = 0) ->
  sa_str (rdW Wc memc) a3 x -> pf_F v pos + lo <= a3 -> a3 + Z.of_nat (length x) < pf_F v pos + hi ->
  Forall (fun iv => alloc_ceiling <= fst iv \/
    (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= fst iv /\ snd iv <= b + req_size m)) Wl ->
  sa_va_arg (rdW Wc memc) Wl (w64 a3) (SegModel.AS x) /\
  (sa_heap B lyc Sc (bv_unsigned (w64 a3)) (Z.of_nat (length x) + 1) \/
   sa_fframe lyc Sc (bv_unsigned (w64 a3)) (Z.of_nat (length x) + 1)).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc lo hi a3 x Wl (CX & FI & OBJ & SL & FSH) Hlo Hlo8 Hhi8 Hhi Hcell Hstr Hb1 Hb2
  HWl.
destruct (a6_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (proj1 (proj1 FI)) as HAR.
pose proof alloc_ceiling_lt as Hac.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
assert (Hu : bv_unsigned (w64 a3) = a3) by (apply a6_w64_u; lia).
rewrite Hu.
assert (Hm8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
pose proof (Z.div_mod hi 8 ltac:(lia)) as Dhi. pose proof (Z.div_mod lo 8 ltac:(lia)) as Dlo.
(* the shadow cell of a byte of the frame *)
assert (HSC : forall y, pf_F v pos <= y < pf_F v pos + 2048 ->
  shadow_of_addr SHADOW_OFF y = pf_SH v pos + (y - pf_F v pos) / 8).
{ intros y Hy. unfold shadow_of_addr, pf_SH, shadow_addr.
  assert (Hy8 : y / 8 = (y - pf_F v pos) / 8 + pf_F v pos / 8).
  { rewrite <- Z.div_add by lia. f_equal. pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). lia. }
  lia. }
split.
- cbn [sa_va_arg]. rewrite Hu. split; [lia|]. split; [exact Hstr|].
  split; [assert (Hl : Z.of_nat (length x) < 1088) by lia; apply Nat2Z.inj_le; change (Z.of_nat 65535) with 65535; lia|].
  split.
  + unfold sa_addr. split; [lia|]. split; [lia|].
    split.
    { unfold amem_range. rewrite E5 in HFapp. unfold in_app in HFapp. destruct HFapp as [_ [Hl | [Hh1 _]]].
      - left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
      - right. unfold YG0f.kHighMemBeg, kHighMemEnd in *. lia. }
    split.
    * intros y Hy. exists 0. split; [|left; reflexivity].
      rewrite (HSC y) by lia. rewrite (FSH ((y - pf_F v pos) / 8)).
      -- f_equal. apply Hcell. split.
         ++ apply Z.div_le_mono; lia.
         ++ apply Z.div_lt_upper_bound; lia.
      -- split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
    * intros _ s Hs. unfold shadow_addr in Hs.
      assert (D1 : (pf_F v pos + 32) / 8 <= a3 / 8) by (apply Z.div_le_mono; lia).
      assert (D1' : (pf_F v pos + 32) / 8 = pf_F v pos / 8 + 4).
      { rewrite <- (Z.div_add (pf_F v pos) 4 8) by lia. reflexivity. }
      assert (D2 : (a3 + (Z.of_nat (length x) + 1) - 1) / 8 <= (pf_F v pos + 1087) / 8)
        by (apply Z.div_le_mono; lia).
      assert (D2' : (pf_F v pos + 1087) / 8 = pf_F v pos / 8 + 135).
      { rewrite (Z.div_mod (pf_F v pos) 8) at 1 by lia. rewrite Hm8, Z.add_0_r.
        replace (8 * (pf_F v pos / 8) + 1087) with (7 + (pf_F v pos / 8 + 135) * 8) by lia.
        rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
      assert (HSH4 : (SHADOW_OFF + pf_F v pos / 8) mod 4 = 0).
      { pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)). pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)).
        unfold SHADOW_OFF in *. rewrite Z.add_mod by lia.
        replace (pf_F v pos / 8) with (4 * (pf_F v pos / 32)) by lia.
        rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
      pose proof (Z.mod_pos_bound (SHADOW_OFF + a3 / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + a3 / 8) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (SHADOW_OFF + (a3 + (Z.of_nat (length x) + 1) - 1) / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + (a3 + (Z.of_nat (length x) + 1) - 1) / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHADOW_OFF + pf_F v pos / 8) 4 ltac:(lia)).
      assert (Hs2 : pf_SH v pos <= s < pf_SH v pos + 144) by (unfold pf_SH, shadow_addr; lia).
      replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
      rewrite (FSH (s - pf_SH v pos)) by lia. discriminate.
  + unfold sa_apart_all. eapply Forall_impl; [|exact HWl]. cbv beta. intros iv [Hiv | (b & m & Hinb & Hb & Hm)].
    * left. unfold seg_spec.cstr_span.
      pose proof (Z.mod_pos_bound (- (a3 + Z.of_nat (length x) + 1)) 8 ltac:(lia)). lia.
    * pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hinb Hfin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFE, E5 in Hd. unfold seg_spec.cstr_span.
      pose proof (Z.mod_pos_bound (- (a3 + Z.of_nat (length x) + 1)) 8 ltac:(lia)).
      destruct Hd as [Hd | Hd]; [right | left]; lia.
- right. exists 5, pos. split; [exact Hfin|]. split; [lia|]. rewrite HFE, E5. lia.
Qed.
(* the buf string of F_neither / F_outside: an argument refuse can read (a6_obj_arg at buf [0x40, 0x240)) *)
Lemma a6_buf_arg : forall v pos lyc Sc Wc rX memc mdc sc (a3 : Z) (x : list Z) (Wl : list (Z * Z)),
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> sc_buf sc = true -> sc_cn sc = true ->
  sa_str (rdW Wc memc) a3 x -> pf_inb (pf_F v pos + PF_O_BUF) a3 x ->
  Forall (fun iv => alloc_ceiling <= fst iv \/
    (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= fst iv /\ snd iv <= b + req_size m)) Wl ->
  sa_va_arg (rdW Wc memc) Wl (w64 a3) (SegModel.AS x) /\
  (sa_heap B lyc Sc (bv_unsigned (w64 a3)) (Z.of_nat (length x) + 1) \/
   sa_fframe lyc Sc (bv_unsigned (w64 a3)) (Z.of_nat (length x) + 1)).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc a3 x Wl HB Hbuf _ Hstr (Hb1 & Hb2) HWl. unfold PF_O_BUF in *.
apply (a6_obj_arg v pos lyc Sc Wc rX memc mdc sc 0x40 0x240 a3 x Wl HB); try lia; [| exact Hstr | exact HWl].
intros i Hi. change (0x40 / 8) with 8 in Hi. change (0x240 / 8) with 72 in Hi. unfold pf_shb.
destruct (i <? 4) eqn:E1; [apply Z.ltb_lt in E1; lia|].
destruct (i <? 6) eqn:E2; [apply Z.ltb_lt in E2; lia|].
destruct (i <? 8) eqn:E3; [apply Z.ltb_lt in E3; lia|].
destruct (i <? 72) eqn:E4; [|apply Z.ltb_ge in E4; lia].
rewrite Hbuf. reflexivity.
Qed.
(* VERIFY rule 1j-bis, edge reac_segconf_parse_file -> refuse at 0x87e74 (refuse(c, lineno, f, a3); entered from
   LONG's path with F_long / 511 and from A9 with F_neither / F_outside and a C string in buf): INV_REF3 at the jal
   gives refuse_contract's premises over the call's registers regsc (the cut's, ra the return 0x87e78) *)
Lemma refuse_site_ok_87e74 : forall n v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3
  (regsc : bvmap 5 word),
  INV_REF3 B n v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3 ->
  (forall r, In r [2; 10; 11; 12; 13] -> getr regsc (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  refuse_pre SEGS B seg_litA_rc gotwA guardA lyc Sc regsc (rdW Wc memc) (p_c v) (ln + 1) fa
    [getr regsc 13; getr regsc 14; getr regsc 15; getr regsc 16; getr regsc 17] cf (ln + 1) f args /\
  sa_room Sc /\ st_nev Sc + EV_refuse <= EV_MAX.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3 regsc
  ((CX & FI & OBJ & SL & FSH) & MID & ST & REF & RG) KR.
pose proof (conj CX (conj FI (conj OBJ (conj SL FSH)))) as BASE0.
destruct (a6_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (a6_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (a6_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
pose proof FI as (HJ & Hly & _ & _ & _ & _ & HFRM & HRG).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & (C0 & _) & _) & Hroom & Hev).
destruct OBJ as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
destruct ST as (RC & COK & NM & CNT).
destruct MID as (Ho & Hn & (Hno & Hlines & Hln & Hle)).
pose proof (pf_next_le (p_s v) o Ho) as HNL.
(* the call registers *)
unfold pf_rg in RG, HRG. rewrite Forall_forall in RG, HRG.
assert (R2 : getr regsc 2 = w64 (pf_s1 v)).
{ change (getr regsc 2) with (getr regsc (Z_to_bv 5 2)). rewrite (KR 2) by (cbn; tauto).
  apply (HRG (2, pf_s1 v)). cbn [In]. left. reflexivity. }
assert (R13 : getr regsc 13 = w64 a3).
{ change (getr regsc 13) with (getr regsc (Z_to_bv 5 13)). rewrite (KR 13) by (cbn; tauto).
  apply (RG (13, a3)). unfold PF_RL, PF_RM. cbn [app In]. repeat (first [left; reflexivity | right]). }
pose proof asan_consts as (C1 & _).
assert (Hsp : spZ regsc = pf_s1 v) by (unfold spZ; rewrite R2; apply a6_w64_u; lia).
assert (Hly0 : (Z.of_nat (length (p_s v)) <= 65535)) by lia.
split; [exact ROD|].
split.
- unfold refuse_pre.
  split; [lia|]. split; [exact Hc16|]. split; [exact RC|]. split; [exact HC|]. split; [exact AC|].
  split; [destruct CNT as [CN1 _]; lia|].
  split; [lia|]. split; [reflexivity|].
  destruct REF as [(-> & -> & -> & ->) | (x & Hfx & -> & Hxs & Hxb)].
  + assert (HL : In F_long PARSE_FILE_LITS)
      by (unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right])).
    pose proof (LITS F_long HL) as HLL.
    split; [unfold seg_spec.REFUSE_FORMATS; cbn [In]; repeat (first [left; reflexivity | right])|].
    split; [vm_compute; reflexivity|].
    split; [destruct HLL as (Hp & _); lia|]. split; [reflexivity|]. split; [exact HLL|].
    split; [cbn [sa_va_args sa_va_arg]; rewrite R13, a6_w64_u by lia; split; [lia | exact I]|].
    split; [cbn [refuse_va_locs]; exact I|].
    split; [exact HFRM|]. split; [exact SSP|].
    intros x Hx. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hx.
  + assert (HWl : Forall (fun iv => alloc_ceiling <= fst iv \/
      (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= fst iv /\ snd iv <= b + req_size m))
      [(ly_stk_lo lyc, spZ regsc);
       (seg_spec.refusal_addr (p_c v) (length (rc_refusal cf)),
        seg_spec.refusal_addr (p_c v) (length (rc_refusal cf)) + seg_spec.RC_REFUSAL_LEN);
       (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)]).
    { destruct (a6_heap_bounds _ _ _ _ _ (p_c v) seg_spec.SEG_C_SIZE HAR HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
        as (bc & mc & Hinc & Hc1 & Hc2 & _).
      destruct RC as (bs & _ & (_ & _ & _ & _ & HL8 & _)).
      constructor; [left; cbn [fst]; rewrite Hly; lia|].
      constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
        unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.SEG_C_SIZE in *; lia|].
      constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
        unfold seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *; lia|].
      constructor. }
    destruct (a6_buf_arg v pos lyc Sc Wc rX memc mdc PF_SC_LINE a3 x _ BASE0 eq_refl eq_refl Hxs Hxb HWl)
      as [HVA HLOC].
    destruct Hfx as [(-> & ->) | (-> & ->)].
    * assert (HL : In F_neither PARSE_FILE_LITS)
        by (unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right])).
      pose proof (LITS F_neither HL) as HLL.
      split; [unfold seg_spec.REFUSE_FORMATS; cbn [In]; repeat (first [left; reflexivity | right])|].
      split; [vm_compute; reflexivity|].
      split; [destruct HLL as (Hp & _); lia|]. split; [reflexivity|]. split; [exact HLL|].
      split; [cbn [sa_va_args]; rewrite R13; exact (conj HVA I)|].
      split; [cbn [refuse_va_locs]; rewrite R13; exact (conj HLOC I)|].
      split; [exact HFRM|]. split; [exact SSP|].
      intros y Hy. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hy.
    * assert (HL : In F_outside PARSE_FILE_LITS)
        by (unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right])).
      pose proof (LITS F_outside HL) as HLL.
      split; [unfold seg_spec.REFUSE_FORMATS; cbn [In]; repeat (first [left; reflexivity | right])|].
      split; [vm_compute; reflexivity|].
      split; [destruct HLL as (Hp & _); lia|]. split; [reflexivity|]. split; [exact HLL|].
      split; [cbn [sa_va_args]; rewrite R13; exact (conj HVA I)|].
      split; [cbn [refuse_va_locs]; rewrite R13; exact (conj HLOC I)|].
      split; [exact HFRM|]. split; [exact SSP|].
      intros y Hy. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hy.
- split.
  + unfold sa_room. unfold sa_room_n in Hroom. rewrite Hfrs. cbn [app length]. lia.
  + unfold EV_refuse. unfold EV_reac_segconf_parse_file in Hev. lia.
Qed.
End e.
End f.
End d.
