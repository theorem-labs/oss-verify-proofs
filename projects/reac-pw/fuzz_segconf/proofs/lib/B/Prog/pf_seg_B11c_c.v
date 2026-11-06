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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 837 of its 889 lines of code are new or changed and 401 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s17.v, with its module paths and module names changed; 200 of its 253 lines of code are new or changed and 836 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): what segment B11c
   of reac_segconf_parse_file's walk carries across its F_badmodel refuse call (jal 0x892f8 at 0x88bec, return
   0x88bf0): from the state at the call (pf_seg_B11c_r.v INV_KCALL) and refuse_contract's post (lib/B/Prog/
   refuse_c.v: c holds SegModel.refuse cf (ln + 1) F_badmodel args, sa_noalloc) with the two journals the call
   rule PaFx.cl_callSF returns, the state at 0x88bf0 satisfies KOUT's invariant (pf_seg_B11c_o.v INV_KOUT) at
   the FP state refuse returned. The B11c segment lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment
   lemma, the call's frame transport).
   ADAPTED from the image-A G3 walk owner's image-A transport lemmas lib/A/Prog/pf_a5_k.v (commit
   385fd095481f: a5_move, a5_rg_pres, a5_set_fs2), lib/A/Prog/cross_check_r.v (commit
   4375c82a2d01: refuse_W_in_block) and image B's parse walk lib/B/Prog/reac_segconf_parse.v (sa_addr_of_heap,
   sa_lit_journal, in_roP_img), re-derived for B's frame.
   WHAT KEEPS EACH FACT (refuse's journal from the call: window [s1 - STK_refuse, s1), footprint refuse_W c cf,
   which lies in the block c, YCbq.ajournal's clauses):
   - the saved registers, the 23 setup slots, c's slot 0xc8, cur's slot 0xc0: above s1, above alloc_ceiling and off
     the footprint (the window clause);
   - the class-5 frame's bytes (cur_name, the flag word) and its 144 shadow cells: a frame of the call state, off
     the footprint (the frames clause);
   - the text's bytes: a live block, off the footprint (reader_pre's sa_disj of the text's read span and the block
     c; the blocks clause); its slack: YG0d_tail.AR_block_word_vis at the new AR state;
   - the literals, the catalogue, the read-only view: image bytes the runtime does not own (the image clause);
   - addressability of the text and of c: AR's shadow law at the new state (sa_addr_of_heap); printf's cells: SSPX;
   - c's bytes: refuse's post; the counters' room after the line: pfA_facts.pf_cnt_refuse;
   - the callee-saved registers: aregs_preserved; the rounding mode: PaFx.fxrel_frm0.
   SECTION HYPOTHESES: VRO (the listing's read-only range, B's SegObj.seg_val_relro), SSPX (the stack-protector
   cells at every AR state; the image-A G3 walk owner's SSPX at image B's cells, as lib/B/Prog/reac_segconf_parse.v takes it). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B11c_k pf_seg_B11c_o
  pf_seg_B11c_r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* every byte refuse writes lies in the block c (refusal[n] for n < 8, n_refusals, refused) *)
Lemma b11_rw_in : forall c rcs a, inFP (refuse_W c rcs) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c rcs a (r & Hr & Ha). unfold refuse_W in Hr. apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst snd] in Ha. unfold seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat eqn:E; intros Hr; [|destruct Hr].
  apply Nat.ltb_lt in E.
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha;
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF,
      seg_spec.SEG_C_SIZE in *; lia.
Qed.
Lemma b11_rw_closed : forall c rcs, 0 < c -> ~ YI16.sink_open_fp (refuse_W c rcs).
Proof.
intros c rcs Hc. apply sink_closed_pos. apply Forall_forall. intros r Hr. unfold refuse_W in Hr.
apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst]. unfold seg_spec.RC_REFUSED. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat; intros Hr; [|destruct Hr].
  destruct Hr as [<- | [<- | []]]; cbn [fst];
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF; lia.
Qed.
Lemma b11_set_fs2 : forall f g s, set_fs f (set_fs g s) = set_fs f s.
Proof. intros f g s. destruct s. reflexivity. Qed.
Lemma b11_rg_pres : forall r1 r2 L, aregs_preserved r1 r2 -> Forall (fun rv => acallee_saved (fst rv)) L ->
  pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 L HP HC H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HP (fst rv) (HC rv Hin)). exact (H rv Hin).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma b11_relro_img : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof.
intros a Ha. destruct VRO as [Hlo Hhi]. apply pa_relro_img. rewrite Hlo, Hhi.
unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Ha. lia.
Qed.
Lemma b11_inro_img : forall a, in_roP SEGS RLO_A RHI_A a -> in_img SEGS a.
Proof.
intros a [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (b11_relro_img a Hr)].
Qed.
(* a range inside a live heap block is addressable, with its shadow words visible, at that state
   (lib/B/Prog/reac_segconf_parse.v sa_addr_of_heap) *)
Lemma b11_addr_of_heap : forall ly S (W : world SEGS) mem md q n, AR SEGS B ly S W mem md -> sa_heap B ly S q n ->
  0 <= q -> 0 < n -> sa_addr (rdW W mem) q n /\ q + n <= alloc_ceiling.
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hm) Hq Hn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4 & Hc & Happ & _ & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. pose proof asan_consts as (C1 & _).
split; [|lia].
split; [lia|]. split; [lia|].
split; [exact (amem_range_sub_app b (req_size m) q n Happ Hc ltac:(lia) ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin ltac:(lia) ltac:(lia))|].
intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin ltac:(lia) ltac:(lia) Hn).
Qed.
Lemma b11_heap_perm : forall ly S ly' S' q n, Permutation (ablocks B ly' S') (ablocks B ly S) ->
  sa_heap B ly S q n -> sa_heap B ly' S' q n.
Proof.
intros ly S ly' S' q n HP (b & m & Hb & H1 & H2). exists b, m. split; [|lia].
exact (Permutation_in _ (Permutation_sym HP) Hb).
Qed.

(* ---------- the post-call transport ---------- *)
Lemma b11_after_refuse : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val
  (fx1 : YK11.FPState) ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
  INV_KCALL (fx := fx) B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 0 ->
  ajournal SEGS B STK_refuse (pf_s1 v) (refuse_W (p_c v) cf) lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 EV_refuse ->
  aregs_preserved rX regs2 ->
  sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known]) ->
  sa_noalloc B lyc Sc ly2 S2 ->
  INV_KOUT (fx := fx1) B n v pos ly2 S2 W2 regs2 mem2 md2 (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known])
    nm o ln d gi.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val fx1 ly2 S2 W2 regs2 mem2 md2 HI Hrel HJp HJc HP HRC2 HNA.
destruct HI as (HBASE & HMID & HST & HVS & HVI & HKS & HRG).
destruct HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b11_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR).
pose proof G as (S1 & S2g & S3 & S4 & S5 & S6 & F1g & F2g & F3g & F4g & _).
destruct (b11_SHb v pos G) as (ESH & SH1 & SH2 & F8 & _).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HSLC & HRG0).
destruct HNA as (HPERM2 & Hly2 & (f2 & HS2e)).
pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & KW & KB & KI & KF & _).
pose proof HOBJ as (T1 & T2 & T3 & C1 & C2 & CA & LI & RO & SS).
pose proof HCX as (_ & _ & _ & HcB & _ & HtB & _ & _ & (fe & HPF) & _).
destruct HPF as (HRP & _). pose proof HRP as (_ & _ & _ & _ & _ & _ & _ & _ & Ht0 & _ & _ & _ & _ & HDJ & _).
pose proof HTF as (C0 & C16 & _ & _ & LS).
pose proof asan_consts as (AC1 & _).
set (FP1 := refuse_W (p_c v) cf) in *.
assert (HFPc : forall a, inFP FP1 a -> p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) by (intros a; apply b11_rw_in).
assert (HFPo : ~ YI16.sink_open_fp FP1) by (apply b11_rw_closed; lia).
(* the block c: below alloc_ceiling, an application range, apart from the frame *)
assert (CB : 4096 <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\
  (p_c v + seg_spec.SEG_C_SIZE <= pf_F v pos \/ pf_F v pos + 2048 <= p_c v) /\
  (p_c v + seg_spec.SEG_C_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= p_c v)).
{ destruct C2 as (b & m & Hb & H1 & H2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4 & Hc & Happ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [_ Hrq].
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  split; [lia|]. split; [lia|]. split; [lia|]. lia. }
assert (NFhigh : forall a, alloc_ceiling <= a -> ~ inFP FP1 a) by (intros a Ha Hf; apply HFPc in Hf; lia).
assert (NFframe : forall a, pf_F v pos <= a < pf_F v pos + 2048 -> ~ inFP FP1 a)
  by (intros a Ha Hf; apply HFPc in Hf; lia).
assert (NFsh : forall i, 0 <= i < 256 -> ~ inFP FP1 (pf_SH v pos + i)) by (intros i Hi Hf; apply HFPc in Hf; lia).
assert (NFimg : forall a, in_img SEGS a -> ~ inFP FP1 a).
{ intros a Ha Hf. apply HFPc in Hf. destruct C2 as (b & m & Hb & H1 & H2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [_ Hrq].
  destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR) as [_ Hn].
  { left. exists b, m. split; [exact Hb | lia]. }
  exact (Hn Ha). }
(* what refuse's journal keeps *)
assert (Khi : forall a, pf_s1 v <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. apply KW; [lia | lia | apply NFhigh; lia]. }
assert (Kfr : forall a, pf_F v pos <= a < pf_F v pos + 2048 -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. apply (KF 5 pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF;
    change (fs_frame_bytes 5) with 2048; lia | apply NFframe; exact Ha]. }
assert (Ksh : forall i, 0 <= i < 256 -> rdW W2 mem2 (pf_SH v pos + i) = rdW Wc memc (pf_SH v pos + i)).
{ intros i Hi. apply (KF 5 pos _ Hin); [right; unfold in_zr; cbn [fst snd]; rewrite EF;
    change (fs_frame_bytes 5 / 8) with 256; change (shadow_addr (pf_F v pos)) with (pf_SH v pos); lia
  | apply NFsh; exact Hi]. }
assert (Kimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Ho He. apply KI; [exact Ha | exact Ho | exact He | apply fp_spares_closed; [exact HFPo | apply NFimg; exact Ha]]. }
assert (Klit : forall a s, sa_lit SEGS B (rdW Wc memc) a s -> sa_lit SEGS B (rdW W2 mem2) a s).
{ intros a s (Ha & ((Hz & Hn) & Ht) & Hp & Hr & Hi).
  split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
  split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
  intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Hm & Ho & He).
  rewrite (Kimg _ Hm Ho He). exact (Hz i Hi'). }
assert (Kcat : sa_cat SEGS B (rdW W2 mem2) catA).
{ destruct CA as (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
  intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (Klit tp _ Hl)].
  assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
  rewrite (rdword_ext (rdW Wc memc) (rdW W2 mem2)); [exact Htp|].
  intros k Hk. destruct (Hi (pin_spec.row_addr catA i + k)) as (Hm & Ho & He);
    [unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES; lia|].
  exact (Kimg _ Hm Ho He). }
assert (Krod : arodata_okP SEGS RLO_A RHI_A B (rdW W2 mem2)).
{ intros a Hro Ho He. rewrite (Kimg a (b11_inro_img a Hro) Ho He). exact (RO a Hro Ho He). }
(* the text: its bytes by the blocks clause (its read span is apart from the block c), its slack at the new state *)
assert (Ktext : sa_str (rdW W2 mem2) (p_t v) (p_s v)).
{ destruct T3 as (b & m & Hb & H1 & H2). destruct T1 as ((Hz & Hn) & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [_ Hrq].
  assert (Hb2 : In (b, m) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HPERM2) Hb).
  assert (HSP : Z.of_nat (length (p_s v)) + 1 <= seg_spec.cstr_span (p_t v) (p_s v)).
  { unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)).
    lia. }
  unfold pf_len in H2.
  split; [split; [|exact Hn]|].
  - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
    replace (p_t v + Z.of_nat i) with (b + (p_t v + Z.of_nat i - b)) by lia.
    rewrite (KB b m (p_t v + Z.of_nat i - b) Hb Hb2 ltac:(lia)).
    + replace (b + (p_t v + Z.of_nat i - b)) with (p_t v + Z.of_nat i) by lia. exact (Hz i Hi).
    + intros Hf. apply HFPc in Hf. unfold sa_disj in HDJ. lia.
  - intros x Hx.
    apply (AR_block_word_vis SEGS B ly2 S2 W2 mem2 md2 b m (p_t v + Z.of_nat (length (p_s v))) x HAR2 Hb2);
      [lia | lia]. }
destruct (b11_addr_of_heap ly2 S2 W2 mem2 md2 (p_t v) (pf_len v) HAR2 (b11_heap_perm _ _ _ _ _ _ HPERM2 T3)
  ltac:(lia) ltac:(unfold pf_len; lia)) as [Atext _].
destruct (b11_addr_of_heap ly2 S2 W2 mem2 md2 (p_c v) seg_spec.SEG_C_SIZE HAR2 (b11_heap_perm _ _ _ _ _ _ HPERM2 C2)
  ltac:(lia) ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [Ac _].
assert (HRG' : pf_rg rX (PF_RL v pos ++ PF_RM v o ln)).
{ unfold pf_rg in *. rewrite Forall_forall in *. intros x Hx. apply HRG. rewrite app_assoc. apply in_or_app.
  left. exact Hx. }
unfold INV_KOUT.
split; [|split; [exact HMID|split]].
- (* pf_base at PF_SC_KNOWN, at the FP state refuse returned *)
  split; [exact HCX|].
  split.
  { split; [exact HJp|].
    split; [rewrite Hly2; exact Hly|].
    split; [destruct HSc as (f0 & Hf0); exists f2; rewrite HS2e, Hf0; apply b11_set_fs2|].
    split; [exact (Permutation_trans HPERM2 HPERM)|].
    split.
    { intros j r Hj. rewrite (rdword_ext (rdW Wc memc) (rdW W2 mem2)); [exact (HSAV j r Hj)|].
      assert (Hj13 : (j < 13)%nat)
        by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
      intros k Hk. apply Khi. lia. }
    split.
    { rewrite (rdword_ext (rdW Wc memc) (rdW W2 mem2)); [exact HFLAG|].
      change (fs_frame_bytes 5) with 2048. intros k Hk. apply Kfr. lia. }
    split; [exact (fxrel_frm0 fx fx1 HFRM Hrel)|].
    split; [exact HTF|].
    split.
    { unfold pf_sl in *. apply Forall_cons; [|apply Forall_nil]. apply Forall_inv in HSLC. cbn [fst snd] in *.
      rewrite (rdword_ext (rdW Wc memc) (rdW W2 mem2)); [exact HSLC|]. intros k Hk. apply Khi. lia. }
    apply (b11_rg_pres rX regs2 _ HP);
      [repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia | exact HRG0]. }
  split.
  { split; [exact Ktext|]. split; [exact Atext|]. split; [exact (b11_heap_perm _ _ _ _ _ _ HPERM2 T3)|].
    split; [exact Ac|]. split; [exact (b11_heap_perm _ _ _ _ _ _ HPERM2 C2)|]. split; [exact Kcat|].
    split; [intros x Hx; exact (Klit _ _ (LI x Hx))|]. split; [exact Krod | exact (SSPX _ _ _ _ _ HAR2)]. }
  split.
  { unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
    pose proof (b11_SL_offs v pos ov Hov) as Ho.
    rewrite (rdword_ext (rdW Wc memc) (rdW W2 mem2)); [exact (HSL ov Hov)|]. intros k Hk. apply Khi. lia. }
  intros i Hi. rewrite (Ksh i ltac:(lia)). exact (HFSH i Hi).
- (* pf_st: c holds the refused state; cur, cur_name, the counters' room after the line *)
  destruct HST as (HRC & HCUR & HNM & HCNT & HCURS).
  destruct HMID as (Ho & _ & _).
  split; [exact HRC2|].
  split; [unfold pf_cur_ok in *; rewrite (proj1 (refuse_proj cf (ln + 1) F_badmodel [AS nm; AS val; AS known]));
    exact HCUR|].
  split.
  { destruct HNM as (f & Hb & Henc). exists f. split; [|exact Henc].
    intros i Hi. destruct Henc as [Hl _]. rewrite Hl in Hi. unfold PF_O_CN in *.
    rewrite (Kfr (pf_F v pos + 0x20 + Z.of_nat i) ltac:(lia)). exact (Hb i ltac:(lia)). }
  split; [exact (pf_cnt_refuse cf (ln + 1) F_badmodel _ _ _ (pf_next_skipn_lt (p_s v) o Ho) HCNT)|].
  rewrite (rdword_ext (rdW Wc memc) (rdW W2 mem2)); [exact HCURS|]. intros k Hk. apply Khi. lia.
- apply (b11_rg_pres rX regs2 _ HP);
    [unfold PF_RL, PF_RM; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia
    | exact HRG'].
Qed.
End d.
