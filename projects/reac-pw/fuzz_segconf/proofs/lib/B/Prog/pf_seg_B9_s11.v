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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 474 of its 524 lines of code are new or changed and 403 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the KREF stretch of
   segment B9 of reac_segconf_parse_file's walk -- S_B9's second conjunct, at the ambient FP state:
     b9_s11 : forall n, HA_TAIL B n -> H_KREF B n                         (lib/B/Prog/pf_pieces.v)
   A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: the KREF stretch of segment B9, image B).
   ADAPTED from the image-A G3 walk owner's image-A REF3 walk lib/A/Prog/pf_a6_r.v (commit 478e17147770, the
   image-A A6 segment lane: refuse then `j` TAIL) and its kit pf_a6_k.v, through the B7 segment lane's image-B port of that kit
   lib/B/Prog/pf_seg_B7_k.v (commit f641b537fd76, built rc=0; b7k_ renamed b9s11_, copied, not
   Required), re-derived on image B's code.

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s):
     KREF 0x889a0  jal refuse        (a0 = c, a1 = s6 = ln + 1, a2 = f's literal, a3 = slot 0x40 = cur_name,
                                      a4 = the string x; pf_pieces.v INV_KREF / pf_kref)
          0x889a4  j 0x88600         (TAIL)
   2 instructions; no inline check, no UBSan trap branch.

   THE WALK.
   - A seed at KREF (every register its own atom, no region) and one run to the call (PaCallRun paj_run_shc).
   - The call: SIGP turns the call target into BASE + AF_refuse; PaFx.cl_callSF with refuse_contract (Section
     hypothesis REFUSE at the cut's FP state), its premises from a sub-lane's closed site lemma
     pf_seg_B9_cs.v b9_refuse_site_kref (VERIFY rule 1j-bis) at the call state, the frame chain from a sub-lane's
     pf_seg_B9_k.v b9_chain, refuse_W inside RC_PARSE_W and inside the block c (b9s11_rfw_blk / b9s11_rfw_sub),
     the window STK_refuse = 12464 at o = pf_s1 - pf_sp0 (sp0 - 368 <= s1, b9_geo; 12464 + 368 = 12832 =
     STK_reac_segconf_parse_file).
   - Back at 0x889a4 at refuse's FP state fx1 (srr_apost_baseF_lift): a fresh seed at fx1, one plain run to TAIL
     (PaLibF paj_run_to_sh).
   - INV_TAIL at fx1, at the next line's offset pf_next s o and line number ln + 1, cur and nm kept, c holding
     refuse cf (ln + 1) f args (refuse's post): pf_base rebuilt by b9s11_base_move over b9s11_keeps_refuse
     (refuse's journal keeps the stack from s1 up, the text, the unowned image bytes, the class-5 frame and its
     shadow; its footprint lies in c's block; sa_noalloc gives the layout, set_fs and the permuted blocks;
     sa_frm0 at fx1 by fxrel_frm0; sa_ssp by SSPX); pf_lctx at the next line is pf_mid's; the measure and the
     counters by pfA_facts.pf_next_skipn_lt / pf_cnt_refuse; cur_name by the frame keep, slot 0xc0 by the stack
     keep; the registers by aregs_preserved. The post is H_TAIL's by pf_postm's definition.
   pf_seg_B9_k.v's b9_move / b9_move0 do not apply here: their keep premise (every byte off b9_Wrx kept) is not
   in refuse's journal (refuse's own class-0 side-stack frame and its shadow, errno and owned statics change).

   SECTION HYPOTHESES (pb9-stretch.md texts): REFUSE, SIGP, VRO, SSPX. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB
  pf_pieces pf_seg_B9_k pf_seg_B9_c pf_seg_B9_cs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== refuse's footprint ======================================== *)
(* every byte refuse writes lies in [c + RC_REFUSAL, c + RC_OVERFLOW) (pf_seg_B7_k.v b7k_refuse_W_in_block) *)
Lemma b9s11_rfw_blk : forall c rcs a, inFP (refuse_W c rcs) a ->
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
Lemma b9s11_rfw_pos : forall c rcs, 0 < c -> ~ YI16.sink_open_fp (refuse_W c rcs).
Proof.
intros c rcs Hc. apply sink_closed_pos. apply Forall_forall. intros r Hr. unfold refuse_W in Hr.
apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst]. unfold seg_spec.RC_REFUSED. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat; intros Hr; [|destruct Hr].
  destruct Hr as [<- | [<- | []]]; cbn [fst];
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF; lia.
Qed.
(* refuse's footprint is inside parse_file's (the range refusal[0] .. overflow + 4 of RC_PARSE_W) *)
Lemma b9s11_rfw_sub : forall c rcs a, inFP (refuse_W c rcs) a -> inFP (seg_spec.RC_PARSE_W c) a.
Proof.
intros c rcs a Ha. apply b9s11_rfw_blk in Ha.
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
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis REFUSE : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ======================================== the image ======================================== *)
Lemma b9s11_relro_img : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof.
intros a Ha. destruct VRO as [Hlo Hhi]. apply pa_relro_img. rewrite Hlo, Hhi.
unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Ha. lia.
Qed.
Lemma b9s11_in_roP_img : forall a, in_roP SEGS RLO_A RHI_A a -> in_img SEGS a.
Proof.
intros a [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (b9s11_relro_img a Hr)].
Qed.
(* a literal keeps its bytes where the image bytes are kept; its tail is ROM, its shadow pinned *)
Lemma b9s11_lit_move : forall (rd : reader) (W' : world SEGS) mem' a s, sa_lit SEGS B rd a s ->
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
Lemma b9s11_cat_move : forall (rd : reader) (W' : world SEGS) mem', sa_cat SEGS B rd catA ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
     rdW W' mem' x = rd x) ->
  sa_cat SEGS B (rdW W' mem') catA.
Proof.
intros rd W' mem' (Hp & Hi & Hrows) K. split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (b9s11_lit_move rd W' mem' tp _ Hl K)].
assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (rdword_ext rd (rdW W' mem')); [exact Htp|]. intros k Hk.
unfold pin_spec.row_addr, pin_spec.CAT_ROW in *.
destruct (Hi (catA + 296 * Z.of_nat i + k) ltac:(unfold pin_spec.CAT_BYTES; lia)) as (Hm & Ho & He).
exact (K _ Hm Ho He).
Qed.

(* ======================================== blocks and frames ======================================== *)
Lemma b9s11_heap_addr : forall ly S (W : world SEGS) mem md q n,
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
Lemma b9s11_heap_bounds : forall ly S (W : world SEGS) mem md q n,
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 <= n ->
  exists b m, In (b, m) (ablocks B ly S) /\ b <= q /\ q + n <= b + req_size m /\ 4096 <= b /\
    b + req_size m <= alloc_ceiling /\ in_app b (req_size m).
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hq) Hn.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
exists b, m. split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Happ].
Qed.
Lemma b9s11_heap_perm : forall ly S ly' S' q n, Permutation (ablocks B ly' S') (ablocks B ly S) ->
  sa_heap B ly S q n -> sa_heap B ly' S' q n.
Proof.
intros ly S ly' S' q n HP (b & m & Hin & Hb & Hq). exists b, m.
split; [exact (Permutation_in _ (Permutation_sym HP) Hin) | lia].
Qed.
(* a byte of the shadow band is in no app range *)
Lemma b9s11_band_not_app : forall b n s, in_app b n -> SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> ~ (b <= s < b + n).
Proof.
intros b n s Happ Hs Hin.
unfold in_app, SHADOW_OFF, kLowShadowBeg, YG0f.kHighMemBeg in *. lia.
Qed.

(* ======================================== the entry facts ======================================== *)
Lemma b9s11_cx : forall v, pf_cx B v ->
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
Definition b9s11_s1v (sp0 : Z) : Z := (sp0 - 0x160) - (sp0 - 0x160) mod 32.
Lemma b9s11_s1 : forall sp0, sp0 mod 16 = 0 ->
  sp0 - 0x180 < b9s11_s1v sp0 <= sp0 - 0x160 /\ b9s11_s1v sp0 mod 32 = 0 /\ b9s11_s1v sp0 mod 16 = 0 /\
  (b9s11_s1v sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H16. unfold b9s11_s1v.
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
Lemma b9s11_s1_eq : forall v, pf_s1 v = b9s11_s1v (pf_sp0 v).
Proof. reflexivity. Qed.
Lemma b9s11_frame : forall v pos lyc Sc Wc rX memc mdc,
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

(* ======================================== the cut facts after refuse ======================================== *)
Lemma b9s11_sl_move : forall (rd rd' : reader) b L, pf_sl rd b L ->
  Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0x100) L -> 0 <= b -> b + 0x100 <= 2 ^ 64 ->
  (forall a, b <= a < 2 ^ 64 -> rd' a = rd a) -> pf_sl rd' b L.
Proof.
intros rd rd' b L HL HB Hb Hb2 K. unfold pf_sl in *. rewrite Forall_forall in HL, HB |- *.
intros ov Hin. rewrite <- (HL ov Hin). apply rdword_ext. intros k Hk.
pose proof (HB ov Hin). apply K. lia.
Qed.
Lemma b9s11_PF_SL_offs : forall v pos, Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0x100) (PF_SL v pos).
Proof. intros v pos. unfold PF_SL. repeat constructor; cbn [fst]; lia. Qed.
(* what the state after refuse agrees on with the cut: the stack from s1 up, the text and its NUL, the unowned
   image bytes, the class-5 frame and its shadow *)
Definition b9s11_keeps (v : pfv) (pos : Z) (Wc : world SEGS) memc (W2 : world SEGS) mem2 : Prop :=
  (forall a, pf_s1 v <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a) /\
  (forall i, 0 <= i <= Z.of_nat (length (p_s v)) -> rdW W2 mem2 (p_t v + i) = rdW Wc memc (p_t v + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW Wc memc a) /\
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 \/
             pf_SH v pos <= a < pf_SH v pos + fs_frame_bytes 5 / 8 ->
     rdW W2 mem2 a = rdW Wc memc a).
(* pf_base at the state after the call, at the FP state fx1 it returned at (image B's pf_fi: 10 conjuncts, the
   register list 2, 3, 4, 8, 9, 20) *)
Lemma b9s11_base_move : forall (fx1 : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc ly2 S2 (W2 : world SEGS) regs2
  mem2 md2,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc sc ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 0 ->
  ly2 = lyc -> (exists f, S2 = set_fs f Sc) -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  b9s11_keeps v pos Wc memc W2 mem2 ->
  (forall r, In r [2; 3; 4; 8; 9; 20] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 sc.
Proof.
intros fx1 v pos lyc Sc Wc rX memc mdc sc ly2 S2 W2 regs2 mem2 md2 (CX & FI & OBJ & SL & FSH) Hfx HJ2 Hly2
  (f2 & HS2) HP2 (K1 & K2 & K3 & K4) KR.
destruct (b9s11_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (b9s11_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (b9s11_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b9s11_s1_eq in S1a, S1b, S1c, S1d.
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
  { apply (b9s11_sl_move (rdW Wc memc) (rdW W2 mem2) (pf_s1 v) [(0xc8, p_c v)] HC8);
      [apply Forall_cons; [cbn [fst]; lia | apply Forall_nil] | lia | lia |].
    intros a Ha. apply K1. exact Ha. }
  unfold pf_rg in *. rewrite Forall_forall in HRG |- *. intros rv Hin.
  rewrite (KR (fst rv)); [exact (HRG rv Hin)|].
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
split.
{ destruct (b9s11_heap_bounds lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
    as (bt & mt & Hint & Hbt1 & Hbt2 & _ & _ & _).
  assert (HT2 : sa_heap B ly2 S2 (p_t v) (Z.of_nat (length (p_s v)) + 1)) by exact (b9s11_heap_perm _ _ _ _ _ _ HP2 HT).
  assert (HC2 : sa_heap B ly2 S2 (p_c v) seg_spec.SEG_C_SIZE) by exact (b9s11_heap_perm _ _ _ _ _ _ HP2 HC).
  split.
  { destruct STR as ((Hz & Hn) & _). split; [split; [|exact Hn]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      rewrite K2 by lia. exact (Hz i Hi).
    - intros x Hx. apply (AR_block_word_vis SEGS B ly2 S2 W2 mem2 md2 bt mt (p_t v + Z.of_nat (length (p_s v))) x HAR2).
      + exact (Permutation_in _ (Permutation_sym HP2) Hint).
      + lia.
      + lia. }
  split; [exact (b9s11_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HT2 ltac:(lia))|].
  split; [exact HT2|].
  split; [exact (b9s11_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HC2 ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact HC2|].
  split; [exact (b9s11_cat_move _ W2 mem2 CAT K3)|].
  split; [intros x Hx; exact (b9s11_lit_move _ W2 mem2 _ _ (LITS x Hx) K3)|].
  split; [intros a Hro Ho He; rewrite (K3 a (b9s11_in_roP_img a Hro) Ho He); exact (ROD a Hro Ho He)|].
  exact (SSPX ly2 S2 W2 mem2 md2 HAR2). }
split.
{ apply (b9s11_sl_move (rdW Wc memc) _ (pf_s1 v) _ SL (b9s11_PF_SL_offs v pos)); [lia | lia |].
  intros a Ha. apply K1. exact Ha. }
intros i Hi. rewrite K4; [exact (FSH i Hi)|]. right. rewrite E5. change (2048 / 8) with 256. lia.
Qed.
(* after a call made at sp = s1 whose footprint lies in the block c: its journal keeps the stack outside its
   window and footprint, the live blocks outside the footprint, the unowned image bytes and the entry's side-stack
   frames *)
Lemma b9s11_keeps_call : forall v pos lyc Sc Wc rX memc mdc sc STKc FPc ly2 S2 (W2 : world SEGS) mem2 md2 k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STKc (pf_s1 v) FPc lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k ->
  (forall a, inFP FPc a -> p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) -> ~ YI16.sink_open_fp FPc ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  b9s11_keeps v pos Wc memc W2 mem2.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc STKc FPc ly2 S2 W2 mem2 md2 k (CX & FI & OBJ & _ & _) HJc NFP HCl HP2.
destruct (b9s11_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (b9s11_frame v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (b9s11_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b9s11_s1_eq in S1a, S1b, S1c, S1d.
pose proof (proj1 (proj1 FI)) as HAR.
destruct OBJ as (_ & _ & HT & _ & HC & _).
destruct (b9s11_heap_bounds _ _ _ _ _ (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
  as (bt & mt & Hint & Hb1 & Hb2 & Hb3 & Hb4 & _).
destruct (b9s11_heap_bounds _ _ _ _ _ (p_c v) seg_spec.SEG_C_SIZE HAR HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as (bc & mc & Hinc & Hc1 & Hc2 & Hc3 & Hc4 & Hcapp).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
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
    apply (b9s11_band_not_app bc (req_size mc) a Hcapp); [lia|].
    unfold seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* after refuse: its footprint refuse_W lies in the block c (refusal[n], n_refusals, refused) *)
Lemma b9s11_keeps_refuse : forall v pos lyc Sc Wc rX memc mdc sc cf ly2 S2 (W2 : world SEGS) mem2 md2 k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_refuse (pf_s1 v) (refuse_W (p_c v) cf) lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  b9s11_keeps v pos Wc memc W2 mem2.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc cf ly2 S2 W2 mem2 md2 k HB HJc HP2.
destruct (b9s11_cx v (proj1 HB)) as (Hc0 & _).
apply (b9s11_keeps_call v pos lyc Sc Wc rX memc mdc sc STK_refuse (refuse_W (p_c v) cf) ly2 S2 W2 mem2 md2 k HB HJc);
  [| exact (b9s11_rfw_pos _ cf Hc0) | exact HP2].
intros a Ha. apply b9s11_rfw_blk in Ha. unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW,
  seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* cur_name's bytes are in the frame *)
Lemma b9s11_nm_move : forall v pos (rd rd' : reader) nm, pf_nm rd (pf_F v pos + PF_O_CN) nm ->
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 -> rd' a = rd a) ->
  pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros v pos rd rd' nm (f & Hb & He) K. exists f. split; [|exact He].
intros i Hi. destruct He as (Hl & _). rewrite Hl in Hi. rewrite K; [exact (Hb i ltac:(lia))|].
change (fs_frame_bytes 5) with 2048. unfold PF_O_CN. lia.
Qed.

(* ======================================== the stretch: KREF -> TAIL ======================================== *)
Lemma b9_s11 : forall n, HA_TAIL B n -> H_KREF B n.
Proof.
intros n HT. unfold H_KREF.
intros v pos lyc Sc Wc rX memc mdc cf cur nm o ln d f fa args xp HINV.
pose proof HINV as (HB & MID & ST & KRF & RG).
pose proof HB as (CX & FI & OBJ & SL & FSH).
pose proof FI as (HJ & Hly' & HFS & HPERM & HSV & HFL & HFRM & HTF & HSLC & HFIRG).
pose proof (b9_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _).
destruct (b9s11_cx v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof (b9s11_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b9s11_s1_eq in S1a, S1b, S1c, S1d.
pose proof (b9_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
destruct (b9_chain B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as [ch1 HCH].
pose proof OBJ as (_ & _ & _ & _ & HCH0 & _).
pose proof MID as (Ho & Hon & HLC).
pose proof STK_values as (_ & SRF & _ & SPF & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof alloc_ceiling_lt as Hac.
destruct (b9s11_heap_bounds lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HCH0
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & _).
destruct ST as (HRC & COK & NM & CNT & SLC0).
destruct KRF as (HFk & Hfa & x & Hargs & HSx & HIx).
subst fa args.
(* the seed at KREF: the cut's registers, no region *)
set (E := Eimg (Ereg rX [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (split; [intros n0 Hn; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E (mkSS PF_KREF sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_KREF)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
unfold cfg_at. change (w64 (BASE + PF_KREF)) with (Z_to_bv 64 (BASE + PF_KREF)).
(* 0x889a0 jal refuse *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ apply awr_ok_nil. }
assert (HM : ms_mem ms = memc).
{ apply functional_extensionality. intros y. apply HF. intros (r & Hr & _). destruct Hr. }
clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
pmkst HS. rewrite HM in HJ |- *.
(* the argument and callee-saved registers at the call are the cut's *)
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX [] HS HA0 ltac:(vm_compute; reflexivity)) as HPR.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
assert (KR : forall r, In r [2; 10; 11; 12; 13; 14] -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]].
  - exact (HPR 2 ltac:(unfold acallee_saved; lia)).
  - exact (eq_trans Q10 (EE 10%nat (10%bv : bv 5) eq_refl)).
  - exact (eq_trans Q11 (EE 11%nat (11%bv : bv 5) eq_refl)).
  - exact (eq_trans Q12 (EE 12%nat (12%bv : bv 5) eq_refl)).
  - exact (eq_trans Q13 (EE 13%nat (13%bv : bv 5) eq_refl)).
  - exact (eq_trans Q14 (EE 14%nat (14%bv : bv 5) eq_refl)). }
assert (R10 : getr rX 10 = w64 (p_c v))
  by (exact (b9_rg_get rX _ 10 _ RG ltac:(apply in_or_app; right; apply in_or_app; right; cbn [In]; tauto))).
assert (R11 : getr rX 11 = w64 (ln + 1))
  by (exact (b9_rg_get rX _ 11 _ RG ltac:(apply in_or_app; right; apply in_or_app; right; cbn [In]; tauto))).
assert (R12 : getr rX 12 = w64 (seg_litA_rc f))
  by (exact (b9_rg_get rX _ 12 _ RG ltac:(apply in_or_app; right; apply in_or_app; right; cbn [In]; tauto))).
assert (R13 : getr rX 13 = w64 (pf_F v pos + PF_O_CN))
  by (exact (b9_rg_get rX _ 13 _ RG ltac:(apply in_or_app; right; apply in_or_app; right; cbn [In]; tauto))).
assert (R14 : getr rX 14 = w64 xp)
  by (exact (b9_rg_get rX _ 14 _ RG ltac:(apply in_or_app; right; apply in_or_app; right; cbn [In]; tauto))).
assert (C1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 15332)) by exact Q1.
assert (C10 : getr (ms_regs ms) 10 = w64 (p_c v)) by (rewrite <- R10; exact (KR 10 ltac:(cbn; tauto))).
assert (C11 : getr (ms_regs ms) 11 = w64 (ln + 1)) by (rewrite <- R11; exact (KR 11 ltac:(cbn; tauto))).
assert (C12 : getr (ms_regs ms) 12 = w64 (seg_litA_rc f)) by (rewrite <- R12; exact (KR 12 ltac:(cbn; tauto))).
assert (C13 : getr (ms_regs ms) 13 = w64 (pf_F v pos + PF_O_CN)) by (rewrite <- R13; exact (KR 13 ltac:(cbn; tauto))).
assert (C14 : getr (ms_regs ms) 14 = w64 xp) by (rewrite <- R14; exact (KR 14 ltac:(cbn; tauto))).
assert (C2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ transitivity (getr rX 2); [exact (HPR 2 ltac:(unfold acallee_saved; lia))|].
  exact (b9_rg_get rX _ 2 _ HFI ltac:(cbn [b9_FI In]; tauto)). }
assert (C3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ transitivity (getr rX 3); [exact (HPR 3 ltac:(unfold acallee_saved; lia))|].
  exact (b9_rg_get rX _ 3 _ HFI ltac:(cbn [b9_FI In]; tauto)). }
assert (C4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ transitivity (getr rX 4); [exact (HPR 4 ltac:(unfold acallee_saved; lia))|].
  exact (b9_rg_get rX _ 4 _ HFI ltac:(cbn [b9_FI In]; tauto)). }
assert (C8 : getr (ms_regs ms) 8 = w64 (pf_sp0 v)).
{ transitivity (getr rX 8); [exact (HPR 8 ltac:(unfold acallee_saved; lia))|].
  exact (b9_rg_get rX _ 8 _ HFI ltac:(cbn [b9_FI In]; tauto)). }
assert (Csp : spZ (ms_regs ms) = pf_s1 v).
{ unfold spZ. rewrite C2. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. lia. }
(* the cut's facts at the call state: memory the cut's, journal the run's (model mdq) *)
assert (HBc : pf_base B v pos lyc Sc Wc rX memc mdq PF_SC_LINE).
{ split; [exact CX|]. split; [|exact (conj OBJ (conj SL FSH))].
  split; [exact HJ|]. split; [exact Hly'|]. split; [exact HFS|]. split; [exact HPERM|].
  split; [exact HSV|]. split; [exact HFL|]. split; [exact HFRM|]. split; [exact HTF|].
  split; [exact HSLC | exact HFIRG]. }
(* VERIFY rule 1j-bis at 0x889a0: refuse_contract's premises from INV_KREF, a sub-lane's closed site lemma *)
destruct (b9_refuse_site_kref B v pos lyc Sc Wc memc mdq (ms_regs ms) cf o ln d n f nm xp x
  (b9_st_of_base B v pos lyc Sc Wc rX memc mdq HBc) HRC (pf_cnt_mono cf _ 0 (Nat.le_0_l _) CNT) MID HFRM HFk
  C10 C11 C12 C13 NM C14 HSx HIx) as (ROD & _ & Hcr & _ & Hlr & _ & Hfr & RPRE & ROOM & EV).
rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms) memc _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdq 0
    STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + 15332)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) f [AS nm; AS x]) /\ sa_noalloc B lyc Sc ly2 S2) HJ).
  - rewrite Csp. lia.
  - exact S1d.
  - lia.
  - rewrite SRF. lia.
  - rewrite SRF, SPF. lia.
  - exact C3.
  - exact C4.
  - exact C1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { exact (REFUSE fx lyc Sc Wc (ms_regs ms) memc mdq ch1 (p_c v) (ln + 1) (seg_litA_rc f) (ln + 1) cf f
        [AS nm; AS x] HPRE1 ROD C10 Hcr C11 Hlr C12 Hfr RPRE ROOM EV). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (b9s11_rfw_sub _ _ a Ha)|].
    apply b9s11_rfw_blk in Ha. exists bc, mc. split; [exact Hinc|].
    unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia. }
(* back at 0x889a4, at the FP state fx1 refuse returned *)
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
unfold pf_postm, PF_POSTr.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
destruct HNA2 as (HP2b & Hly2 & HS2e).
pose proof (b9s11_keeps_refuse v pos lyc Sc Wc rX memc mdq PF_SC_LINE cf ly2 S2 W2 mem2 md2 EV_refuse
  HBc HJc2 HP2b) as HK.
assert (HPR2 : aregs_preserved rX regs2) by exact (aregs_preserved_trans _ _ _ HPR HP2).
(* 0x889a4 j 0x88600: a seed at fx1 with the returned registers, the plain run to TAIL *)
set (E2 := Eimg (Ereg regs2 [])).
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (HA2 : env_agree 32 (Ereg regs2 []) E2)
  by (split; [intros n0 Hn; subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (HS2 : st_ok_pi (fx := fx1) SEGS VAL E2 (mkSS 15332 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (@mkst fx1 regs2 (Z_to_bv 64 (BASE + 15332)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx1) B LAWS) HS2 HJ2 PF_TAIL.
{ apply awr_ok_nil. }
(* at TAIL (0x88600): the `j` wrote nothing and changed no register *)
assert (HM3 : ms_mem ms0 = mem2).
{ apply functional_extensionality. intros y. apply HF. intros (r & Hr & _). destruct Hr. }
clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (md3 := dM) in *; clearbody md3 end.
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 [] HS2 HA2 ltac:(vm_compute; reflexivity)) as HP3.
pmkst HS2. rewrite HM3 in HJ2 |- *.
assert (HPR3 : aregs_preserved rX (ms_regs ms0)) by exact (aregs_preserved_trans _ _ _ HPR2 HP3).
(* pf_base at TAIL, at fx1 *)
assert (HB3 : pf_base (fx := fx1) B v pos ly2 S2 W2 (ms_regs ms0) mem2 md3 PF_SC_LINE).
{ apply (b9s11_base_move fx1 v pos lyc Sc Wc rX memc mdq PF_SC_LINE ly2 S2 W2 (ms_regs ms0) mem2 md3 HBc Hfx1
    HJ2 Hly2 HS2e HP2b HK).
  intros r Hr. apply HPR3. unfold acallee_saved. cbn [In] in Hr. lia. }
assert (RG' : pf_rg rX (PF_RL v pos ++ PF_RM v o ln)).
{ apply (b9_rg_incl rX (PF_RL v pos ++ PF_RM v o ln ++
    [(10, p_c v); (11, ln + 1); (12, seg_litA_rc f); (13, pf_F v pos + PF_O_CN); (14, xp)])); [|exact RG].
  intros y Hy. rewrite app_assoc. apply in_or_app. left. exact Hy. }
destruct HK as (K1 & _ & _ & K4).
assert (HINV2 : INV_TAIL (fx := fx1) B n v pos ly2 S2 W2 (ms_regs ms0) mem2 md3
  (refuse cf (ln + 1) f [AS nm; AS x]) cur nm (pf_next (p_s v) o) (ln + 1) d).
{ split; [exact HB3|]. split; [exact HLC|].
  split; [pose proof (pf_next_skipn_lt (p_s v) o Ho); lia|].
  split.
  - split; [exact HRC2|]. split.
    + destruct cur as [i|]; cbn [pf_cur_ok] in COK |- *; [|exact I].
      rewrite (proj1 (refuse_proj cf (ln + 1) f [AS nm; AS x])). exact COK.
    + split.
      * apply (b9s11_nm_move v pos (rdW Wc memc) _ nm NM).
        intros a Ha. apply K4. left. exact Ha.
      * split; [exact (pf_cnt_refuse cf (ln + 1) f [AS nm; AS x] _ _ (pf_next_skipn_lt (p_s v) o Ho) CNT)|].
        rewrite <- SLC0. apply rdword_ext. intros k Hk. apply K1. lia.
  - apply (b9_rg_pres rX (ms_regs ms0) _ HPR3); [|exact RG'].
    apply Forall_app. split; [exact (b9_RL_cs v pos) | exact (b9_RM_cs v o ln)]. }
exact (HT fx1 v pos ly2 S2 W2 (ms_regs ms0) mem2 md3 (refuse cf (ln + 1) f [AS nm; AS x]) cur nm
  (pf_next (p_s v) o) (ln + 1) d HINV2).
Qed.

End e.
End f.
End d.
