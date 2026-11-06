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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 322 of its 368 lines of code are new or changed and 407 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A: what one pass of segment A11b's join loop (0x8865c..0x886c4, eleven passes, one
   snprintf call each) keeps of the loop-head cut INV_KLOOP (lib/A/Prog/pf_a11b_d.v), and the step of known[]'s
   contents (2026-10-30).

   A pass writes only the snprintf call's stack window below s1 and bytes of known[240] inside the class-5 frame
   (pfj_Wr). pfj_keep carries every fact of INV_KLOOP that names no register and not known[] across such a pass;
   pfj_kmem_step is the new contents of known[].

   The cut-state geometry (a5_G, a5_geo) and every helper not stated over A5's write set are Required from
   segment A5's kit lib/A/Prog/pf_a5_k.v (at commit 01534c6baa27); a kept word is YCbq.rdword_ext. The lemmas below
   named pfj_out, pfj_heap_out, pfj_heap_shadow_out, pfj_heap_tail_out, pfj_img_out, pfj_low_out and pfj_keep_* are
   that file's a5_out, a5_heap_out, a5_heap_shadow_out, a5_heap_tail_out, a5_img_out, a5_low_out and a5_keep_*,
   restated over pfj_Wr in place of a5_Wrx, with their proofs kept (only the case split of the write set changes). As in
   a5_keep_rod0 / a5_keep_ssp, the read-only window and the stack-protector cells lie in [0x10000, kImgEnd), which
   holds no frame byte, so the file takes no Section hypothesis. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_d pf_a5_k pf_a11b_d pf_a11b_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= the contents of known[] after one pass ======================= *)
(* known[0 .. pf_kn ti) kept, and the call wrote the pass's text T = pf_sep ti ++ pf_tok ti and its NUL at
   known + pf_kn ti *)
Lemma pfj_kmem_step : forall (rd rd' : reader) (kb : Z) (ti : nat),
  (ti <= 10)%nat ->
  pf_kmem rd kb ti ->
  (forall i, 0 <= i < pf_kn ti -> rd' (kb + i) = rd (kb + i)) ->
  (forall i, 0 <= i < Z.of_nat (length (pf_sep ti ++ pf_tok ti)) + 1 ->
     rd' (kb + pf_kn ti + i) = Some (nth (Z.to_nat i) ((pf_sep ti ++ pf_tok ti) ++ [0]) 0)) ->
  pf_kmem rd' kb (S ti).
Proof.
intros rd rd' kb ti Hti HM HP HW.
assert (HJ : pf_J (S ti) = pf_J ti ++ (pf_sep ti ++ pf_tok ti))
  by (rewrite (pf_J_step ti Hti), (pf_fmt_ss ti Hti); reflexivity).
assert (Hkn : pf_kn ti = Z.of_nat (length (pf_J ti))) by reflexivity.
assert (Hold : forall i, (i < length (pf_J ti))%nat -> rd (kb + Z.of_nat i) = Some (nth i (pf_J ti) 0)).
{ intros i Hi. destruct ti as [|ti'].
  - pose proof pf_kn_0 as H0. unfold pf_kn in H0. lia.
  - change (sa_zs rd kb (pf_J (S ti') ++ [0])) in HM. unfold sa_zs in HM.
    rewrite <- (app_nth1 (pf_J (S ti')) [0] 0 Hi). apply HM. rewrite length_app. cbn [length]. lia. }
change (sa_zs rd' kb (pf_J (S ti) ++ [0])). rewrite HJ, <- app_assoc. unfold sa_zs.
intros i Hi. rewrite !length_app in Hi. cbn [length] in Hi.
destruct (Nat.lt_ge_cases i (length (pf_J ti))) as [Hlt | Hge].
- rewrite (app_nth1 _ _ _ Hlt). rewrite HP by (rewrite Hkn; lia). exact (Hold i Hlt).
- rewrite (app_nth2 _ _ _ Hge).
  pose proof (HW (Z.of_nat (i - length (pf_J ti)))) as HWi. rewrite Nat2Z.id in HWi.
  replace (kb + Z.of_nat i) with (kb + pf_kn ti + Z.of_nat (i - length (pf_J ti))) by (rewrite Hkn; lia).
  apply HWi. rewrite length_app. lia.
Qed.

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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the bytes one pass writes: the callee windows below s1, and known[240] *)
Definition pfj_Wr (v : pfv) (pos : Z) (a : Z) : Prop :=
  (pf_sp0 v - STK_reac_segconf_parse_file <= a < pf_s1 v) \/
  (pf_F v pos + PF_O_KNOWN <= a < pf_F v pos + PF_O_KNOWN + 240).

(* ======================= bytes a pass does not write (pf_a5_k.v's a5_out .. a5_low_out over pfj_Wr) ============ *)
(* a byte below alloc_ceiling and outside the frame is not one *)
Lemma pfj_out : forall v pos a, a5_G v pos -> a < alloc_ceiling -> ~ (pf_F v pos <= a < pf_F v pos + 2048) ->
  ~ pfj_Wr v pos a.
Proof.
intros v pos a G Hc Hf W. pose proof STK_values as (_ & _ & _ & SPF & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
unfold pfj_Wr, PF_O_KNOWN in W. rewrite SPF in G1, W.
destruct W as [W | W]; lia.
Qed.
(* a heap byte *)
Lemma pfj_heap_out : forall v pos lyc Sc Wc memc mdc b m a,
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ pfj_Wr v pos a.
Proof.
intros v pos lyc Sc Wc memc mdc b m a G HAR Hin Hly Hb Ha. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
change (fs_frame_bytes 5) with 2048 in Hd.
apply (pfj_out v pos a G); lia.
Qed.
(* the shadow cell of a heap byte *)
Lemma pfj_heap_shadow_out : forall v pos lyc Sc Wc memc mdc b m x,
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m -> ~ pfj_Wr v pos (SHADOW_OFF + x / 8).
Proof.
intros v pos lyc Sc Wc memc mdc b m x G HAR Hin Hly Hb Hx. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, G9.
unfold pfj_Wr, PF_O_KNOWN. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF in *.
intros [W | W]; lia.
Qed.
(* a byte after a heap string's NUL in the NUL's granule *)
Lemma pfj_heap_tail_out : forall v pos lyc Sc Wc memc mdc b m e x,
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= e < b + req_size m -> e < x < e - e mod 8 + 8 -> ~ pfj_Wr v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc b m e x G HAR Hin Hly Hb He Hx. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
change (fs_frame_bytes 5) with 2048 in Hd.
pose proof (alloc_ceiling_value) as (_ & AC4).
pose proof (Z.div_mod e 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Me.
pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as DA.
pose proof G as (_ & _ & _ & _ & _ & _ & _ & G8 & _).
pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as DF.
apply (pfj_out v pos x G); lia.
Qed.
(* an image byte *)
Lemma pfj_img_out : forall v pos lyc Sc Wc memc mdc a,
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  in_img SEGS a -> ~ pfj_Wr v pos a.
Proof.
intros v pos lyc Sc Wc memc mdc a G HAR Hin Hly Hi. subst lyc.
pose proof (pa_img_range a Hi) as Hr. unfold kImgEnd in Hr.
pose proof (frm_img SEGS B LAWS (p_ly v) Sc Wc memc mdc 5 pos a HAR Hin) as Hf.
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hf. change (fs_frame_bytes 5) with 2048 in Hf.
pose proof asan_consts as (C1 & _).
apply (pfj_out v pos a G); [lia | intros Ha; exact (Hf Ha Hi)].
Qed.
(* a byte of the layout's image range [0x10000, kImgEnd), which holds no frame byte (AR's ledger, PAImg's
   pa_img_cover and al_client_img) *)
Lemma pfj_low_out : forall v pos lyc Sc Wc memc mdc a,
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  0x10000 <= a < kImgEnd -> ~ pfj_Wr v pos a.
Proof.
intros v pos lyc Sc Wc memc mdc a G HAR Hin Hly Ha. subst lyc.
pose proof HAR as (M & LG & _).
pose proof (pa_img_cover (p_ly v) Sc mdc LG) as [IC1 IC2].
pose proof asan_consts as (AC & _).
apply (pfj_out v pos a G).
- unfold kImgEnd in *. lia.
- intros Hf. destruct (al_client_img _ _ LAWS (p_ly v) Sc Wc memc mdc a HAR) as [Hz _].
  { right. left. exists 5, pos. split; [exact Hin|].
    change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048. exact Hf. }
  apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
Qed.

(* ======================= what a pass keeps (pf_a5_k.v's a5_keep_* over pfj_Wr) ======================= *)
Section k.
Variables (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (mdc : Model) (Wc' : world SEGS) (memc' : word -> option byte).
#[local] Notation rd' := (rdW Wc' memc').
Hypothesis G : a5_G v pos.
Hypothesis HAR : AR SEGS B lyc Sc Wc memc mdc.
Hypothesis Hin : In (5, pos) (frames Sc).
Hypothesis Hly : lyc = p_ly v.
Hypothesis HK : forall a, 0 <= a < 2 ^ 64 -> ~ pfj_Wr v pos a -> rd' a = rdW Wc memc a.
Hypothesis HV : forall a, rdW Wc memc a <> None -> rd' a <> None.

Lemma pfj_keep_addr : forall q n, sa_heap B lyc Sc q n -> sa_addr (rdW Wc memc) q n -> sa_addr rd' q n.
Proof.
intros q n (b & m & Hb & H1 & H2) (A0 & A1 & A2 & A3 & A4).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- intros x Hx. destruct (A3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite HK; [exact Hs | |].
  + pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 x ltac:(lia) ltac:(lia)).
    unfold SHADOW_OFF. lia.
  + exact (pfj_heap_shadow_out v pos lyc Sc Wc memc mdc b m x G HAR Hin Hly Hb ltac:(lia)).
- intros Hn s Hs. apply HV. exact (A4 Hn s Hs).
Qed.
Lemma pfj_keep_hstr : forall q s, sa_heap B lyc Sc q (Z.of_nat (length s) + 1) -> sa_str (rdW Wc memc) q s ->
  sa_str rd' q s.
Proof.
intros q s (b & m & Hb & H1 & H2) ((Hz & Hn) & Ht).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite HK; [exact (Hz i Hi) | lia |].
  refine (pfj_heap_out v pos lyc Sc Wc memc mdc b m _ G HAR Hin Hly Hb _). lia.
- intros x Hx. pose proof (Z.mod_pos_bound (q + Z.of_nat (length s)) 8 ltac:(lia)).
  rewrite HK; [exact (Ht x Hx) | lia |].
  exact (pfj_heap_tail_out v pos lyc Sc Wc memc mdc b m (q + Z.of_nat (length s)) x G HAR Hin Hly Hb ltac:(lia) Hx).
Qed.
Lemma pfj_keep_lit : forall a s, sa_lit SEGS B (rdW Wc memc) a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & ((Hz & Hn) & Ht) & Hp & Hr & Hi).
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Himg & _ & _).
pose proof (pa_img_range _ Himg) as Hrg. unfold kImgEnd in Hrg.
rewrite HK; [exact (Hz i Hi') | lia | exact (pfj_img_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly Himg)].
Qed.
Lemma pfj_keep_img_word : forall a, (forall k, 0 <= k < 8 -> in_img SEGS (a + k)) ->
  rdword rd' a = rdword (rdW Wc memc) a.
Proof.
intros a Hi. apply rdword_ext. intros k Hk. pose proof (pa_img_range _ (Hi k Hk)) as Hrg. unfold kImgEnd in Hrg.
apply HK; [lia | exact (pfj_img_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly (Hi k Hk))].
Qed.
Lemma pfj_keep_cat : sa_cat SEGS B (rdW Wc memc) catA -> sa_cat SEGS B rd' catA.
Proof.
intros (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (pfj_keep_lit tp _ Hl)].
rewrite pfj_keep_img_word; [exact Htp|].
intros k Hk. assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
refine (proj1 (Hi (pin_spec.row_addr catA i + k) _)). unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
(* the stack-protector cells and the read-only window lie in [0x10000, kImgEnd) (pfj_low_out) *)
Lemma pfj_keep_ssp : sa_ssp (rdW Wc memc) gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (S1 & g & S2).
assert (KW : forall a, 0x10000 <= a -> a + 8 <= kImgEnd -> rdword rd' a = rdword (rdW Wc memc) a).
{ intros a H1 H2. apply rdword_ext. intros k Hk. apply HK; [unfold kImgEnd in *; lia|].
  apply (pfj_low_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly). unfold kImgEnd in *; lia. }
split; [rewrite KW; [exact S1 | unfold gotwA; lia | unfold gotwA, kImgEnd; lia]|].
exists g. rewrite KW; [exact S2 | unfold guardA; lia | unfold guardA, kImgEnd; lia].
Qed.
Lemma pfj_keep_rod0 : arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros HR a Hro Ho He.
assert (Hlow : 0x10000 <= a < kImgEnd /\ ~ pfj_Wr v pos a).
{ destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
    pose proof (pa_img_range _ Hi) as Hrg.
    split; [exact Hrg | exact (pfj_img_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly Hi)].
  - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr.
    assert (Hl : 0x10000 <= a < kImgEnd) by (unfold kImgEnd; lia).
    split; [exact Hl | exact (pfj_low_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly Hl)]. }
rewrite HK; [exact (HR a Hro Ho He) | unfold kImgEnd in *; lia | exact (proj2 Hlow)].
Qed.
Lemma pfj_keep_obj0 : pf_obj B v lyc Sc (rdW Wc memc) -> pf_obj B v lyc Sc rd'.
Proof.
intros (T1 & T2 & T3 & C1 & C2 & CA & LI & RO & SS).
split; [exact (pfj_keep_hstr _ _ T3 T1)|]. split; [exact (pfj_keep_addr _ _ T3 T2)|]. split; [exact T3|].
split; [exact (pfj_keep_addr _ _ C2 C1)|]. split; [exact C2|]. split; [exact (pfj_keep_cat CA)|].
split; [intros x Hx; exact (pfj_keep_lit _ _ (LI x Hx))|].
split; [exact (pfj_keep_rod0 RO) | exact (pfj_keep_ssp SS)].
Qed.
(* c's bytes and cur_name (F + 0x20 .. F + 0x30, below known) *)
Lemma pfj_keep_st : forall cf cur nm k, sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  pf_st v pos (rdW Wc memc) cf cur nm k -> pf_st v pos rd' cf cur nm k.
Proof.
intros cf cur nm k (b & m & Hb & H1 & H2) ((bs & Hbs & Henc) & HC & (f & Hf & Hfe) & HN).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
pose proof asan_consts as (AC1 & _).
split; [|split; [exact HC|split; [|exact HN]]].
- exists bs. split; [|exact Henc]. intros i Hi. destruct Henc as [Hl _].
  rewrite HK; [exact (Hbs i Hi) | unfold seg_spec.SEG_C_SIZE in *; lia |].
  refine (pfj_heap_out v pos lyc Sc Wc memc mdc b m _ G HAR Hin Hly Hb _). unfold seg_spec.SEG_C_SIZE in *. lia.
- exists f. split; [|exact Hfe]. intros i Hi. destruct Hfe as [Hl _].
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
  pose proof STK_values as (_ & _ & _ & SPF & _).
  rewrite HK; [exact (Hf i Hi) | unfold PF_O_CN; lia |].
  unfold pfj_Wr, PF_O_KNOWN, PF_O_CN. rewrite SPF in *.
  intros [W | W]; lia.
Qed.
End k.

(* the stack slots, the saved registers, the flag word, the frame's shadow, the value string in buf and ntok,
   kept by a pass (pf_a5_k.v's a5_keep_sl / _slot / _saved / _flag / _fsh over pfj_Wr) *)
(* any slot s1 + off with 0 <= off <= 0xb8: above s1, so above the window, and above alloc_ceiling *)
Lemma pfj_keep_slots : forall v pos (rd rd' : reader) L, a5_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfj_Wr v pos a -> rd' a = rd a) ->
  Forall (fun ov => 0 <= fst ov <= 0xb8) L ->
  pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros v pos rd rd' L G HK HL H.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _).
unfold pf_sl in *. rewrite Forall_forall in *. intros [off x] Hov.
specialize (H _ Hov). specialize (HL _ Hov). cbn [fst snd] in *.
rewrite rdword_ext with (rd := rd); [exact H|]. intros k Hk. apply HK; [lia|].
unfold pfj_Wr, PF_O_KNOWN. rewrite SPF in *. intros [W | W]; lia.
Qed.
Lemma pfj_PF_SL_off : forall v pos, Forall (fun ov => 0 <= fst ov <= 0xb8) (PF_SL v pos).
Proof. intros v pos. unfold PF_SL. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. Qed.
Lemma pfj_sl2_off : forall x y : Z, Forall (fun ov => 0 <= fst ov <= 0xb8) [(0x18, x); (0xb0, y)].
Proof. intros x y. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. Qed.
Lemma pfj_keep_saved : forall v pos (rd rd' : reader) regs, a5_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfj_Wr v pos a -> rd' a = rd a) ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos rd rd' regs G HK H j r Hj.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
rewrite rdword_ext with (rd := rd); [exact (H j r Hj)|]. intros k Hk. apply HK; [lia|].
unfold pfj_Wr, PF_O_KNOWN. rewrite SPF in *. intros [W | W]; lia.
Qed.
Lemma pfj_keep_flag : forall v pos (rd rd' : reader) x, a5_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfj_Wr v pos a -> rd' a = rd a) ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some x -> rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some x.
Proof.
intros v pos rd rd' x G HK H.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _).
change (fs_frame_bytes 5) with 2048 in *.
rewrite rdword_ext with (rd := rd); [exact H|]. intros k Hk. apply HK; [lia|].
unfold pfj_Wr, PF_O_KNOWN. rewrite SPF in *. intros [W | W]; lia.
Qed.
Lemma pfj_keep_fsh : forall v pos (rd rd' : reader) sc, a5_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfj_Wr v pos a -> rd' a = rd a) ->
  pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros v pos rd rd' sc G HK H i Hi.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite HK; [exact (H i Hi) | unfold kHighShadowEnd in G12; lia |].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
unfold pfj_Wr, PF_O_KNOWN. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd in *.
intros [W | W]; lia.
Qed.
(* a C string and its NUL inside buf[512] at F + 0x40 (pf_inb): its bytes and its tail granule end below
   F + 0x248, under known at F + 0x320 *)
Lemma pfj_keep_fstr : forall v pos (rd rd' : reader) p s, a5_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfj_Wr v pos a -> rd' a = rd a) ->
  pf_inb (pf_F v pos + PF_O_BUF) p s -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros v pos rd rd' p s G HK (Hb1 & Hb2) ((Hz & Hn) & Ht).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
unfold PF_O_BUF in Hb1, Hb2.
assert (NW : forall a, pf_F v pos <= a < pf_F v pos + 0x320 -> ~ pfj_Wr v pos a).
{ intros a Ha. unfold pfj_Wr, PF_O_KNOWN. intros [W | W]; lia. }
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite HK; [exact (Hz i Hi) | lia | apply NW; lia].
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
  rewrite HK; [exact (Ht x Hx) | lia | apply NW; lia].
Qed.
(* ntok's 8 bytes at F + 0x450, above known's F + 0x410 *)
Lemma pfj_keep_val : forall v pos (rd rd' : reader) x, a5_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfj_Wr v pos a -> rd' a = rd a) ->
  sa_val rd (pf_F v pos + PF_O_NTOK) 8%nat x -> sa_val rd' (pf_F v pos + PF_O_NTOK) 8%nat x.
Proof.
intros v pos rd rd' x G HK H k Hk.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
rewrite HK; [exact (H k Hk) | unfold PF_O_NTOK; lia |].
unfold pfj_Wr, PF_O_KNOWN, PF_O_NTOK. intros [W | W]; lia.
Qed.

(* ======================= what one pass keeps of INV_KLOOP ======================= *)
(* every fact of INV_KLOOP that names no register and not known[] *)
Lemma pfj_keep : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti memc',
  INV_KLOOP B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pfj_Wr v pos a -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  sa_ssp (rdW Wc memc') gotwA guardA ->
  pf_obj B v lyc Sc (rdW Wc memc') /\
  pf_sl (rdW Wc memc') (pf_s1 v) (PF_SL v pos) /\
  pf_fsh (rdW Wc memc') (pf_SH v pos) PF_SC_KN /\
  pf_saved (rdW Wc memc') (pf_sp0 v) (p_regs v) /\
  rdword (rdW Wc memc') (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) /\
  pf_st v pos (rdW Wc memc') cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc') vp val /\
  sa_val (rdW Wc memc') (pf_F v pos + PF_O_NTOK) 8%nat 11 /\
  pf_sl (rdW Wc memc') (pf_s1 v) [(0x18, vp); (0xb0, seg_spec.rseg_addr (p_c v) gi)].
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti memc' HI HK HV _.
destruct HI as (HB & _ & HST & HSTR & HINB & _ & _ & HNT & HSL2 & _).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
destruct HB as (_ & HFI & HOBJ & HSL & HFSH).
destruct HFI as (_ & _ & _ & _ & HSV & HFL & _).
pose proof HOBJ as (_ & _ & _ & _ & HC & _).
split; [eapply pfj_keep_obj0; eassumption|].
split; [exact (pfj_keep_slots v pos _ _ _ G HK (pfj_PF_SL_off v pos) HSL)|].
split; [exact (pfj_keep_fsh v pos _ _ _ G HK HFSH)|].
split; [exact (pfj_keep_saved v pos _ _ _ G HK HSV)|].
split; [exact (pfj_keep_flag v pos _ _ _ G HK HFL)|].
split; [eapply pfj_keep_st; eassumption|].
split; [exact (pfj_keep_fstr v pos _ _ _ _ G HK HINB HSTR)|].
split; [exact (pfj_keep_val v pos _ _ _ G HK HNT)|].
exact (pfj_keep_slots v pos _ _ _ G HK (pfj_sl2_off _ _) HSL2).
Qed.
End e.
End f.
End d.
