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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 254 of its 296 lines of code are new or changed and 411 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a6_l_c.v, with its module paths, module names and numbers changed; 347 of its 417 lines of code are new or changed and 226 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): what the three INTERCEPTOR calls of
   segment B7 of reac_segconf_parse_file's walk ask, derived once from a cut of B7 (the B7 segment lane of the image-B G3 walk owner,
   2026-10-30). No instruction is walked here.
   ADAPTED from the image-A G3 walk owner's image-A A7 segment lane lib/A/Prog/pf_a7_r.v (commit ebe0b30cca65): the
   same lemmas over image B's pf_pieces.v, with image B's numbers where they differ:
     - the realigned locals base s1 = (sp0 - 0x160) & -32 (B 0x87e38 `addi sp,sp,-352`, 0x87e78 `andi sp,sp,-32`),
       so sp0 - 368 <= s1 <= sp0 - 352 (A: 0x140, -336 .. -320); parse_file's STK at image B is 12832 = 352 + 16 +
       12464 (SegInstB.STK_values);
     - the three call pcs: strchr 0x883bc (a1 = ']' at 0x883b4, a0 = s7 at 0x883b8), strncasecmp 0x88500 (a1 =
       .str.6 0x214a0 "segment" at 0x884f0 / 0x884f4, a2 = 7 at 0x884f8, a0 = s3 at 0x884fc), strlen 0x887b4 (a0 = s7
       at 0x887b0); the trampolines are the listing's pa_sigma SS___interceptor_trampoline_{strchr,strncasecmp,
       strlen} (image B 0x43ab4, 0x43aac, 0x43a98).
   Each call's premise list is the one its carrier text states (lib/B/Rt/RtSeg.v rows 6 and 7, lib/B/Rt/RtString.v
   astrlen_realizes): ecall_pre_stk with its window, astr_at, aread_ok, amem_range, atail_vis, rt_rom_view.
   Section 8 is this lane's: the bridges from the strchr and strncasecmp answers (RtSeg.first_at, RtSeg.strncase_eq)
   to SegModel's strchr / strncasecmp.
   No Section hypothesis: the file is closed over the listing instance PI and the symbols B. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase reac_segconf_parse_file_c SegInstB pf_pieces pf_seg_B7_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require PaArt reac_segconf_parse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the 8-byte shadow hull of a sub-range lies inside the hull of the range *)
Lemma b7_hull_sub : forall (rd : reader) q n q' n', shadow_hull_vis rd q n -> q <= q' -> 0 < n' ->
  q' + n' <= q + n -> shadow_hull_vis rd q' n'.
Proof.
  intros rd q n q' n' H Hq Hn Hle s Hs. apply H.
  pose proof (shadow_mono q q' Hq) as M1.
  pose proof (shadow_mono (q' + n' - 1) (q + n - 1) ltac:(lia)) as M2.
  assert (R8 : forall u w, u <= w -> u / 8 * 8 <= w / 8 * 8)
    by (intros u w Huw; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
  pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* sa_addr of a sub-range *)
Lemma b7_sa_addr_sub : forall (rd : reader) q n q' n', sa_addr rd q n -> q <= q' -> 0 <= n' ->
  q' + n' <= q + n -> sa_addr rd q' n'.
Proof.
  intros rd q n q' n' (A0 & A1 & A2 & A3 & A4) Hq Hn Hle.
  split; [lia|]. split; [lia|].
  split; [unfold amem_range in *; destruct A2 as [A2|A2]; [left; lia | right; lia]|].
  split; [eapply range_addressable_sub; [exact A3 | lia | lia]|].
  intros Hn'. exact (b7_hull_sub rd q n q' n' (A4 ltac:(lia)) Hq Hn' Hle).
Qed.

(* every byte of a C string and its NUL is mapped *)
Lemma b7_str_some : forall (rd : reader) p s a, sa_str rd p s -> p <= a <= p + Z.of_nat (length s) ->
  rd a <> None.
Proof.
  intros rd p s a [[Hz _] _] Ha.
  assert (Hi : (Z.to_nat (a - p) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (Hz _ Hi) as E. rewrite Z2Nat.id in E by lia.
  replace (p + (a - p)) with a in E by lia. rewrite E. discriminate.
Qed.

(** ** 8. The bridges from the interceptors' answers to SegModel (this lane's) *)
Lemma b7_first_at_strchr : forall l c j, ~ In 0 l -> c <> 0 -> RtSeg.first_at l c j -> strchr l c = Some j.
Proof.
  induction l as [|x l IH]; intros c j Hn Hc (Hj & Hx & Hf); cbn in Hj; [lia|].
  cbn [strchr]. destruct j as [|j].
  - cbn in Hx. subst x. rewrite Z.eqb_refl. reflexivity.
  - cbn [nth] in Hx. cbn [firstn] in Hf.
    assert (Hxc : x <> c) by (intros E; apply Hf; left; exact E).
    assert (Hx0 : x <> 0) by (intros E; apply Hn; left; exact E).
    apply Z.eqb_neq in Hxc. apply Z.eqb_neq in Hx0. rewrite Hxc, Hx0.
    rewrite (IH c j); [reflexivity | intros Hi; apply Hn; right; exact Hi | exact Hc |].
    split; [lia|]. split; [exact Hx|]. intros Hi. apply Hf. right. exact Hi.
Qed.
Lemma b7_notin_strchr : forall l c, ~ In 0 l -> ~ In c l -> strchr l c = None.
Proof.
  induction l as [|x l IH]; intros c Hn Hc; [reflexivity|]. cbn [strchr].
  assert (Hxc : x <> c) by (intros E; apply Hc; left; exact E).
  assert (Hx0 : x <> 0) by (intros E; apply Hn; left; exact E).
  apply Z.eqb_neq in Hxc. apply Z.eqb_neq in Hx0. rewrite Hxc, Hx0.
  rewrite IH; [reflexivity | intros Hi; apply Hn; right; exact Hi | intros Hi; apply Hc; right; exact Hi].
Qed.
Lemma b7_lc_lower : forall c, RtSeg.lc c = lower c.
Proof. intros c. unfold RtSeg.lc, lower. destruct ((65 <=? c) && (c <=? 90)); lia. Qed.
Lemma b7_ncase_seg : forall b, ~ In 0 b -> (RtSeg.strncase_eq 7 b S_segment <-> strncasecmp b S_segment 7 = 0).
Proof.
  intros b Hn.
  pose proof (strncasecmp_segment b Hn) as E.
  unfold RtSeg.strncase_eq.
  assert (ES : map RtSeg.lc (firstn 7 (S_segment ++ [0])) = [115; 101; 103; 109; 101; 110; 116])
    by (vm_compute; reflexivity).
  rewrite ES. rewrite S_segment_eq in *.
  destruct b as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 r]]]]]]];
    cbn [app firstn map length Nat.leb andb] in *;
    rewrite ?firstn_O in *;
    cbn [map length Nat.eqb ieq ieq_go andb] in *.
  1-7: split;
       [ intros H; exfalso; rewrite ?b7_lc_lower in H;
         first [ apply (f_equal (@length Z)) in H; cbn in H; lia
               | injection H as H0 H1 H2 H3 H4 H5 H6; cbn in H6; lia
               | congruence ]
       | intros H; rewrite H, Z.eqb_refl in E; discriminate E ].
  rewrite !b7_lc_lower.
  split.
  - intros H. injection H as H0 H1 H2 H3 H4 H5 H6. apply Z.eqb_eq. rewrite E.
    rewrite H0, H1, H2, H3, H4, H5, H6. reflexivity.
  - intros H. apply (proj2 (Z.eqb_eq _ _)) in H. rewrite E in H.
    repeat (let Hq := fresh "Hq" in apply andb_prop in H as [Hq H]; apply Z.eqb_eq in Hq; rewrite Hq).
    reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(** ** 1. The text bridge: sa_str (list Z) to astr_at / astr_atR (list byte) *)
Lemma b7_astr_of_sa : forall (W : world SEGS) mem q l,
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

(** ** A range parse_file's memory holds, as aread_ok *)
Lemma b7_read_ok_of_addr : forall (W : world SEGS) regs mem stk q n,
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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** The read-only view at the cut's reader *)
(* rt_rom_view (RtDefs.v) is arodata_okP's read-only-segment arm: in_rom is in_roP's first disjunct, and the
   two exclusions are the same (aerrno_cell B a unfolds to arodata_okP's errno range). As image A's segment-A5 file pf_a5_k.v
   a5_rom (commit 385fd095481f), from b7_obj in place of pf_base. *)
Lemma b7_rom : forall v pos lyc Sc Wc memc mdc, b7_st B v pos lyc Sc Wc memc mdc ->
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc [_ _ _ _ Hobj _].
  destruct Hobj as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
  intros a (sg & Hsg & Hw & Hr) Ho He.
  exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
Qed.

(** ** The stack at a cut of A7: sp0, s1 = pf_s1, and the windows of the calls made at s1 *)
Lemma b7_stk : forall v pos lyc Sc Wc memc mdc, b7_st B v pos lyc Sc Wc memc mdc ->
  pf_sp0 v mod 16 = 0 /\ alloc_ceiling <= ly_stk_lo lyc /\
  ly_stk_lo lyc + STK_reac_segconf_parse_file <= pf_sp0 v /\
  pf_s1 v mod 32 = 0 /\ pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ (pf_s1 v - pf_sp0 v) mod 16 = 0.
Proof.
  intros v pos lyc Sc Wc memc mdc [_ Hj Ely _ _ _].
  pose proof Hj as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (Hal16 & _ & Hceil & Hslo & _).
  subst lyc.
  pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D0.
  pose proof (Z.div_mod (pf_sp0 v - 0x160) 32 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (pf_sp0 v - 0x160) 32 ltac:(lia)) as M1.
  assert (E1 : pf_s1 v = 32 * ((pf_sp0 v - 0x160) / 32)) by (unfold pf_s1; lia).
  pose proof (Z.div_mod (pf_s1 v) 32 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_s1 v) 32 ltac:(lia)) as M2.
  pose proof (Z.div_mod (pf_s1 v - pf_sp0 v) 16 ltac:(lia)) as D3.
  pose proof (Z.mod_pos_bound (pf_s1 v - pf_sp0 v) 16 ltac:(lia)) as M3.
  split; [exact Hal16|]. split; [exact Hceil|]. split; [exact Hslo|].
  split; [lia|]. split; [lia|]. lia.
Qed.

(* a call made at s1 with a window stk <= 3 * ESTACK: the window lies above alloc_ceiling, fits the layout's
   stack, and fits parse_file's STK (12832 = 352 + 16 + 12464, SegInstB.STK_values) *)
Lemma b7_win : forall v pos lyc Sc Wc memc mdc stk, b7_st B v pos lyc Sc Wc memc mdc ->
  0 <= stk <= 3 * ESTACK ->
  ly_stk_lo lyc + stk <= pf_s1 v /\ alloc_ceiling <= pf_s1 v - stk /\
  stk - (pf_s1 v - pf_sp0 v) <= STK_reac_segconf_parse_file.
Proof.
  intros v pos lyc Sc Wc memc mdc stk H Hs.
  destruct (b7_stk v pos lyc Sc Wc memc mdc H) as (_ & Hc & Hlo & _ & Hs1 & _).
  pose proof STK_values as (_ & _ & _ & E & _). unfold ESTACK in Hs.
  rewrite E in Hlo |- *. lia.
Qed.

(* every byte of the class-5 frame is mapped (AR_laws' al_frames: a live frame's bytes are present) *)
Lemma b7_frame_some : forall v pos lyc Sc Wc memc mdc a, b7_st B v pos lyc Sc Wc memc mdc ->
  pf_F v pos <= a < pf_F v pos + 2048 -> rdW Wc memc a <> None.
Proof.
  intros v pos lyc Sc Wc memc mdc a H Ha.
  pose proof (b7_AR B v pos lyc Sc Wc memc mdc H) as HAR.
  pose proof (b7_fin B v pos lyc Sc Wc memc mdc H) as Hfin.
  destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (_ & _ & Hpres & _).
  destruct H as [_ _ Ely _ _ _]. subst lyc.
  apply (aview_some_of_apresent SEGS). apply (Hpres a).
  unfold pf_F in Ha. rewrite b7_fb5. exact Ha.
Qed.

(** ** 2. aread_ok of a range of buf at a call made at s1 *)
Lemma b7_read_ok_buf : forall v pos lyc Sc Wc memc mdc regsc stk q n, b7_st B v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> 0 <= stk <= 3 * ESTACK ->
  b7_buf v pos <= q -> 0 <= n -> q + n <= b7_buf v pos + 512 ->
  aread_ok SEGS stk Wc regsc memc q n.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc stk q n H Hsp Hs Hq Hn Hqn.
  pose proof (b7_addr_buf B v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn) as HA.
  destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc H) as (_ & F2 & _ & _).
  destruct (b7_win v pos lyc Sc Wc memc mdc stk H Hs) as (_ & W2 & _).
  unfold b7_buf, PF_O_BUF in Hq, Hqn.
  apply b7_read_ok_of_addr; [exact HA | lia | | rewrite Hsp; lia].
  intros a Ha. apply (b7_frame_some v pos lyc Sc Wc memc mdc a H). lia.
Qed.

(** ** 3. amem_range of a range of the class-5 frame *)
Lemma b7_amem_frame : forall v pos lyc Sc Wc memc mdc q n, b7_st B v pos lyc Sc Wc memc mdc ->
  pf_F v pos <= q -> 0 <= n -> q + n <= pf_F v pos + 2048 -> amem_range q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc H) as (H1 & H2 & H3 & _).
  apply amem_range_high; [lia| |lia].
  destruct H3 as [_ [Hlo | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
    [left; lia | right; lia].
Qed.

(** ** 4. atail_vis at a NUL inside buf *)
Lemma b7_tail_vis_buf : forall v pos lyc Sc Wc memc mdc e, b7_st B v pos lyc Sc Wc memc mdc ->
  b7_buf v pos <= e < b7_buf v pos + 512 -> atail_vis SEGS Wc memc e.
Proof.
  intros v pos lyc Sc Wc memc mdc e H He a Ha.
  destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc H) as (H1 & _ & _ & H4).
  unfold b7_buf, PF_O_BUF in He.
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D0.
  pose proof (Z.div_mod e 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M1.
  apply (b7_frame_some v pos lyc Sc Wc memc mdc a H). lia.
Qed.

(** ** 5. The runtime-call pre-state at a call of A7 *)
Lemma b7_ecall_pre_buf : forall v pos lyc Sc Wc memc mdc regsc stk, b7_st B v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> ESTACK <= stk <= 3 * ESTACK ->
  YK0s.ret_ok (getr regsc 1) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  ecall_pre_stk SEGS B stk lyc Sc Wc regsc memc mdc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc stk H Hsp Hs Hra Hgp Htp.
  destruct (b7_stk v pos lyc Sc Wc memc mdc H) as (_ & _ & _ & _ & Hs1 & Hal).
  destruct (b7_win v pos lyc Sc Wc memc mdc stk H ltac:(unfold ESTACK in *; lia)) as (_ & _ & Hbud).
  destruct H as [_ Hj _ _ _ _].
  apply (PaArt.ecall_pre_stk_at SEGS B stk STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 regsc (pf_s1 v - pf_sp0 v) Hj);
    [lia | exact Hal | lia | exact (proj1 Hs) | exact Hbud | exact Hra | exact Hgp | exact Htp].
Qed.

(** ** A literal of PARSE_FILE_LITS at a call made at s1 (sa_lit of b7_obj: sa_pinned, sa_img, the bytes) *)
Lemma b7_lit_read : forall v pos lyc Sc Wc memc mdc regsc stk s m, b7_st B v pos lyc Sc Wc memc mdc ->
  In s PARSE_FILE_LITS -> spZ regsc = pf_s1 v -> 0 <= stk <= 3 * ESTACK ->
  0 <= m <= Z.of_nat (length s) + 1 ->
  0 < seg_litA_rc s /\
  astr_at SEGS Wc memc (seg_litA_rc s) (seg_spec.zb s) /\ astr_len (seg_spec.zb s) = Z.of_nat (length s) /\
  aread_ok SEGS stk Wc regsc memc (seg_litA_rc s) m /\
  amem_range (seg_litA_rc s) (Z.of_nat (length s) + 8) /\
  atail_vis SEGS Wc memc (seg_litA_rc s + Z.of_nat (length s)).
Proof.
  intros v pos lyc Sc Wc memc mdc regsc stk s m H Hin Hsp Hs Hm.
  pose proof (b7_AR B v pos lyc Sc Wc memc mdc H) as HAR.
  destruct (b7_win v pos lyc Sc Wc memc mdc stk H Hs) as (_ & W2 & _).
  destruct H as [_ _ _ _ Hobj _].
  destruct Hobj as (_ & _ & _ & _ & _ & _ & HL & _).
  destruct (HL s Hin) as (Ha & Hstr & Hp & _ & Hi).
  destruct (b7_astr_of_sa Wc memc _ s Hstr) as (HA & _ & HLn & _ & HT).
  pose proof (Hp lyc Sc Wc memc mdc HAR) as HP.
  pose proof (proj1 (Hi (seg_litA_rc s + Z.of_nat (length s)) ltac:(lia))) as Himg.
  pose proof (pa_img_range _ Himg) as Hrg.
  pose proof asan_consts as (C1 & _ & _ & _ & C5). unfold kImgEnd in Hrg.
  split; [exact Ha|]. split; [exact HA|]. split; [exact HLn|].
  split; [|split].
  - apply b7_read_ok_of_addr.
    + apply (b7_sa_addr_sub _ _ _ _ _ HP); lia.
    + lia.
    + intros a Ha'. apply (b7_str_some _ _ _ a Hstr). lia.
    + rewrite Hsp. lia.
  - unfold amem_range. left. rewrite C5. lia.
  - rewrite HLn in HT. exact HT.
Qed.

(** ** 6. The premise lists of the three interceptor calls *)
(* strchr(lp, ']') at 0x883bc (0x883b4 `li a1,93`, 0x883b8 `mv a0,s7`): RtSeg.astrchr_realizes's
   premises in its order, for the C string l at x in buf (at HDR, x = lp and l = the trimmed line) *)
Lemma b7_strchr_pre_883bc : forall v pos lyc Sc Wc memc mdc regsc x l,
  b7_st B v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 x -> getr regsc 11 = w64 0x5d ->
  sa_str (rdW Wc memc) x l -> pf_inb (pf_F v pos + PF_O_BUF) x l ->
  ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc Wc regsc memc mdc /\
  getr regsc 10 = w64 x /\ getr regsc 11 = w64 0x5d /\ 0 < 0x5d < 256 /\ 0 < x /\
  astr_at SEGS Wc memc x (seg_spec.zb l) /\
  aread_ok SEGS (2 * ESTACK) Wc regsc memc x (astr_len (seg_spec.zb l) + 1) /\
  amem_range x (astr_len (seg_spec.zb l) + 8) /\
  atail_vis SEGS Wc memc (x + astr_len (seg_spec.zb l)) /\
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc x l H Hsp Hra Hgp Htp H10 H11 Hs [Hb Hl].
  destruct (b7_astr_of_sa Wc memc x l Hs) as (HA & _ & HLn & _ & HT).
  destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  unfold PF_O_BUF in Hb, Hl.
  split; [exact (b7_ecall_pre_buf v pos lyc Sc Wc memc mdc regsc (2 * ESTACK) H Hsp
                   ltac:(unfold ESTACK; lia) Hra Hgp Htp)|].
  split; [exact H10|]. split; [exact H11|]. split; [lia|]. split; [lia|].
  split; [exact HA|].
  split; [rewrite HLn; apply (b7_read_ok_buf v pos lyc Sc Wc memc mdc regsc);
          [exact H | exact Hsp | unfold ESTACK; lia | unfold b7_buf, PF_O_BUF; lia | lia
          | unfold b7_buf, PF_O_BUF; lia]|].
  split; [rewrite HLn; apply (b7_amem_frame v pos lyc Sc Wc memc mdc); [exact H | lia | lia | lia]|].
  split; [exact HT|].
  exact (b7_rom v pos lyc Sc Wc memc mdc H).
Qed.

(* strncasecmp(body, "segment", 7) at 0x88500 (0x884f0-0x884f4 a1 = .str.6 0x214a0 = seg_litA_rc S_segment,
   0x884f8 `li a2,7`, 0x884fc `mv a0,s3`): RtSeg.astrncasecmp_realizes's premises in its order, for
   the C string l at x in buf (the trimmed body); the literal's facts from b7_obj's sa_lit *)
Lemma b7_ncase_pre_88500 : forall v pos lyc Sc Wc memc mdc regsc x l,
  b7_st B v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 x -> getr regsc 11 = w64 (seg_litA_rc S_segment) -> getr regsc 12 = w64 7 ->
  sa_str (rdW Wc memc) x l -> pf_inb (pf_F v pos + PF_O_BUF) x l ->
  ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc Wc regsc memc mdc /\
  getr regsc 10 = w64 x /\ getr regsc 11 = w64 (seg_litA_rc S_segment) /\ getr regsc 12 = w64 7 /\
  0 <= 7 < 2 ^ 32 /\ 0 < x /\ 0 < seg_litA_rc S_segment /\
  astr_at SEGS Wc memc x (seg_spec.zb l) /\ astr_at SEGS Wc memc (seg_litA_rc S_segment) (seg_spec.zb S_segment) /\
  aread_ok SEGS (2 * ESTACK) Wc regsc memc x (Z.min 7 (astr_len (seg_spec.zb l) + 1)) /\
  amem_range x (astr_len (seg_spec.zb l) + 8) /\
  aread_ok SEGS (2 * ESTACK) Wc regsc memc (seg_litA_rc S_segment)
    (Z.min 7 (astr_len (seg_spec.zb S_segment) + 1)) /\
  amem_range (seg_litA_rc S_segment) (astr_len (seg_spec.zb S_segment) + 8) /\
  atail_vis SEGS Wc memc (x + astr_len (seg_spec.zb l)) /\
  atail_vis SEGS Wc memc (seg_litA_rc S_segment + astr_len (seg_spec.zb S_segment)) /\
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc x l H Hsp Hra Hgp Htp H10 H11 H12 Hs [Hb Hl].
  (* "segment" is the seventh text of PARSE_FILE_LITS (reac_segconf_parse_file_c.v:126) *)
  assert (HIN : In S_segment PARSE_FILE_LITS)
    by (unfold PARSE_FILE_LITS; apply in_or_app; left; do 6 right; left; reflexivity).
  assert (L7 : Z.of_nat (length S_segment) = 7) by (vm_compute; reflexivity).
  assert (L7b : astr_len (seg_spec.zb S_segment) = 7)
    by (unfold astr_len, seg_spec.zb; rewrite length_map; exact L7).
  destruct (b7_lit_read v pos lyc Sc Wc memc mdc regsc (2 * ESTACK) S_segment
    (Z.min 7 (astr_len (seg_spec.zb S_segment) + 1)) H HIN Hsp ltac:(unfold ESTACK; lia)
    ltac:(rewrite L7b, L7; lia)) as (Ly0 & LyA & LyL & LyR & LyM & LyT).
  destruct (b7_astr_of_sa Wc memc x l Hs) as (HA & _ & HLn & _ & HT).
  destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  unfold PF_O_BUF in Hb, Hl.
  split; [exact (b7_ecall_pre_buf v pos lyc Sc Wc memc mdc regsc (2 * ESTACK) H Hsp
                   ltac:(unfold ESTACK; lia) Hra Hgp Htp)|].
  split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [lia|]. split; [lia|].
  split; [exact Ly0|]. split; [exact HA|]. split; [exact LyA|].
  split; [rewrite HLn; apply (b7_read_ok_buf v pos lyc Sc Wc memc mdc regsc);
          [exact H | exact Hsp | unfold ESTACK; lia | unfold b7_buf, PF_O_BUF; lia | lia
          | unfold b7_buf, PF_O_BUF; lia]|].
  split; [rewrite HLn; apply (b7_amem_frame v pos lyc Sc Wc memc mdc); [exact H | lia | lia | lia]|].
  split; [exact LyR|].
  split; [rewrite LyL; exact LyM|].
  split; [exact HT|].
  split; [rewrite LyL; exact LyT|].
  exact (b7_rom v pos lyc Sc Wc memc mdc H).
Qed.

(* strlen(name) at 0x887b4 (0x887b0 `mv a0,s7`): RtString.astrlen_realizes's premises in its order, for the
   C string l at x in buf (the trimmed name) *)
Lemma b7_strlen_pre_887b4 : forall v pos lyc Sc Wc memc mdc regsc x l,
  b7_st B v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 x ->
  sa_str (rdW Wc memc) x l -> pf_inb (pf_F v pos + PF_O_BUF) x l ->
  ecall_pre_stk SEGS B ESTACK lyc Sc Wc regsc memc mdc /\
  getr regsc 10 = w64 x /\ 0 < x /\
  astr_at SEGS Wc memc x (seg_spec.zb l) /\
  aread_ok SEGS ESTACK Wc regsc memc x (astr_len (seg_spec.zb l) + 1) /\
  atail_vis SEGS Wc memc (x + astr_len (seg_spec.zb l)) /\
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc x l H Hsp Hra Hgp Htp H10 Hs [Hb Hl].
  destruct (b7_astr_of_sa Wc memc x l Hs) as (HA & _ & HLn & _ & HT).
  destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  unfold PF_O_BUF in Hb, Hl.
  split; [exact (b7_ecall_pre_buf v pos lyc Sc Wc memc mdc regsc ESTACK H Hsp
                   ltac:(unfold ESTACK; lia) Hra Hgp Htp)|].
  split; [exact H10|]. split; [lia|].
  split; [exact HA|].
  split; [rewrite HLn; apply (b7_read_ok_buf v pos lyc Sc Wc memc mdc regsc);
          [exact H | exact Hsp | unfold ESTACK; lia | unfold b7_buf, PF_O_BUF; lia | lia
          | unfold b7_buf, PF_O_BUF; lia]|].
  split; [exact HT|].
  exact (b7_rom v pos lyc Sc Wc memc mdc H).
Qed.

(** ** 7. After an art_post call: b7_st again at the call's new memory *)
(* the caller's objects carry over to a reader that agrees below alloc_ceiling, at a state with AR: the text's
   and the block's bytes and shadow (sa_addr re-derived from the live blocks, reac_segconf_parse.v
   sa_addr_of_heap), the catalogue, the literals, the read-only window, the stack-protector cells *)
Lemma b7_obj_low : forall v lyc Sc (Wc : world SEGS) memc memc' mdc',
  AR SEGS B lyc Sc Wc memc' mdc' -> pf_obj B v lyc Sc (rdW Wc memc) ->
  (forall a, 0 <= a < alloc_ceiling -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_obj B v lyc Sc (rdW Wc memc').
Proof.
  intros v lyc Sc Wc memc memc' mdc' HAR' (Ht & At & Ht2 & Ac & Hc & CAT & LITS & ROD & SSP) LK.
  assert (Ht0 : 0 <= p_t v) by (destruct At; lia).
  assert (Hc0 : 0 <= p_c v) by (destruct Ac; lia).
  destruct (reac_segconf_parse.sa_addr_of_heap B lyc Sc Wc memc' mdc' (p_t v) (pf_len v) HAR' Ht2 Ht0
    ltac:(unfold pf_len; lia)) as [At' Hte].
  destruct (reac_segconf_parse.sa_addr_of_heap B lyc Sc Wc memc' mdc' (p_c v) seg_spec.SEG_C_SIZE HAR' Hc Hc0
    ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [Ac' _].
  split; [apply (reac_segconf_parse.sa_str_low _ _ _ _ Ht); [exact Ht0 | unfold pf_len in Hte; lia | exact LK]|].
  split; [exact At'|]. split; [exact Ht2|]. split; [exact Ac'|]. split; [exact Hc|].
  split; [exact (reac_segconf_parse.sa_cat_low B _ _ CAT LK)|].
  split; [intros x Hx; exact (reac_segconf_parse.sa_lit_low B _ _ _ _ (LITS x Hx) LK)|].
  split; [|exact (reac_segconf_parse.sa_ssp_low _ _ SSP LK)].
  intros a Hro Ho He.
  assert (Ha : 0 <= a < alloc_ceiling).
  { pose proof asan_consts as (C1 & _).
    destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
    - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
      pose proof (pa_img_range a Hi) as Hrg. unfold kImgEnd in Hrg. lia.
    - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. lia. }
  rewrite (LK a Ha). exact (ROD a Hro Ho He).
Qed.

(* What aj_art_at (PaArt.v) / aj_art_atF (PaFx.v) return after a call made at sp0 + o with window stk and no
   written cells (Eb = fun _ => False): the journal at the new memory memc' and the keep clause outside
   [sp0 + o - stk, sp0 + o). Every fact of b7_st other than the journal is about bytes below alloc_ceiling
   (the heap text and block, image literals and cells, the frame's shadow), which the journal's astk_ok puts
   below sp0 - STK <= sp0 + o - stk, so the keep clause keeps them all. *)
Lemma b7_keep_art : forall v pos lyc Sc Wc memc mdc memc' mdc' o stk,
  b7_st B v pos lyc Sc Wc memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  stk - o <= STK_reac_segconf_parse_file ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_sp0 v + o - stk <= a < pf_sp0 v + o) -> ~ (fun _ : Z => False) a ->
     rdW Wc memc' a = rdW Wc memc a) ->
  b7_st B v pos lyc Sc Wc memc' mdc'.
Proof.
  intros v pos lyc Sc Wc memc mdc memc' mdc' o stk H HJ' Hbud HK.
  destruct (b7_stk v pos lyc Sc Wc memc mdc H) as (_ & Hceil & Hslo & _).
  destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  pose proof asan_consts as (C1 & C2 & _ & C4 & C5).
  assert (LK : forall a, 0 <= a < alloc_ceiling -> rdW Wc memc' a = rdW Wc memc a).
  { intros a Ha. apply HK; [lia | lia | intros Hf; exact Hf]. }
  pose proof (proj1 HJ') as HAR'.
  pose proof (shadow_addr_bounds (pf_F v pos) ltac:(rewrite C4; lia)) as HSB.
  rewrite C2, C5 in HSB.
  destruct H as [Hcx _ Ely Hperm Hobj Hfsh].
  constructor.
  - exact Hcx.
  - exact HJ'.
  - exact Ely.
  - exact Hperm.
  - exact (b7_obj_low v lyc Sc Wc memc memc' mdc' HAR' Hobj LK).
  - intros i Hi.
    assert (HS : 0 <= pf_SH v pos + i < alloc_ceiling) by (unfold pf_SH; lia).
    rewrite (LK _ HS). exact (Hfsh i Hi).
Qed.

End e.
End f.
End d.
